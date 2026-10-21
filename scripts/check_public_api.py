#!/usr/bin/env python3
"""Compare the full public namespace API with a built baseline checkout.

Run both builds first, then: python3 scripts/check_public_api.py BASELINE_DIRECTORY
This is a migration check, not an assertion that definition bodies are unchanged.
The lexical inventory is an additional missing-target guard, not the comparison
boundary. Every compiled AsymmetricTensor namespace declaration is compared,
including structures, constructors, recursors, projections and instances.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from source_boundary import production_sources

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:noncomputable\s+)?"
    r"(?:def|abbrev|opaque|axiom|lemma|theorem|alias)\s+([^\s(:]+)",
    re.MULTILINE,
)
AUXILIARY_THEOREM = re.compile(r"\._(?:simp|abel|proof)_[0-9]+(?:_[0-9]+)*$")
NULLARY_CONSTANT = re.compile(r"\(Lean\.Expr\.const `([^\s()]+) \[\]\)")


def inventory(root):
    files = production_sources(root)
    names = ["AsymmetricTensor." + name for path in files for name in DECL.findall(path.read_text())]
    if len(names) != len(set(names)):
        raise RuntimeError(f"Duplicate source declaration in {root}")
    return set(names)


def parse_snapshot(output):
    entries = {}
    for line in output.splitlines():
        if line.startswith("API|"):
            _, name, kind, levels, expression = line.split("|", 4)
            if name in entries:
                raise RuntimeError(f"Duplicate elaborated declaration: {name}")
            entries[name] = (kind, levels, expression)
    if not entries:
        raise RuntimeError("No elaborated API snapshot")
    return entries


def snapshot(root, log=None):
    result = subprocess.run(
        ["lake", "env", "lean", str(ROOT / "tests/ApiSnapshot.lean")],
        cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False,
    )
    if log is not None:
        log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f"API snapshot failed for {root}: exit {result.returncode}\n"
                           + result.stdout)
    return parse_snapshot(result.stdout)


def differences(before_names, after_names, before, after):
    return {
        "Removed source declaration": sorted(before_names - after_names),
        "Added source declaration": sorted(after_names - before_names),
        "Missing elaborated source declaration": sorted(
            (before_names - before.keys()) | (after_names - after.keys())),
        "Removed compiled declaration": sorted(before.keys() - after.keys()),
        "Added compiled declaration": sorted(after.keys() - before.keys()),
        "Changed kind/type/universes": sorted(
            name for name in before.keys() & after.keys() if before[name] != after[name]),
    }


def auxiliary_theorems(entries, source_names):
    """Only the independently diagnosed compiler helper class, never source API.

    Lean's branch-local auxiliary cache is not serialized in .olean files.
    Splitting a legacy monolith changes helper allocation, visibility and names.
    Keep these entries in the full inventory; only their name identity is not a
    public compatibility contract. A similarly named axiom/definition is NOT a
    helper, and source-declared names are never classified here.
    """
    return {name: entry for name, entry in entries.items()
            if name not in source_names and entry[0] == "theorem"
            and AUXILIARY_THEOREM.search(name)}


def normalize_proof_references(entry, helpers):
    """Canonicalize a closed helper proof by its exact recorded proposition.

    This is a comparison representation, not a Lean term or an inserted proof.
    No type reduction, proposition erasure or arbitrary constant renaming occurs.
    Only zero-universe constants with actual theorem metadata are supported;
    unfamiliar expressions stay literal and therefore fail closed on a delta.
    Every affected public type additionally requires a kernel certificate below.
    """
    def replace(match):
        proof = helpers.get(match.group(1))
        if proof is None or proof[0] != "theorem" or proof[1] != "[]":
            return match.group(0)
        identity = hashlib.sha256(json.dumps(proof, ensure_ascii=False).encode()).hexdigest()
        return f"(PROOF_OF_EXACT_RECORDED_TYPE {identity})"
    return entry[0], entry[1], NULLARY_CONSTANT.sub(replace, entry[2])


def public_comparison(before_names, after_names, before, after):
    source_names = before_names | after_names
    before_helpers = auxiliary_theorems(before, source_names)
    after_helpers = auxiliary_theorems(after, source_names)
    before_public = {n: normalize_proof_references(e, before_helpers)
                     for n, e in before.items() if n not in before_helpers}
    after_public = {n: normalize_proof_references(e, after_helpers)
                    for n, e in after.items() if n not in after_helpers}
    delta = differences(before_names, after_names, before_public, after_public)
    certificates = sorted(n for n in before_public.keys() & after_public.keys()
                          if before[n] != after[n] and before_public[n] == after_public[n])
    return {"reference_count": len(before_public), "integrated_count": len(after_public),
            "reference_auxiliary_theorems": before_helpers,
            "integrated_auxiliary_theorems": after_helpers,
            "differences": delta, "kernel_certificates_required": certificates}


def certificate_source(names, before):
    """Ask the kernel to type each candidate constant at its full raw type.

    The raw expression is used verbatim, without proof-name normalization.
    No declaration is added to production, no axiom/sorry is introduced, and
    direct Kernel.Environment.addDecl cannot substitute an axiom on failure.
    """
    commands = ["import AsymmetricTensor", "import Lean", "open Lean Elab Command",
                "set_option maxRecDepth 10000", "set_option maxHeartbeats 2000000"]
    for index, name in enumerate(names):
        _, levels, expression = before[name]
        # reprStr emits Lean constructors; snapshot expressions are compiler
        # output, not source text from a PR body or an external instruction.
        raw_expression = expression.replace("\\n", "\n")
        indented_expression = "\n".join("    " + line for line in raw_expression.splitlines())
        commands.append(f'''run_cmd do
  let rawType : Expr :=
{indented_expression}
  let levelParams : List Name := {levels}
  let declaration := Declaration.defnDecl {{
    name := `ReferenceTypeCertificate.c{index}
    levelParams := levelParams
    type := rawType
    value := mkConst `{name} (levelParams.map Level.param)
    hints := .opaque
    safety := .safe
  }}
  let options := (← getOptions).setBool `debug.skipKernelTC false
  match (← getEnv).toKernelEnv.addDecl options declaration with
  | .ok _ => logInfo "KERNEL_TYPE_EQUIVALENT: {name}"
  | .error _ => throwError "KERNEL_TYPE_MISMATCH: {name}"
''')
    return "\n".join(commands) + "\n"


def certify_public_types(names, before, output):
    if not names:
        return
    if output is None:
        raise RuntimeError("Changed proof references require a retained --output certificate")
    path = output / "ApiCertificates.lean"
    path.write_text(certificate_source(names, before))
    result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    (output / "kernel-type-certificates.log").write_text(result.stdout)
    if result.returncode:
        raise RuntimeError("Kernel type certificates failed:\n" + result.stdout)
    for name in names:
        if f"KERNEL_TYPE_EQUIVALENT: {name}" not in result.stdout:
            raise RuntimeError(f"Missing kernel type certificate: {name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("--output", type=Path,
                        help="retain raw snapshots and machine-readable comparison")
    args = parser.parse_args()
    baseline = args.baseline.resolve()
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
    before_names, after_names = inventory(baseline), inventory(ROOT)
    before = snapshot(baseline, args.output / "reference-api.log" if args.output else None)
    after = snapshot(ROOT, args.output / "integrated-api.log" if args.output else None)
    delta = differences(before_names, after_names, before, after)
    public = public_comparison(before_names, after_names, before, after)
    report = {"source_names": len(before_names), "reference": before,
              "integrated": after, "differences": delta, "public_comparison": public,
              "kernel_certificate_status": "pending"}
    if args.output:
        (args.output / "api-comparison.json").write_text(json.dumps(report, indent=2) + "\n")
    for label, names in delta.items():
        for name in sorted(names):
            print(f"{label}: {name}")
    if any(public["differences"].values()):
        for label, names in public["differences"].items():
            for name in names:
                print(f"PUBLIC_API_FAILURE: {label}: {name}")
        sys.exit(1)
    certify_public_types(public["kernel_certificates_required"], before, args.output)
    report["kernel_certificate_status"] = "passed"
    if args.output:
        (args.output / "api-comparison.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"API_COMPATIBLE: {len(before_names)} source-declared names and "
          f"all {public['reference_count']} public/generated API declarations; "
          "identical declaration kinds, full elaborated types and universe parameters "
          "after binder-hygiene and certified proof-reference normalization. "
          f"Complete unfiltered inventories retained: {len(before)} raw, {len(after)} integrated.")


if __name__ == "__main__":
    main()
