#!/usr/bin/env python3
"""Compare the full public namespace API with a built baseline checkout.

Run both builds first, then: python3 scripts/check_public_api.py BASELINE_DIRECTORY
This is a migration check, not an assertion that definition bodies are unchanged.
The lexical inventory is an additional missing-target guard, not the comparison
boundary. Every compiled AsymmetricTensor namespace declaration is compared,
including structures, constructors, recursors, projections and instances.
"""
import argparse
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
    if args.output:
        report = {"source_names": len(before_names), "reference": before,
                  "integrated": after, "differences": delta}
        (args.output / "api-comparison.json").write_text(json.dumps(report, indent=2) + "\n")
    for label, names in delta.items():
        for name in sorted(names):
            print(f"{label}: {name}")
    if any(delta.values()):
        sys.exit(1)
    print(f"API_COMPATIBLE: {len(before_names)} source-declared names and "
          f"all {len(before)} compiled AsymmetricTensor namespace declarations; "
          "identical declaration kinds, full elaborated types and universe parameters "
          "after binder-hygiene normalization (including generated APIs and instances).")


if __name__ == "__main__":
    main()
