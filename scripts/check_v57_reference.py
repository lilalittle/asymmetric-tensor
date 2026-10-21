#!/usr/bin/env python3
"""Build the immutable v5.7 author reference and verify integration fidelity.

Uses the already provisioned, revision-checked dependency packages. The raw
reference has an independent first-party build directory and no split modules.
This is a strict verification gate, not an advisory author diagnostic.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE_COMMIT = "5be4d7101a1ab28624872a8f7e5001ea8ebb8449"
SOURCE_PATH = "AsymmetricTensor/Asymmetric Tensor v5.7.lean"
SOURCE_BLOB = "e03381d54d82fcfde0577ec33aa5f4923a2f0788"
SOURCE_SHA256 = "2c39b9ad9a6c75314b6fccf39157962588e58620b0beebe5dd54e6456a12c558"
REVIEW_URL = "https://github.com/lilalittle/asymmetric-tensor/issues/4#issuecomment-6319297490"
LOCK_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
SUMMARY_BEFORE = "Lorentz boost symmetry breaking (`α_s = √(1 - β^2)`)".encode()
SUMMARY_AFTER = (
    "Lorentz boost symmetry breaking (`α_s = 1` under the stated scalar residual hypotheses)"
).encode()


def git_blob(source):
    return hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest()


def validate_source(source):
    if git_blob(source) != SOURCE_BLOB or hashlib.sha256(source).hexdigest() != SOURCE_SHA256:
        raise RuntimeError("The immutable v5.7 reference does not match its reviewed hashes")


def validate_upload(source, candidate):
    if source.count(SUMMARY_BEFORE) != 1:
        raise RuntimeError("Expected exactly one reviewed overview correction site")
    if candidate != source.replace(SUMMARY_BEFORE, SUMMARY_AFTER, 1):
        raise RuntimeError("Candidate author upload differs beyond the approved overview correction")


def prepare_reference(root, reference, source):
    """Copy only configuration and the monolith; share only dependency packages."""
    (reference / "AsymmetricTensor.lean").write_bytes(source)
    for name in LOCK_FILES:
        (reference / name).write_bytes((root / name).read_bytes())
    packages = root / ".lake" / "packages"
    if not packages.is_dir():
        raise RuntimeError("Pinned dependency packages are absent; provision the existing CI cache first")
    (reference / ".lake").mkdir()
    (reference / ".lake" / "packages").symlink_to(packages.resolve(), target_is_directory=True)
    if (reference / "AsymmetricTensor").exists() or (reference / ".lake" / "build").exists():
        raise RuntimeError("Reference must start without split source or first-party build artifacts")


def dependency_revisions(root):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    revisions = {}
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise RuntimeError(f"Unreviewed non-git dependency: {package['name']}")
        path = root / manifest["packagesDir"] / package["name"]
        actual = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"],
                                         text=True).strip()
        if actual != package["rev"]:
            raise RuntimeError(f"Dependency {package['name']} is {actual}, expected {package['rev']}")
        revisions[package["name"]] = actual
    return revisions


def run_logged(command, cwd, log):
    print(f"REFERENCE_CHECK: {' '.join(map(str, command))} (log: {log.name})", flush=True)
    with log.open("w") as output:
        try:
            result = subprocess.run(command, cwd=cwd, stdout=output, stderr=subprocess.STDOUT,
                                    timeout=1200, check=False)
        except (OSError, subprocess.TimeoutExpired) as exc:
            output.write(f"\nReference verification could not complete: {exc}\n")
            raise RuntimeError(f"Reference verification unavailable; see {log}") from exc
    if result.returncode:
        # Keep the full retained log; show enough tail for ordinary Actions inspection.
        print("\n".join(log.read_text().splitlines()[-80:]), file=sys.stderr)
        raise RuntimeError(f"Reference verification failed with exit {result.returncode}; see {log}")


def check_locks(root, reference, expected):
    for name, contents in expected.items():
        if (root / name).read_bytes() != contents or (reference / name).read_bytes() != contents:
            raise RuntimeError(f"Reference verification changed dependency configuration: {name}")


def main():
    output = ROOT / ".lake" / "v57-reference-evidence"
    output.mkdir(parents=True, exist_ok=True)
    # A run must not inherit a previous successful status or old API snapshots.
    for name in ("manifest.json", "reference-build.log", "source-comparison.log",
                 "api-comparison.log", "reference-api.log", "integrated-api.log",
                 "api-comparison.json"):
        (output / name).unlink(missing_ok=True)
    evidence = {"source_commit": SOURCE_COMMIT, "source_path": SOURCE_PATH,
                "source_blob": SOURCE_BLOB, "source_sha256": SOURCE_SHA256,
                "source_review": REVIEW_URL, "status": "running"}
    try:
        evidence["candidate_commit"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        evidence["candidate_tree"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD^{tree}"], cwd=ROOT, text=True).strip()
        source = subprocess.check_output(["git", "show", f"{SOURCE_COMMIT}:{SOURCE_PATH}"], cwd=ROOT)
        validate_source(source)
        candidate = (ROOT / SOURCE_PATH).read_bytes()
        validate_upload(source, candidate)
        evidence["candidate_upload_blob"] = git_blob(candidate)
        evidence["candidate_upload_sha256"] = hashlib.sha256(candidate).hexdigest()
        evidence["approved_overview_change"] = {
            "before": SUMMARY_BEFORE.decode(), "after": SUMMARY_AFTER.decode()}
        evidence["dependency_revisions"] = dependency_revisions(ROOT)
        locks = {name: (ROOT / name).read_bytes() for name in LOCK_FILES}
        for name, contents in locks.items():
            pinned = subprocess.check_output(["git", "show", f"{SOURCE_COMMIT}:{name}"], cwd=ROOT)
            if contents != pinned:
                raise RuntimeError(f"Candidate changes the reviewed dependency configuration: {name}")
        evidence["configuration_sha256"] = {
            name: hashlib.sha256(contents).hexdigest() for name, contents in locks.items()}
        with tempfile.TemporaryDirectory(prefix="v57-reference-", dir=ROOT / ".lake") as directory:
            reference = Path(directory)
            prepare_reference(ROOT, reference, source)
            try:
                run_logged(["lake", "build", "AsymmetricTensor"], reference,
                           output / "reference-build.log")
                run_logged([sys.executable, str(ROOT / "scripts/check_module_source.py"),
                            str(reference)], ROOT, output / "source-comparison.log")
                run_logged([sys.executable, str(ROOT / "scripts/check_public_api.py"),
                            str(reference), "--output", str(output)], ROOT,
                           output / "api-comparison.log")
            finally:
                check_locks(ROOT, reference, locks)
        # Also reject unexpected checkout-revision drift in shared dependencies.
        if dependency_revisions(ROOT) != evidence["dependency_revisions"]:
            raise RuntimeError("Dependency revisions changed during reference verification")
        evidence["status"] = "passed"
        print("V57_REFERENCE_VERIFIED: immutable author build, source tokens/docstrings, "
              "full compiled namespace API and unchanged dependency pins")
        return 0
    except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
        evidence["status"] = "failed"
        evidence["error"] = str(exc)
        print(f"V57_REFERENCE_FAILED: {exc}", file=sys.stderr)
        return 1
    finally:
        (output / "manifest.json").write_text(json.dumps(evidence, indent=2) + "\n")


if __name__ == "__main__":
    sys.exit(main())
