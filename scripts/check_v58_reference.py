#!/usr/bin/env python3
"""Build the immutable v5.8 author reference and verify integration fidelity.

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

from check_public_api import differences, inventory, parse_snapshot, snapshot
from source_boundary import is_author_draft

ROOT = Path(__file__).resolve().parents[1]
SOURCE_COMMIT = "38f4fb06a6b21fe38557afa90bc10aa36dde2f68"
SOURCE_PATH = "AsymmetricTensor/Asymmetric Tensor v5.8.lean"
SOURCE_BLOB = "9040d932eb4ed68e7c5ccb67e490383cf0b9527c"
SOURCE_SHA256 = "aff0033565c3f41139e3b5c26491542b885643bf14eb116aac0dafecf14b4102"
REVIEW_URL = "https://github.com/lilalittle/asymmetric-tensor/issues/4#issuecomment-6389877444"
# Build the exact previous stable umbrella/modules, not its monolithic author upload.
# The full compiled delta is retained separately from source-to-integration fidelity.
STABLE_COMMIT = "8ad507caa6625c810507a01c031040833af9c318"
STABLE_TREE = "3e0a27fb8d5e095e6f0b9b65b4fa19b4815fcba5"
LOCK_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")


def git_blob(source):
    return hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest()


def validate_source(source):
    if git_blob(source) != SOURCE_BLOB or hashlib.sha256(source).hexdigest() != SOURCE_SHA256:
        raise RuntimeError("The immutable v5.8 reference does not match its reviewed hashes")


def validate_upload(source, candidate):
    if candidate != source:
        raise RuntimeError("Candidate author upload differs from the immutable v5.8 source bytes")


def prepare_dependency_workspace(root, reference):
    """Share only existing dependency packages, never first-party build outputs."""
    for name in LOCK_FILES:
        (reference / name).write_bytes((root / name).read_bytes())
    packages = root / ".lake" / "packages"
    if not packages.is_dir():
        raise RuntimeError("Pinned dependency packages are absent; provision the existing CI cache first")
    (reference / ".lake").mkdir()
    (reference / ".lake" / "packages").symlink_to(packages.resolve(), target_is_directory=True)
    if (reference / ".lake" / "build").exists():
        raise RuntimeError("Reference must start without first-party build artifacts")


def prepare_reference(root, reference, source):
    """Copy only configuration and the monolith; share only dependency packages."""
    (reference / "AsymmetricTensor.lean").write_bytes(source)
    prepare_dependency_workspace(root, reference)
    if (reference / "AsymmetricTensor").exists() or (reference / ".lake" / "build").exists():
        raise RuntimeError("Reference must start without split source or first-party build artifacts")


def stable_sources(root):
    tree = subprocess.check_output(["git", "rev-parse", f"{STABLE_COMMIT}^{{tree}}"],
                                   cwd=root, text=True).strip()
    if tree != STABLE_TREE:
        raise RuntimeError("Stable v5.7 baseline tree differs from its pinned identity")
    paths = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", STABLE_COMMIT],
                                    cwd=root, text=True).splitlines()
    selected = [p for p in paths if p == "AsymmetricTensor.lean" or (
        p.startswith("AsymmetricTensor/") and p.endswith(".lean") and not is_author_draft(p))]
    if "AsymmetricTensor.lean" not in selected or len(selected) != 10:
        raise RuntimeError("Expected the pinned stable v5.7 umbrella and nine modules")
    return {p: subprocess.check_output(["git", "show", f"{STABLE_COMMIT}:{p}"], cwd=root)
            for p in selected}


def prepare_stable_reference(root, reference, sources):
    prepare_dependency_workspace(root, reference)
    for relative, source in sources.items():
        target = reference / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(source)


def migration_inventory(before_names, after_names, before, after):
    """Record an intentionally nonempty migration; missing snapshots still fail."""
    if not before or not after:
        raise RuntimeError("Stable migration inventory requires both compiled API snapshots")
    delta = differences(before_names, after_names, before, after)
    if delta["Missing elaborated source declaration"]:
        raise RuntimeError("Stable migration inventory is missing elaborated source targets: "
                           + ", ".join(delta["Missing elaborated source declaration"]))
    return {"stable_source_names": len(before_names), "integrated_source_names": len(after_names),
            "stable_compiled_count": len(before), "integrated_compiled_count": len(after),
            "stable": before, "integrated": after, "differences": delta}


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
    output = ROOT / ".lake" / "v58-reference-evidence"
    output.mkdir(parents=True, exist_ok=True)
    # A run must not inherit a previous successful status or old API snapshots.
    for name in ("manifest.json", "reference-build.log", "source-comparison.log",
                 "api-comparison.log", "reference-api.log", "integrated-api.log",
                 "api-comparison.json", "stable-v57-build.log", "stable-v57-api.log",
                 "stable-v57-migration.json", "ApiCertificates.lean",
                 "kernel-type-certificates.log"):
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
        evidence["dependency_revisions"] = dependency_revisions(ROOT)
        locks = {name: (ROOT / name).read_bytes() for name in LOCK_FILES}
        for name, contents in locks.items():
            for commit in (SOURCE_COMMIT, STABLE_COMMIT):
                pinned = subprocess.check_output(["git", "show", f"{commit}:{name}"], cwd=ROOT)
                if contents != pinned:
                    raise RuntimeError(
                        f"Candidate changes dependency configuration from {commit}: {name}")
        evidence["configuration_sha256"] = {
            name: hashlib.sha256(contents).hexdigest() for name, contents in locks.items()}
        with tempfile.TemporaryDirectory(prefix="v58-reference-", dir=ROOT / ".lake") as directory:
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
        # Deliberately separate from the strict zero-difference v5.8 comparison.
        # Preserve every old/new compiled API entry, including generated entries,
        # so intentional migration changes cannot disappear behind scanner counts.
        sources = stable_sources(ROOT)
        evidence["stable_baseline"] = {
            "commit": STABLE_COMMIT, "tree": STABLE_TREE,
            "source_blobs": {name: git_blob(contents) for name, contents in sources.items()}}
        with tempfile.TemporaryDirectory(prefix="v57-stable-", dir=ROOT / ".lake") as directory:
            stable = Path(directory)
            prepare_stable_reference(ROOT, stable, sources)
            try:
                run_logged(["lake", "build", "AsymmetricTensor"], stable,
                           output / "stable-v57-build.log")
                before = snapshot(stable, output / "stable-v57-api.log")
                # This exact integrated snapshot has already passed the strict
                # raw-v5.8 comparison above; reuse it rather than resampling.
                after = parse_snapshot((output / "integrated-api.log").read_text())
                migration = migration_inventory(inventory(stable), inventory(ROOT), before, after)
                migration["baseline"] = evidence["stable_baseline"]
                (output / "stable-v57-migration.json").write_text(
                    json.dumps(migration, indent=2) + "\n")
                evidence["stable_migration_counts"] = {
                    name: len(values) for name, values in migration["differences"].items()}
            finally:
                check_locks(ROOT, stable, locks)
        # Also reject unexpected checkout-revision drift in shared dependencies.
        if dependency_revisions(ROOT) != evidence["dependency_revisions"]:
            raise RuntimeError("Dependency revisions changed during reference verification")
        evidence["status"] = "passed"
        print("V58_REFERENCE_VERIFIED: immutable author build, source tokens/docstrings, "
              "full compiled namespace API, complete stable-v5.7 migration inventory "
              "and unchanged dependency pins")
        return 0
    except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
        evidence["status"] = "failed"
        evidence["error"] = str(exc)
        print(f"V58_REFERENCE_FAILED: {exc}", file=sys.stderr)
        return 1
    finally:
        (output / "manifest.json").write_text(json.dumps(evidence, indent=2) + "\n")


if __name__ == "__main__":
    sys.exit(main())
