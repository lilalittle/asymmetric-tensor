#!/usr/bin/env python3
"""Compare this library's source-declared API with a built baseline checkout.

Run both builds first, then: python3 scripts/check_public_api.py BASELINE_DIRECTORY
This is a migration check, not an assertion that definition bodies are unchanged.
The declaration inventory matches this project's single public namespace and
its current declaration syntax, including attributes and aliases, not arbitrary Lean syntax.
"""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:noncomputable\s+)?"
    r"(?:def|abbrev|opaque|axiom|lemma|theorem|alias)\s+([^\s(:]+)",
    re.MULTILINE,
)


def inventory(root):
    files = [root / "AsymmetricTensor.lean", *sorted((root / "AsymmetricTensor").rglob("*.lean"))]
    names = ["AsymmetricTensor." + name for path in files for name in DECL.findall(path.read_text())]
    if len(names) != len(set(names)):
        raise RuntimeError(f"Duplicate source declaration in {root}")
    return set(names)


def snapshot(root):
    result = subprocess.run(
        ["lake", "env", "lean", str(ROOT / "tests/ApiSnapshot.lean")],
        cwd=root, text=True, capture_output=True, check=True,
    )
    entries = {}
    for line in result.stdout.splitlines():
        if line.startswith("API|"):
            _, name, levels, expression = line.split("|", 3)
            entries[name] = (levels, expression)
    if not entries:
        raise RuntimeError(f"No elaborated API snapshot from {root}")
    return entries


def main():
    if len(sys.argv) != 2:
        sys.exit("Usage: python3 scripts/check_public_api.py BUILT_BASELINE_DIRECTORY")
    baseline = Path(sys.argv[1]).resolve()
    before_names, after_names = inventory(baseline), inventory(ROOT)
    removed, added = before_names - after_names, after_names - before_names
    before, after = snapshot(baseline), snapshot(ROOT)
    missing = (before_names - before.keys()) | (after_names - after.keys())
    changed = {name for name in before_names & after_names
               if name in before and name in after and before[name] != after[name]}
    for label, names in [("Removed", removed), ("Added", added),
                         ("Missing elaborated declaration", missing), ("Changed type", changed)]:
        for name in sorted(names):
            print(f"{label}: {name}")
    if removed or added or missing or changed:
        sys.exit(1)
    print(f"API_COMPATIBLE: {len(before_names)} source-declared public names; "
          "identical full elaborated types and universe parameters "
          "after binder-hygiene normalization.")


if __name__ == "__main__":
    main()
