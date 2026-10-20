#!/usr/bin/env python3
"""Fail closed on unsupported imports across the stable/draft boundary.

This bounded lexical guard supports the project's single-line module imports,
not arbitrary Lean metaprogramming. Lean elaboration and the proof audit remain
mandatory. Escaped imports require review rather than bypassing the inventory.
"""
from pathlib import Path
import re
import sys

from roadmap_inventory import mask_comments
from source_boundary import production_sources

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\b(.*)$")
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")


def check(root):
    errors = []
    files = production_sources(root) + [root / "ProofAudit.lean"]
    files += sorted((root / "tests").glob("*.lean"))
    for path in files:
        relative = path.relative_to(root).as_posix()
        try:
            text = mask_comments(path.read_text())
        except (OSError, ValueError) as exc:
            errors.append(f"{relative}: {exc}")
            continue
        lines = text.splitlines()
        for index, line in enumerate(lines):
            match = IMPORT.match(line)
            following = next((item for item in lines[index + 1:] if item.strip()), "")
            if match and (following[:1].isspace() or not match[1].strip() or
                          not all(MODULE.fullmatch(name) for name in match[1].split())):
                errors.append(f"{relative}: unsupported import syntax; stable imports must "
                              "use ordinary module names on one line, never author drafts")
    return errors


if __name__ == "__main__":
    errors = check(ROOT)
    for error in errors:
        print(error, file=sys.stderr)
    sys.exit(bool(errors))
