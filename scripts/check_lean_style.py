#!/usr/bin/env python3
"""A small, explicit production-module/style baseline; not a full Mathlib linter."""
from collections import Counter
import json
from pathlib import Path
import re
import sys

from source_boundary import production_sources

ROOT = Path(__file__).resolve().parents[1]
HEADER = """/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module
"""
# v3.1: Binyamin's drop has no unused-section-variable suppressions.
# The v2 legacy instances were removed with the v2 module structure.
LEGACY_INSTANCES = {}


def check(root):
    baseline = json.loads((root / "scripts/lean-style-baseline.json").read_text())
    files = production_sources(root)
    errors, module_imports, long_count = [], {}, 0
    for path in files:
        relative = path.relative_to(root).as_posix()
        text = path.read_text()
        if not text.startswith(HEADER):
            errors.append(f"{relative}: expected copyright header and module declaration")
        imports = re.findall(r"^public import (AsymmetricTensor(?:\.[A-Za-z0-9_]+)*)$", text, re.M)
        module_imports[relative[:-5].replace("/", ".")] = imports
        if re.search(r"^import ", text, re.M):
            errors.append(f"{relative}: review a non-public import explicitly")
        if relative != "AsymmetricTensor.lean":
            for directive in ["@[expose] public section", "set_option autoImplicit false",
                              "set_option linter.unusedSectionVars true"]:
                if directive not in text:
                    errors.append(f"{relative}: missing {directive}")
        exceptions = re.findall(
            r"-- Preserve this legacy typeclass argument for source compatibility\.\n"
            r"set_option linter\.unusedSectionVars false in\ntheorem (\w+)", text)
        if exceptions != LEGACY_INSTANCES.get(relative, []):
            errors.append(f"{relative}: unused-section-variable exceptions need review")
        if text.count("set_option linter.unusedSectionVars false") != len(exceptions):
            errors.append(f"{relative}: unreviewed unused-section-variable suppression")
        allowed = Counter(baseline.get(relative, []))
        actual = Counter(line for line in text.splitlines() if len(line) > 100)
        long_count += sum(actual.values())
        for line, count in (actual - allowed).items():
            errors.append(f"{relative}: {count} unreviewed long line(s): {line}")
        for number, line in enumerate(text.splitlines(), 1):
            if line != line.rstrip() or "\t" in line:
                errors.append(f"{relative}:{number}: trailing whitespace or tab")
    reached, pending = set(), ["AsymmetricTensor"]
    while pending:
        module = pending.pop()
        if module not in reached:
            reached.add(module)
            pending.extend(module_imports.get(module, []))
    for module in sorted(module_imports.keys() - reached):
        errors.append(f"{module}: production module is unreachable from the umbrella and audit")
    for module in sorted(reached - module_imports.keys()):
        errors.append(f"{module}: imported production module has no source")
    if not errors:
        exception_count = sum(len(v) for v in LEGACY_INSTANCES.values())
        print(f"STYLE_BASELINE_OK: {len(files)} reachable production modules; "
              f"{long_count} grandfathered lines over 100 columns; "
              f"{exception_count} declaration-local compatibility exceptions.")
    return errors


if __name__ == "__main__":
    failures = check(ROOT)
    for failure in failures:
        print(failure, file=sys.stderr)
    sys.exit(bool(failures))
