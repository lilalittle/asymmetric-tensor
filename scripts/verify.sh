#!/usr/bin/env bash
# Run from any directory; fetch the pinned Mathlib cache first.
set -euo pipefail
cd "$(dirname "$0")/.."

# Compare bytes, rather than HEAD, so this also works on an uncommitted candidate.
locks=$(mktemp -d)
trap 'rm -rf "$locks"' EXIT
for file in lean-toolchain lakefile.toml lake-manifest.json; do
  cp "$file" "$locks/$file"
done
check_locks() {
  for file in lean-toolchain lakefile.toml lake-manifest.json; do
    cmp "$locks/$file" "$file" || {
      echo "Verification unexpectedly changed $file" >&2
      return 1
    }
  done
}

python3 scripts/check_source_boundary.py
python3 scripts/test_source_boundary.py

# Check production module boundaries and reviewed style compatibility exceptions.
python3 scripts/check_lean_style.py
python3 scripts/test_lean_style.py
python3 scripts/test_module_source.py
python3 scripts/test_v57_reference.py
python3 scripts/check_module_context.py
python3 scripts/test_module_context.py
python3 tests/test_v57_inventory.py

# Warnings remain visible but are not fatal; proof completeness is checked below.
lake build AsymmetricTensor ProofAudit
python3 scripts/test_draft_build_isolation.py
check_locks
# Include every checked-in Lean regression from the merged mathematical repairs.
for regression in tests/*.lean; do
  echo "Verifying $regression"
  lake env lean "$regression"
done
python3 tests/test_roadmap_inventory.py
python3 tests/check_roadmap.py
python3 scripts/test_proof_audit.py
python3 scripts/check_v57_reference.py
check_locks
