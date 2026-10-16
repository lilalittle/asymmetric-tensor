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

# Warnings remain visible but are not fatal; proof completeness is checked below.
lake build AsymmetricTensor ProofAudit
check_locks
# Include every checked-in Lean regression from the merged mathematical repairs.
for regression in tests/*.lean; do
  echo "Verifying $regression"
  lake env lean "$regression"
done
python3 tests/check_roadmap.py
python3 scripts/test_proof_audit.py
check_locks
