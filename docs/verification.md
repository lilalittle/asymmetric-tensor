# Verification contract

## v5.8 candidate and independent source review

The [v5.8 integration record](v5.8-integration.md) pins the immutable author upload,
independent source verdict and separate integration evidence. Source approval
permits faithful preparation; it is not a passing integration build or final
candidate approval. The candidate retains nine implementation modules, unchanged
dependency pins and the strict zero-custom-axiom production policy from v5.7.

The [workflow](../.github/workflows/lean_action_ci.yml) uses Lean `v4.35.0` and
Mathlib `aa35a481e5f0cdb3b04a899ead15d6ca7305a624`. Actions stay pinned,
first-party build caching stays disabled, and author-upload compiler diagnostics
remain a separate advisory job. A configured workflow is not evidence of success.

## Reproduction without upgrading dependencies

Use the committed setup and pinned Mathlib cache, then run:

```sh
bash scripts/verify.sh
git diff --check
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

Do not run `lake update`, delete the manifest or change pins to silence a failure.
The aggregate checks lock bytes at entry and exit; CI also checks against Git.

## What the aggregate executes

The aggregate checks source boundaries, style/context and their mutation tests,
source-parser/reference guard tests and the v5.8 inventory. It builds
`AsymmetricTensor` and `ProofAudit`, runs every top-level `tests/*.lean`, and
executes roadmap and proof-audit regressions. The glob is nonrecursive; archived
v2 tests remain history, not passing current tests. `lake build` alone is not the
aggregate verification contract.

Active Lean suites retain full API snapshots, whole-production/transitive axiom
audits, exact theorem policies, finite roadmap/counterexample contracts, matrix
and fixed-chart calculus regressions, optics/force tests and the v5.7 migration.
`V58Migration.lean` adds changed-conjunction call sites plus raising, boost,
admissible-domain, contraction-sign and pointwise-connection checks. See
[regression coverage](regression-coverage.md) for limits.

## Exact-source reference and API fidelity

`python3 scripts/check_v58_reference.py` retrieves
`38f4fb06a6b21fe38557afa90bc10aa36dde2f68:AsymmetricTensor/Asymmetric Tensor v5.8.lean`,
checks Git blob `9040d932eb4ed68e7c5ccb67e490383cf0b9527c` and SHA-256
`aff0033565c3f41139e3b5c26491542b885643bf14eb116aac0dafecf14b4102`, and requires
the candidate upload to remain byte-identical. It builds that monolith separately
as `AsymmetricTensor.lean`, sharing only revision-checked dependency packages,
never integrated first-party build outputs.

- The bounded lexical comparator requires all 473 named declaration token
  sequences and 75 docstrings to match. Structure/instance token checks retain
  both structures and all three explicit instances; this is not full generated
  API verification.
- Both complete compiled namespace snapshots and their unfiltered differences
  are retained. The separate public/generated comparison preserves structures,
  constructors, recursors, projections, instances and equation declarations,
  including full types, universes and declaration kinds.
- Only terminal theorem-valued `_simp_N[_N]`, `_abel_N[_N]` and `_proof_N[_N]`
  helpers can enter the reviewed helper class; never source-declared names,
  helper-shaped non-theorems or unknown entries. Binder hygiene and elaborator
  metadata normalization remain unchanged.
- A proof-helper constant reference is normalized only with zero universe
  parameters and matching actual theorem kind, full type and universes. The
  surrounding type stays compared, and a changed public equation type requires
  an actual kernel-checked certificate. Mutation tests reject changed helper
  propositions, kinds/universes and missing/generated API evidence.
- A separately built stable v5.7 umbrella/modules snapshot at
  `8ad507caa6625c810507a01c031040833af9c318`, tree
  `3e0a27fb8d5e095e6f0b9b65b4fa19b4815fcba5`, records every added, removed or
  changed compiled entry with full types, universes and kinds. This intentionally
  nonempty stable-to-v5.8 delta is not backward compatibility and never weakens
  the strict raw-v5.8-to-candidate fidelity comparison.

Evidence is retained in `.lake/v58-reference-evidence/` and the hosted
`v58-reference` artifact, including manifests, build/source/API logs, certificates
and `stable-v57-migration.json` with complete snapshots and baseline module blobs.
Missing source identity, dependency pins, build, snapshot or comparison evidence
fails the strict gate. Historical v5.7 counts do not certify a v5.8 candidate.

## Completeness and axiom policy

`#audit_root AsymmetricTensor declared []` includes first-party private/generated
declarations and names outside the public namespace. It rejects transitive
`sorryAx` and every declared custom axiom. `EquationAxioms.lean` independently
checks the whole production transitive inventory; selected theorem audits pin
exact empty custom-axiom sets. Ordinary logical axioms `propext`,
`Classical.choice` and `Quot.sound` remain allowed. This is not an assumption-free
physical theory or empirical validation.

The inhabited `DynamicClebschFields` on-shell bundle, vacuum witness, opaque
selected state and conservation projections are unchanged from v5.7. Conservation
is not proved for arbitrary fields; the nonconserved coordinate-field regression
remains. No axiom/proof-completeness baseline is refreshed for v5.8.

## Failure regressions

Proof-audit fixtures require both nonzero exit and the intended diagnostic for
`sorry`/`admit`, imported/private incomplete proofs, unexpected custom axioms and
missing theorem/module targets. Malformed fixtures or unrelated missing imports
do not count as valid rejection. Source/context/style/boundary/roadmap checks keep
their acceptance and rejection cases. None replaces the actual compiled gate.

## Current validation boundary

Preparation has Python/Git but no local Lean/Lake or dependency cache. Static
checks and hosted outcomes are reported separately in the integration record and
PR. Exact-head hosted success must include the full strict gate, independent raw
reference, all generated API/certificate checks and the stable migration build.
A previous source advisory COMPILED result or v5.7 stable pass does not transfer.

An independent final integration review must cover the exact candidate head/tree,
source mapping and actual check evidence before any separately authorized merge.
The latest source and base/head must be rechecked; changed bytes require renewed
applicable review/check evidence. Preserve history without squash, then verify
resulting-main CI. Pending or failing post-merge verification is not completion.

The [v5.7](v5.7-integration.md) and [v5.0](v5.0-integration.md) records preserve
previous source/API and policy history. The historical equation ledger and
Poppler-dependent tests remain separate; neither the old ledger nor an unchanged
PDF is upgraded by current Lean compilation.

## Historical validation records

The following pre-v4.5 records are retained for provenance only. Their old API,
declaration counts, six-axiom inventory, test counts and successful runs do not
certify the current candidate. Linked historical scope pages have the same limit.

Historical candidate validation on 2026-10-15 passed the production build,
conservation regressions, 240-declaration completeness/inventory check, eleven
exact theorem axiom checks, and mutation suite. The exact published head
`6b667bbc6e3657cc8727bd7565fd3aa0509299b6` also passed the
[hosted proof-audit run](https://github.com/subtleGradient/asymmetric-tensor/actions/runs/38788710791),
including lock preservation and negative regression checks. Later source or merge
revisions require their own successful run; this pinned result does not certify
them. Neither a green local run nor a green hosted run validates empirical physics
or manuscript coverage.

The CI-only rebased candidate on main `94c49e59d796fdbec846d59c6cbfa45f0304d598` had a
separate local validation on 2026-10-15: production/support builds, all eight
inherited Lean regression files plus `tests/ProofAudit.lean`, the then-current
360-declaration completeness/inventory check, eleven general and seventeen
action-specific exact theorem axiom checks, the roadmap inventory and
finite-contract checks, and the mutation suite. Its production source was
byte-identical to that main revision. Later scope/API documentation stacks and
their additional examples are recorded in the
[scope validation snapshot](formalization-status.md#reviewed-snapshot-and-validation). The historical hosted run above does not
cover this combined source or the expanded regression gate; the new published
revision requires its own hosted result.

The module-split stack has a separate local validation on 2026-10-15: all ten
production modules, the audit support library, all eleven Lean regression files,
the 364-declaration completeness check with the same six declared axioms, eleven
general and seventeen action-specific exact dependency checks, roadmap checks,
and proof-audit and style mutation regressions pass. The increase from 360 to 364
is compiler-generated implementation detail; the 304 source-declared public
names and their full types/universes are unchanged. All 78 API declaration
docstrings and the scope text are retained. See [module evidence](modules.md).
This local result uses the existing shared Mathlib cache; it does not certify
hosted CI or a fresh checkout of the final published revision.

The later historical-ledger integration was validated separately on 2026-10-15:
`./scripts/verify.sh` passed all twelve Lean regression files, including
`tests/EquationAxioms.lean`. That added current-source audit enumerates all 364
production declarations and permits only the six named custom axioms plus
`propext`, `Classical.choice` and `Quot.sound` transitively. It does not establish
a current equation-to-declaration map or replace the archived 240-declaration
#9/#33 audit. The [historical ledger](equation-coverage.md) also passed its
explicit `--check --historical` validation and all 22 Python regression/mutation
tests; the default live check rejected the changed current source as intended.
The historical source, mapping, coverage JSON, audit JSON and accepted hashes
were preserved. These separate Python ledger checks require Poppler `pdftotext`
and are not part of the hosted workflow; the Lean declaration check is part
of its normal `tests/*.lean` gate.
