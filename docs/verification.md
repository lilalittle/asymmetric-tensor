# Verification contract

## v5.9 candidate and independent source review

The [v5.9 integration record](v5.9-integration.md) pins the immutable author
upload, independent source verdict and separate integration evidence. Approval
permits faithful preparation; it is not a passing integration build, final
candidate review, merge approval or scientific/manuscript endorsement. Historical
[v5.8](v5.8-integration.md), [v5.7](v5.7-integration.md) and
[v5.0](v5.0-integration.md) evidence remains revision-specific.

The [workflow](../.github/workflows/lean_action_ci.yml) retains Lean `v4.35.0`,
Mathlib `aa35a481e5f0cdb3b04a899ead15d6ca7305a624`, pinned Actions, no first-party
build caching and separate advisory author diagnostics. No dependency, audit or
proof baseline is refreshed. Configuration is not evidence of execution.

## Reproduction without upgrading dependencies

Provision the committed setup and pinned Mathlib cache, then run:

```sh
bash scripts/verify.sh
git diff --check
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

Do not run `lake update`, delete the manifest or change pins to silence failures.
The aggregate checks configuration bytes at entry and exit; CI also checks Git.

## What the aggregate executes

Source boundaries, reviewed style/context, bounded parser/reference guards and
their mutations remain strict. Both historical v5.8 and current v5.9 reference
unit suites run. The historical v5.8 lexical assertions now read the immutable
previous stable modules, not v5.9 candidate modules; all assertions remain.
The v5.9 inventory independently checks exact-source identity, declaration and
docstring equality, both structures, three instances and the precise source delta.

The aggregate builds `AsymmetricTensor` and `ProofAudit`, checks draft build
isolation, runs every top-level `tests/*.lean`, and executes roadmap/proof-audit
regressions. The test glob is nonrecursive; archived v2 suites remain historical.
`lake build` alone is not this contract. V45/V57/V58 migrations stay active;
`V59Migration.lean` adds whole-type checks, changed magnitude projections,
conditional optical derivatives and determinant/volume/nonunit matrix call sites.
See [regression coverage](regression-coverage.md).

## Exact-source reference and API fidelity

`python3 scripts/check_v59_reference.py` retrieves immutable source
`83bbc73eb1b12d97c2ee81be5813c6bc9e20ffe0:AsymmetricTensor/Asymmetric Tensor v5.9.lean`,
Git blob `ec92bedca9a3fc6fda46feba2a10528f30ea2885`, SHA-256
`a37c4c32d727f4d9d6f2cad7214f64c6b4e76f0f9499cfb7cf4a0dab328ed5c8`.
It rejects changed candidate upload bytes and builds the exact monolith separately
as `AsymmetricTensor.lean`. Only revision-checked dependency packages are shared;
first-party outputs and split sources are never reused.

- All 475 bounded named declaration token sequences and 75 declaration docstrings
  must match. Separate tokens retain both structures and all three explicit
  instances; scanner counts never substitute for generated API verification.
- Both complete compiled namespace snapshots and their unfiltered differences
  are retained. The unchanged public/generated comparator preserves structures,
  constructors, recursors, projections, instances and equation declarations,
  including full types, universes and declaration kinds.
- Only terminal theorem-valued `_simp_N[_N]`, `_abel_N[_N]` and `_proof_N[_N]`
  helpers enter the previously reviewed helper class. Source-declared names,
  helper-shaped non-theorems and unknown differences stay strict failures.
  Binder-hygiene/elaborator-metadata normalization is unchanged.
- Proof-helper references normalize only for zero universe parameters and
  matching actual theorem kind, full proposition and universes. Surrounding
  types remain compared. Any affected public equation type requires its actual
  kernel-checked certificate. Mutation tests reject changed helper propositions,
  kinds/universes, missing generated APIs and missing snapshots.
- A separately built prior-stable **v5.8 umbrella and nine modules** at
  `ca4f10eca7ef6138ce43d38cab0cac390110ef89`, tree
  `81f50656bea7469414eb56bd45088ea584e21697`, records every added, removed or
  changed compiled entry, with full types, universes and kinds. This intentionally
  nonempty migration is not backward compatibility and cannot weaken the strict
  raw-v5.9-to-candidate comparison. The magnitude contract changes from `A ∧ B`
  to `A ∧ C ∧ B`; old positivity users move from `.2` to `.2.2`.

Evidence goes to `.lake/v59-reference-evidence/` and the hosted `v59-reference`
artifact: manifests, source/build/API logs, complete snapshots, kernel certificates
and `stable-v58-migration.json` with baseline module blobs. Missing source identity,
pins, build, comparison or snapshot evidence fails closed. Old v5.8 reference
code/tests remain historical evidence, not a zero-difference gate against v5.9.

## Completeness and axiom policy

`#audit_root AsymmetricTensor declared []` covers private/generated production
names and first-party names outside the public namespace. It rejects transitive
`sorryAx` and all declared custom axioms. `EquationAxioms.lean` independently
checks the complete production transitive inventory; selected theorem policies
remain exactly empty. Ordinary logical `propext`, `Classical.choice` and
`Quot.sound` remain permitted. No axiom/proof-completeness baseline changes.

The inhabited on-shell `DynamicClebschFields`, vacuum witness, opaque selected
state and conservation projections are unchanged. This is not arbitrary-field
conservation or an assumption-free empirical theory. Negative proof fixtures
require both failure and the intended diagnostic, not unrelated broken imports.

## Current validation boundary

Preparation has Python/Git but no local Lean/Lake or dependency cache. Static
checks and hosted outcomes are reported separately. The raw-source advisory
COMPILED job does not certify an integration. Exact-head hosted success must
include the full strict gate, independent raw reference, public/generated API
and certificates, and complete prior-stable v5.8 migration build.

Before any separately authorized merge, recheck the newest author source,
base/head and concurrent writes; rerun affected checks and full strict CI on the
reconciled candidate and obtain independent final integration review of its exact
head/tree, source map and actual evidence. Preserve history without squash,
then verify resulting-main CI. Pending or failed checks are not completion.

The source's optical theorem assumes both derivative premises, concludes the
unscaled derivative and proves no definite integral or delay inequality. The
Born–Infeld-named result is determinant algebra, not an action, physical field
normalization, finite self-energy or universal cutoff. Pointwise zero connection
does not imply curvature flatness. Prior unresolved scientific/manuscript
findings and unchanged PDFs are not cleared by compilation.

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
