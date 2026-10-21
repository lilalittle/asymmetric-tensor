# Verification contract

## v5.7 candidate and source review

The [v5.7 integration record](v5.7-integration.md) pins the author upload and
[independent Astra source approval](https://github.com/lilalittle/asymmetric-tensor/issues/4#issuecomment-6319297490).
Source approval permits faithful integration; it is not a passing integration
build or final candidate review. The candidate retains the nine-module layout
and changes the reviewed production policy from one custom axiom to zero.

The [workflow](../.github/workflows/lean_action_ci.yml) uses Lean `v4.35.0` and
Mathlib `aa35a481e5f0cdb3b04a899ead15d6ca7305a624`, runs the strict aggregate,
and keeps versioned-upload diagnostics in a separate advisory job. Actions remain
pinned and first-party GitHub build caching remains disabled. A configured
workflow is not evidence that a revision passed.

## Reproduction without upgrading dependencies

Use Git, Bash, Python 3 and [elan](https://lean-lang.org/install/). From the root:

```sh
lake exe cache get
bash scripts/verify.sh
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

Keep every committed dependency revision. Do not run `lake update`, delete the
manifest or change pins to repair a build. The aggregate compares lock bytes with
its entry state; CI also checks them against the checkout. Intentional upgrades
require separate review.

## What the aggregate executes

The aggregate checks the author/stable source boundary, style and context,
source-parser and inventory regressions, then builds `AsymmetricTensor` and
`ProofAudit`. It executes every top-level `tests/*.lean`, roadmap checks and
proof-audit acceptance/rejection fixtures. Warnings remain visible; elaboration
errors, failed checks and transitive `sorryAx` dependencies fail the strict job.
`lake build` alone does not execute this contract.

The top-level Lean regressions include:

- `ApiSnapshot.lean`: full elaborated public types, universes and kinds for reference comparison
- `EquationAxioms.lean`: every first-party declaration's transitive custom-axiom policy
- `ProofAudit.lean`: production completeness, declared axioms and selected exact dependencies
- `RoadmapCounterexample.lean` and `RoadmapTargets.lean`: counterexample and bounded target contracts
- `V45FieldCalculus.lean`: coordinate calculus, witnessed conservation, Lie and continuity checks
- `V45MatrixAction.lean`: contraction signs, Clebsch/frame restrictions and action algebra
- `V45OpticsForces.lean`: natural-log/scaled-force contracts and test-local recovered algebra
- `V57Migration.lean`: changed dimensional, state, spectral, optical and mass interfaces

The glob is nonrecursive. Seven files in
[`tests/archive/v2`](../tests/archive/v2/README.md) remain historical and are not
executed. [Regression coverage](regression-coverage.md) distinguishes their
replacement checks and remaining gaps.

## Exact-source reference and API fidelity

The aggregate invokes `python3 scripts/check_v57_reference.py`. It retrieves the
monolith at source commit `5be4d7101a1ab28624872a8f7e5001ea8ebb8449`, verifies its
Git blob and SHA-256, and builds it separately as `AsymmetricTensor.lean` using
the same dependency pins. The disposable reference shares the pinned dependency
packages but has separate first-party build outputs; it cannot reuse a compiled
integrated library as its reference.

The checks establish different contracts:

- The bounded source comparator checks **466 named declaration token sequences**
  and **74 declaration docstrings** against the immutable raw source. It does
  not inventory structures, generated declarations or arbitrary Lean commands.
- The elaborated API comparison checks all constants in the `AsymmetricTensor`
  namespace, including the affected structure constructors, projections and
  instances. It compares declaration kind, full normalized type and universe
  parameters. Only binder hygiene and elaborator metadata are normalized.
- `V57Migration.lean` exercises the intentional prior-stable-to-v5.7 changes,
  including `UnitDim.L/V/S` becoming `K/Omega/E`. A passing source/reference
  comparison does not claim backward compatibility with v5.0.
- The context/import guard, actual build and source provenance audit cover
  separate module-placement and origin concerns.

Reference build logs, snapshots, comparisons and a manifest are retained under
`.lake/v57-reference-evidence/` and by the hosted `v57-reference` artifact. The
exact candidate run remains the evidence of success or failure. The source's
one separately approved overview correction is recorded in the integration
report; the raw reference is not silently repaired.

## Completeness and axiom policy

`#audit_root AsymmetricTensor declared []` audits declarations owned by the
umbrella and its first-party modules, including private/generated declarations
and names outside the public namespace. It rejects transitive `sorryAx` and any
custom declared axiom. `tests/EquationAxioms.lean` independently checks the
whole production transitive custom-axiom inventory, also expecting none.
Ordinary logical axioms `propext`, `Classical.choice` and `Quot.sound` remain
permitted; zero custom axioms is not the absence of all kernel assumptions.

Selected exact dependency checks retain empty custom-axiom sets for the
foundation, matrix, field and application results. In v5.7,
`covariant_conservation`, `bernoulli_energy_conservation` and
`navier_stokes_momentum_conservation` no longer depend on a custom conservation
axiom. The field regression pins the changed theorem kind and its exact scope:
`∀ x : SpaceTime, metric_divergence U_hat_dynamic x = 0`.

`DynamicClebschFields` bundles eight scalar fields and their conservation
condition. `vacuum_clebsch_witness` constructs an inhabitant; opaque `dyn_state`
selects the active configuration; the named scalar fields project from it.
This conservative witness construction does not derive conservation for arbitrary
fields or establish a nontrivial physical solution. The coordinate-field
counterexample remains in the regressions. Conditional material-acceleration,
continuity and Eulerian-balance identities retain their explicit premises.

Expected audit sets are reviewed policy, not automatically learned from output.
`collectAxioms` follows bodies, types and imports; these checks are not independent
kernel certification or empirical validation.

## Failure regressions

`scripts/test_proof_audit.py` creates disposable fixtures and requires the
intended diagnostic plus a nonzero exit. Coverage includes direct `sorry` and
`admit`, incomplete imported/private proofs, unexpected imported or unreferenced
first-party axioms, and missing theorem/module targets. A malformed fixture or
unrelated missing dependency does not count as successful rejection.

Style, source-token, context, source-boundary and roadmap tests retain their
acceptance/rejection cases. They do not replace compilation, exact dependency
audits or comparison with the independently built source reference.

## Current validation boundary

Local preparation has no Lean/Lake/elan toolchain or Mathlib cache. Available
static/Python checks and actual hosted outcomes must be recorded separately in
[the v5.7 integration report](v5.7-integration.md) and its PR. The existing hosted
pipeline provides the pinned build environment; no new deployment, permission
or dependency upgrade is part of this integration.

The author-upload run at `5be4d710` reports v5.7 COMPILED with exit 0 and a passing
unchanged stable library. It does not certify this integration candidate. Final
acceptance requires the complete strict gate, raw-reference comparison,
provenance checks, independent Astra review and hosted CI for the exact candidate
head/tree. A changed head requires renewed applicable evidence.

The [v5.0 reconciliation report](v5.0-integration.md#current-main-reconciliation-2026-10-20)
and [PR #80](https://github.com/lilalittle/asymmetric-tensor/pull/80) retain the
previous 431-name/67-docstring source/API comparison and one-axiom policy as
historical evidence. The older records below do not certify v5.7.

The [historical equation ledger](equation-coverage.md) keeps its original source,
PDF hashes and audit. Its Poppler-dependent checks remain separate:
`python3 scripts/equation_ledger.py --check --historical` and
`python3 tests/test_equation_ledger.py`. Current production axiom output is not a
replacement equation mapping or permission to rewrite that archive.

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
