# Contributing

## Binyamin's single-file authoring lane

For source review and promotion, follow the canonical
[binyamin-ingest skill](.agents/skills/binyamin-ingest/SKILL.md). Review each upload
at its immutable commit/path/blob in one source-pinned PR or issue record, then
use a separate integration PR after independent source approval. No duplicate
root-copy review PR is needed. Historical review records and unresolved findings
remain evidence; a newer upload or successful compilation does not clear them.

Edit **`AsymmetricTensor/Asymmetric Tensor v5.7.lean`** directly for the current
single-file draft. Major rewrites, new declarations, incomplete proofs, formatting
changes, and even syntax errors there do not change the integrated stable library.
For a new version, add `AsymmetricTensor/Asymmetric Tensor v5.8.lean` (and so on).
The exact recognized form is `AsymmetricTensor/Asymmetric Tensor v<N>[.<N>...].lean`,
with numeric version components and no additional directory levels. Existing
versioned author uploads remain source history; a reviewed snapshot is pinned
by commit and blob even if the authoring lane later changes.

- **Stable `verify` job:** the root `AsymmetricTensor.lean` umbrella, nine topic
  modules, proof audit, API/context/style checks and regressions remain strict.
  Do not overwrite the root umbrella with a draft to submit research updates.
- **Author uploads (advisory diagnostics):** each versioned upload is compiled
  independently with the pinned toolchain. See its job summary and downloadable
  `author-diagnostics` artifact for compiler logs and COMPILED / COMPILE_FAILED /
  TIMEOUT / TOOL_FAILURE outcomes. Draft compilation failures are advisory, not
  stable verification failures. Toolchain setup, lock-file failures, missing reports and TOOL_FAILURE outcomes
  are still genuine CI infrastructure failures, not silently swallowed.
- **COMPILED is not verified:** Lean may accept `sorry` and new axioms. A green
  stable check certifies only the integrated library, never the newest upload.
  Existing files, unsupported filenames, and imports into the stable code are
  not automatically exempted merely because their names contain spaces.

Promoting a draft is a separate reviewed integration: preserve its source,
mechanically migrate declarations into the topic modules, compare source and
elaborated APIs, update relevant tests and reviewed baselines deliberately, and
pass the complete stable verifier. A branch that replaces the root umbrella
(like the v5.0 review-only #78) crosses that boundary and should still fail until
properly integrated. There is no automatic promotion or proof-baseline refresh.

Run draft diagnostics locally with `python3 scripts/check_author_drafts.py`.
It returns nonzero for failed drafts; only its specifically named workflow step
is advisory. The aggregate `scripts/verify.sh` deliberately does not run drafts.

## Reproduce, then make one focused change

Use [README → Building the committed version](README.md#building-the-committed-version).
Keep the committed Lean toolchain and dependency manifest; do not upgrade them
as part of an unrelated proof change. Check existing issues and PRs before
starting so an already-covered repair is not duplicated.

`import AsymmetricTensor` is the public umbrella for nine implementation modules.
Declarations remain in namespace `AsymmetricTensor`; `FutureWork` is a section,
not a namespace. See the [module map](docs/modules.md). The current source is
Binyamin Tsadik Bair-Mosheh's v5.7 formalization; earlier API and test results are
not automatically compatible with it.

## A path through the current API

1. `V4` is a four-component real vector and `T2` a 4×4 real matrix.
2. `symPart U` and `antiPart U` split an arbitrary `T2` by transposition;
   `matrix_decomposition U` proves their sum is `U`.
3. `asBilinear U` interprets a matrix in the fixed basis. `raiseBoth gInv A` and
   `contract2 gInv U V` take an explicit raising matrix; they do not prove it is
   the inverse of a supplied physical metric.
4. `wedge_covec` and `omega_clebsch_2form` form the exterior product of two
   four-component covectors. `U_hat` takes two such gradient inputs instead of
   three independent vorticity scalars.
5. `partial_deriv` uses the Fréchet derivative in a fixed real coordinate chart.
   `d_scalar_field` assembles its four components and `Omega_clebsch_field`
   constructs their wedge.

Read the declaration types and `/-- ... -/` contracts in the Lean editor.
The nonsymmetric matrix example and electric/magnetic sign tests are in
[`tests/V45MatrixAction.lean`](tests/V45MatrixAction.lean). Field examples and a
nonconserved coordinate-field counterexample are in
[`tests/V45FieldCalculus.lean`](tests/V45FieldCalculus.lean).
[`tests/V45OpticsForces.lean`](tests/V45OpticsForces.lean) distinguishes the
retained natural-log and scaled-force statements, decimal calibration, and
unscaled/scaled ratios. It does not yet directly exercise the new base-10
positivity theorem or the first and third EM theorem conjuncts.
See [coverage and remaining gaps](docs/regression-coverage.md).

Run from the repository root:

```sh
bash scripts/verify.sh
git diff --check
```

The aggregate builds the library and audit support, runs every top-level
`tests/*.lean`, and executes the Python checks and mutation regressions.
`lake build` alone does not execute those test files. The glob is nonrecursive:
files in `tests/archive/v2/` are historical evidence, not passing current tests.
For a focused iteration after a build, use `lake env lean tests/V45MatrixAction.lean`
or the corresponding field/optics file. Report commands actually run and distinguish
focused checks from the aggregate and hosted CI.

## Contracts that need particular care

- Conservation is proved for the active `U_hat_dynamic` through the
  `DynamicClebschFields.conservation` field of opaque `dyn_state`. The vacuum
  witness establishes that this on-shell structure is inhabited. The old
  `CoordinateConserved` interface remains absent, and arbitrary fields are not
  thereby conserved; a coordinate field has nonzero divergence.
- `UnitDim` uses `K`, `Omega`, and `E` projections in v5.7. Its old `L`, `V`,
  and `S` projections are not compatibility aliases. Follow the explicit basis
  map in `unit_basis_isomorphism_LVS_KOE` and the
  [migration tests](tests/V57Migration.lean), including constructor and instance
  behavior. The source/reference API check must retain generated structure APIs.
- `schwinger_zero_slip_aligned_bridge` requires zero velocity slip, zero x/y
  vorticity and the stated saturation premises. `tensor_four_effects_unification`
  now takes total `alpha_s` and its product relation to `alpha_g`/`alpha_a`; keep
  its pressure-only refraction specialization distinct from the combined tensor.
- `lie_derivative` contains both lower-index terms, but
  `is_translationally_symmetric` takes a general `VectorField`. The current
  `lorentz_symmetry_broken` theorem assumes a scalar residual equation; the older
  bridge from actual boost invariance is not supplied by that statement.
- `tensor_contract` is a Frobenius pairing; `lorentzian_contract` has the explicit
  Minkowski signs. `U_hat_eq_comoving_U_covariant` requires spatial Clebsch
  gradients. Arbitrary time-space wedges do not satisfy the same equality.
- The axial vorticity convention uses wedge entries `(3,2)`, `(1,3)`, `(2,1)`.
  Keep the sign and spatial restriction in tests when migrating scalar vorticity
  examples to gradients.
- The optics module retains natural-log magnitude identities and also provides
  `log10` and `magnitude_anomaly_log10_pos`. The latter assumes `0 < r_true`,
  `r_true < r_opt`, `0 < 1 + z`, and the two base-10 modulus prescriptions.
  `optical_path_retardation` derives the distance inequality from an assumed
  average index and product relation, not from a constructed finite-path integral.
- `interaction_hierarchy_em` returns the unscaled `α²` expression, the scaled
  `α³` expression, and the unscaled `α⁴` strong-force ratio. Keep that production
  ratio separate from the test-local scaled `α⁵` ratio, including their nonzero
  mass/coupling hypotheses and nonunit regression cases.

## Mathematical and scientific scope

Identify what every result assumes and actually proves. `VolAvg` is
symmetrization, not an integral. The divergence is a partial-coordinate operator,
not a constructed general connection. Material-acceleration and momentum results
use explicit continuity, product-rule, conservation, or partition hypotheses.
Lean's totalized division at zero is not a limiting physical theorem.

Section 16 has algebraic corollaries with physical hypotheses, not the ten old
`h_target` specifications. For example, `alpha_decay_wkb_mapping` assumes the
exponential transmission relation; it does not construct a WKB path integral.
`optimal_transport_minimization` establishes an energy identity and nonnegativity,
not a minimizer or Wasserstein metric. Read actual conclusions rather than names.

Do not replace a missing derivation with a new axiom or its conclusion as a
hypothesis and then call it complete. Preserve author attribution and distinguish
the software license from manuscript licensing. Intended physical-model decisions
belong to the author; Lean checks statements under their dependencies.

## Source-preserving integrations

For layout-only integrations, retain an exact author-source baseline, use the
committed dependency pins, and preserve declarations, docstrings, imports, and
section-variable context. Compare both source tokens and full elaborated types
against a separately built reference; neither comparison replaces the other.
The named-declaration comparators do not cover every structure, constructor,
projection, instance or generated API. Inventory affected APIs explicitly and
compare their elaborated types and call sites, with migration regressions for
intentional changes (including changes to structure fields).
See [module compatibility checks](docs/modules.md#compatibility-checks).
The import/context guard is deliberately lexical and cannot certify arbitrary
Lean syntax or declaration placement.

For a PR, identify the issue, source revision and mathematical/API changes;
list actual test results and remaining gaps. Do not refresh a baseline merely to
silence a failure. Keep intentional dependency upgrades separate, and do not
claim that an unchanged PDF or an unexecuted test has been verified.
