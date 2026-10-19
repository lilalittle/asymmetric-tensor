# Contributing

## Reproduce, then make one focused change

Use [README → Building the committed version](README.md#building-the-committed-version).
Keep the committed Lean toolchain and dependency manifest; do not upgrade them
as part of an unrelated proof change. Check existing issues and PRs before
starting so an already-covered repair is not duplicated.

`import AsymmetricTensor` is the public umbrella for nine implementation modules.
Declarations remain in namespace `AsymmetricTensor`; `FutureWork` is a section,
not a namespace. See the [module map](docs/modules.md). The current source is
Binyamin Tsadik Bair-Mosheh's v4.5 formalization; earlier API and test results are
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
current natural-log and scaled-force statements from the older conventions.
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

- Conservation is postulated only for `U_hat_dynamic`. The old
  `CoordinateConserved` production interface is absent. Do not generalize the
  postulate to arbitrary fields; a coordinate field has nonzero divergence.
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
- The current optics module provides pointwise algebra and natural-log magnitude
  identities. Test-local division by `Real.log 10` checks decimal calibration but
  does not restore a production base-10 API or finite-path integral theorem.
- The named electromagnetic hierarchy result is the scaled `α³` expression.
  Keep unscaled `α⁴` and scaled `α⁵` ratios separate, including their nonzero
  hypotheses and nonunit regression cases.

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
See [module compatibility checks](docs/modules.md#compatibility-checks).
The import/context guard is deliberately lexical and cannot certify arbitrary
Lean syntax or declaration placement.

For a PR, identify the issue, source revision and mathematical/API changes;
list actual test results and remaining gaps. Do not refresh a baseline merely to
silence a failure. Keep intentional dependency upgrades separate, and do not
claim that an unchanged PDF or an unexecuted test has been verified.
