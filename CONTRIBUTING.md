# Contributing

## Reproduce, then make one focused change

Use the single setup recipe in [README → Building the committed version](README.md#building-the-committed-version).
Keep the committed Lean toolchain and dependency manifest; do not update them as
part of an unrelated proof change. Read the issue and existing PRs before
starting, so an already-covered repair is not duplicated.

`import AsymmetricTensor` remains the public compatibility entry point. The
implementation is organized into topic modules under `AsymmetricTensor/`;
see the [module map and naming/style policy](docs/modules.md). Every declaration
still lives in namespace `AsymmetricTensor`. Section comments follow the
manuscript's topic order, not a claim that each physical theory is formalized.
Declaration docstrings are in the implementation modules; no generated API site
is required.

## A checked path through the reusable API

1. `V4` is a four-component real vector and `T2` a 4×4 real matrix.
2. `symPart U` and `antiPart U` split an arbitrary `T2` by transposition.
3. `matrix_decomposition U` proves their sum is `U`, by ring algebra.
4. `asBilinear U` turns the matrix into a bilinear form in the fixed basis.
5. `raiseBoth gInv A` and `contract2 gInv U V` explicitly accept the matrix used
   for raising indices. They do not prove it is the correct inverse metric.

Read the `/-- ... -/` declaration docstrings in the Lean editor for exact input,
output, and scope contracts. The small worked example in
[`tests/ApiExamples.lean`](tests/ApiExamples.lean) starts from a nonsymmetric
matrix with one nonzero entry, computes both projections, and applies the
checked decomposition theorem. It also demonstrates a constant field satisfying
the explicitly assumed coordinate-conservation predicate, and checks the current
Lie derivative, Lorentzian action, base-10 optical, and force-baseline interfaces.

Run these real commands from the repository root:

```sh
bash scripts/verify.sh
git diff --check
```

The aggregate script builds the library and whole-library `ProofAudit`, then runs
every `tests/*.lean` regression and the Python roadmap/audit/style checks. See
[verification](docs/verification.md) for the enforced declaration and transitive
axiom policy. `lake build` alone does not execute files under `tests/`.
For a quick local iteration after building the library, run
`lake env lean tests/ApiExamples.lean`; its printed axiom lists are focused
reports and do not replace the aggregate gate.

## Navigate the repaired interfaces

- [Lie derivative](docs/lie-derivative.md): `lie_derivative` includes both
  covariant index terms. `directional_transport` names only the transport term;
  `is_translationally_symmetric` takes a constant translation vector. Component
  derivative witnesses give the classical interpretation of the totalized operator.
- [Action](docs/lorentzian-action.md): `frobenius_contract` and the legacy
  `unified_action_separation` are Frobenius algebra. Use
  `lorentzian_action_density` / `lorentzian_action_separation` for the fixed
  background-Minkowski scalar, and `kinematic_lagrangian_density` for its exact
  pressure normalization. These are not an integrated or varied action.
- [Optics and base-10 magnitudes](docs/optical-path.md): `decimalLog` uses base 10.
  `optical_distance` is an actual finite radial integral for the explicit
  exponential ansatz. Positive scale and path length give its strict inequality;
  the modulus prescriptions and positive common redshift factor remain hypotheses
  in `magnitude_anomaly_of_optical_path`. No asymptotic or horizon claim follows.
- [Force baseline](docs/force-hierarchy.md): `interaction_hierarchy_em` has the
  unscaled `α²` baseline and `interaction_hierarchy_em_strong_ratio` gives `α⁴`.
  Names containing `scaled` retain the optional extra-`α` algebra separately.

- [Saturation and limits](docs/saturation-limits.md): `admissibleTensor` enforces
  positive, pressure-bounded scalar admittance. One-sided spatial divergence is
  proved separately from exact totalized zero values. The boundary determinant
  counterexample rules out inferring spin lock from actual determinant zero.

## Mathematical and scientific scope

Do not replace a missing proof with an axiom or a hypothesis that simply states
the desired conclusion, then call the derivation complete. Conditional algebra
can be useful, but identify the conditions and actual objects it proves.

`tensor_contract` is a Frobenius pairing; `contract2` raises indices with an
explicit supplied matrix. `VolAvg` is currently symmetrization, not an integral.
The field model uses a fixed ℝ⁴ chart and partial divergence, not a general
connection. Lean's totalized division at zero is not a limiting physical theorem.
See [the conservation repair](docs/conservation.md) for a concrete example of
separating an admissible-field premise from an invalid universal axiom.

Manuscript corrections and intended physical-model decisions belong to the
author. A Lean build checks statements under their dependencies; it does not
empirically validate the manuscript. Preserve attribution and distinguish the
software license from manuscript licensing.

## Small independent starter contributions

Check open PRs first, then propose a bounded patch such as:

- Prove the transpose laws for `symPart` and `antiPart` for arbitrary `T2`;
  complete when focused Lean examples compile without new axioms or unfinished
  proofs and the contracts state no physical assumptions.
- Prove `symPart (symPart U) = symPart U` and
  `antiPart (antiPart U) = antiPart U`; include a nonsymmetric concrete regression.
- Add a declaration docstring and a focused checked example for one unannotated
  algebraic lemma. Explain every nonzero/positivity premise, and distinguish its
  actual conclusion from a physically suggestive name.

For a PR, name the issue, explain mathematical/API changes and assumptions, list
commands actually run and their results, and disclose untested or author-dependent
parts. Keep intentional toolchain upgrades separate. Do not claim that an
unchanged PDF or an unexecuted test has been verified.
