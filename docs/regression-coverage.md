# v5.7 API and regression coverage

This candidate integrates the
[author's pinned v5.7 source](https://github.com/lilalittle/asymmetric-tensor/blob/5be4d7101a1ab28624872a8f7e5001ea8ebb8449/AsymmetricTensor/Asymmetric%20Tensor%20v5.7.lean).
The [integration record](v5.7-integration.md) separates the approved author API
changes from source-preserving module construction and the summary-only repair.
Retained tests keep their V45 filenames because the corresponding contracts
remain useful. Source review is complete; candidate Lean and hosted verification
remain pending until exact-head results are recorded.

The bounded source inventory is 466 named declarations and 74 declaration
docstrings. It excludes structures, instances and generated declarations.
Source comparison, full elaborated API comparison, migration call sites and
whole-production proof audits provide separate evidence. None establishes
empirical validity or full manuscript coverage.

## v5.7 migration checks

[`V57Migration.lean`](../tests/V57Migration.lean) targets the intentional changes
from stable v5.0. The reference comparison separately requires fidelity to the
approved v5.7 source, including generated public API types, universes and kinds.

| Changed interface | Migration contract |
|---|---|
| `UnitDim` | Constructor, `K/Omega/E` projections, derived `DecidableEq`/`Repr`, and `Mul`/`Div`/`HPow`; the basis map sends `(L,V,S)` to `(-(L+V),V-S,S)` |
| `DynamicClebschFields` | Constructor, eight scalar-field projections and conservation field; witness and opaque selected-state interfaces |
| Conservation | `covariant_conservation` must be a theorem with exactly the dynamic-field scope; the root and transitive policies expect zero custom axioms |
| Schwinger bridge | Zero-slip and axial-alignment premises, full shifted-matrix equality and four-component eigenvector equations |
| Four-effects optics | New total-admittance argument/product premise and seven-conjunct result; pressure-only refraction remains distinct |
| Frobenius mass | The new mass/positivity API with its load, energy, volume, coupling and nonzero-vorticity premises |

The test code must compile on the exact candidate before these rows count as
passing evidence. The source also adds conditional galactic, horizon and optical
algebra; an inventory entry is not an independent regression for every theorem.

## Current interfaces and assumptions

- `U_hat`, `U_sym` and `U_anti` now take two `V4` Clebsch gradients. The derived
  vorticity uses `omega_clebsch_2form = wedge_covec`. For positive z-vorticity `w`,
  one witness is `dλ = (0,0,1,0)`, `dβ = (0,w,0,0)`, because the axial convention
  selects wedge component `(2,1)`. These parameters are not the old independent
  vorticity scalars.
- `U_hat_eq_comoving_U_covariant` identifies the two tensor constructions for
  spatial gradients built with `v_perp_covec`. A time-space wedge is retained by
  `U_covariant` but not by the spatial-vorticity entries of `U_hat`. A concrete
  counterexample guards that restriction in `V45MatrixAction.lean`.
- `covariant_conservation` applies exactly to the selected `U_hat_dynamic`.
  `DynamicClebschFields` carries conservation as a field; a vacuum witness
  establishes inhabitance and opaque `dyn_state` selects the configuration.
  The component results project its theorem. This does not quantify over all
  physical solutions or all fields. The former `CoordinateConserved` API remains
  absent, and generic coordinate calculus retains its nonconserved-field example.
- `lie_derivative` retains transport and both covariant-index terms.
  `is_translationally_symmetric` now takes a general vector field.
  [`lie_derivative_translation_bridge`](../AsymmetricTensor/FieldCalculus.lean)
  reduces the operator to transport under a zero-Jacobian hypothesis.
  [`conformal_dilation_micro_macro_asymmetry`](../AsymmetricTensor/Applications/Geometry.lean)
  gives transport plus `2σU` under the stipulated dilation Jacobian.
  `lorentz_symmetry_broken` assumes a scalar residual; it does not take actual
  boost invariance as its premise.
- `lorentzian_contract` is the explicit fixed-Minkowski component pairing;
  `tensor_contract` remains Frobenius. The action-named results are algebraic
  contractions, not integrated/varied actions.
- [The optics module](../AsymmetricTensor/Applications/Optics.lean) provides
  pointwise refraction, retained natural-log magnitude identities, and the
  production definition `log10 x = Real.log x / Real.log 10`.
  `magnitude_anomaly_log10_pos` proves the base-10 modulus-difference identity
  and strict positivity, assuming `0 < r_true`, `r_true < r_opt`, `0 < 1 + z`,
  and the two base-10 modulus prescriptions. The separate
  `magnitude_anomaly_divergence` still proves only a natural-log identity,
  despite its base-10/positivity caption; it does not prove divergence to infinity.
  `optical_path_retardation` proves the distance inequality from `n_avg > 1`
  and `r_opt = n_avg * r_true` for positive `r_true`, not from a defined integral.
- [`interaction_hierarchy_em`](../AsymmetricTensor/Applications/WavesForces.lean)
  takes both radii, their defining formulas, and nonzero mass/coupling hypotheses.
  Its three conjuncts give the unscaled `F_fund a₀ = α² m² c³ / ℏ`, the scaled
  `α * F_fund a₀ = α³ m² c³ / ℏ`, and `F_fund a₀ / F_fund L_crit = α⁴`.
  The scaled `α⁵` ratio remains a separate test-local result, not a fourth conjunct.

## Seven historical regression files

The aggregate runs only top-level `tests/*.lean`. These files in
[`tests/archive/v2`](../tests/archive/v2/README.md) remain historical and are not
executed. Recovered test-local facts are not restored production declarations.

| Archived file | Current coverage | Remaining gap or changed contract |
|---|---|---|
| `ApiExamples.lean` | `V45MatrixAction` covers the nonsymmetric decomposition and contraction signs; `V45FieldCalculus` covers constant fields and dilation | Old names/signatures involving `CoordinateConserved`, `decimalLog` and `optical_distance_gt` remain absent; base-10 positivity is available through `log10`/`magnitude_anomaly_log10_pos`, and the unscaled EM expression is now the first conjunct of `interaction_hierarchy_em` |
| `Conservation.lean` | Test-local constant-field divergence and coordinate-field counterexample; exact-kind/type guard for the dynamic theorem; witnessed `DynamicClebschFields` and both component projections | The old `CoordinateConserved` interface is not restored; inhabitance of the new on-shell structure does not establish nontrivial physical solutions |
| `LieDerivative.lean` | Constant translation of constant tensors, constant-tensor dilation, varying-field transport and dilation, and independent first/second index responses | Historical helper names/signatures, generic linear-flow/boost suite, regularity bridge and actual-invariance-to-residual API remain absent; current replacement translation/dilation helpers described above are not directly exercised here |
| `LorentzianAction.lean` | Electric/magnetic/mixed signs, generic raising-to-component bridge, arbitrary symmetric/antisymmetric orthogonality, current action separation, comoving constraints, spatial-gradient restriction, Eq. 123 null/nonunit cases | Old Eq. 121 normalization, dynamic inverse/one-index raising, background-subtracted pressure-normalized action API and the seventeen old exact audits are not restored |
| `DistanceModulus.lean` | Natural-log tenfold/e-fold/equal-distance behavior and common redshift cancellation; test-local division by `log 10` recovers decimal tenfold calibration | Production `log10` and `magnitude_anomaly_log10_pos` are available, but these regressions do not directly exercise the latter; `decimalLog` is still a historical name, and the retained natural-log tenfold result is `5 * log 10`, not `5` |
| `ForceHierarchy.lean` | Direct exercise of the named theorem's scaled second conjunct; test-local unscaled/scaled ratios; nonunit coupling distinguishes `1/16` and `1/32`; excluded zero-mass case | The production theorem also supplies the unscaled baseline and `α⁴` ratio as first/third conjuncts, without direct projection-specific regressions here; the old separately named helpers are absent, and the tests do not decide the physical model |
| `OpticalPath.lean` | Pointwise refraction substitution and the origin value; production now also has the conditional average-index result `optical_path_retardation` | No constructed finite path/travel-time integral, continuity/integrability proof, integral-derived strict path/delay inequality, zero-scale boundary theorem, or integral-linked positive magnitude anomaly; the new average-index result is not directly exercised here |

## Additional v4.5 checks

[`V45FieldCalculus.lean`](../tests/V45FieldCalculus.lean) computes a nonzero
Clebsch wedge from coordinate scalar fields and checks all three spatial
transport terms in `material_deriv`. A nontrivial scalar continuity example and
exact dependency audits exercise the conditional material-acceleration,
field-continuity, and Eulerian momentum identities. Those identities assume
the displayed product-rule, continuity and balance relations; they do not prove
regularity or derive all those relations from `U_hat_dynamic`.

[`V45MatrixAction.lean`](../tests/V45MatrixAction.lean) explicitly checks the
spatial-gradient restriction and z-vorticity orientation instead of silently
substituting old scalar vorticities. Its Eq. 123 examples use nonunit shear,
vorticity and timescale values to guard signs and coefficients.

[`V45OpticsForces.lean`](../tests/V45OpticsForces.lean) includes a whole-type
ascription for `isochoric_velocity_scaling`, preserving the author's argument
order. This catches a section-variable ordering change that can survive both
compilation and declaration-token comparison.

[`RoadmapCounterexample.lean`](../tests/RoadmapCounterexample.lean) and
[`RoadmapTargets.lean`](../tests/RoadmapTargets.lean) retain their explicit spatial
Clebsch gradients and bounded target contracts. v5.7 additionally supplies the
author's `aligned_charpoly_factorization`, nonzero-slip counterexample and
zero-slip eigenvector bridge. The new results do not silently discharge every
older roadmap target or extend the aligned eigenpairs to arbitrary slip.

## Section 16 and the scientific boundary

The old ten `h_target`-bearing statements are not the current Section 16 API.
v5.7 has no such binder there. Examples of changed scope:

- `alpha_decay_wkb_mapping` evaluates a tensor diagonal and proves positivity and
  a logarithm identity under an assumed exponential transmission formula.
- `optimal_transport_minimization` proves an energy identity and nonnegativity
  under an admittance relation, without a transport space, functional infimum or minimizer.
- `gravitoelectromagnetism_mapping` and related results expand the specified
  tensor components; that does not derive field dynamics.

The remaining assumptions need individual review even when they have more
specific names than `h_target`. The [roadmap](formalization-roadmap.md) separates
these algebraic conclusions from the stronger missing models and decisions.

## Evidence must stay separated

- Declaration tokens/docstrings compared to the raw author source establish only
  the bounded source-preservation contract.
- Full elaborated types/universes compared to a separately built reference check
  API preservation against that author source, not against the historical v2 API.
- Production completeness and custom-axiom checks apply to the current build.
- Test-local recovered properties have only the scope of their stated hypotheses.
- The [historical equation ledger](equation-coverage.md) retains its own source,
  dependency and audit-program snapshots; it is not a v5.7 equation mapping.
- A successful local or hosted run validates its exact candidate, not later edits
  or the empirical interpretation of the physical names.
