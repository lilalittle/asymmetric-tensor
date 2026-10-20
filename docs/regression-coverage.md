# v5.0 API and regression coverage

Local integration of [the author's raw v5.0 source](https://github.com/lilalittle/asymmetric-tensor/blob/3778783fd29bd92ff76081caf1abcfc032a4e00f/AsymmetricTensor.lean).
The nine-module split preserves declaration tokens and docstrings. Tests retain
their V45 filenames because those APIs and regressions still apply. Exact audit
lists now exclude the six former foundational axioms; only the dynamic scoped
conservation postulate remains. The foundation guard checks definitions and
theorems, not axioms. The v4.6 EM argument/projection repair is retained.

The 35 added results have source-inventory coverage; they do not yet each have
independent mathematical regressions. Python checks are not Lean elaboration.
See [integration evidence](v5.0-integration.md) for this candidate's actual gates.

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
- `covariant_conservation` applies exactly to `U_hat_dynamic`. The former
  `CoordinateConserved` production API is absent. The two component conservation
  theorems use the scoped axiom; generic coordinate calculus does not.
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
| `Conservation.lean` | Test-local constant-field divergence and coordinate-field counterexample; exact-type guard for the dynamic postulate; both component projections | No general production admissible-field interface or nonempty-solution-class theorem for that former interface |
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
[`RoadmapTargets.lean`](../tests/RoadmapTargets.lean) use explicit spatial Clebsch
gradients for their aligned matrix. The counterexample supplies proved evidence;
the target propositions remain specifications, not completed determinant proofs.

## Section 16 and the scientific boundary

The old ten `h_target`-bearing statements are not the current Section 16 API.
v4.5 has no such binder there. Examples of changed scope:

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
  dependency and audit-program snapshots; it is not a v4.5 equation mapping.
- A successful local or hosted run validates its exact candidate, not later edits
  or the empirical interpretation of the physical names.
