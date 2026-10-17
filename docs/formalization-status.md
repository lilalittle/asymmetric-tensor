# Formalization status and scope

This is the reader-facing scope map for [#33][i33]. It distinguishes implemented
mathematics from physical assumptions, missing constructions, and specification
targets. The separate [historical equation ledger](equation-coverage.md) accounts
for 239 numbered v9 equations and 40 unnumbered claims in the exact #9/#33
snapshot requested by [#29][i29]. It does not establish current-source equation
coverage. Neither document changes the manuscript or resolves its scientific
interpretation.

## Reviewed snapshot and validation

- **Historical review baseline:** [`9f69988d17c9fb86f35a563eb6466be9dbf4e524`][snapshot].
  Finding evidence links remain pinned to that revision; they are not claims
  about the repaired source. The original scope-only review was commit
  `16b25ef7d2bb8d5484dc0a19ab5df03509c3a30e` on its conservation-repair base.
- **Historical equation evidence:** the [ledger](equation-coverage.md) preserves
  its reviewed source and dependency manifest as inert text archives, with
  complete types and transitive dependencies for 240 declarations. Its accepted
  hashes and mappings are unchanged. Run
  `python3 scripts/equation_ledger.py --check --historical` to validate those
  archives; the default live check rejects
  later source or dependency changes. A current-source audit must not overwrite
  this historical evidence. Current-source equation remapping remains open.
- **Current mathematical base:** [`94c49e59d796fdbec846d59c6cbfa45f0304d598`][current],
  which already contains the merged conservation, action, Lie-derivative,
  distance-modulus, optical-path and electromagnetic-baseline repairs, plus
  pinned setup, software/manuscript citation separation, and the roadmap.
  Section and target links below identify this immutable repaired source.
- **Verification layer:** this scope revision also includes the rebased CI and
  proof-audit implementation described in [verification.md](verification.md).
  That layer adds no production mathematics; its build/test support and roadmap
  marker reconciliation are separate from the mathematical base above.
- **Source identity:** the base `AsymmetricTensor.lean` SHA-256 is
  `af1b28227043e80f0f746087ea9cddfd58c8682bb73adf611cf1196284447568`.
  This hash identifies the pre-split mathematical base, not the current umbrella
  or implementation-module bytes. The module split preserves every declaration's
  statement and body tokens and all 304 public types/universes; scope text and all
  78 declaration docstrings from the subsequent API stack are retained. See
  [module compatibility evidence](modules.md#compatibility-evidence). Record
  `git rev-parse HEAD` and any uncommitted changes separately for this checkout.
- **Manuscript inspected:** [v9, dated September 25, 2026][pdf], published as
  [Zenodo 22953897](https://doi.org/10.5281/zenodo.22953897). PDF SHA-256:
  `0d97cbca284e68aeed75c98b830ce16ab0453fa54f7333ce50eb90e1f4f4e7a7`.
  The PDF is unchanged; code repairs do not imply manuscript corrections.
- **Toolchain:** Lean 4.35.0; Mathlib
  `aa35a481e5f0cdb3b04a899ead15d6ca7305a624`, as recorded in the committed
  toolchain, Lake configuration and manifest.
- **Historical validation:** the [baseline README][f30] and [#30][i30]
  reported elaboration with no errors or `sorry` occurrences. That build did
  not detect the inconsistent custom conservation axiom.
- **Local validation, 2026-10-15:** the combined `./scripts/verify.sh` run
  passed production/support builds, all twelve checked-in Lean regression files
  (including the [API examples](../tests/ApiExamples.lean) and the separate
  current-source [declaration audit](../tests/EquationAxioms.lean)),
  the 364-declaration completeness and six-axiom inventory check, 11 general
  and 17 action-specific exact dependency audits, the roadmap inventory and
  finite-contract checks, and the clean/negative mutation suite. It used the
  existing shared package cache. The ten production modules compile without warnings; warnings from supporting
  regressions remain visible. Dependency pins
  and all three configuration-file byte sequences were preserved during the run;
  the CI layer intentionally adds the separate `ProofAudit` library target.
  No hosted CI result or fresh-checkout run for this combination is asserted.

**Historical consistency blocker:** the baseline `covariant_conservation`
quantified over *every* `MetricField`, although `metric_divergence` is an explicit
coordinate derivative. The field `U x μ ν = x 0` has divergence component `1`,
while the axiom forced it to be `0`. [#9][i9] retains the kernel-checked `False`
reproducer. Thus the baseline's custom theory was inconsistent.

**Current repair:** `CoordinateConserved U` is an explicit proposition
`∀ x, metric_divergence U x = 0`. The component-projection theorems require it as
`hU`; constant-field witnesses show a nonempty class, and
`coordinate_field_not_conserved` rejects the original linear field. See the
[repair documentation](conservation.md) and [regression file](../tests/Conservation.lean).
This removes the demonstrated universal-axiom contradiction. It does not derive
conservation for `U_hat_dynamic`, introduce a connection, or prove the physical
momentum PDE; [#13][i13] and [#18][i18] remain open.

The regression run printed transitive dependencies for these **seven selected
statements**, not the entire library:

| Checked declarations | Printed dependencies |
|---|---|
| `constant_coordinate_conserved`, `exists_coordinate_conserved`, `coordinate_field_not_conserved`, `bernoulli_energy_conservation`, `navier_stokes_momentum_conservation` | `propext`, `Classical.choice`, `Quot.sound` |
| `geometric_navier_stokes` | The same standard logical axioms plus `c`, `c_pos`, `hbar`, `hbar_pos`, `l_p`, `l_p_pos` |
| `unified_action_separation` | The same standard logical axioms plus `c` |

None of those seven lists contains `sorryAx` or a custom conservation axiom.
The separate [verification layer](verification.md) checks all 364 declarations
owned by the production root and its implementation modules for transitive `sorryAx` and verifies the six-axiom
first-party inventory. It additionally enforces exact custom dependencies for
11 general and 17 action-specific theorems. Those selective lists are not a
whole-library allowlist of imported custom axioms. The additional
[`EquationAxioms.lean`](../tests/EquationAxioms.lean) check enumerates all 364
current production declarations and rejects transitive axioms outside the six
allowed custom names and the three standard logical axioms. Its current-source
output does not update equation correspondence and must not overwrite the
historical 240-declaration audit. These checks do not establish consistency or
empirical validity of the model assumptions. Further review requirements are
[listed below](#reconciliation-before-candidate-review).

## How to read the status labels

- **Algebra:** a concrete identity, inequality, or rewriting argument about the
  implemented real numbers, matrices, or modules. The label describes the
  statement, not a claim of zero dependencies or physical completeness.
- **Conditional model:** an implication whose physical relationships are supplied
  as hypotheses. The conclusion can be useful while the assumed mechanism remains
  unproved.
- **Specification target:** the proposed conclusion is supplied as a premise and
  returned unchanged. This is valid implication logic, not a derivation of that
  premise.
- **Open construction:** the named geometry, dynamics, or object is absent or
  represented only by scalar/component stand-ins.
- **Known mismatch/counterexample:** a stronger intended claim is contradicted by
  an example or does not match the chosen formula. A scope note does not repair
  that claim.

A single section can have several labels. Physical names below are retained as
navigation aids; the object and hypothesis columns determine what was encoded.
“Open” means the construction or scientific interpretation remains unresolved
in this checkout; it is not a live GitHub issue-state report. The current
implementation is distinguished from historical finding evidence below.

## Where to start

1. **Matrix splitting:** `T2`, `symPart`, `antiPart`, and
   `matrix_decomposition` in [§1][s1] and [§3][s3]. `T2` is a real 4×4 matrix;
   decomposition is an entrywise algebraic identity.
2. **The component ansatz:** `U_hat`, `U_sym`, `U_anti`,
   `symmetric_diagonals`, and `antisymmetric_shear` in [§3][s3]. Inspect the
   fixed-chart entries and the use of `1 / alpha_s^2`; the definition does not
   bundle admissibility. The separately proved selected-frame velocity and
   projector constraints are in §6.
3. **Two contractions:** `tensor_contract` and `unified_action_separation`
   retain valid Frobenius algebra. For the Minkowski-raised quadratic scalar,
   use `lorentzian_action_density` and `lorentzian_action_separation` in
   [§6][s6]. Read the [action conventions](lorentzian-action.md) for the
   selected rest frame, sign witnesses, and separate one-index measurement.
4. **Coordinate dynamics:** read `partial_deriv`, `metric_divergence`,
   `CoordinateConserved`, and `geometric_navier_stokes` in [§5][s5]. The last
   result still rewrites assumed component conservation, without deriving a
   material-acceleration PDE. By contrast, the complete `lie_derivative`
   now includes both covariant index terms. Its [repair note](lie-derivative.md)
   states the differentiability and constant-field restrictions precisely.
5. **A physical premise in plain sight:**
   `baryonic_tully_fisher_derivation` in [§11][s11] squares its `h_plateau`
   hypothesis. Inspect that premise before interpreting the theorem name.
6. **An assumed target:** `alpha_decay_wkb_mapping` in [§16][s16] takes exactly
   its result as `h_target`. Compare it with the real algebra in
   `volumetric_admittance_scaling` in the same section.

## Section-by-section status

The numbering follows the source's advertised paper topics. Section links point
to the repaired mathematical base above. Old subsection/equation comments are
not an exhaustive verified v9 mapping. The [historical #29 ledger](equation-coverage.md)
establishes that correspondence only for its archived #9/#33 snapshot;
current-source equation remapping remains open. Individual repair notes give
bounded mappings.

| Section/topic | Entry-point declarations and implemented objects | Essential assumptions and completion status |
|---|---|---|
| [0. Constants][s0] | `c`, `l_p`, `hbar`; definitions `t_p`, `M_P`, `G`, `rho_tau`, `P_c`; positivity and bridge lemmas such as `M_P_sq_eq_hbar_c_div_G`. | **Algebra with custom assumptions.** Three real constants and their positivity are postulated. Definitions fix the relationships; they are not empirical determinations of constants. |
| [1. Kinematic parametrization][s1] | `V4`, `T2`; `v_macro` adds three elements of a real module; `Omega` applies `ext_deriv` to `curl_phase`. | **Definitions; open exterior calculus.** `V_3D` and `Forms_2D` are arbitrary real modules, not dimension-constrained spaces of forms. `ext_deriv` is an arbitrary function with no derivative, wedge, or closure laws. See [#19][i19]. |
| [2. Thermodynamic budget][s2] | `P_dyn_scalar`, `P_g`, `P_dyn_components`; `emergent_critical_pressure`, `compliance_equivalence`. | **Algebra.** Pressure expressions and the velocity-square budget are definitions using the postulated constants. There is no general admissible-state subtype or universal subcritical pressure bound. A pressure/energy interpretation remains additional modeling content. See [#12][i12], [#22][i22]. |
| [3. Tensor assembly][s3] | `symPart`, `antiPart`, `matrix_decomposition`, `asBilinear`, `raiseBoth`, `contract2`; fixed-chart `U_hat` and its parts. | **Concrete matrix algebra; open general covariant assembly.** The #10 repair in §6 proves normalized rest-frame velocity/projector and slip/vorticity constraints and identifies `U_sym`/`U_anti` in that selected frame. A general-coordinate transformation law, arbitrary observer construction and admissibility model remain absent. See [#12][i12], [#13][i13] and [action conventions](lorentzian-action.md). |
| [4. Field equation / macroscopic reduction][s4] | Budget rearrangements (`energy_density_proof`, `spatial_stress_proof`), scalar `cosmological_constant_derivation`; `VolAvg` is `symPart`; `macroscopic_torsion_nullification` is a linear-map identity. | **Algebra and conditional model.** Pressure and cosmological relations are premises. `Inc` is an arbitrary linear map commuting with `VolAvg` by hypothesis. There is no volume integral, torsion, or Einstein tensor. Coherent antisymmetric averages contradict the averaging interpretation. See [#14][i14], [#15][i15]. |
| [5. Differential geometry / equation of motion][s5] | `SpaceTime = Fin 4 → ℝ`; coordinate `partial_deriv` and `metric_divergence`; `CoordinateConserved`, constant-field witnesses and linear-field nonconservation. Full covariant rank-two `lie_derivative`, with translation/dilation/linear-generator formulas. | **Conditional conservation and fixed-chart calculus.** Both projection theorems require `hU`; `geometric_navier_stokes` assumes a vanishing component sum. The #11 repair adds both index terms, explicit derivative witnesses and constant-tensor boost results. Opaque dynamic fields still have no regularity guarantees; no general connection, physical momentum PDE or defect equation is constructed. See [repairs](lie-derivative.md), [#13][i13], [#17][i17], [#18][i18]. |
| [6. Action / singularity resolution][s6] | Legacy Frobenius algebra plus explicit `minkowskiInv`, `lorentzian_action_density`, `lorentzian_action_separation`, and `kinematic_lagrangian_density`. Rest-frame constraints, Eqs. (121)/(123), electric/magnetic sign witnesses, and separate `raiseFirst` measurements are proved. | **Lorentzian component algebra and conditional models; open variation and regularization.** Nonzero admittance is explicit where an inverse is interpreted. The scalar action is not a spacetime integral; `h_variation` still supplies the purported varied equation, and named differential operators remain parameters. No curvature bridge, boundary variation, Green function or singularity bound follows. Page-15 manuscript prose still has a sign inconsistency. See [action note](lorentzian-action.md), [#15][i15], [#16][i16], [#19][i19]. |
| [7. Conformal symmetry / dressing][s7] | `lorentz_symmetry_broken` derives `alpha_s_val = 1` from actual boost invariance of a constant isotropic tensor, positive admittance and nonzero boost. `conformal_pressure_coupling` substitutes a pressure-gradient premise; `dressing_field_invariance` cancels module elements. | **Restricted operator-derived symmetry result and conditional algebra.** The former `h_residual` premise is gone: the residual follows from §5. The theorem does not establish invariance/breaking for arbitrary dynamic fields. Poincaré/Noether currents, conformal action and a gauge connection remain absent; §§7.3–7.4 are placeholders. See [Lie-derivative scope](lie-derivative.md), [#19][i19], [#29][i29]. |
| [8. Mass mechanism / yield][s8] | `tensor_vev_origin`, `orthogonal_mass_extraction`, `topological_yield_limit`, `yield_partition`, `mass_yield_equivalence` manipulate real scalar relations. | **Conditional models.** Inputs include the pressure/velocity equation, Lagrangian split, Compton/Schwarzschild radius intersection, positive mass, and the equal-load partition. §8.2 has no phase-lock construction. No stress/energy calculation derives the mass identification or 50/50 partition. See [#22][i22]. |
| [9. Gauge / spectra / cavitation][s9] | Actual aligned `Matrix.det` and characteristic polynomial; complex block/full eigenvector relations with proved zero-transverse-slip decoupling; matrix-entry ratios and conditional scalar algebra. | **Bounded spectral repair implemented.** [Spectral scope and proposed correction](full-tensor-spectra.md) restrict `schwinger_limit_eigenvalues` to the aligned zero-slip tensor and prove the nonzero-slip counterexample. No physical impedance, unitary dynamics or mass-yield law follows. `isochoric_volume_preservation` still assumes a determinant-shaped scalar condition; the actual nonzero-admittance determinant is proved separately. `legal_cavitation_collapse` uses totalized division, not a limit. See [#12][i12], [#20][i20], [#21][i21]. |
| [10. Covariance / frames / CPT][s10] | `active_kinematic_contraction` and `rotational_covariance_leakage` substitute scalar premises; `equivalence_principle_gradients` rewrites module equalities; `T_symmetry_*` and `P_symmetry_*` are scalar sign identities. | **Conditional algebra; open tensor transformation model.** The coordinate-transformation expression is assumed, not derived from an action on tensor fields. §§10.1 and 10.4 are empty headings. There are no field-level CPT or antimatter objects. See [#13][i13], [#29][i29]. |
| [11. Galactic kinematics / cosmological boundary][s11] | `P_cosmo` is an exponential ansatz, `P_shear_2D` a logarithmic ansatz; `kinematic_plateau_extraction` solves `h_accel`; `baryonic_tully_fisher_derivation` squares `h_plateau`. | **Conditional model; open dynamics and known boundary mismatch.** Nonzero radii and sign bounds appear in the algebra, but the shear amplitude/baryon coupling is assumed. The exponential does not saturate at finite `r = R_h`. There is no formal no-go theorem against other gravity/halo theories. See [#23][i23], [#24][i24], [#28][i28]. |
| [12. Einstein–Cartan / affine connection][s12] | `longitudinal_transport_acceleration` rewrites a module-valued gradient premise; `einstein_cartan_lagrangian` distributes a scalar multiplier. | **Conditional algebra; open geometry.** `R_tilde`, `K_trace_1`, and `K_trace_2` are real inputs. No connection, contortion, curvature, torsion, or isomorphism is constructed. §§12.1, 12.3, 12.4, and 12.5 are empty. See [#13][i13], [#15][i15]. |
| [13. Wave mechanics / induction][s13] | `transverse_wave_propagation` rescales `h_wave` in a module; `transverse_energy_transmission` is a cosine-square identity; `eigenstate_convergence` cancels a nonzero scalar factor; `debye_attenuation_length` substitutes the definition of `P_c`. | **Conditional algebra; open evolution.** The wave equation, projected energies, steady-state relation, and attenuation formula are premises. `wedge_product` is a real number, not an exterior product. No convergence theorem, quantum measurement model, or Maxwell closure is supplied; §13.2 is empty. See [#12][i12], [#19][i19]. |
| [14. Pressure dynamics / force hierarchy][s14] | Velocity/pressure scaling, `geometric_action_boundary`, `action_constant_identity`, `F_fund`, force/radius substitutions, `kinematic_acceleration_floor`, `universal_gravitation_limit`. | **Conditional models and algebra.** The corrected `interaction_hierarchy_em` gives the unscaled Eq. (224) baseline with quadratic coupling; `interaction_hierarchy_em_strong_ratio` gives `alpha_em^4`. The old scaled identity and `alpha_em^5` ratio have explicit algebra-only names. Radius, energy/action, mass, aggregation and horizon relationships remain hypotheses. See [force note](force-hierarchy.md), [#22][i22], [#23][i23]. |
| [15. Lensing / redshift / optical distance][s15] | Redshift and refractive-index substitutions; `decimalLog`; actual `optical_distance` and `refractive_travel_time` interval integrals. Continuity, integrability, strict optical-distance/time-delay inequalities and a positive base-10 magnitude consequence. | **Finite-path analysis for an explicit ansatz and conditional modulus model.** Theorems require a fixed `L > 0`, finite `r ≥ 0` (strict results `r > 0`), positive baseline speed where used, and `1 + z > 0` for the modulus bridge. Modulus prescriptions and the exponential ansatz are not derived physical laws. No null-geodesic derivation, asymptotic divergence, finite-horizon interpretation or empirical fit is established. See [optical note](optical-path.md), [#23][i23], [#25][i25], [#26][i26]. |
| [16. Predictive corollaries / future work][s16] | A mixture of square-root, trigonometric and module identities, hypothesis substitutions, and the ten exact targets below, all within the `FutureWork` section. | **Algebra, conditional models, and specification targets.** `dirac_spinor_double_cover` is two real cosine identities; `rydberg_energy_quantization` accepts `n_integer : ℝ` and assumes energy equals pressure; `fourier_curvature_decomposition` proves positivity of two nonzero real squares. No spinor representation, integer-mode quantization, Fourier curvature decomposition, or SU(3) mass-gap theory is present. The paper itself presents this section as a roadmap. See [#19][i19], [#21][i21], [#26][i26], [#29][i29]. |

## Assumptions and unspecified symbols

### Explicit source axioms

The current candidate has six declarations beginning with `axiom`, unchanged
from §0 of the baseline:

| Declarations | What is assumed | Evidence |
|---|---|---|
| `c`, `l_p`, `hbar` | Three specified-but-not-numerically-fixed real constants. | [§0][s0] |
| `c_pos`, `l_p_pos`, `hbar_pos` | Strict positivity of those constants. | [§0][s0] |

The baseline had a seventh explicit axiom, `covariant_conservation`, asserting
zero divergence for every field. It was inconsistent and has been **removed**
by the [#9 repair](conservation.md). `CoordinateConserved` is a defined
predicate supplied as a theorem premise, not a replacement universal axiom.

This inventory is **not** the transitive custom-axiom dependency list for any
particular theorem. Imported declarations, opaque declarations, proof-generating
tactics, and all dependencies of the checked expression need kernel-level
inspection, for example with `#print axioms` after the relevant build. Standard
logical axioms such as `propext`, `Classical.choice`, and `Quot.sound` should be
reported separately from model assumptions and `sorryAx`. The seven selected
prints above and the historical review prints in [#9][i9] and [#18][i18] are not
by themselves a whole-library audit. The verification layer's distinct coverage
and limits are described above and in [its contract](verification.md).

### Opaque fields and parameterized stand-ins

The nine body-less `opaque` field declarations are:

- `alpha_s_f`, `alpha_f`, `v_x_f`, `v_y_f`, `v_z_f`, `Omega_x_f`, `Omega_y_f`,
  `Omega_z_f : ScalarField` ([source][opaque-fields]);
- `epsilon_vec_f : VectorField` ([source][opaque-vector]).

Their types do not assert continuity, differentiability, pressure bounds,
nonvanishing admittance, equations of motion, or relationships among the fields.
They must be included when inspecting the dependencies and intended meaning of
`U_hat_dynamic` and results built from it. The word “continuous” in a comment
cannot supply a missing regularity hypothesis. In particular, a total
`fderiv`-based expression is not itself proof that its input is differentiable.

Other unspecified symbols are **parameters**, not extra global physical axioms:

- `V_3D`, `Forms_2D`, and `Force3D` have additive-group/real-module structure;
  their names do not enforce dimension, spacetime dependence, or form degree.
- `ext_deriv : V_3D → Forms_2D` is an arbitrary function; `Inc : T2 →ₗ[ℝ] T2`
  is an arbitrary linear map, with commutation separately assumed.
- `Laplacian`, `Biharmonic : ℝ → ℝ` and `dAlembertian : T2 → T2` have the
  specific properties supplied by the theorems' premises. Their names do not
  make them differential operators on fields.
- Scalar names such as `R_tilde`, `K_trace_1`, `K_trace_2`, `A_anti_trace`,
  `wedge_product`, `WKB_integral`, and `Minimized_Action` do not create curvature,
  contortion, a tensor contraction, an exterior product, an integral, or a
  minimization problem. `Lambda_ab` and `Lambda_ab_prime` are arbitrary `Type`s.
- Hypotheses including `h_variation`, `h_intersection`, `h_det`,
  `h_plateau`, and `h_wave` carry substantive proposed relationships. Inspect the
  full theorem type, including parameters introduced earlier by `variable`.

Real division and square root are total in Lean. For example, `1 / (0 : ℝ) = 0`
is a valid library convention, not a physical singular limit. Algebraic
statements valid with that convention still need an explicit admissible domain
before an interpretation involving inverse compliance, positive energy, or
propagating fields. See [#12][i12].

## The ten `exact h_target` cases

These are all ten occurrences in the repaired source; their statements are unchanged. Each theorem assumes
exactly the proposition it concludes. None supplies the proposed underlying
model. They are recorded as specification targets, not invalid proofs.

| Declaration | Assumed and returned proposition | Missing construction; source |
|---|---|---|
| `alpha_decay_wkb_mapping` | `T_transmission = Real.exp (-WKB_integral)` for real inputs. | No tunneling model or WKB integral. [Lines 2689–2692][t1] |
| `optimal_transport_minimization` | `W_2_distance = Minimized_Action` for real inputs. | No measures, Wasserstein distance, admissible transport, or minimizer. [Lines 2694–2697][t2] |
| `gravitoelectromagnetism_mapping` | `GravitoElectric = v_perp_val ∧ GravitoMagnetic = Omega_val` in an arbitrary real module. | No defined gravitoelectric/magnetic fields or dynamics. [Lines 2743–2746][t3] |
| `poynting_vector_convection` | `Poynting_Vector = Lamb_Vector` in an arbitrary real module. | No cross products, flux, or field-level identification. [Lines 2748–2751][t4] |
| `entanglement_contextuality` | `Lambda_ab ≠ Lambda_ab_prime` for two `Type`s. | No measurement settings, probability model, or contextuality theorem. [Lines 2754–2757][t5] |
| `helicity_orbital_arrest` | `alpha_s_val > 0` for a real input. | No helicity or orbital evolution. [Lines 2759–2762][t6] |
| `almansi_finite_strain` | `e_ij = (1 / 2) * (delta_ij - S_ij_inv)` for real inputs. | No deformation map, inverse matrix, or strain derivation. [Lines 2842–2845][t7] |
| `su3_mass_gap_transition` | `De = 1` for a real parameter. | No SU(3) structure, spectral gap, or transition proof. [Lines 2848–2851][t8] |
| `lorentz_force_magnus_mapping` | `F_mu = A_mu_nu_v_nu` for real inputs. | No tensor contraction, Lorentz-force dynamics, or Magnus-force derivation. [Lines 2853–2856][t9] |
| `wake_detachment_stabilization` | `Normalized_Shear = A_ij / alpha_s` for real inputs. | No wake evolution, stability criterion, or derived normalization. [Lines 2858–2861][t10] |

Other theorems can also be conditional or lack the objects suggested by their
names without using the literal text `exact h_target`. For example,
`michelson_morley_invariance` assumes equal formulas for both times;
`casimir_pressure_scaling` assumes the pressure law; and
`mott_scattering_cross_section` transforms an assumed cosine-square amplitude
using a half-angle identity. The ten-count is not a complete measure of coverage.

## Review findings and dispositions

All 22 findings from #9 through #30 are accounted for below. “Counterexample”
refers to the specific claim or interpretation identified in the issue; it does
not mean the corresponding conditional Lean proof term is invalid. “Missing”
identifies an absent inference or construction and is not evidence that the
physical proposal is impossible. The issue links preserve the detailed review,
PDF page references, defense checks, and acceptance criteria.

The evidence column records the historical finding; the disposition column
reports the implementation at the current mathematical base. Repairs for #9,
#10, #11, #25, #26 and #27 are already in that base. This is not a claim that
related manuscript or broader scientific work is finished, nor a live GitHub
issue-state report. Paper corrections remain the author's responsibility.

| Finding | Evidence and kind of gap | Current disposition |
|---|---|---|
| [#9 Universal conservation][i9] | **Historical contradiction:** `U x μ ν = x 0` gives a divergence component `1`; the old universal axiom set it to `0`. [Baseline source][f9] | **Implemented on current main.** [Repair](conservation.md) removes the axiom, adds `CoordinateConserved`, constant-field witnesses and linear-field nonconservation, and requires `hU` in projections. [Regressions](../tests/Conservation.lean) check the interface and print standard logical axioms only for those five statements. Historical contradiction evidence stays outside production. A covariant connection and physical momentum PDE remain open. |
| [#10 Physical action contraction][i10] | **Sign mismatch:** a pure-electric antisymmetric pair has Frobenius self-contraction `+2` but Minkowski-raised contraction `-2`. [Source][f10] | **Bounded Lean repair implemented.** [Action note](lorentzian-action.md) and [regressions](../tests/LorentzianAction.lean) cover explicit Minkowski raising, electric/magnetic signs, orthogonality, rest-frame constraints, Eqs. (121)/(123), normalized scalar density and separate one-index measurements. Legacy Frobenius algebra remains. Page-15 manuscript prose needs author correction; variation and general-coordinate construction remain open. |
| [#11 Tensor Lie derivative][i11] | **Operator counterexample:** constant `η` under dilation has baseline transport derivative `0`, whereas the covariant rank-two Lie derivative is `2η`. [Source][f11] | **Bounded Lean repair implemented.** [Full operator](lie-derivative.md) has both index terms and a derivative-witness interface. [Regressions](../tests/LieDerivative.lean) check translation, dilation, nonsymmetric tensors and boosts. The restricted symmetry theorem derives the residual from actual invariance. General manifold/flow, dynamic-field and Noether claims remain open. |
| [#12 Saturation and limits][i12] | **Boundary/limit mismatch:** `inv_zero` yields zero at `alpha_s = 0`; positive `alpha_s = 1/n` yields growing spatial diagonal `n²`. [Source][f12] | **Open Lean and paper repair.** Separate the subcritical domain, one-sided limits, and any post-yield phase; repair the determinant boundary argument. |
| [#13 Covariant field model][i13] | **Historical missing objects:** fixed-chart functions/matrix, no normalized velocity/projector or connection; `metric_divergence` is a partial divergence. [Baseline source][f13] | **General covariant field model remains open.** The action repair now proves normalized velocity, projector and slip/vorticity constraints in the selected rest frame; this resolves the blanket claim that no such objects exist at all. It does not give a general observer/coordinate transformation construction, connection or covariant divergence. See [action scope](lorentzian-action.md). |
| [#14 Coarse-graining][i14] | **Counterexample to averaging interpretation:** `VolAvg = symPart` annihilates a constant nonzero antisymmetric field, while normalized spatial averaging preserves it. [Source][f14] | **Open Lean and paper repair.** Add a field/domain/measure model and appropriate zero-mean, boundary and regularity assumptions; keep projection algebra distinct. |
| [#15 Einstein-curvature inference][i15] | **Missing inference:** arbitrary linear `Inc` and scalar distributivity do not construct an Einstein tensor or Einstein–Cartan equivalence. [Source][f15] | **Open derivation/postulate decision.** Supply domains, derivative order, metrics, normalization and the geometric bridge, or explicitly state the intended correspondence as a postulate. |
| [#16 Variation and regularization][i16] | **Missing derivation:** `h_variation` already assumes the varied equation; differential operators, boundary terms and regularity bounds are not constructed. [Source][f16] | **Open Lean and paper repair.** Retain rescaling algebra; separately define/vary an action and prove any singularity-resolution claim. |
| [#17 Weak-field ordering][i17] | **Approximation mismatch:** the manuscript says fourth-order spatial terms are dropped while retaining convective flux at that order. The conditional component identity does not resolve the ordering. [Source][f17] | **Open paper specification and Lean target.** State a consistent small-parameter scaling and propagate it through all retained components before deriving the PDE. |
| [#18 Actual momentum PDE][i18] | **Missing bridge:** `kinematic_accel_f` is defined from a tensor time derivative; `geometric_navier_stokes` has no material-velocity term and assumes component conservation. [Source][f18] | **Open Lean derivation.** Preserve the conditional rewriting lemma; define velocity, density and stress and prove their links to the intended conservation/PDE model. |
| [#19 Exterior calculus / Maxwell closure][i19] | **Missing structure/dynamics:** arbitrary `ext_deriv`, additive operator, and a supplied `h_wave`; no exterior-derivative laws or temporal closure. [Source][f19] | **Open Lean and paper assumptions.** Construct forms and closure/evolution equations or retain only explicitly conditional algebraic support lemmas. |
| [#20 Full-matrix spectra][i20] | **Proved counterexample:** the actual complexified `U_hat` with nonzero transverse slip has `det(U - (1+i)I) = -1/4`. [Baseline finding][f20] | **Bounded Lean repair implemented; paper correction proposed.** [Spectral repair](full-tensor-spectra.md) computes the aligned determinant/characteristic polynomial, proves the invariant-plane criterion and explicit eigenvector equations, and restricts the Schwinger theorem. [Regressions](../tests/FullTensorSpectra.lean) include exact axiom checks. Impedance, symmetry-breaking, mass-yield and Appendix 16.3 conclusions are not derived; the manuscript remains author-owned. |
| [#21 Finite volume preservation][i21] | **Counterexample:** an additive trace-free antisymmetric load can give `det(U) = -2`, not `-1`. Scalar `h_det` is assumed; spatial determinant and square-root density also differ. [Source][f21] | **Counterexample and aligned determinant checked; density/volume task remains open.** [Roadmap regression](../tests/RoadmapCounterexample.lean) proves the trace-free rotational counterexample for the actual `U_hat`. The [bounded finite-determinant task](finite-determinant-task.md) and typechecked target propositions separate determinant, trace and volume density. The [spectral repair](full-tensor-spectra.md) now supplies the aligned production determinant proof. Density statements and manuscript interpretation remain open. |
| [#22 Mass / pressure budget][i22] | **Missing energy/partition inference:** a Lorentzian antisymmetric action can be signed, and equal vector component norms do not establish equal physical loads. The Lean mass/radius and partition relationships are premises. [Source][f22] | **Open Lean and paper modeling work.** Define stress/energy and the signed/nonnegative ledger consistently; identify quantum postulates and derive or label the partition conjecture. |
| [#23 Finite horizon][i23] | **Boundary counterexample:** at `r = R_h`, the ansatz gives `v/c = 1 - exp(-1)` and `P/P_c = (1 - exp(-1))²`, below saturation. [Source][f23] | **Open Lean and paper interpretation.** Resolve the horizon/domain and fitted-versus-derived status before propagating acceleration-floor and optical conclusions. |
| [#24 Galactic coupling / BTFR][i24] | **Missing coupling, plus specific counterexamples/mismatch:** `h_plateau` already encodes BTFR before squaring; axial invariance does not force plane stress; equations (169)/(173) do not yield the printed (178) ratio. [Source][f24] | **Open dynamics and paper correction.** Retain conditional plateau algebra; provide the constitutive/boundary coupling or label it an ansatz, and separately correct the pressure-ratio formula. |
| [#25 Distance-modulus logarithm][i25] | **Numerical mismatch:** a tenfold distance ratio gives `5 ln(10)` rather than `5` with the baseline `Real.log`. [Source][f25] | **Lean correction implemented.** `decimalLog x = Real.log x / Real.log 10`; [regressions](../tests/DistanceModulus.lean) check the corrected modulus identity and exact tenfold anomaly `5`. The [optical note](optical-path.md#correct-base-10-magnitude-consequence) states positive dimensionless ratios and the Mpc distance convention. |
| [#26 Optical path integral][i26] | **Missing bridge:** arbitrary distances/moduli and a local speed identity; no `∫ n`, integrability, strict distance inequality, or travel-time theorem. [Source][f26] | **Finite-ansatz mathematical bridge implemented.** [Optical note](optical-path.md) and [regressions](../tests/OpticalPath.lean) cover actual finite path/inverse-speed integrals, continuity, integrability, strict distance/time inequalities and positive base-10 anomaly on explicit domains. The ansatz and modulus prescriptions remain assumptions; #23 horizon interpretation and physical/empirical correspondence remain open. |
| [#27 Electromagnetic force factor][i27] | **Formula mismatch:** Lean proves `alpha_em * F_fund(a0)` with cubic coupling; v9 (224) specifies the unscaled baseline with quadratic coupling. [Source][f27] | **Lean/paper formula reconciliation implemented.** [Force note](force-hierarchy.md) and [regressions](../tests/ForceHierarchy.lean) cover the unscaled Eq. (224) baseline and `alpha_em^4` ratio. The prior scaled identity is retained under an explicit algebra-only name, with its distinct `alpha_em^5` ratio. No new physical coupling law is claimed. |
| [#28 Universal no-go claims][i28] | **Unsupported generalization:** a source-free 3D Laplace observation does not quantify over other gravity/halo models; no such exclusion theorem exists in this Lean section. [Source][f28] | **Open paper correction.** Scope the exclusion to its actual operator, dimension, source and domain, or supply a precise broader target and argument. No empirical verdict is supplied here. |
| [#29 Equation-level ledger][i29] | **Coverage/documentation gap:** named targets, empty headings and scalar stand-ins do not amount to exhaustive paper coverage. [Source][f29] | **Historical snapshot accounting completed; current-source equation remapping remains open.** The [historical ledger](equation-coverage.md) accounts for all 239 numbered equations, 40 unnumbered claims and 240 declarations in its exact #9/#33 snapshot. Its archived source, manifest, hashes and audit are preserved; later repaired declarations have not been remapped equation by equation. This map describes current scope, while the [roadmap](formalization-roadmap.md) records open constructions. Neither extends the historical ledger or claims complete scientific correspondence. |
| [#30 Reproducible workflow][i30] | **Repository mismatch:** baseline README refers to absent `.github` CI and starts reproduction with `lake update`. [Baseline README][f30] | **Pinned setup and verification workflow implemented.** The merged [#34][i34] repair preserves the committed Mathlib selection. The included [verification layer](verification.md) builds production/support targets, runs every Lean regression plus the roadmap checks and mutation suite, and separates whole-production proof-hole checks from selective exact dependency audits. A historical hosted run is revision-specific; it does not establish hosted success for this rebased combination. |

## Reconciliation before candidate review

1. Record the final candidate commit alongside the source and PDF identities
   above. This rebased map changes the old scope review substantively: the
   repaired action, Lie-derivative, optical and force results must be re-reviewed
   as current coverage, rather than described as unimplemented work.
2. Preserve the merged repair implementations, tests and explanatory notes.
   The module split changes file organization, imports, and local linter settings;
   declaration tokens, all public signatures, and computational definitions are
   preserved. Scope paragraphs and API docstrings are retained. Keep general
   geometry, physical PDEs, action variation and empirical validation distinct
   from bounded coordinate, algebraic and integral results.
3. Re-run the build and every retained regression after integration, verify
   dependency files remain unchanged, and inspect any audit's exact coverage.
   Local elaboration, fresh setup, hosted CI and consistency are distinct claims.
4. The [roadmap](formalization-roadmap.md) deliberately pins its main inventory
   to the historical baseline and includes dated pre-merge progress. Use this
   map and current source for the repair status; do not read its old PR-state
   notes as current status. The finite-determinant task remains an open target.
5. Keep [#29][i29]'s [historical ledger](equation-coverage.md) separate from
   current-source coverage. Preserve the archived snapshot and validate it with
   `--check --historical`; review equation mappings anew before claiming coverage
   for later repairs. The citation/license repair distinguishes software from
   manuscript identity; neither a software commit nor a successful check means
   the unchanged v9 paper has been corrected.

[current]: https://github.com/lilalittle/asymmetric-tensor/tree/94c49e59d796fdbec846d59c6cbfa45f0304d598
[snapshot]: https://github.com/lilalittle/asymmetric-tensor/tree/9f69988d17c9fb86f35a563eb6466be9dbf4e524
[pdf]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/papers/asymmetric-metric-tensor.pdf
[s0]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L41-L141
[s1]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L144-L156
[s2]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L159-L201
[s3]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L204-L283
[s4]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L286-L428
[s5]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L431-L836
[s6]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L839-L1227
[s7]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L1230-L1324
[s8]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L1327-L1473
[s9]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L1476-L1678
[s10]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L1681-L1770
[s11]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L1773-L1842
[s12]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L1845-L1894
[s13]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L1897-L1979
[s14]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L1982-L2327
[s15]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2330-L2584
[s16]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2587-L2869
[i9]: https://github.com/lilalittle/asymmetric-tensor/issues/9
[i10]: https://github.com/lilalittle/asymmetric-tensor/issues/10
[i11]: https://github.com/lilalittle/asymmetric-tensor/issues/11
[i12]: https://github.com/lilalittle/asymmetric-tensor/issues/12
[i13]: https://github.com/lilalittle/asymmetric-tensor/issues/13
[i14]: https://github.com/lilalittle/asymmetric-tensor/issues/14
[i15]: https://github.com/lilalittle/asymmetric-tensor/issues/15
[i16]: https://github.com/lilalittle/asymmetric-tensor/issues/16
[i17]: https://github.com/lilalittle/asymmetric-tensor/issues/17
[i18]: https://github.com/lilalittle/asymmetric-tensor/issues/18
[i19]: https://github.com/lilalittle/asymmetric-tensor/issues/19
[i20]: https://github.com/lilalittle/asymmetric-tensor/issues/20
[i21]: https://github.com/lilalittle/asymmetric-tensor/issues/21
[i22]: https://github.com/lilalittle/asymmetric-tensor/issues/22
[i23]: https://github.com/lilalittle/asymmetric-tensor/issues/23
[i24]: https://github.com/lilalittle/asymmetric-tensor/issues/24
[i25]: https://github.com/lilalittle/asymmetric-tensor/issues/25
[i26]: https://github.com/lilalittle/asymmetric-tensor/issues/26
[i27]: https://github.com/lilalittle/asymmetric-tensor/issues/27
[i28]: https://github.com/lilalittle/asymmetric-tensor/issues/28
[i29]: https://github.com/lilalittle/asymmetric-tensor/issues/29
[i30]: https://github.com/lilalittle/asymmetric-tensor/issues/30
[i33]: https://github.com/lilalittle/asymmetric-tensor/issues/33
[i34]: https://github.com/lilalittle/asymmetric-tensor/issues/34
[t1]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2689-L2692
[t2]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2694-L2697
[t3]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2743-L2746
[t4]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2748-L2751
[t5]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2754-L2757
[t6]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2759-L2762
[t7]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2842-L2845
[t8]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2848-L2851
[t9]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2853-L2856
[t10]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L2858-L2861
[f9]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L438-L466
[f10]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L636-L676
[f11]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L612-L621
[f12]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1116-L1141
[f13]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L430-L476
[f14]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L370-L425
[f15]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1426-L1435
[f16]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L715-L776
[f17]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L587-L607
[f18]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L493-L607
[f19]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1442-L1520
[f20]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1048-L1114
[f21]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1055-L1065
[f22]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L907-L1011
[f23]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1319-L1324
[f24]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1314-L1383
[f25]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1897-L1920
[f26]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1835-L1920
[f27]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1723-L1740
[f28]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L1314-L1383
[f29]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/AsymmetricTensor.lean#L2018-L2193
[f30]: https://github.com/lilalittle/asymmetric-tensor/blob/9f69988d17c9fb86f35a563eb6466be9dbf4e524/README.md#L17-L41
[opaque-fields]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L504-L511
[opaque-vector]: https://github.com/lilalittle/asymmetric-tensor/blob/94c49e59d796fdbec846d59c6cbfa45f0304d598/AsymmetricTensor.lean#L649-L649
