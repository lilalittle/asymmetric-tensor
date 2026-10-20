# Mathematical formalization roadmap

This planning document addresses [issue #39](https://github.com/lilalittle/asymmetric-tensor/issues/39).
Its original inventory was pinned to [revision 9f69988](https://github.com/lilalittle/asymmetric-tensor/tree/9f69988d17c9fb86f35a563eb6466be9dbf4e524)
and manuscript v9. Current-scope paragraphs and declaration markers below are
updated for the author's raw v4.5 source
`5a84e0c52b71295a678dcc1c50f80d430e5475f2` and the PR #70 repair. The older
planning decisions are retained where still relevant; historical progress records
are not current PR status or validation evidence.

Section 16 currently contains **40 theorems, 32 definitions, and zero `h_target`
binders**. The bounded inventory identifies **28 conditional declarations** there;
these include substantive physical assumptions as well as domain conditions.
Removing the old target binders does not derive every formerly named physical
claim. Some targets were replaced by narrower algebra, some assumptions were
renamed, and `helicity_orbital_arrest` was removed. This roadmap separates those
actual conclusions from missing models and author decisions. It is not an
empirical assessment or a promise to formalize the entire manuscript.

## Bounded recommendation and historical progress

Select the finite determinant calculation in existing [issue #21](https://github.com/lilalittle/asymmetric-tensor/issues/21).
The exact bounded contract is in [finite-determinant-task.md](finite-determinant-task.md).
It connects an actual `Matrix.det` to existing scalar algebra, supplies a concrete
counterexample to trace implying finite volume preservation, and separates three
different volume expressions. It needs no choice of constitutive law, connection,
quantum model, or cosmology. The task only completes the mathematical portion
specified there; it does not close the mixed paper-and-Lean issue by itself.

Historical progress recorded on 2026-10-15, after the original inventory revision
(the PR/branch states in this block are dated observations, not current status):

- [PR #48](https://github.com/lilalittle/asymmetric-tensor/pull/48), head
  `63e464cf8dec7f61d8a9e89a738bca8edcf6fa26`, implements the fixed-chart covariant
  tensor Lie derivative and its translation, constant-tensor dilation, and
  constant isotropic boost results. It is open, not merged. Do not reassign that
  same bounded implementation as new work.
- The finite exponential optical-path implementation for issue #26 is prepared
  at [commit `29c66b139e9f3e0131584343651125d00b013cee`](https://github.com/subtleGradient/asymmetric-tensor/commit/29c66b139e9f3e0131584343651125d00b013cee)
  in the `subtleGradient/asymmetric-tensor` fork, on branch
  `dot/optical-path-integral`, awaiting a PR. Its base-10 magnitude normalization
  uses [PR #47](https://github.com/lilalittle/asymmetric-tensor/pull/47). It proves
  consequences of a fixed positive-scale ansatz on finite nonnegative intervals;
  it does not settle a physical horizon interpretation or empirical Shapiro delay.
- These implementations are not in the pinned source used by this inventory.
  The statements below describe both the audited gap and the remaining scope.
  Recheck upstream status before starting implementation.

## How to read the inventory

Each entry gives the present result, intended mathematical claim, missing objects
and assumptions, intermediate results, and library investigation. A named physical
claim is not accepted merely by giving it a type or defining a variable equal to
its desired answer. Where the intended claim is ambiguous, an explicit scientific
decision blocks the stronger target; a smaller conditional lemma can still proceed.

Library tags refer to the inspected Mathlib paths at the end. Those paths exist
at the pinned revision; their presence does not establish that a complete domain
API or the desired theorem is already available. In particular, algebraic exterior
powers, a Spin group definition, and manifold charts do not supply Maxwell,
spinor-field, or gravitational dynamics automatically.

## A. Disposition of the ten former target specifications

These headings preserve the original research directions. Their **Current**
paragraphs describe v4.5, not the superseded `h_target` signatures.

### A1. WKB transmission
<!-- declarations: alpha_decay_wkb_mapping -->
- **Current:** evaluates `sqrt(-U_00)` under positive admittance and derives
  positive transmission and `log(T) = -I` from `h_wkb : T = exp(-I)`.
  The transmission law is still assumed. `I` is an arbitrary real, not a defined
  path integral; neither nonnegative `I` nor `T ≤ 1` is established.
- **Intended claim:** connect a transmission coefficient from a specified barrier
  problem to an integral through the classically forbidden region.
- **Missing objects/assumptions:** a potential, energy, mass and positive semiclassical
  parameter; turning points and boundary conditions; wave solution and flux-defined
  transmission; regularity and integrability of the selected momentum integrand.
- **Intermediate results:** define the integral and show it is nonnegative; prove
  `0 < exp(-I) ≤ 1`; then connect it to the scattering solution by a justified
  approximation or error estimate.
- **Decision block:** exact equality, a defined WKB approximation, and an asymptotic
  statement are different claims. Specify the coefficient in the exponent and the
  approximation regime before attempting the physical bridge. Investigate L2/L3.

### A2. Optimal transport and minimized action
<!-- declarations: optimal_transport_minimization -->
- **Current:** proves a dynamic-pressure/tensor-diagonal identity and
  nonnegativity under an admittance relation. The Wasserstein-distance and
  minimized-action parameters and their equality were deleted, not proved.
- **Intended claim:** identify a specified transport cost between probability
  measures with the infimum of a dynamical action over admissible paths.
- **Missing objects/assumptions:** a metric space, probability measures with finite
  second moment, couplings or density/velocity paths, continuity equation, endpoint
  constraints, cost/action functional, and nonempty admissible class.
- **Intermediate results:** construct an admissible competitor; prove nonnegativity
  and lower/upper comparisons; prove attainment separately if claiming a minimum.
- **Decision block:** choose static versus dynamical formulation and normalization.
  The usual quadratic-cost comparison involves `W₂²`, not automatically `W₂`;
  time interval and action factors matter. Existence of minimizers is not needed
  merely to define an infimum. Investigate L3; a suitable Wasserstein/dynamical
  equivalence API has not been verified in this checkout.

### A3. Gravitoelectromagnetic mapping
<!-- declarations: gravitoelectromagnetism_mapping -->
- **Current:** expands six components of `U_anti` into specified electric-slip
  and Clebsch-vorticity expressions. The old abstract field-identification
  equalities are absent. Physical field definitions, normalization and dynamics
  do not follow merely from those component calculations.
- **Intended claim:** electric and magnetic components of a defined field or
  curvature split equal specified normalized slip and vorticity fields.
- **Missing objects/assumptions:** a time/space split, observer, metric/index
  convention, three-dimensional fields, actual derivatives and coupling constants;
  a declared weak-field order if curvature is used.
- **Intermediate results:** connect the existing component formulas to the
  selected physical fields; establish units and transformation behavior; only
  then prove field equations.
- **Decision block:** extracting components of an algebraically defined 2-form
  and deriving a curvature-based approximation are alternative models. Neither
  forces completion of the other's geometry. Investigate L1/L2/L4.

### A4. Poynting and Lamb vectors
<!-- declarations: poynting_vector_convection -->
- **Current:** computes a component product and a two-term scalar contraction
  giving a scaled x-component cross-product expression. The abstract full-vector
  `Poynting_Vector = Lamb_Vector` target was removed; no energy balance follows.
- **Intended claim:** compare a defined energy flux (for example, a normalized
  `E × B`) to a hydrodynamic expression built from velocity and vorticity.
- **Missing objects/assumptions:** oriented inner-product 3-space, cross product,
  definitions of flux and Lamb-vector sign, field identifications and units.
- **Intermediate results:** compute the cross product under explicit identifications;
  prove the coefficient/sign relation; derive an energy balance separately.
- **Decision block:** component matching can be a finite algebraic task once the
  normalizations are selected. It alone is not an energy-conservation derivation.
  Investigate L1/L4; Maxwell dynamics is not required for that algebraic subtask.

### A5. Contextuality
<!-- declarations: entanglement_contextuality -->
- **Current:** proves distinct affine scalar projections and a nonzero
  difference product from distinct angles and a nonzero coefficient. The old
  type-valued inequality was deleted. There is no quantum state, correlation
  model or noncontextuality theorem in this statement.
- **Intended claim:** measurement statistics for specified contexts cannot be
  represented by one specified noncontextual model.
- **Missing objects/assumptions:** settings, outcomes, a probability model,
  admissible hidden-variable representations and a precise noncontextuality
  condition; an explicit state/measurement family for a counterexample.
- **Intermediate results:** derive a constraint for the chosen model class and
  compute statistics violating that constraint. Distinct type names do not do this.
- **Decision block:** choose a finite Bell-style, contextuality-scenario, or other
  definition before there is a theorem to prove. These are alternatives, not a
  chain of prerequisites. Investigate L3; no ready contextuality API is claimed.

### A6. Helicity and orbital arrest
<!-- declarations: -->
<!-- v4.5: helicity_orbital_arrest removed from Binyamin's drop -->
- **Current:** `helicity_orbital_arrest` is absent. The new Coulomb/Bernoulli
  result retains inverse-fourth-power positivity under positive admittance and
  adds conditional flux/pressure algebra; it does not construct helicity or an
  orbital-arrest theorem. See B18 for its remaining assumptions.
- **Intended claim:** a specified helicity-bearing evolution prevents the admittance
  from reaching zero on a specified time interval.
- **Missing objects/assumptions:** evolution equation, admissible solutions, helicity
  functional, initial/boundary data, and a relation between energy and admittance.
- **Intermediate results:** prove conservation or a monotone bound, and an estimate
  forcing a positive lower bound for admittance on the relevant interval.
- **Decision block:** choose the evolution and meaning of “arrest.” Local positivity,
  a uniform global bound, and stability are different claims. Investigate L2/L3;
  positivity may remain a model-domain assumption until the estimate exists.

### A7. Euler–Almansi finite strain
<!-- declarations: almansi_finite_strain -->
- **Current:** computes a scalar strain expression from `U_sym` when
  `alpha_s ≠ 0`, relates it to pressure under `h_compliance`, and evaluates
  `(1/2) * (1 - 0^2) = 1/2`. The literal-zero evaluation is not a limit of the
  tensor or its inverse, and there is no deformation-gradient model.
- **Intended claim:** for an invertible deformation gradient `F`, construct the
  spatial strain `e = (I - (F Fᵀ)⁻¹)/2` and establish its tensor properties.
- **Missing objects/assumptions:** matrix-valued deformation gradient, a deformation
  map if a geometric interpretation is intended, nonsingularity, and identification
  of the manuscript's `S` with the relevant spatial tensor.
- **Intermediate results:** show `F Fᵀ` is symmetric/invertible, prove zero strain
  for orthogonal `F`, and connect the matrix formula to the chosen displacement.
- **Decision block:** interpreting `S` as a metric, strain, or left Cauchy–Green
  tensor is not interchangeable. A definition alone is not a derived constitutive
  relation. Investigate L1/L2. No gauge theory is required for this finite task.

### A8. SU(3) and mass-gap transition
<!-- declarations: su3_mass_gap_transition -->
- **Current:** proves `1 ≤ ratio` and `1 ≤ De` from positive imaginary part,
  scalar ordering and a definition of `De`, alongside `(5 : ℕ) + 3 = 8`.
  This replaces the old equality with a conditional bound. It constructs no
  SU(3) generators, spanning theorem, Hamiltonian or spectral gap.
- **Intended claim:** the manuscript must first distinguish a phenomenological
  Deborah-number crossover from a positive spectral gap in an SU(3) model.
- **Missing objects/assumptions:** for crossover, a defined relaxation time and
  forcing scale with constitutive law; for a spectral gap, a state space,
  SU(3) action/fields, Hamiltonian or other operator and spectral-domain conditions.
- **Intermediate results:** crossover route: identify the dimensionless ratio and
  solve its threshold equation. Spectral route: construct the operator and specify
  the gap above its ground state before attempting estimates.
- **Decision block:** no well-posed spectral mass-gap theorem follows from a scalar `De` bound.
  The routes are alternatives and differ greatly in scope. Investigate L5 for
  group/spectral building blocks only; no claim of solving a Yang–Mills mass gap.

### A9. Lorentz force and Magnus mapping
<!-- declarations: lorentz_force_magnus_mapping -->
- **Current:** expands a spatial antisymmetric matrix-velocity contraction
  and proves its zero-work orthogonality. The old physical four-force equality
  is absent; identification with a physical force and its normalization remain
  additional choices.
- **Intended claim:** a specified force equals the contraction `q F^μ_ν u^ν`, and
  its spatial projection matches a defined fluid-force expression.
- **Missing objects/assumptions:** velocity/force vectors, antisymmetric field,
  index-raising metric, normalization and signs, and the hydrodynamic force law.
- **Intermediate results:** extend the existing spatial contraction and
  zero-work identity to the selected four-force and metric conventions, then
  compare the physical force terms.
- **Decision block:** define the Magnus constitutive coefficient and field mapping.
  The finite contraction does not require a curved connection; a dynamical
  derivation would require more. Investigate L1/L4.

### A10. Wake detachment and stabilization
<!-- declarations: wake_detachment_stabilization -->
- **Current:** divides a concrete antisymmetric component by `sqrt(-U_00)`
  and proves its explicit formula for `alpha_s > 0`. The abstract normalized-shear
  target was deleted. No detachment dynamics, bounded evolution or decay is proved.
- **Intended claim:** under a specified wake evolution or boundary model, a defined
  normalized shear or perturbation stays bounded or decays after detachment.
- **Missing objects/assumptions:** spatial/time domain, wake/phase boundary,
  solution class, norm and stability criterion; nonzero or positive admittance.
- **Intermediate results:** retain the computed normalization on its positive
  domain, then prove an energy/decay estimate that implies the chosen stability.
- **Decision block:** normalization is not stabilization. Select dynamics, boundary
  conditions and meaning of stability before stating that stronger target.
  Investigate L2/L3; a finite normalization lemma is independent of that choice.

## B. Simplified structures and conditional models

### B1. Coordinate fields, conservation and covariant geometry
<!-- declarations: partial_deriv metric_divergence divergence_expansion bernoulli_energy_conservation navier_stokes_momentum_conservation -->
<!-- v3.1: CoordinateConserved, constant_coordinate_conserved, exists_coordinate_conserved, coordinate_field_not_conserved removed; v2-only, not in Binyamin's v3.1 drop -->
Current divergence is a sum of coordinate derivatives with no connection terms.
The historical universal-field axiom was inconsistent (issue #9); it is not the
current postulate. v4.5 assumes divergence freedom only for `U_hat_dynamic`, and
the two component projections inherit it. The former `CoordinateConserved`
production interface is absent. Current test-local proofs recover constant-field
witnesses and a nonconserved coordinate-field counterexample, while an exact-type
guard protects the postulate's scope. See [coverage](regression-coverage.md).
A stronger geometric
target still needs a symmetric nondegenerate metric, observer and index
conventions, admissible tensor fields, connection and torsion, and differentiability.
For contravariant rank-two components, specify and derive
`∇_μ T^{μν} = ∂_μ T^{μν} + Γ^μ_{μλ} T^{λν} + Γ^ν_{μλ} T^{μλ}`;
a covariant-index formulation has a different formula. Prove the zero-connection
limit and recover the rest-frame matrix. **Decision block:** choose flat-chart,
linearized, or curved model and which tensor defines the metric; torsion-free does
not imply flat. Investigate L1/L2/L6. See issue #13 for the larger model.

### B2. Symmetrization versus averaging, incompatibility and curvature
<!-- declarations: VolAvg macroscopic_torsion_nullification einstein_cartan_lagrangian -->
`VolAvg` is symmetrization, `Inc` is an arbitrary linear map commuting with it,
and the Einstein–Cartan result distributes scalar multiplication. The intended
claims need an actual normalized field average and a defined compatibility/curvature
operator. For averaging: choose measure/domain or probability law, integrability,
regularity and boundary conditions; prove constants are preserved and derivatives
commute under stated hypotheses; zero mean of shear is an additional condition.
For curvature: define metric/connection, linearized incompatibility and its
curvature identity before a nonlinear extension or Lagrangian comparison.
**Decision block:** spatial averaging and expectation are alternatives; averaging
is not required for a pointwise finite determinant, nor does conservation alone
select Einstein curvature. Investigate L2/L3/L6 (issues #14/#15).

### B3. Action, variation, regularization and wave operator
<!-- declarations: tensor_contract unified_action_separation lorentzian_contract lorentzian_action_separation modified_poisson_equation unified_wave_propagation -->
The source contains both Frobenius and explicit Lorentzian quadratic identities.
“Variation” is assumed for scalar operators and the wave result uses an arbitrary
additive map.
Retain these as conditional algebra. A physical target needs an explicitly selected use of the Lorentzian
contraction, field space, action integral, source dependence and admissible
variations with boundary conditions. Prove the first variation and integration by
parts, then the Euler–Lagrange PDE; prove a solution or estimate for each quantity
claimed regularized, separately from rescaling. Specify actual differential
operators before propagation results. **Decision block:** fixed versus varied
source, background versus dynamical metric, linearized versus nonlinear action,
and what “finite” means. The existing Lorentzian contraction is a bounded algebraic step; it does not
supply variational dynamics. Investigate L1/L2/L3
(issues #10/#16).

### B4. Tensor Lie derivative and symmetries
<!-- declarations: lie_derivative is_translationally_symmetric lorentz_symmetry_broken conformal_pressure_coupling -->
The current fixed-chart covariant rank-two operator includes transport and both
index terms. Current regressions cover translation on constants, dilation,
nonconstant transport and each index response. However,
`is_translationally_symmetric` takes an arbitrary vector field, and
`lorentz_symmetry_broken` takes a scalar residual rather than actual boost
invariance. The historical boost/regularity bridges are not restored by the
current replacement suite. Further targets need
regular dynamic fields, all selected generators, and a chart-change or flow/pullback
interpretation. **Decision block:** state which transformations and which fields
are invariant; one directional derivative vanishing does not imply homogeneity.
Conservation/Noether claims require a separately specified action. Investigate L2/L6.

### B5. Fluid projections and weak-field ordering
<!-- declarations: kinematic_accel_f div_T_perp_f geometric_navier_stokes longitudinal_transport_acceleration material_acceleration_from_continuity material_derivative_continuity_field_link eulerian_momentum_pde_eq46 kinematic_navier_stokes_clebsch_eq46 -->
`geometric_navier_stokes` rearranges an assumed zero sum. The newer material
acceleration and Eulerian momentum identities perform actual algebraic
cancellation under explicit product-rule, continuity and balance hypotheses.
The field link packages these relations using `partial_deriv`; the Clebsch
momentum result additionally assumes pressure/shear partitions. Establish those
premises for defined regular fields to obtain a stronger dynamical derivation.
Define physical velocity, density,
pressure and stress, the constitutive mapping to `U`, and mass continuity. Prove
`ρ(∂_t v + (v·∇)v)` equals the selected pressure/stress force, with signs and units.
If using a weak-field approximation, introduce a small parameter, retained orders
and remainder bounds before the expansion; track both moving-frame shear and
isotropic corrections at that order. **Decision block:** select the constitutive
law and approximation regime. A finite exact tensor identity is an alternative
smaller claim, not a substitute for the PDE. Investigate L2/L4 (issues #17/#18).

### B6. Gauge, exterior calculus, waves and discrete symmetries
<!-- declarations: Omega dressing_field_invariance transverse_wave_propagation T_symmetry_mass T_symmetry_charge P_symmetry_mass P_symmetry_axial P_symmetry_charge u1_gauge_invariance -->
The abstract-form layer uses linear maps `d0`/`d1` and a bilinear wedge with
explicit nilpotency/Leibniz assumptions. The concrete coordinate layer constructs
scalar-field gradients and their exterior wedge. Dressing invariance follows
from linearity, U(1)-named claims cancel vectors, discrete-symmetry lemmas track
signs, and wave propagation rearranges its assumed equation. Define
forms on a chosen flat domain or manifold, exterior derivative, field strength,
Hodge/codifferential conventions and regularity. First prove `d² = 0`, gauge
invariance of a constructed field strength and required closure; then derive a
wave equation under specified source-free and coupling assumptions. A genuine
U(1) action needs phases/representations, not just addition. A CPT claim needs
specified transformations of fields and invariance of chosen equations/action.
**Decision block:** flat-space forms and a curved bundle theory are alternatives;
constant and variable coupling give different derivative terms. Investigate
L2/L4/L6/L7 (issue #19).

### B7. Spectra, determinants, finite strain and volume
<!-- declarations: transverse_eigenvalues_are_real_iff_no_spin isochoric_volume_preservation schwinger_limit_eigenvalues transverse_U1_decomposition generalized_cavitation volumetric_admittance_scaling -->
Current “eigenvalue” results prove scalar square/diagonal identities. The
source's hand-written `det4x4` and `det3x3` have concrete algebraic results;
an explicit bridge to Mathlib's `Matrix.det` remains the bounded selected task.
Use `α_s ≠ 0` for the general aligned determinant. Full spectra additionally require
complexification, characteristic polynomial, eigenvectors and a proved invariant
subspace/decoupling condition. Nonzero electric slip can destroy the presumed
transverse-block eigenvalues. For volume, distinguish `det U`, the symmetric
spacetime determinant and the spatial determinant/square root; trace-free additive
shear is not finite isochoric deformation. **Decision block:** whether a volume
constraint is imposed, a finite deformation is constructed, or a different density
is selected belongs to the author. An exponential of a suitable generator is an
alternative model, not a prerequisite for the additive determinant calculation.
Investigate L1/L5/L8 (issues #20/#21).

### B8. Singular domains and post-yield phase
<!-- declarations: metric_is_continuous metric_is_cavitated spatial_diagonal_one_sided_divergence polynomial_cavitation_lock -->
<!-- v3.1: legal_cavitation_collapse, cavitated_determinant_lock removed; v2-only, not in Binyamin's v3.1 drop -->
The source distinguishes positive admissibility and zero cavitation, proves
pointwise reciprocal-parameter growth, and derives a boundary consequence from
an assumed cleared polynomial relation. `spatial_diagonal_one_sided_divergence`
proves `U11(1/n) = n²` and a bound for sufficiently large positive `n`; it is not
a filter/`Tendsto` theorem. `polynomial_cavitation_lock` does not derive its
boundary premise from a singular determinant. The remaining analysis requires
admissible positive/nonzero parameters and one-sided limits, for example
`1/a² → +∞` as `a → 0+`; a totalized value is not that limit. Prove denominator
bounds on the subcritical domain and state all square-root/logarithm assumptions.
**Decision block:** a post-yield phase needs a distinct defined object and matching
conditions; it cannot inherit a limiting signature from `inv_zero`. Investigate
L2/L8 (issue #12). Restricting a finite theorem to `a ≠ 0` does not require solving
this singular-limit problem first.

### B9. Mass, energy, pressure partition and force hierarchy
<!-- declarations: tensor_vev_origin orthogonal_mass_extraction topological_yield_limit yield_partition mass_yield_equivalence geometric_action_boundary spatial_confinement_gradient action_constant_identity interaction_hierarchy_gravity interaction_hierarchy_weak interaction_hierarchy_strong interaction_hierarchy_em -->
Current formulas derive consequences of stipulated radius/energy relations and
partitions. Define stored energy separately from signed shear pressure, identify
inertial/gravitational mass assumptions, and state an acyclic assumption graph for
`E = ℏω`, `E = mc²`, Compton radius, `κ = h`, and Planck threshold. A 50/50 load
partition needs a solution/variational argument, not eigenvector normalization.
The current named EM theorem uses the extra coupling and `α³`; replacement
tests distinguish unscaled `α⁴` and scaled `α⁵` ratios. Those test-local results
do not choose the physical coupling or restore the old production helpers. **Decision block:** select energy functional, constitutive
partition and physical coupling; these are not supplied by scalar cancellation.
Investigate L1/L2/L3; spectral results matter only if that derivation is chosen
(issues #22/#27).

### B10. Galactic coupling and radial harmonic model
<!-- declarations: P_shear_2D kinematic_plateau_extraction baryonic_tully_fisher_derivation -->
Current BTFR squares an assumed plateau relation. A bounded mathematical target is
`P(r) = k log(R/r)` harmonic on a specified two-dimensional annulus and
`P'(r) = -k/r`, with positive radii. A physical BTFR target additionally requires
boundary matching deriving `k` from baryonic quantities and a stated dimensional
reduction. Separate axial invariance, tensor constraints and plane stress.
**Decision block:** choose that boundary/constitutive model; correct the pressure
ratio before propagating magnetic or lensing estimates. The logarithmic harmonic
calculation does not choose the coupling or prove observational agreement.
Investigate L2/L8 (issues #24/#44).

### B11. Cosmological ansatz, optics and horizon
<!-- declarations: P_cosmo kinematic_acceleration_floor cosmological_redshift_ratio tensor_refractive_index refractive_index_substitution magnitude_anomaly_divergence shapiro_delay_refraction -->
Current results simplify an exponential ansatz, modulus assumptions and a local
speed identity. The finite-path target has a concrete mathematical domain:
`L > 0`, `r > 0`, `n(s) = 1/[1-(1-exp(-s/L))²]` on `[0,r]`; prove positivity,
continuity, integrability, `∫ n > r`, positive travel-time excess for positive
baseline speed, and `5 log₁₀((∫ n)/r) > 0`. Issue #26's prepared implementation
supplies that bridge, with PR #47 normalization. **Decision block:** the scale's
physical meaning and a finite horizon versus an asymptotic limit remain separate;
choose a consistent ansatz/boundary and distinguish fitted from derived parameters.
The historical implementation is not present as a finite-integral API in v4.5.
Current magnitude identities use natural log; decimal calibration is recovered
only test-locally. A null-geodesic/Fermat derivation or empirical distance
comparison is additional work. Investigate L2/L3/L8 (issues #23/#25/#26).

### B12. Spinorial sign, quantization and scattering
<!-- declarations: rydberg_energy_quantization dirac_spinor_double_cover mott_scattering_cross_section cp_violation_energy_shift -->
The source uses a real `n_integer`, cosine identities, a half-angle identity for
an assumed amplitude, and a sign flip of a concrete tensor-component product
identified with `E_CP` by hypothesis. A finite spectrum
step can use `n : ℕ` with `0 < n` and retain conditional `1/n²` scaling; this still
does not establish that allowed energies are discrete. A spin-cover target needs
a group, rotation representation and covering homomorphism with kernel `{±1}`;
a rotation path should act as `-1` at `2π` and `+1` at `4π` in the specified
representation. Scattering requires a state/equation, amplitudes, flux and cross
section; CP violation requires a defined CP operation and a noninvariant observable.
**Decision block:** Spin(3)/unit-quaternion rotations and Lorentz/Dirac spinors are
alternative levels, not identical targets. Select the spectral/scattering model
before claiming its observables. Investigate L1/L5/L7/L8.

### B13. Casimir, interference and integral conservation corollaries
<!-- declarations: casimir_pressure_scaling wakefield_cavitation_gradient michelson_morley_invariance inertia_conservation action_reaction_equilibrium -->
The Casimir result now computes energy, pressure and force coefficients by
substituting assumed Bernoulli/Euler–Maclaurin factors and energy/pressure/force
relations. It does not prove an Euler–Maclaurin formula or evaluate a mode sum.
Wakefield balance rearranges assumed gradient relations; interferometer times
follow from prescribed geometry and speed; inertia proves equal pressures and
zero net force from squared-speed symmetry and Bernoulli/net-force hypotheses;
action–reaction rearranges an assumed conserved scalar sum.
The intended results require actual boundary stresses/modes and subtraction or
regularization for Casimir pressure; gradients of defined differentiable pressures
for wakefield balance; paths, motion and propagation law for interferometer
round-trip times; integrable stress/force and boundary flux for inertia and
momentum exchange. Intermediate steps are evaluating the actual gradient,
path/time or force integrals and proving the relevant conservation/boundary law.
**Decision block:** choose each boundary/dynamical model and normalization; none
of these names follows from the existing scalar algebra. L2/L3 apply. These
independent corollaries need not block each other or the selected finite task.

### B14. Kinematic scalings, instability and Fourier interpretation
<!-- declarations: acoustic_covariance_volume electromagnetic_decoupling_ratio z_pinch_sausage_instability viscoelastic_phase_angle_reduction fourier_curvature_decomposition geometric_deborah_derivation kinematic_crossover_limit phenomenological_energy_scale -->
Current results substitute a length contraction and fixed area, divide two
prescribed tensor scalings, solve a pressure budget with zero dynamic pressure,
rewrite a reciprocal power, derive a stipulated crossover scaling, and split a
specified Fourier multiplier across the tensor decomposition. The Fourier result
also derives dispersion from an explicit on-shell temporal-component hypothesis
and nonzero admittance; it does not define or transform a differential operator.
The intended stronger claims
need, respectively, a transformation/deformation and volume Jacobian; a field
coupling law; a cylindrical equilibrium and perturbation evolution; a complex
response/relaxation model; and actual spatial/time differential operators acting
on Fourier modes. Intermediate targets are a computed Jacobian, verified component
ratio, a linearized perturbation operator and growth rate, a derived response phase,
and the mode identities for those operators. **Decision block:** choose those
models and domains; pressure algebra does not imply an instability, and an
assumed on-shell multiplier does not supply a curvature/Fourier derivation. Investigate
L1/L2/L5/L8/L9. These are separate possible tasks, not mandatory prerequisites.

### B15. Radius identification, scalar constants and no-go claims
<!-- declarations: metric_density_derivation cosmological_constant_derivation cavitation_schwarzschild_radius universal_gravitation_limit -->
Current results substitute stipulated pressure/source/radius relations; a radius
formula does not construct a Schwarzschild geometry. A geometric target needs the
metric, connection, field equation, source/domain and a solution with the stated
boundary or horizon. Constant/cosmological scaling can remain explicitly
conditional algebra. Any no-go target must quantify the actual operator,
dimension, source, domain and model class excluded; a Laplacian fact in one chosen
ansatz is not a universal exclusion of other theories. **Decision block:** select
that geometric model or narrow the claim to its proved scalar consequences.
Intermediate work is constructing the metric/solution and checking the proposed
boundary, or proving the explicitly limited operator statement. Investigate
L2/L6/L8 (issues #15/#23/#28). This does not block the finite determinant.

### B16. Wave observables and attenuation
<!-- declarations: transverse_energy_transmission eigenstate_convergence debye_attenuation_length isochoric_velocity_scaling -->
Current results use prescribed amplitude/projection, steady-state scalar, pressure
balance and velocity scaling formulas. The intended claims need a defined field
solution, measurement/projection rule, nonzero cross/wedge product where used,
attenuation law and domain, and an actual area or volume-flux conservation law.
Intermediate targets are computing the projected energy, proving the stated
steady-state condition, solving the attenuation relation with positive length,
and deriving the radius dependence from the selected flux. **Decision block:**
select these laws and clarify whether the target is conditional scaling or a
dynamical/spectral conclusion; zero of a sine factor alone does not construct
quantum eigenstates. Investigate L1/L2/L3/L4/L8.

### B17. Section 16 dimensions and cosmological algebra
<!-- declarations: unit_section16_corollaries unit_section16_2_antisymmetric_corollaries unit_section16_3_cross_coupled_corollaries lemaitre_tolman_bondi_compliance holographic_bound_area_scaling unit_combinatorial_possibility_space unit_integer_action_closure_and_coulomb_elimination unit_structural_equivalences unit_three_structural_ladders -->
<!-- v4.5: added four §16.4 combinatorial/structural UnitDim theorems -->
The dimensional corollaries compare integer exponents in `UnitDim`; v4.5 adds
28 definitions and four structural/combinatorial theorems. Dimensional equality
is not a physical law or an existence result. The Lemaître–Tolman–Bondi-named
statement substitutes an admittance relation into a diagonal; the holographic
statement substitutes assumed area/entropy relations. Neither constructs the
named spacetime or derives the entropy law.

<!-- declarations: u_inv_energy u_einstein_kappa u_compliance u_mobility u_source_kappa u_spec_volume u_time_sq u_spacetime_vol u_num_density u_gradient u_hypervolume u_wave_vel u_kin_visc u_freq_sq u_surf_density u_lin_density u_compton_inv u_moment_inertia u_mass_flux_div u_mom_density u_dyn_visc u_line_mom u_charge_tau u_surf_tension u_force_const u_power_density u_poynting_flux u_power -->

### B18. v4.5 Section 16 additions (kinematic charge origin and Coulomb structure)
<!-- declarations: coulomb_bernoulli_superposition_and_deficit coulomb_phase_flux_and_force_constant dirac_moment_and_magnetic_anomaly kinematic_origin_of_charge -->
These new results are conditional algebra, not independent derivations of the
named physical laws. The Bernoulli result assumes flux conservation and spherical
flux-to-velocity relations; unrestricted flux signs do not establish negativity
of the expression called a deficit. The phase-flux result assumes a surface-force
identification with `alpha_em * F_fund` and a definition of its constant. Charge
scaling assumes transduction balance and a force equality, then derives a squared
charge and its nonnegative square root. The magnetic-moment result explicitly
assumes `h_anomaly : a_e = alpha_em / (2 * Real.pi)` and substitutes it into the
moment formula; it does not derive the Schwinger anomaly.

### B19. v4.6 Section 16 additions (thermodynamic vacuum and particle entropy)
<!-- declarations: thermodynamic_vacuum_and_particle_entropy -->
This result proves the thermodynamic vacuum identity relating temperature,
entropy density, energy density, pressure, and volume, with the continuum
Boltzmann constant identified with the action quantum. The proof assumes
nonzero volume, time, and Boltzmann constant, and the first law of
thermodynamics as a hypothesis.

### B20. v5.0 additions and foundational axiom reduction
<!-- declarations: bounded_kinematic_baseline_limits burgers_dislocation_incompatibility c_pos cauchy_strain_spatial_diagonal chiral_induction_orthogonality conformal_dilation_micro_macro_asymmetry galactic_shear_pressure_ratio_eq178 hbar_pos kinematic_discrepancy_core_and_plateau l_p_pos linearized_riemann_kroner_identities macroscopic_metric_homogenization macroscopic_torsion_decay_and_levi_civita_limit noether_lorentz_spin_conservation noether_translational_stress_conservation phase_locked_vortex_rest_mass_generation phenomenological_envelope_synthesis plasma_metric_depletion_and_chiral_wave_coupling saint_venant_homogeneous_flatness scalar_translation_gradient_isomorphism symmetric_diagonals_isotropic_strain symmetry_breaking_gordon_deflection tensor_covariance_kinematic_mixing topological_phase_lock_cavitation unit_section10_1_observer_frames unit_section10_4_conformal_scale_variance unit_section11_2_to_11_5_kinematics unit_section12_5_torsion_boundary unit_section13_2_chiral_induction unit_section3_1_symmetric_diagonals unit_section6_2_incompatibility unit_section7_3_symmetry_breaking unit_section7_4_noether_currents unit_section8_2_phase_lock universal_no_go_laplacian_and_btfr -->
The source has 268 theorem/lemma declarations, 147 definitions and one custom
axiom. The 35 new theorem/lemma declarations include three positivity proofs.
The previous 233 theorem/lemma declarations retain their author tokens.
`c`, `l_p` and `hbar` are concrete noncomputable definitions sealed irreducible;
their positivity is proved, not assumed. `covariant_conservation` remains an
axiom scoped to `U_hat_dynamic`. The raw overview's zero-axiom and opaque-state
claims do not describe the declarations at this revision.

New results cover symmetric strain, incompatibility and linearized curvature,
symmetry breaking, Noether-named currents, phase locking, observer covariance,
galactic envelopes, torsion boundaries and chiral wave coupling. These remain
the precise conditional statements in the source; names alone do not establish
curved geometry, dynamical conservation, empirical validity or roadmap completion.
Section 16 remains at 40 theorems and 32 definitions.

## C. Dependencies, alternatives and author decisions

### True mathematical inputs to the selected finite task

Only the existing `U_hat` with explicit spatial Clebsch-gradient witnesses,
`symPart`, `antiPart`, real matrix determinant/trace,
and elementary nonzero-denominator algebra are used. The required parameter
restriction is `a ≠ 0` for the general determinant, and `a > 0` for positive
volume-density formulas. No unresolved external implementation issue provides
an input to that proof. Audit proof dependencies: the current scoped conservation
postulate is not a determinant hypothesis, and no universal-field conservation
law should be added.

### What must not become invented blockers

- A curved connection is needed for a curved divergence theorem; it is not needed
  for fixed-chart Lie derivatives or the finite determinant.
- Spectra may consume the determinant calculation, but the determinant does not
  need a Schwinger interpretation or mass/yield mechanism.
- An exponential deformation and an imposed determinant constraint are alternative
  modeling routes; neither is needed to refute the additive trace inference.
- Full Yang–Mills dynamics, spinor fields and optimal transport are independent
  research directions. They do not form a mandatory chain to the next contribution.
- A finite-interval optical consequence of a declared ansatz can be proved before
  selecting the ansatz's cosmological interpretation. Changing that ansatz requires
  rechecking its consequences.

### Decisions requiring the author before stronger physical claims

1. Which symmetric metric, observer, connection and covariance regime are intended?
2. Is finite isochoric behavior an additional constraint, a deformation theorem,
   or a claim to withdraw? Which tensor supplies each volume density?
3. What are the energy, stress, action/source dependence, pressure partition and
   approximation regime? Which quantum/radius relations are postulates?
4. What dynamics and observable definitions support the WKB, contextuality,
   mass-gap, helicity, wake and scattering claims?
5. Which galactic boundary/coupling and cosmological scale/domain are selected?

Until answered, retain explicit conditional algebra and accurately limited target
specifications. Do not silently add the desired conclusion as an assumption and
report the intended physical claim as proved.

### Native issue relationship handoff

Use the existing implementation issue rather than creating a speculative backlog.
The selected finite contract has **zero unresolved external required-input issues**,
so there is no blocked-by edge to add. Do not add “blocked by” lists to its issue
description. If the scope later gains a genuine external required input, verify
that input and record it using GitHub's native issue relationship controls.
No issue or relationship is created or edited by this documentation patch.
This is deliberately separate from the issue-ready implementation description.

## D. Library investigation map

Inspected Mathlib revision: `aa35a481e5f0cdb3b04a899ead15d6ca7305a624`.
Paths below are relative to the Mathlib checkout. Exact imports, theorem signatures
and applicability must be checked for each selected implementation.

- **L1 — finite tensor algebra:** `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
  (`Matrix.det_diagonal`, `Matrix.det_fin_three`),
  `Mathlib/LinearAlgebra/Matrix/Trace.lean` (`Matrix.trace_transpose`, `Matrix.trace_sub`),
  `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`,
  `Mathlib/LinearAlgebra/Matrix/BilinearForm.lean`.
  No `det_fin_four` helper was found; investigate row/column expansion or finite
  determinant evaluation instead of inventing that API.
- **L2 — calculus and limits:** `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`,
  `Mathlib/Analysis/Calculus/ContDiff/Basic.lean`,
  `Mathlib/Analysis/Calculus/Taylor.lean`,
  `Mathlib/Analysis/Calculus/ParametricIntegral.lean`.
  Totalized derivatives still require regularity for their classical interpretation.
- **L3 — integration/probability:**
  `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`,
  `Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean`,
  `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`,
  `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`.
- **L4 — vector and exterior calculus:** `Mathlib/LinearAlgebra/CrossProduct.lean`,
  `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`,
  `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`.
  Verify the exterior-derivative API and regularity requirements; do not confuse
  algebraic alternating forms with a complete spacetime differential-form model.
- **L5 — characteristic polynomial and spectra:**
  `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`,
  `Mathlib/Analysis/Matrix/Spectrum.lean`, `Mathlib/Algebra/Lie/Basic.lean`.
  Nonsymmetric `U_hat` does not qualify for symmetric/Hermitian spectral theorems.
- **L6 — geometry:** `Mathlib/Geometry/Manifold/ChartedSpace.lean`,
  `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`.
  Connection, curvature, torsion and global tensor APIs need a focused feasibility
  investigation; no complete Einstein–Cartan library is asserted here.
- **L7 — spin/group building blocks:** `Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup.lean`,
  `Mathlib/Algebra/Quaternion.lean`,
  `Mathlib/Analysis/Normed/Algebra/QuaternionExponential.lean`.
  Existence of a `Spin` definition is not a verified covering-map or spinor theorem.
- **L8 — scalar and exponential algebra:**
  `Mathlib/Analysis/SpecialFunctions/Sqrt.lean`,
  `Mathlib/Analysis/SpecialFunctions/Log/Base.lean`,
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`,
  `Mathlib/Analysis/Normed/Algebra/Exponential.lean`.
- **L9 — Fourier building blocks:** `Mathlib/Analysis/Fourier/FourierTransform.lean`,
  `Mathlib/Analysis/Fourier/FourierTransformDeriv.lean`.
  These do not select a perturbation equation, stability norm, or boundary problem.

## Validation and stopping point

- `python3 tests/check_roadmap.py` checks the reviewed zero-`h_target` inventory,
  40 Section 16 theorems and 32 definitions, and current declaration references.
  It also checks candidate library paths and independently evaluates the finite
  determinant contract using exact arithmetic.
- `lake build AsymmetricTensor` checks production source against the pinned setup.
  It does not run these tests or prove the proposed roadmap targets.
- `lake env lean tests/RoadmapTargets.lean` checks the proposed target types and
  matrix specialization. It does **not** prove the proposed targets.
- `lake env lean tests/RoadmapCounterexample.lean` proves the actual zero-electric
  rotational counterexample, skew symmetry and zero trace, and prints axiom audits.
  This bounded evidence is separate from the general target specifications.
- `git diff --check` checks patch whitespace.

Actual validation results belong in [verification](verification.md), including
which commands ran on which candidate. This planning deliverable ends at a
concrete mathematical contract and a source-checked inventory. General production
determinant proofs, author-approved manuscript correction, new issue creation,
publication and issue closure are outside this planning patch.
