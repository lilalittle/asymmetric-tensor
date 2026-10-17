# Mathematical formalization roadmap

This planning document addresses [issue #39](https://github.com/lilalittle/asymmetric-tensor/issues/39).
The source inventory is pinned to [revision 9f69988](https://github.com/lilalittle/asymmetric-tensor/tree/9f69988d17c9fb86f35a563eb6466be9dbf4e524),
`AsymmetricTensor.lean`, and manuscript v9. It distinguishes verified algebra,
conditional reductions, specifications that return their own hypotheses, and
mathematical models that have not been constructed. It is not an empirical
assessment or a promise to formalize all of the manuscript.

## Recommendation and current progress

Select the finite determinant calculation in existing [issue #21](https://github.com/lilalittle/asymmetric-tensor/issues/21).
The exact bounded contract is in [finite-determinant-task.md](finite-determinant-task.md).
It connects an actual `Matrix.det` to existing scalar algebra, supplies a concrete
counterexample to trace implying finite volume preservation, and separates three
different volume expressions. It needs no choice of constitutive law, connection,
quantum model, or cosmology. The task only completes the mathematical portion
specified there; it does not close the mixed paper-and-Lean issue by itself.

Progress verified separately on 2026-10-15, after the inventory revision:

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

## A. All ten hypothesis-returning target specifications

### A1. WKB transmission
<!-- declarations: alpha_decay_wkb_mapping -->
- **Current:** returns the assumed equality `T = exp(-I)` for two free real inputs.
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
- **Current:** returns equality of two free reals, with no metric or minimization.
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
- **Current:** returns two assumed equalities in an arbitrary real module.
- **Intended claim:** electric and magnetic components of a defined field or
  curvature split equal specified normalized slip and vorticity fields.
- **Missing objects/assumptions:** a time/space split, observer, metric/index
  convention, three-dimensional fields, actual derivatives and coupling constants;
  a declared weak-field order if curvature is used.
- **Intermediate results:** derive component formulas from the selected tensor;
  establish units, signs and transformation behavior; only then prove field equations.
- **Decision block:** extracting components of an algebraically defined 2-form
  and deriving a curvature-based approximation are alternative models. Neither
  forces completion of the other's geometry. Investigate L1/L2/L4.

### A4. Poynting and Lamb vectors
<!-- declarations: poynting_vector_convection -->
- **Current:** returns equality of two arbitrary module elements.
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
- **Current:** assumes and returns inequality between two Lean types.
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
<!-- declarations: helicity_orbital_arrest -->
- **Current:** assumes and returns positivity of a free scalar.
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
- **Current:** returns an assumed scalar formula `e = (δ - S⁻¹)/2`.
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
- **Current:** assumes and returns `De = 1` for a real scalar.
- **Intended claim:** the manuscript must first distinguish a phenomenological
  Deborah-number crossover from a positive spectral gap in an SU(3) model.
- **Missing objects/assumptions:** for crossover, a defined relaxation time and
  forcing scale with constitutive law; for a spectral gap, a state space,
  SU(3) action/fields, Hamiltonian or other operator and spectral-domain conditions.
- **Intermediate results:** crossover route: identify the dimensionless ratio and
  solve its threshold equation. Spectral route: construct the operator and specify
  the gap above its ground state before attempting estimates.
- **Decision block:** no well-posed mass-gap theorem follows from `De = 1`.
  The routes are alternatives and differ greatly in scope. Investigate L5 for
  group/spectral building blocks only; no claim of solving a Yang–Mills mass gap.

### A9. Lorentz force and Magnus mapping
<!-- declarations: lorentz_force_magnus_mapping -->
- **Current:** returns an assumed equality of two reals; no tensor contraction exists.
- **Intended claim:** a specified force equals the contraction `q F^μ_ν u^ν`, and
  its spatial projection matches a defined fluid-force expression.
- **Missing objects/assumptions:** velocity/force vectors, antisymmetric field,
  index-raising metric, normalization and signs, and the hydrodynamic force law.
- **Intermediate results:** expand the actual matrix-vector contraction; prove
  orthogonality to velocity under the selected metric; compare spatial terms.
- **Decision block:** define the Magnus constitutive coefficient and field mapping.
  The finite contraction does not require a curved connection; a dynamical
  derivation would require more. Investigate L1/L4.

### A10. Wake detachment and stabilization
<!-- declarations: wake_detachment_stabilization -->
- **Current:** returns the assumed scalar normalization `shear = A/α_s`.
- **Intended claim:** under a specified wake evolution or boundary model, a defined
  normalized shear or perturbation stays bounded or decays after detachment.
- **Missing objects/assumptions:** spatial/time domain, wake/phase boundary,
  solution class, norm and stability criterion; nonzero or positive admittance.
- **Intermediate results:** first validate the normalization on its domain; then
  prove an energy/decay estimate that actually implies the chosen stability.
- **Decision block:** normalization is not stabilization. Select dynamics, boundary
  conditions and meaning of stability before stating that stronger target.
  Investigate L2/L3; a finite normalization lemma is independent of that choice.

## B. Simplified structures and conditional models

### B1. Coordinate fields, conservation and covariant geometry
<!-- declarations: partial_deriv metric_divergence CoordinateConserved constant_coordinate_conserved exists_coordinate_conserved coordinate_field_not_conserved divergence_expansion bernoulli_energy_conservation navier_stokes_momentum_conservation -->
Current divergence is a sum of coordinate derivatives with no connection terms;
the baseline axiom asserts it vanishes for every field. That universal assertion
is inconsistent (issue #9), not an admissibility condition. The finite repair is
a predicate on selected fields and explicit conservation hypotheses.

**Merged-source update:** the [conservation repair](conservation.md) removes that
axiom. `CoordinateConserved` now restricts selected fields; constant fields provide
a nonempty solution class, and `coordinate_field_not_conserved` proves the
counterexample. The declaration marker above tracks this current API, while the
baseline explanation retains the history of the finding. A stronger geometric
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
<!-- declarations: tensor_contract unified_action_separation modified_poisson_equation unified_wave_propagation -->
Current action separation is a Frobenius quadratic identity; “variation” is assumed
for arbitrary scalar operators and the wave result uses an arbitrary additive map.
Retain these as conditional algebra. A physical target needs a selected Lorentzian
contraction, field space, action integral, source dependence and admissible
variations with boundary conditions. Prove the first variation and integration by
parts, then the Euler–Lagrange PDE; prove a solution or estimate for each quantity
claimed regularized, separately from rescaling. Specify actual differential
operators before propagation results. **Decision block:** fixed versus varied
source, background versus dynamical metric, linearized versus nonlinear action,
and what “finite” means. The Lorentzian contraction correction is a bounded
algebraic step; it does not supply variational dynamics. Investigate L1/L2/L3
(issues #10/#16).

### B4. Tensor Lie derivative and symmetries
<!-- declarations: lie_derivative is_translationally_symmetric lorentz_symmetry_broken conformal_pressure_coupling -->
At the audit, the operator is only `X^α ∂_α U_μν`. The correct fixed-chart covariant
rank-two formula adds `U_αν ∂_μ X^α + U_μα ∂_ν X^α`. The finite targets are constant
translation agreement, `L_x U = 2U` for a constant tensor, and an actual isotropic
boost residual. PR #48 supplies these (see status above). Further targets need
regular dynamic fields, all selected generators, and a chart-change or flow/pullback
interpretation. **Decision block:** state which transformations and which fields
are invariant; one directional derivative vanishing does not imply homogeneity.
Conservation/Noether claims require a separately specified action. Investigate L2/L6.

### B5. Fluid projections and weak-field ordering
<!-- declarations: kinematic_accel_f div_T_perp_f geometric_navier_stokes longitudinal_transport_acceleration -->
Current results rename component derivatives and rearrange an assumed zero sum;
they do not derive material acceleration. Define physical velocity, density,
pressure and stress, the constitutive mapping to `U`, and mass continuity. Prove
`ρ(∂_t v + (v·∇)v)` equals the selected pressure/stress force, with signs and units.
If using a weak-field approximation, introduce a small parameter, retained orders
and remainder bounds before the expansion; track both moving-frame shear and
isotropic corrections at that order. **Decision block:** select the constitutive
law and approximation regime. A finite exact tensor identity is an alternative
smaller claim, not a substitute for the PDE. Investigate L2/L4 (issues #17/#18).

### B6. Gauge, exterior calculus, waves and discrete symmetries
<!-- declarations: Omega dressing_field_invariance transverse_wave_propagation T_symmetry_mass T_symmetry_charge P_symmetry_mass P_symmetry_axial P_symmetry_charge u1_gauge_invariance -->
`ext_deriv` is an arbitrary function, gauge claims cancel vectors, CPT-related
lemmas multiply signs, and wave propagation rearranges its assumed PDE. Define
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
Current “eigenvalue” results prove scalar square/diagonal identities; determinant
conclusions assume an expanded expression. Compute the actual aligned determinant
first, using `α_s ≠ 0`; this is the selected task. Full spectra additionally require
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
<!-- declarations: metric_is_continuous metric_is_cavitated legal_cavitation_collapse cavitated_determinant_lock -->
The [saturation repair](saturation-limits.md) supplies a positive scalar subtype,
subcritical total-pressure bounds, continuity, one-sided spatial divergence and
no-finite-limit theorems. Exact totalized zero values are kept separately. A
nonzero-rotation aligned boundary matrix has determinant zero, disproving the
spin-lock inference from actual determinant zero; denominator clearing is valid
only at nonzero admittance. A bounded inverse-derived scalar and an explicitly normalized
matrix family are distinct from the raw divergent family.
**Supplied author decision:** [#43, point 1](https://github.com/lilalittle/asymmetric-tensor/issues/43#issuecomment-6217484113)
assigns zero-division evaluation a discrete post-cavitation convention, separate
from continuum relations on `(0, 1]` and their divergent positive-side limit.
**Remaining scope:** incorporate that clarification in the manuscript, including
the determinant-domain correction. A transition or matching law, or a physical
identification of the normalized/strain examples, would require additional
modeling; none follows from `inv_zero`. Investigate L2/L8 (issue #12). Restricting
a finite theorem to `a ≠ 0` does not require a physical post-yield model.

### B9. Mass, energy, pressure partition and force hierarchy
<!-- declarations: tensor_vev_origin orthogonal_mass_extraction topological_yield_limit yield_partition mass_yield_equivalence geometric_action_boundary spatial_confinement_gradient action_constant_identity interaction_hierarchy_gravity interaction_hierarchy_weak interaction_hierarchy_strong interaction_hierarchy_em -->
Current formulas derive consequences of stipulated radius/energy relations and
partitions. Define stored energy separately from signed shear pressure, identify
inertial/gravitational mass assumptions, and state an acyclic assumption graph for
`E = ℏω`, `E = mc²`, Compton radius, `κ = h`, and Planck threshold. A 50/50 load
partition needs a solution/variational argument, not eigenvector normalization.
For force ratios, prove the exact baseline formula first and explicitly define
any added coupling. **Decision block:** select energy functional, constitutive
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
A null-geodesic/Fermat derivation or empirical distance comparison is additional
work. Investigate L2/L3/L8 (issues #23/#25/#26).

### B12. Spinorial sign, quantization and scattering
<!-- declarations: rydberg_energy_quantization dirac_spinor_double_cover mott_scattering_cross_section cp_violation_energy_shift -->
The source uses a real `n_integer`, cosine identities, a half-angle identity for an
assumed amplitude, and a sign flip of an assumed scalar energy. A finite spectrum
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
The current theorems respectively multiply an assumed pressure by area, rearrange
an assumed zero pressure gradient, equate two assumed identical travel times,
return an assumed zero force integral, and rearrange an assumed conserved sum.
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
rewrite a reciprocal power, derive a stipulated crossover scaling, and prove `k², ω² > 0`. The intended stronger claims
need, respectively, a transformation/deformation and volume Jacobian; a field
coupling law; a cylindrical equilibrium and perturbation evolution; a complex
response/relaxation model; and actual spatial/time differential operators acting
on Fourier modes. Intermediate targets are a computed Jacobian, verified component
ratio, a linearized perturbation operator and growth rate, a derived response phase,
and the mode identities for those operators. **Decision block:** choose those
models and domains; pressure algebra does not imply an instability, and positive
squares do not supply a curvature or dispersion decomposition. Investigate
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

## C. Dependencies, alternatives and author decisions

### True mathematical inputs to the selected finite task

Only the existing `U_hat`, `symPart`, `antiPart`, real matrix determinant/trace,
and elementary nonzero-denominator algebra are used. The required parameter
restriction is `a ≠ 0` for the general determinant, and `a > 0` for positive
volume-density formulas. No unresolved external implementation issue provides
an input to that proof. Audit the proof dependencies to exclude the baseline's
universal conservation axiom; its repair is a repository-consistency integration
concern, not a determinant hypothesis.

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

- `python3 tests/check_roadmap.py` checks that every `h_target` declaration and
  every Section 16 theorem is inventoried, declaration references exist, the
  candidate library paths exist, and the finite determinant contract passes
  independent exact-arithmetic regression examples.
- `lake build` checks the unchanged production source against the pinned setup.
- `lake env lean tests/RoadmapTargets.lean` checks the proposed target types and
  matrix specialization. It does **not** prove the proposed targets.
- `lake env lean tests/RoadmapCounterexample.lean` proves the actual zero-electric
  rotational counterexample, skew symmetry and zero trace, and prints axiom audits.
  This bounded evidence is separate from the general target specifications.
- `git diff --check` checks patch whitespace.

This deliverable ends at a concrete mathematical contract and a validated
inventory. General production determinant proofs, author-approved manuscript correction,
new issue creation, publication and issue closure are outside this planning patch.
