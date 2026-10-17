# Admissible domain and saturation limits

This mathematical correction addresses [issue #12](https://github.com/lilalittle/asymmetric-tensor/issues/12).
It separates a continuous, subcritical component family from exact evaluation of
Lean's totalized formulas at zero. It does not define a new physical phase or
revise the published PDF. The manuscript's publication remains Binyamin's
responsibility.

## Supplied author interpretation

In [the author decision on #43, point 1](https://github.com/lilalittle/asymmetric-tensor/issues/43#issuecomment-6217484113),
Binyamin explicitly restricts the continuum compliance relations to `(0, 1]`,
identifies the positive-side saturation boundary as singular with divergent
spatial components, and assigns the totalized zero-input identities a discrete
post-cavitation regime interpretation. This supplies the intended convention;
it is not awaiting a further choice about whether zero division was intended
as an analytic limit. The proofs below distinguish that convention from the
continuum limits and from the determinant of the actual boundary matrix.
The comment announces manuscript-v10 scope updates; this patch does not claim
that the committed PDF already incorporates them or derive a transition law.

## Domain contract

`SubcriticalPressure capacity pressure` means

- `capacity > 0`;
- `0 ≤ pressure < capacity`;
- `pressure` denotes the **total applied load** used in the scalar capacity
  equation, including any gravitational, dynamic, and shear contributions in
  that model. A bound on only one contribution does not bound their sum.

Then `q = 1 - pressure/capacity` lies in `(0, 1]`, and the positive square root
`pressureAdmittance capacity pressure = sqrt(q)` lies in `(0, 1]`. In particular,
`capacity`, `capacity - pressure`, `q`, and `sqrt(q)` are strictly positive.
Reciprocals of these quantities are defined in the usual nonzero sense, and
logarithms have positive arguments. `pressure_admittance_exp_log` checks the
positive-argument logarithm contract. Nonnegative pressure is needed for the
upper bound `sqrt(q) ≤ 1`, not for reciprocal divergence itself.

`AdmissibleAdmittance` enforces `0 < alpha_s ≤ 1` as a subtype, and
`admissibleTensor` accepts that subtype. Its fixed-load component family is
proved continuous. This is scalar admissibility, **not** a theorem that arbitrary
off-diagonal loads preserve matrix invertibility. The separately exposed
`U_hat` is retained as a totalized algebraic formula for compatibility and exact
counterexamples. The opaque dynamic fields are not automatically admissible.

## The true one-sided limits

The following are checked filter limits, with no additional physical axioms:

- `inverse_sq_tendsto_at_top`: `1/a² → +∞` as `a → 0+`.
- `admissible_inverse_sq_tendsto_at_top`: the same limit within `(0, 1]`.
- `subcritical_pressure_tendsto_at_top`: `1/(1-p/capacity) → +∞`
  as `p ↑ capacity` within `[0, capacity)`.
- `pressure_admittance_inverse_sq_tendsto_at_top`: the same result for the
  actual square-root parametrization `1/(pressureAdmittance capacity p)²`.
- `tensor_spatial_diagonal_tendsto_at_top`: the actual `U_hat` spatial diagonal
  diverges for every fixed choice of the off-diagonal loads.
- `inverse_sq_has_no_finite_limit`: no finite real number is this one-sided
  spatial limit.

In contrast, `totalized_inverse_sq_at_zero` says only that Lean evaluates
`1/(0:ℝ)²` to zero. `unloaded_tensor_at_zero` shows that setting admittance and
all loads to zero gives the zero matrix, not a matrix with three positive
spatial entries. The old `legal_cavitation_collapse` name is deprecated and
retained as a compatibility wrapper for the author's discrete post-cavitation
convention. The zero-input identity checks that convention's scalar evaluation;
it does not derive physical loss of elasticity or a transition from the continuum
family. The author expressly excludes its interpretation as an analytic limit.

## Determinant boundary correction

The manuscript's Eq. (141) is a rational determinant formula for the aligned
configuration on **nonzero** admittance. Writing its normalized slip and
rotation terms as `E` and `B`, denominator clearing gives

`-1/a⁴ - B² + E²/a⁴ = 0  ↔  E² - a⁴ B² = 1`, provided `a ≠ 0`.

`cavitation_formula_iff_of_ne_zero` proves precisely this scalar equivalence.
It is not an independent proof that the scalar formula equals the determinant
of an arbitrary component matrix. The Eq. (141) determinant identification and
its chosen frame must be justified separately.

The extension to `a = 0` is invalid, for two independent reasons:

1. At `a=E=B=0`, Lean's rational expression is zero but the cleared equation is
   false. `cavitation_formula_not_equivalent_at_zero` checks this counterexample.
2. The actual aligned boundary matrix `U_hat 0 alpha vx vy 0 0 0 oz tp` has a
   zero last row, so its determinant is zero for **every** slip and rotation.
   Its determinant is therefore not the totalized rational value `-B²`.
   `boundary_determinant_does_not_force_zero_rotation` uses rotation square
   one, and `totalized_formula_not_boundary_determinant` checks the mismatch.

This second statement concerns the aligned transverse configuration. A general
four-dimensional antisymmetric boundary matrix need not have zero determinant.
The old `cavitated_determinant_lock` is deprecated; its replacement name
`totalized_cavitation_formula_at_zero` explicitly describes scalar algebra.
The author's discrete convention does not change this mathematical distinction:
its scalar hypothesis is not actual boundary determinant collapse. A physical
spin lock or phase transition still does not follow from that determinant alone.

Taking a limit of the cleared equation is also different from substituting in
the rational formula. For a family satisfying the nonzero equation, obtaining
`E² → 1` additionally needs `a⁴ B² → 0` (for example, bounded `B`) and suitable
limits of `E`. A rotation that diverges with admittance can violate that
condition. No such dynamical or boundedness law is assumed here.

## Manuscript incorporation and remaining scope

The supplied author decision settles the continuum-versus-discrete interpretation.
For the committed September 25, 2026 v9 PDF, incorporation of that decision should
preserve the following mathematical distinctions:

- **§3.1, Eq. (117), Eq. (120), and §8.1:** use the positive, subcritical domain
  and one-sided limits, as the author has specified. Saturation is a boundary of
  this domain; the discrete convention is separate. Divergence alone does not
  derive a phase-transition law or discrete mass.
- **§9.7, Eqs. (141)–(142):** restrict the rational identity and its
  denominator-clearing equivalence to `alpha_s ≠ 0`; remove the claim that the
  same equivalence evaluates the full closed interval `[0,1]`. Label any
  limiting boundary equation with its assumptions on the varying loads.
- **§9.8:** state the author's distinction explicitly: the temporal continuum
  coefficient tends to zero and each spatial coefficient diverges to positive
  infinity; totalized zero-input evaluation implements the separate discrete
  convention. The claimed finite raw signature limit `(0,+,+,+)` cannot be a
  finite real component-matrix limit. In addition, signature terminology
  naturally applies to the symmetric form, not eigenvalues of an arbitrary
  nonsymmetric matrix.
- **§6.2 and finite-strain language:** specify the strain observable and its
  relationship to the raw components. A bounded inverse-derived scalar
  `(1 - 1/(1/a²))/2 = (1-a²)/2` tends to `1/2`, as checked by
  `inverse_derived_scalar_strain` and `inverse_derived_scalar_strain_tendsto`.
  That fact can coexist with diverging raw components. It does not by itself
  construct the paper's nonlinear strain or curvature tensor.

An explicit normalization is a separate mathematical object. For fixed finite
loads, multiplying the whole matrix by `a²` gives a punctured limit
`diag(0,1,1,1)`: the temporal entry tends to zero, each spatial diagonal tends
to one, and the scaled off-diagonal entries tend to zero. The full matrix limit is checked in `normalized_tensor_tendsto`; the two diagonal
limits are also checked in `normalized_temporal_diagonal_tendsto_zero` and
`normalized_spatial_diagonal_tendsto_one`. The exact totalized value of
`a² • U_hat a ...` at `a=0` is nevertheless zero, as
`normalized_tensor_at_zero` checks. A normalized limit must not be silently
identified with either the raw limit or the exact zero-input value.

The author has selected the discrete zero-division convention, not identified
it with this normalized limit or the bounded scalar strain example. Those
examples supply no additional physical model. A stronger claim connecting
continuum and discrete regimes would require a specified transition or matching
law; none is supplied or inferred here. Any physical use of the normalized
family or strain example likewise needs an explicit observable definition and
justification. The remaining manuscript acceptance item is to incorporate the
supplied clarification consistently, including the determinant-domain correction,
rather than to request the already-supplied choice again.

## Regression and proof audit

`tests/SaturationLimits.lean` checks ordinary subcritical inputs, saturation,
negative pressure, zero capacity, totalized supercritical square roots,
actual matrix entries, both true-limit filters, denominator-clearing failures,
and the nonzero-rotation boundary counterexample. It also checks the retained
compatibility names and exact custom-axiom sets. Pure analysis and scalar
algebra require no custom axioms; statements containing `U_hat` retain only
its existing constant `c` in their dependency set.

Run `bash scripts/verify.sh` and `git diff --check`. The historical equation
ledger is unchanged: its source, hashes, mapping, and coverage remain evidence
for the pinned historical snapshot, not for this repair.

## V3.0 review-vehicle compatibility

This patch is based on main `c6e33e56f80a4f65743ea9f84c19c03d2afe7260`,
whose source tree matches the earlier base `9cc32ea7e141a7a1a039494d47e655fcc7f545e8`,
not on [PR #61](https://github.com/lilalittle/asymmetric-tensor/pull/61).
The reviewed v3.0 head `2fa2e6ad2bb836043ecf83831e51096ca7dbdf6c` retains
the totalized-zero identities and substitutes zero into the nonzero-domain
rational determinant formula. The author clarification supplies the discrete
interpretation; it does not make that scalar formula the boundary determinant. Its §§9.7–9.8 use real powers
`a^(-2:ℝ)` and `a^(-4:ℝ)` in place of explicit reciprocals. On positive `a`
these equal `1/a²` and `1/a⁴`; the distinction between a divergent positive
limit and a totalized zero value therefore survives that notation change.
`tests/SaturationLimits.lean` includes checked positive-domain equivalences
for both real-power notations and the `a^(-2:ℝ)` divergence theorem, each with
an exact empty custom-axiom set. These are notation-compatibility checks on
this main-based library, not a build of PR #61.

Source compatibility is a separate integration task: v3.0 removes the topic
modules and changes explicit parameter interfaces, including replacing the
free `t_p_val` argument with the model's `t_p = l_p/c`. The main-based `T2`
and `P_c_pos` interfaces are absent there. Imports, theorem application arguments,
and exact dependency audits must be adapted and rerun against the
author-approved integration. Matrix statements using the global `t_p` can
therefore acquire `l_p` dependencies; the current `c`-only checks do not certify
v3.0. This patch has not built or certified that
review-vehicle source, chosen its integration strategy, or changed its physics.
