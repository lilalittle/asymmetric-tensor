# Tensor Lie derivative: scope and paper mapping

This note addresses [issue #11](https://github.com/lilalittle/asymmetric-tensor/issues/11)
against manuscript **v9, September 25, 2026**, pages 18–20. The manuscript PDF is
unchanged. The correction here is to the Lean operator and its claimed scope.

## Operator and regularity

`SpaceTime = Fin 4 → ℝ` is one fixed real coordinate chart. `MetricField` stores
the **covariant `(0,2)` components** of a tensor, including nonsymmetric tensors.
`lie_derivative X U x` now computes

    (L_X U)μν = Σα Xα ∂α Uμν + Σα Uαν ∂μ Xα + Σα Uμα ∂ν Xα.

The former expression is retained as `directional_transport`. It is generally
not a tensor Lie derivative. `is_lie_invariant` allows any specified generator;
`is_translationally_symmetric` now accepts a translation vector and constructs
a constant generator, rather than allowing an arbitrary vector field.

`partial_deriv` uses Mathlib's totalized `fderiv`. A classical interpretation of
the full expression at a point requires differentiability of each component of
both fields at that point. `lie_derivative_eq_of_hasFDerivAt` explicitly takes
those derivative witnesses and proves the component formula. The translation,
dilation and linear-generator formulas also hold as identities of the totalized
operator for arbitrary `U`, because they do not use a differentiation rule for
`U`. This does not assert classical differentiability of an arbitrary tensor
field. The generators are constant or linear; their component derivatives are
proved. In all constant-tensor regressions both fields are differentiable.

No chart-change law, flow/pullback construction on a general manifold, covariant
connection, or regularity of the opaque `U_hat_dynamic` fields is established by
these results.

## Paper-to-Lean map

| Manuscript v9 | Lean result | Exact scope |
|---|---|---|
| Eq. (91), p. 18 | `lie_derivative`; `lie_derivative_eq_of_hasFDerivAt` | All three covariant rank-two terms in a fixed chart; explicit component derivative witnesses for the classical interpretation |
| Eq. (92), p. 19 | `lie_derivative_translation` | Constant generator gives precisely directional transport; one generator's vanishing does not imply every partial derivative vanishes |
| Eq. (93), p. 19 | `partial_deriv_linear`; `lie_derivative_linear` | Arbitrary constant mixed matrix `B`, with `Xα = Σβ Bαβ xβ` |
| Eqs. (95)–(96), p. 19 | `lie_derivative_const_boost_zero_spatial`; `lie_derivative_isotropic_boost`; `lie_derivative_isotropic_boost_lowered` | Residual derived from the operator for constant tensors, then specialized to the isotropic symmetric sector |
| Symmetry limit following Eq. (96) | `lorentz_symmetry_broken` | Actual invariance of the constant isotropic tensor, positive admittance and a nonzero boost imply `a = 1`; the residual is no longer a premise |
| Eq. (99), p. 20 | `lie_derivative_dilation`; `lie_derivative_const_dilation`; `lie_derivative_const_identity` | `L_(σx) U = transport + 2σ U`; constant tensors satisfy `L_x U = 2U` |

## Boost convention and restriction

`boost_matrix b i` has mixed entries `B⁰ᵢ = Bⁱ₀ = b`, for `i ≠ 0`, and all
others zero. With the background convention `η = diag(-1,1,1,1)`, lowering the
first generator index gives the manuscript's `ω₀ᵢ = -b`. Consequently the computed
residual is

    (L_X S)0i = b (1/a² − a²) = −ω₀ᵢ (1/a² − a²).

There is no sign discrepancy once index positions are fixed. The diagonal tensor
`isotropic_covariant_tensor a = diag(-a²,1/a²,1/a²,1/a²)` is proved equal to the
existing `U_sym` for all its constant parameters by
`U_sym_eq_isotropic_covariant_tensor`. This is a calculation on a **constant
field**. It does not silently replace a varying field with a constant one.
The physical symmetry implication explicitly requires `a > 0`; the algebraic
formulas at `a = 0` use Lean's totalized division and have no singular-limit
interpretation.

The result does not establish the paper's broader claims about arbitrary dynamic
fields, conservation/Noether consequences, special conformal generators, or
symmetry breaking due to defects. In particular, a vanishing directional
transport or radial derivative alone does not establish spatial homogeneity.

## Regressions

Run the pinned toolchain and dependency cache, then:

    lake build
    lake env lean tests/LieDerivative.lean

The focused file checks the dilation counterexample (`(L_x η)00 = -2`), the
translation reduction and nonconstant translation/dilation examples, both index terms for a
general nonsymmetric tensor, all three boost directions, the lowered-parameter
sign, a full flat-metric boost invariance check, and the updated symmetry theorem.
Its axiom reports make dependencies auditable; the new derivative results must
not depend on the repository's unrelated conservation axiom or `sorryAx`.
