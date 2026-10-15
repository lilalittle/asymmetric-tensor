# Lorentzian contraction and action convention

This is the bounded Lean repair for [issue #10](https://github.com/lilalittle/asymmetric-tensor/issues/10), against manuscript v9 and repository revision `9f69988`. The existing Frobenius algebra is retained with compatible types. The new action API uses the background Minkowski inverse metric explicitly.

## Index and metric choices

- `T2` stores two lower-index components, such as `U_μν`.
- `raiseBoth gInv V` computes `g^{μα} g^{νβ} V_αβ`.
- `contract2 gInv U V` computes `U_μν V^{μν}` using that same `gInv`.
- `minkowskiInv` is `diag(-1,1,1,1)`. `minkowskiInv_sq` proves that this matrix is its own inverse. It is the unperturbed background `g` specified on [manuscript page 3](../papers/asymmetric-metric-tensor.pdf#page=3).
- `lorentzian_action_density U` is the dimensionless quadratic scalar `contract2 minkowskiInv U U` in Eqs. (65)–(66). It is not a spacetime-integrated action or a derived equation of motion.
- `kinematic_lagrangian_density U` is exactly `P_c / 4 * (lorentzian_action_density U - 4)`, the first line of Eq. (124). The exact separation theorem does not invoke the weak-field approximation in Eq. (122).

For a time-space antisymmetric pair `A_01 = e`, `A_10 = -e`, the Lorentzian scalar is `-2 e²`; for a spatial pair `A_12 = b`, `A_21 = -b`, it is `+2 b²`. Both strict sign theorems require nonzero amplitude. The mixed regression `e = 2`, `b = 3` gives `10`, whereas the Frobenius product gives `26`.

## The selected frame and Eqs. (121), (123)

`U_hat` is already the manuscript's comoving-frame component ansatz. This repair makes the frame data explicit:

- Covariant rest velocity `u_μ = (-1,0,0,0)`, so raised `u^μ = (1,0,0,0)`
- Covariant transverse slip `v_μ = (0,v_x,v_y,v_z)`
- Spatial projector `h_μν = diag(0,1,1,1) = η_μν + u_μ u_ν`
- Spatial vorticity `ω_0ν = 0`, `ω_12 = -Ω_z`, `ω_13 = Ω_y`, `ω_23 = -Ω_x`, with the opposite entries fixed by antisymmetry

`rest_frame_constraints` proves `u_μ u^μ = -1`, `u_μ v^μ = 0`, `u^μ h_μν = 0`, and `u^μ ω_μν = 0`. These are consequences of the displayed frame definitions, not additional physical axioms. `rest_symmetric_covariant_form` and `rest_antisymmetric_covariant_form` identify the existing `U_sym` and `U_anti` with the corresponding covariant formulas in that frame.

The checked formulas are:

- `symmetric_action_eq121`: `S_μν S^{μν} = α_s⁴ + 3/α_s⁴`, with `α_s ≠ 0`
- `spatial_slip_norm`: `v_μ v^μ = v_x² + v_y² + v_z²`
- `spatial_vorticity_contraction`: `ω_μν ω^{μν} = 2(Ω_x² + Ω_y² + Ω_z²)`
- `antisymmetric_action_eq123`: `A_μν A^{μν} = -2 α² v_perp²/c² + α² t_p² ω_μν ω^{μν}`

Thus no normalization factor is suppressed in translating vorticity to the three `Omega` components. The orthogonality and separation theorems apply more generally to the symmetric/antisymmetric parts of arbitrary real `4 × 4` matrices under the fixed Minkowski contraction. The derivations of Eqs. (121) and (123) are explicitly in `U_hat`'s selected frame; this change does not add a general-coordinate field construction or prove a coordinate-transformation law for the manuscript model.

`symmetric_action_components` is the underlying totalized real-algebra identity; Lean also evaluates it at `α_s = 0`. That evaluation must not be interpreted as the physical limit. The Eq. (121) interface states its nonzero domain explicitly. This is not a repair of the separate saturation-limit issue #12.

## Page 56 uses a different operation

The [page 56](../papers/asymmetric-metric-tensor.pdf#page=56) mixed-index measurement is `A^μ_ν = S^{μλ} A_λν`, with `S^{-1} = diag(-1/α_s²,α_s²,α_s²,α_s²)`. It raises **one** index with the inverse of `U_sym`, rather than both indices with the background `η^{-1}`.

- `raiseFirst` implements one-index raising with an explicit supplied inverse metric.
- `symmetricMetricInv_left_inverse` proves the claimed `S^{-1}` really is a matrix inverse when `α_s ≠ 0`.
- `mixed_electric_measurement` gives `A^0_1 = (α/α_s²)(v_x/c)`.
- `mixed_magnetic_measurement` gives `A^1_2 = -(α α_s²)t_p Ω_z`, with the sign fixed by the stored `ω_12` convention.

These component formulas are algebraically totalized, but interpreting `symmetricMetricInv` as an inverse requires the nonzero-admittance hypothesis. A regression confirms it is not an inverse at zero. The mixed-index operation is not substituted into the quadratic action definition.

## Legacy compatibility

`tensor_contract`, `contract_sym_anti_proven`, and `unified_action_separation` retain their original types and valid Frobenius meaning. The explicit aliases `frobenius_contract`, `frobenius_sym_anti_orthogonality`, and `frobenius_action_separation` are preferred for new purely algebraic uses. In particular, the legacy theorem named `unified_action_separation` must not be cited as a Lorentzian action result; use `lorentzian_action_separation`.

## Remaining manuscript correction and scope

The prose on [page 15](../papers/asymmetric-metric-tensor.pdf#page=15) calls the electromagnetic scalar `E² - B²`. Under the declared `(-,+,+,+)` convention, the implemented contraction and Eq. (123) instead have electric-negative/magnetic-positive signs, proportional to `B² - E²`. This inconsistency needs an author-approved prose correction. No PDF is modified or claimed corrected here.

The repair establishes the component contraction identities and exact scalar normalization. It does not prove the weak-field approximation, a curvature bridge, action variation, Maxwell equations, mass extraction, or empirical validity. The repository's separate conservation-axiom repair remains necessary; the new theorem dependency tests reject any dependence on that old axiom.

## Verification

Run from the repository root:

```sh
lake build
lake env lean tests/LorentzianAction.lean
```

The regression file checks the original electric-sign counterexample, magnetic and mixed fields, arbitrary-matrix orthogonality and separation, Eqs. (121)/(123), explicit frame constraints, vorticity normalization, the separate mixed measurements, the zero-admittance inverse failure, background subtraction, and legacy API compatibility. Its transitive axiom audit fails on `sorryAx`, the legacy conservation axiom, or any unexpected axiom; it permits only the exact existing physical-constant dependencies of each theorem and Lean's standard logical axioms. No new axioms or imports are introduced in the production source.
