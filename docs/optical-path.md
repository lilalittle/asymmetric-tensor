# Finite optical paths for the exponential ansatz

This is the Lean mathematical repair for [issue #26](https://github.com/lilalittle/asymmetric-tensor/issues/26),
using the base-10 normalization repair from [issue #25](https://github.com/lilalittle/asymmetric-tensor/issues/25).
The source is manuscript v9 (September 25, 2026), Sections 15.3-15.5,
[Eqs. (235)-(239), pages 49-50](../papers/asymmetric-metric-tensor.pdf#page=49).
The manuscript is unchanged by this implementation.

## Explicit model and domain

Fix a real scale `L > 0`, held constant along the radial path. Adopt the
manuscript's exponential ansatz for the pressure fraction:

\[
q(s) = (1-e^{-s/L})^2,\qquad
n(s) = \frac{1}{1-q(s)}
     = \frac{1}{e^{-s/L}(2-e^{-s/L})}.
\]

Here `s ≥ 0`, and the endpoint `r` is any finite nonnegative real number.
Strict path and anomaly results require `r > 0`. All distances and `L`
use the same units. There is no infinite interval or singular limiting
endpoint in these theorems.

The parameter name `L` deliberately does not settle whether the paper's
`ct` or `R_h` is a causal boundary, an age radius, a Hubble radius, or a
characteristic length. The proof does not require `r < L` or `r ≤ L`.
It applies to every finite interval in the stated mathematical domain,
including a shorter interval if the author later selects one.
[Issue #23](https://github.com/lilalittle/asymmetric-tensor/issues/23)
still owns the physical interpretation, boundary reconciliation, and
propagation to other cosmological claims. If the author changes the ansatz,
the consequences must be checked again for that replacement.

Lean functions are total on the reals. Their definitions therefore exist
outside the stated domain; the physical interpretation and positivity
theorems do not. In particular, Lean evaluates division by zero as zero.
The tests show that `L = 0` makes this expression give `n = 1` and
`optical_distance 0 r = r`, so the positive-scale condition is essential.

## What is proved

The definitions and theorems are in Section 15.4 of
[`AsymmetricTensor.lean`](../AsymmetricTensor.lean):

- `exponential_refractive_index_eq_ansatz` proves the normalized pressure
  and factored-denominator formulas agree.
- `exponential_denominator_pos` proves the denominator is strictly positive
  for `L > 0` and `s ≥ 0`. No nonzero denominator is assumed silently.
- `exponential_refractive_index_zero` gives `n(0) = 1`.
- `exponential_refractive_index_one_le` gives `n(s) ≥ 1` for `s ≥ 0`.
- `exponential_refractive_index_one_lt` gives `n(s) > 1` for `s > 0`.
- `exponential_refractive_index_continuousOn` establishes continuity on
  the nonnegative half-line.
- `exponential_refractive_index_intervalIntegrable` establishes
  integrability on every finite interval `[0,r]`, including `r = 0`.
- `optical_distance` is the actual interval integral
  `∫ s in 0..r, exponential_refractive_index L s`.
- `optical_distance_gt` proves `r < optical_distance L r` when `r > 0`.

For the strict integral comparison, the proof compares `n` with the
constant function `1`. Both are continuous on `[0,r]`; `n ≥ 1` throughout,
and `n(r) > 1` at a point of this nontrivial interval. Mathlib's strict
integral comparison supplies the inequality. Thus the proof does not assume
`r_opt > r`, does not assume strictness at the origin, and does not use a
numerical quadrature approximation.

## Actual travel-time integral

For a positive constant baseline speed `c₀`, define the model speed and
travel time by

\[
v(s)=c_0/n(s),\qquad T(r)=\int_0^r\frac{1}{v(s)}\,ds.
\]

- `refractive_speed_eq_ansatz` identifies this speed with
  `c₀ * (1 - (1 - exp(-s/L))²)`, the stated ansatz form of Eq. (233).
- `refractive_speed_pos` establishes positive speed on the allowed domain;
  `refractive_speed_lt` establishes `v(s) < c₀` at positive radius.
- `refractive_travel_time_intervalIntegrable` proves integrability of the
  inverse speed on the finite interval.
- `refractive_travel_time_eq` proves `T(r) = optical_distance L r / c₀`.
- `refractive_travel_time_delay_pos` proves `T(r) - r/c₀ > 0` for `r > 0`.
- `refractive_travel_time_zero` gives zero transit time at zero path length.

This is a path/time-delay theorem for the specified radial speed model.
It does not derive the speed from a null-geodesic differential equation,
establish Fermat's principle, or reproduce a measured or standard
solar-system Shapiro-delay formula. The pre-existing
`shapiro_delay_refraction` theorem is explicitly documented as a local
speed identity; its name remains for compatibility.

## Correct base-10 magnitude consequence

Issue #25 supplies `decimalLog x = Real.log x / Real.log 10`, the
base-10 modulus identity, and the exact regression
`5 * decimalLog 10 = 5`. The absolute distance-modulus expressions treat
distances as numerical values in Mpc, implicitly divided by the reference
`1 Mpc`, with the conventional `+25` offset for the `10 pc` reference.
The final ratio `r_opt/r` is dimensionless and independent of the common
choice of distance units.

`optical_magnitude_anomaly_pos` now derives

\[
5\log_{10}(r_{\rm opt}/r)>0
\]

from the optical integral theorem. `magnitude_anomaly_of_optical_path`
connects this result to the two base-10 modulus prescriptions in Eq. (239),
with the explicit common-factor condition `1 + z > 0`. It proves both

\[
\mu_{\rm obs}-\mu_{\rm lin}
 =5\log_{10}(r_{\rm opt}/r),\qquad
\mu_{\rm obs}-\mu_{\rm lin}>0.
\]

The distance-modulus prescriptions remain hypotheses. These results do
not establish Tolman scaling, a luminosity-distance identification,
empirical agreement with Pantheon+, or an explanation of dark energy.
No asymptotic divergence theorem or finite-horizon saturation is claimed.

## Reproduce and audit

Use the committed Lean toolchain and Mathlib manifest. After following
the repository setup instructions, run:

```sh
lake build
lake env lean tests/DistanceModulus.lean
lake env lean tests/OpticalPath.lean
```

If downloading only the necessary official Mathlib cache, include
`Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` along with the
repository's other imports. No package or toolchain version changed.

The optical regression file checks the actual integral definitions,
positive/nonnegative domains, the origin, an excluded zero scale, finite
radii at and beyond the scale, speed and time identities, the strict
modulus difference, and base-10 normalization. It prints the axiom dependencies
of the new substantive theorems. They use only Lean's standard logical
foundations (`propext`, `Classical.choice`, `Quot.sound`), not the repository's
physical constant or conservation axioms. No `sorry` or new axiom is added.
