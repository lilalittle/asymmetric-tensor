import AsymmetricTensor

open AsymmetricTensor

-- The path and time are integrals, not unconstrained scalar hypotheses.
example (L r : ℝ) :
    optical_distance L r = ∫ s in (0 : ℝ)..r, exponential_refractive_index L s := rfl

example (L c₀ r : ℝ) :
    refractive_travel_time L c₀ r = ∫ s in (0 : ℝ)..r, 1 / refractive_speed L c₀ s := rfl

-- The ansatz agrees with manuscript Eqs. (236)-(237); the origin is not strict.
example (L s : ℝ) :
    exponential_refractive_index L s = 1 / (1 - (1 - Real.exp (-s / L)) ^ 2) :=
  exponential_refractive_index_eq_ansatz L s

example (L : ℝ) : exponential_refractive_index L 0 = 1 := by simp

example (L s : ℝ) (hL : 0 < L) (hs : 0 ≤ s) :
    1 ≤ exponential_refractive_index L s :=
  exponential_refractive_index_one_le L s hL hs

example (L s : ℝ) (hL : 0 < L) (hs : 0 < s) :
    1 < exponential_refractive_index L s :=
  exponential_refractive_index_one_lt L s hL hs

example (L : ℝ) (hL : 0 < L) :
    ContinuousOn (exponential_refractive_index L) (Set.Ici 0) :=
  exponential_refractive_index_continuousOn L hL

example (L r : ℝ) (hL : 0 < L) (hr : 0 ≤ r) :
    IntervalIntegrable (exponential_refractive_index L) MeasureTheory.volume 0 r :=
  exponential_refractive_index_intervalIntegrable L r hL hr

example (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    r < optical_distance L r := optical_distance_gt L r hL hr

-- The finite scale point and a larger finite radius both belong to this
-- mathematical domain. Neither test assigns a physical horizon to the scale.
example (L : ℝ) (hL : 0 < L) : L < optical_distance L L :=
  optical_distance_gt L L hL hL

example (L : ℝ) (hL : 0 < L) : 2 * L < optical_distance L (2 * L) :=
  optical_distance_gt L (2 * L) hL (mul_pos (by norm_num) hL)

example (L : ℝ) : optical_distance L 0 = 0 := by simp

-- At the excluded scale L=0, Lean's totalized division gives a trivial
-- n=1 and path=r. A strict theorem without hL would therefore be false.
example (r : ℝ) : optical_distance 0 r = r := by
  norm_num [optical_distance, exponential_refractive_index]

example (L c₀ s : ℝ) (hL : 0 < L) (hc : 0 < c₀) (hs : 0 ≤ s) :
    0 < refractive_speed L c₀ s := refractive_speed_pos L c₀ s hL hc hs

example (L c₀ s : ℝ) (hL : 0 < L) (hc : 0 < c₀) (hs : 0 < s) :
    refractive_speed L c₀ s < c₀ := refractive_speed_lt L c₀ s hL hc hs

example (L c₀ s : ℝ) :
    refractive_speed L c₀ s = c₀ * (1 - (1 - Real.exp (-s / L)) ^ 2) :=
  refractive_speed_eq_ansatz L c₀ s

example (L c₀ r : ℝ) (hL : 0 < L) (hr : 0 ≤ r) :
    IntervalIntegrable (fun s => 1 / refractive_speed L c₀ s) MeasureTheory.volume 0 r :=
  refractive_travel_time_intervalIntegrable L c₀ r hL hr

example (L c₀ r : ℝ) : refractive_travel_time L c₀ r = optical_distance L r / c₀ :=
  refractive_travel_time_eq L c₀ r

example (L c₀ r : ℝ) (hL : 0 < L) (hc : 0 < c₀) (hr : 0 < r) :
    0 < refractive_travel_time L c₀ r - r / c₀ :=
  refractive_travel_time_delay_pos L c₀ r hL hc hr

example (L c₀ : ℝ) : refractive_travel_time L c₀ 0 - 0 / c₀ = 0 := by simp

example (L r : ℝ) (hL : 0 < L) (hr : 0 < r) :
    0 < 5 * decimalLog (optical_distance L r / r) :=
  optical_magnitude_anomaly_pos L r hL hr

-- Concrete distance-modulus expressions, with no assumed path inequality
-- or assumed positive anomaly. The common redshift factor is positive.
example (L r z : ℝ) (hL : 0 < L) (hr : 0 < r) (hz : 0 < 1 + z) :
    0 < (5 * decimalLog (optical_distance L r * (1 + z)) + 25) -
      (5 * decimalLog (r * (1 + z)) + 25) :=
  (magnitude_anomaly_of_optical_path _ _ L r z hL hr hz rfl rfl).2

-- Retain the #25 normalization regression: tenfold distance means five magnitudes.
example : 5 * decimalLog 10 = 5 := tenfold_distance_magnitude_anomaly

#print axioms exponential_denominator_pos
#print axioms exponential_refractive_index_one_le
#print axioms exponential_refractive_index_one_lt
#print axioms exponential_refractive_index_continuousOn
#print axioms exponential_refractive_index_intervalIntegrable
#print axioms optical_distance_gt
#print axioms refractive_speed_pos
#print axioms refractive_speed_lt
#print axioms refractive_speed_eq_ansatz
#print axioms refractive_travel_time_intervalIntegrable
#print axioms refractive_travel_time_eq
#print axioms refractive_travel_time_delay_pos
#print axioms optical_magnitude_anomaly_pos
#print axioms magnitude_anomaly_of_optical_path
