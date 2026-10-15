import AsymmetricTensor

open AsymmetricTensor

example : 5 * decimalLog ((10 : ℝ) / 1) = 5 := by
  simpa using tenfold_distance_magnitude_anomaly

example (r : ℝ) (hr : 0 < r) : 5 * decimalLog ((10 * r) / r) = 5 := by
  have hratio : (10 * r) / r = 10 := by
    exact mul_div_cancel_right₀ 10 (ne_of_gt hr)
  rw [hratio]
  exact tenfold_distance_magnitude_anomaly

example (r : ℝ) (hr : 0 < r) : 5 * decimalLog (r / r) = 0 := by
  simp [decimalLog, ne_of_gt hr]

#print axioms logarithmic_magnitude_anomaly
#print axioms tenfold_distance_magnitude_anomaly
#print axioms magnitude_anomaly_divergence

example (mu_o mu_l r z : ℝ) (hr : 0 < r) (hz : 0 < 1 + z)
    (ho : mu_o = 5 * decimalLog ((10 * r) * (1 + z)) + 25)
    (hl : mu_l = 5 * decimalLog (r * (1 + z)) + 25) :
    mu_o - mu_l = 5 := by
  have h := logarithmic_magnitude_anomaly mu_o mu_l (10 * r) r z
    (mul_pos (by norm_num) hr) hr hz ho hl
  have hratio : (10 * r) / r = 10 := mul_div_cancel_right₀ 10 (ne_of_gt hr)
  rw [hratio, tenfold_distance_magnitude_anomaly] at h
  exact h
