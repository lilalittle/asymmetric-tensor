import AsymmetricTensor

open AsymmetricTensor

-- Eq. (224) contains no extra alpha multiplier on F_fund.
example (m_e alpha a_0 : ℝ) (hm : m_e ≠ 0) (ha : alpha ≠ 0)
    (h_radius : a_0 = hbar / (alpha * m_e * c)) :
    F_fund a_0 = alpha^2 * m_e^2 * c^3 / hbar := by
  exact interaction_hierarchy_em m_e alpha a_0 hm ha h_radius

-- The two symbolic ratios have different exponents.
example (m_e alpha a_0 L_crit : ℝ) (hm : m_e ≠ 0) (ha : alpha ≠ 0)
    (h_a_0 : a_0 = hbar / (alpha * m_e * c))
    (h_L_crit : L_crit = alpha * hbar / (m_e * c)) :
    F_fund a_0 / F_fund L_crit = alpha^4 ∧
      (alpha * F_fund a_0) / F_fund L_crit = alpha^5 := by
  exact ⟨interaction_hierarchy_em_strong_ratio m_e alpha a_0 L_crit hm ha h_a_0 h_L_crit,
    interaction_hierarchy_em_scaled_strong_ratio m_e alpha a_0 L_crit hm ha h_a_0 h_L_crit⟩

-- A nonunit coupling catches accidental conflation of alpha^4 and alpha^5.
example :
    F_fund (hbar / ((1 / 2 : ℝ) * 1 * c)) /
      F_fund (((1 / 2 : ℝ) * hbar) / (1 * c)) = (1 / 16 : ℝ) := by
  have h := interaction_hierarchy_em_strong_ratio 1 (1 / 2)
    (hbar / ((1 / 2) * 1 * c)) (((1 / 2) * hbar) / (1 * c))
    (by norm_num) (by norm_num) rfl rfl
  norm_num at h ⊢
  exact h

example :
    ((1 / 2 : ℝ) * F_fund (hbar / ((1 / 2 : ℝ) * 1 * c))) /
      F_fund (((1 / 2 : ℝ) * hbar) / (1 * c)) = (1 / 32 : ℝ) := by
  have h := interaction_hierarchy_em_scaled_strong_ratio 1 (1 / 2)
    (hbar / ((1 / 2) * 1 * c)) (((1 / 2) * hbar) / (1 * c))
    (by norm_num) (by norm_num) rfl rfl
  norm_num at h ⊢
  exact h

example : (1 / 16 : ℝ) ≠ (1 / 32 : ℝ) := by norm_num

-- Without nonzero mass, totalized division yields zero, not alpha^4.
example :
    F_fund (hbar / ((1 / 2 : ℝ) * 0 * c)) /
      F_fund (((1 / 2 : ℝ) * hbar) / (0 * c)) ≠ (1 / 2 : ℝ)^4 := by
  norm_num [F_fund]
