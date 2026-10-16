-- ==========================================
-- SECTION 8: The Mass Mechanism (Topological Tensor Yield)
-- ==========================================
-- 8.1 The Tensor Yield Criterion (The VEV Origin)
variable (S_ii P_static P_dyn_val v_val : ℝ)
-- PROVEN LEMMA: The spatial diagonal Lorentz expansion
-- Formally derives S_ii = 1 / (1 - v^2/c^2) from thermodynamic capacities
lemma spatial_diagonal_lorentz_derivation (hc : c ≠ 0)
    (h_S_ii : S_ii = P_c / P_static)
    (h_Bernoulli : P_static = P_c - P_dyn_val)
    (h_P_dyn : P_dyn_val = (1 / 2) * rho_tau * v_val^2) :
    S_ii = 1 / (1 - v_val^2 / c^2) := by
  have h_Pc : P_c = (1 / 2) * rho_tau * c^2 := by rfl
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 hc
  calc
    S_ii = P_c / P_static := by exact h_S_ii
    _ = P_c / (P_c - P_dyn_val) := by rw [h_Bernoulli]
    _ = ((1 / 2) * rho_tau * c^2) / (((1 / 2) * rho_tau * c^2) - ((1 / 2) * rho_tau * v_val^2)) := by rw [h_Pc, h_P_dyn]
    _ = ((1 / 2) * rho_tau * c^2) / (((1 / 2) * rho_tau) * (c^2 - v_val^2)) := by ring
    _ = c^2 / (c^2 - v_val^2) := by
      have h12 : (1/2 : ℝ) ≠ 0 := by norm_num
      have h_cancel : (1/2) * rho_tau ≠ 0 := mul_ne_zero h12 rho_tau_ne_zero
      exact mul_div_mul_left (c^2) (c^2 - v_val^2) h_cancel
    _ = 1 / (1 - v_val^2 / c^2) := by
      have h_div : c^2 / (c^2 - v_val^2) = (c^2 / c^2) / ((c^2 - v_val^2) / c^2) := by
        field_simp [hc2]; ring
      rw [h_div]
      have h_one : c^2 / c^2 = 1 := by exact div_self hc2
      rw [h_one]
      have h_dist : (c^2 - v_val^2) / c^2 = c^2 / c^2 - v_val^2 / c^2 := by exact sub_div c^2 v_val^2 c^2
      rw [h_dist, h_one]
      rfl
-- Theorem 46: The Vacuum Expectation Value (VEV)
variable (v_vev P_ambient : ℝ)
theorem tensor_vev_origin (hrho : rho_tau ≠ 0)
    (h_yield : P_ambient = (1 / 2) * rho_tau * v_vev^2) :
    v_vev^2 = 2 * P_ambient / rho_tau := by
  calc
    v_vev^2 = ((1 / 2) * rho_tau * v_vev^2) * 2 / rho_tau := by field_simp [hrho]; ring
    _ = P_ambient * 2 / rho_tau := by rw [←h_yield]
    _ = 2 * P_ambient / rho_tau := by ring
-- ==========================================
-- 8.2 The Topological Phase Lock (Mass Generation)
-- ==========================================
-- (Continuous phase conservation locked into the antisymmetric off-diagonals.
-- Metric transitions from compliant medium to discrete rotational boundary.
-- Formalized geometrically via the Kinematic Lagrangian trace below).
-- ==========================================
-- 8.3 The Kinematic Lagrangian & Orthogonal Mass Extraction
-- ==========================================
variable (L_kin P_shear_val A_anti_trace : ℝ)
variable (v_macro_scalar : ℝ)
-- Theorem 47: The Kinematic Lagrangian Trace (Equation 140)
theorem orthogonal_mass_extraction (hc : c ≠ 0)
    (h_L_kin : L_kin = (1 / 4) * P_c * (4 * (v_macro_scalar^2 / c^2) + A_anti_trace))
    (h_P_dyn : P_dyn_val = (1 / 2) * rho_tau * v_macro_scalar^2)
    (h_P_shear : P_shear_val = (1 / 4) * P_c * A_anti_trace) :
    L_kin = P_dyn_val + P_shear_val := by
  have h_Pc : P_c = (1 / 2) * rho_tau * c^2 := by rfl
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 hc
  calc
    L_kin = (1 / 4) * ((1 / 2) * rho_tau * c^2) * (4 * (v_macro_scalar^2 / c^2) + A_anti_trace) := by
      rw [h_L_kin]
      rw [h_Pc]
    _ = (1 / 4) * ((1 / 2) * rho_tau * c^2) * (4 * (v_macro_scalar^2 / c^2)) +
        (1 / 4) * ((1 / 2) * rho_tau * c^2) * A_anti_trace := by ring
    _ = (1 / 2) * rho_tau * v_macro_scalar^2 + (1 / 4) * ((1 / 2) * rho_tau * c^2) * A_anti_trace := by
      congr 1
      field_simp [hc2]
      ring
    _ = P_dyn_val + P_shear_val := by
      rw [←h_P_dyn, h_Pc, ←h_P_shear]
-- ==========================================
-- 8.4 The Topological Yield Transition (Planck Mass)
-- ==========================================
variable (M_val : ℝ)
-- EUREKA MOMENT: We define the Planck Mass here, mid-file, as an emergent
-- geometric combination of the foundational constants. From this line downwards,
-- Lean now recognizes M_P globally.
noncomputable def M_P : ℝ := Real.sqrt (hbar * c / G)
-- PROVEN LEMMA: Isolates the mass relationship algebraically before taking the square root
lemma isolate_planck_yield_algebra (m_var : ℝ) (hm : m_var ≠ 0) :
  hbar / (m_var * c) = 2 * G * m_var / c^2 →
  m_var^2 = M_P^2 / 2 := by
  intro h_int
  have hc2 : c^2 ≠ 0 := pow_ne_zero 2 c_ne_zero

  have h_Mp : M_P^2 = hbar * c / G := by
    dsimp [M_P]
    -- Explicit positivity guarantee to prevent tactic failures
    have h1 : (0 : ℝ) < hbar * c := mul_pos hbar_pos c_pos
    have h_pos : 0 ≤ hbar * c / G := le_of_lt (div_pos h1 G_pos)
    exact Real.sq_sqrt h_pos

  have h1 : (hbar / (m_var * c)) * (m_var * c) = (2 * G * m_var / c^2) * (m_var * c) := by rw [h_int]
  have h2 : hbar = (2 * G * m_var^2) / c := by
    calc
      hbar = (hbar / (m_var * c)) * (m_var * c) := by field_simp [hm, c_ne_zero]; ring
      _ = (2 * G * m_var / c^2) * (m_var * c) := by rw [h1]
      _ = (2 * G * m_var^2) / c := by field_simp [c_ne_zero, hc2]; ring
  have h3 : M_P^2 = ((2 * G * m_var^2) / c) * c / G := by rw [h2] at h_Mp; exact h_Mp
  calc
    m_var^2 = (((2 * G * m_var^2) / c) * c / G) / 2 := by field_simp [c_ne_zero, G_ne_zero]; ring
    _ = M_P^2 / 2 := by rw [←h3]
-- PROVEN LEMMA: Isolates the positive root natively
lemma positive_sqrt_reduction (m_var : ℝ) (hm_pos : m_var > 0) :
  m_var^2 = M_P^2 / 2 → m_var = M_P / Real.sqrt 2 := by
  intro h
  have h2 : Real.sqrt (m_var^2) = Real.sqrt (M_P^2 / 2) := by rw [h]

  have hMp_nonneg : 0 ≤ M_P := by
    dsimp [M_P]
    exact Real.sqrt_nonneg _

  rw [Real.sqrt_sq (le_of_lt hm_pos)] at h2
  have h_split : Real.sqrt (M_P^2 / 2) = Real.sqrt (M_P^2) / Real.sqrt 2 := by
    exact Real.sqrt_div (sq_nonneg M_P)
  rw [h_split] at h2
  rw [Real.sqrt_sq hMp_nonneg] at h2
  exact h2
-- Theorem 48: The Topological Yield Limit (Equation 145)
theorem topological_yield_limit (hm : M_val ≠ 0) (hm_pos : M_val > 0)
    (h_intersection : hbar / (M_val * c) = 2 * G * M_val / c^2) :
    M_val = M_P / Real.sqrt 2 := by
  have h1 : M_val^2 = M_P^2 / 2 := isolate_planck_yield_algebra M_val hm h_intersection
  exact positive_sqrt_reduction M_val hm_pos h1
-- Theorem 49: Yield Partition (alpha_yield) (Equation 147)
theorem yield_partition (alpha_yield : ℝ)
    (h_yield : alpha_yield = Real.sqrt (1 - 1 / 2)) :
    alpha_yield = 1 / Real.sqrt 2 := by
  calc
    alpha_yield = Real.sqrt (1 - 1 / 2) := by exact h_yield
    _ = Real.sqrt (1 / 2) := by norm_num
    _ = 1 / Real.sqrt 2 := by
      rw [show (1/2 : ℝ) = 1 / 2 from rfl]
      have h_split : Real.sqrt (1 / 2) = Real.sqrt 1 / Real.sqrt 2 := Real.sqrt_div (by norm_num)
      rw [h_split, Real.sqrt_one]
-- ==========================================
-- Theorem 50: The Mass-Yield Equivalence
-- ==========================================
-- Explicitly locks in the connection between the mass ratio and
-- the geometric yield compliance at the VEV transition boundary.
theorem mass_yield_equivalence (alpha_yield : ℝ)
    (h_mass : M_val = M_P / Real.sqrt 2)
    (h_yield : alpha_yield = 1 / Real.sqrt 2) :
    M_val / M_P = alpha_yield := by
  have h1 : M_val / M_P = (M_P / Real.sqrt 2) / M_P := by rw [h_mass]
  have h2 : (M_P / Real.sqrt 2) / M_P = (M_P / M_P) / Real.sqrt 2 := by ring
  rw [h2] at h1

  -- Explicit proof that M_P is strictly positive to allow division
  have h_Mp_pos : 0 < M_P := by
    dsimp [M_P]
    have hp1 : (0 : ℝ) < hbar * c := mul_pos hbar_pos c_pos
    have hp2 : (0 : ℝ) < hbar * c / G := div_pos hp1 G_pos
    exact Real.sqrt_pos.mpr hp2
  have h_Mp_ne_zero : M_P ≠ 0 := ne_of_gt h_Mp_pos

  rw [div_self h_Mp_ne_zero] at h1
  rw [←h_yield] at h1
  exact h1
