-- SECTION 10: TENSOR COVARIANCE & NON-INERTIAL REFERENCE FRAMES
-- ======================================================================
-- ----------------------------------------------------------------------
-- 10.1 Kinematic Classification of Observer Frames
-- ----------------------------------------------------------------------
-- [Manuscript Section Placeholder: 1. Scalar Translation (Gradient Isomorphism)
--  and 2. Tensor Covariance (Kinematic Mixing: U'_{αβ} = Λ^μ_α Λ^ν_β U_{μν})].
-- ----------------------------------------------------------------------
-- 10.2 Active Kinematic Strain & The Invariant Phase Limit
-- ----------------------------------------------------------------------
-- Dimensional Audit: Active kinematic contraction ratio (P_static / P_c = 1 - v_rel^2 / c^2) is dimensionless:
theorem unit_section10_active_strain :
    u_P_c / u_P_c = (u_c^(2:ℤ)) / (u_c^(2:ℤ)) ∧
    (u_c^(2:ℤ)) / (u_c^(2:ℤ)) = u_dimless := by
  constructor <;> rfl
lemma temporal_diagonal_collapse (P_static_val P_c_val P_dyn_val rho_t v_rel c_val : ℝ)
    (hc : c_val ≠ 0) (hrho : rho_t ≠ 0)
    (h_static : P_static_val = P_c_val - P_dyn_val)
    (h_Pc : P_c_val = (1 / 2) * rho_t * c_val^2)
    (h_Pdyn : P_dyn_val = (1 / 2) * rho_t * v_rel^2) :
    - (P_static_val / P_c_val) = - (1 - v_rel^2 / c_val^2) := by
  rw [h_static, h_Pc, h_Pdyn]
  have hc2 : c_val^2 ≠ 0 := pow_ne_zero 2 hc
  have h_denom : (1 / 2) * rho_t * c_val^2 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hrho) hc2
  have h1 : (((1 / 2) * rho_t * c_val^2) - ((1 / 2) * rho_t * v_rel^2)) / ((1 / 2) * rho_t * c_val^2) =
            (((1 / 2) * rho_t * c_val^2) / ((1 / 2) * rho_t * c_val^2)) -
            (((1 / 2) * rho_t * v_rel^2) / ((1 / 2) * rho_t * c_val^2)) := by ring
  rw [h1]
  have h2 : ((1 / 2) * rho_t * c_val^2) / ((1 / 2) * rho_t * c_val^2) = 1 := div_self h_denom
  rw [h2]
  have h3 : (((1 / 2) * rho_t * v_rel^2) / ((1 / 2) * rho_t * c_val^2)) = v_rel^2 / c_val^2 := by
    rw [mul_div_mul_left (v_rel^2) (c_val^2) (mul_ne_zero (by norm_num) hrho)]
  rw [h3]
-- Theorem 67: Active Kinematic Contraction (U'_00 = -(1 - v_rel^2 / c^2), Manuscript Section 10.2)
theorem active_kinematic_contraction (U_00_prime P_static_val P_dyn_val v_rel : ℝ)
    (h_U : U_00_prime = - (P_static_val / P_c))
    (h_Bernoulli : P_static_val = P_c - P_dyn_val)
    (h_P_dyn : P_dyn_val = (1 / 2) * rho_tau * v_rel^2) :
    U_00_prime = - (1 - v_rel^2 / c^2) := by
  have h_collapse : - (P_static_val / P_c) = - (1 - v_rel^2 / c^2) := by
    have h_Pc_sub : P_c = (1 / 2) * rho_tau * c^2 := emergent_critical_pressure
    exact temporal_diagonal_collapse P_static_val P_c P_dyn_val rho_tau v_rel c c_ne_zero rho_tau_ne_zero h_Bernoulli h_Pc_sub h_P_dyn
  rw [h_U, h_collapse]
-- ----------------------------------------------------------------------
-- 10.3 Rotational Covariance & Transverse Leakage
-- ----------------------------------------------------------------------
-- Theorem 68: Rotational Transverse Leakage (U'_0i = Λ^β_i U_0β + ω Λ^β_i U_φβ, Manuscript Section 10.3)
theorem rotational_covariance_leakage (U_0i_prime U_0beta U_phi_beta Lambda_beta_i omega Lambda_0_0 Lambda_phi_0 : ℝ)
    (h_Lambda0 : Lambda_0_0 = 1)
    (h_LambdaPhi : Lambda_phi_0 = omega)
    (h_U_prime : U_0i_prime = (Lambda_0_0 * Lambda_beta_i * U_0beta) + (Lambda_phi_0 * Lambda_beta_i * U_phi_beta)) :
    U_0i_prime = Lambda_beta_i * U_0beta + omega * Lambda_beta_i * U_phi_beta := by
  rw [h_Lambda0, h_LambdaPhi] at h_U_prime
  have h1 : (1 * Lambda_beta_i * U_0beta) + (omega * Lambda_beta_i * U_phi_beta) =
            Lambda_beta_i * U_0beta + omega * Lambda_beta_i * U_phi_beta := by ring
  rw [←h1, ←h_U_prime]
-- ----------------------------------------------------------------------
-- 10.4 Conformal Scale Variance (The Micro-Macro Asymmetry)
-- ----------------------------------------------------------------------
-- [Manuscript Section Placeholder: Microscopic topological boundary gradient
--  (σ x^α ∂_α U_μν ≠ 0) vs. Macroscopic volumetric homogenization (∭_V A_ij dV = 0)].
-- ----------------------------------------------------------------------
-- 10.5 The Equivalence Principle (Acceleration Isomorphism)
-- ----------------------------------------------------------------------
variable (a_grav a_kin grad_P_static grad_P_dyn : V_3D)
-- Theorem 69: Equivalence Principle Acceleration Isomorphism (a_grav = -a_kin, Manuscript Section 10.5)
theorem equivalence_principle_gradients
    (h_conservation : grad_P_static = - grad_P_dyn)
    (h_a_grav : a_grav = grad_P_static)
    (h_a_kin : a_kin = grad_P_dyn) :
    a_grav = - a_kin := by
  rw [h_a_grav, h_conservation, ←h_a_kin]
-- ----------------------------------------------------------------------
-- 10.6 Discrete Frame Inversion (CPT Symmetry & Antimatter)
-- ----------------------------------------------------------------------
variable (U_00 U_ii U_0i U_ij : ℝ)
-- Theorem 70: Time-Reversal Mass Invariance (U'_00 = (-1)(-1) U_00 = U_00, Manuscript Section 10.6 Part I.1)
theorem T_symmetry_mass : (-1 : ℝ) * (-1) * U_00 = U_00 := by ring
-- Theorem 71: Time-Reversal Charge Inversion (U'_0i = (-1)(1) U_0i = -U_0i, Manuscript Section 10.6 Part I.2)
theorem T_symmetry_charge : (-1 : ℝ) * (1) * U_0i = - U_0i := by ring
-- Theorem 72: Parity Volumetric Mass Invariance (U'_ii = (-1)(-1) U_ii = U_ii, Manuscript Section 10.6 Part II.3)
theorem P_symmetry_mass : (-1 : ℝ) * (-1) * U_ii = U_ii := by ring
-- Theorem 73: Parity Axial Vorticity Invariance (U'_ij = (-1)(-1) U_ij = U_ij, Manuscript Section 10.6 Part II.4)
theorem P_symmetry_axial : (-1 : ℝ) * (-1) * U_ij = U_ij := by ring
-- Theorem 74: Parity Polar Winding/Charge Inversion (U'_0i = (1)(-1) U_0i = -U_0i, Manuscript Section 10.6 Part II.5)
theorem P_symmetry_charge : (1 : ℝ) * (-1) * U_0i = - U_0i := by ring

-- ======================================================================
-- SECTION 11: GALACTIC KINEMATICS AND THE COSMOLOGICAL BOUNDARY
-- ======================================================================
-- Dimensional Audit: Centripetal acceleration (v_rot^2 / r = (c^2 / 2 P_c) * (k_shear / r)) and Baryonic Tully-Fisher (v_rot^4 = a_0 G M_bar):
theorem unit_section11_galactic_kinematics :
    (u_c^(2:ℤ)) / u_l_p = ((u_c^(2:ℤ)) / u_P_c) * (u_P_c / u_l_p) ∧
    u_c^(4:ℤ) = u_accel * u_G * u_M_P := by
  constructor <;> rfl
-- ----------------------------------------------------------------------
-- 11.1 The Total Dynamic Pressure State
-- ----------------------------------------------------------------------
variable (Phi_r R_h : ℝ)
/-- Cosmological background expansion pressure `P_cosmo(r) = (1/2) ρ_τ c^2 (1 - exp(-r/R_h))^2`. -/
noncomputable def P_cosmo (r_val R_h_val rho_val c_val : ℝ) : ℝ :=
  (1 / 2) * rho_val * c_val^2 * (1 - Real.exp (-r_val / R_h_val))^2
/-- Total dynamic pressure state (Manuscript Section 11.1):
    `P_dyn(r) = -ρ_τ Φ(r) + (1/2) ρ_τ c^2 (1 - exp(-r/R_h))^2`. -/
noncomputable def P_dyn_total (r_val R_h_val rho_val c_val Phi_val : ℝ) : ℝ :=
  - rho_val * Phi_val + P_cosmo r_val R_h_val rho_val c_val
-- ----------------------------------------------------------------------
-- 11.2 The Bounded Kinematic Baseline
-- ----------------------------------------------------------------------
-- [Manuscript Section Placeholder: Radial derivative baseline
--  v_base^2(r) = r ∂_r Φ - (c^2 r / R_h) exp(-r/R_h)(1 - exp(-r/R_h)),
--  establishing the Core Bound (r → 0), Hill Sphere, and Macroscopic Asymptote (r → ∞)].
-- ----------------------------------------------------------------------
-- 11.3 Isolating the Kinematic Discrepancy
-- ----------------------------------------------------------------------
-- [Manuscript Section Placeholder: Empirical kinematic discrepancy ansatz
--  Γ_anom(r) = v_obs^2(r) - [GM_bar(r)/r - (c^2 r / R_h) exp(-r/R_h)(1 - exp(-r/R_h))]].
-- ----------------------------------------------------------------------
-- 11.4 The Universal No-Go Theorem
-- ----------------------------------------------------------------------
-- [Manuscript Section Placeholder: Geometric falsification of 3D modified gravity
--  (∇^2(-ln r) = -1/r^2 ≠ 0) and causal falsification of uncoupled ΛCDM halos].
-- ----------------------------------------------------------------------
-- 11.5 The Phenomenological Envelope
-- ----------------------------------------------------------------------
-- [Manuscript Section Placeholder: Required structural profile:
--  (1) Logarithmic spatial pressure gradient, (2) Baryonic causal coupling, (3) Inertial decoupling].
-- ----------------------------------------------------------------------
-- 11.6 Proposed Resolution: Elastic Metric Tension (Scale-Invariant Vorticity Coupling)
-- ----------------------------------------------------------------------
variable (k_shear R_max : ℝ)
variable (a_0 M_bar : ℝ)
/-- 2D polarized logarithmic shear pressure field `P_shear^2D(r) = k ln(R_max / r)` (Manuscript Section 11.6.3). -/
noncomputable def P_shear_2D (r_val : ℝ) : ℝ := k_shear * Real.log (R_max / r_val)
-- Theorem 75: Elastic Metric Tension Modified Temporal Diagonal (S_00, Manuscript Section 11.6.4)
theorem temporal_diagonal_admittance (P_dyn_3D r S_00 : ℝ)
    (h : S_00 = - (1 - (P_dyn_3D + P_shear_2D k_shear R_max r) / P_c)) :
    S_00 = - (1 - (P_dyn_3D + k_shear * Real.log (R_max / r)) / P_c) := by
  dsimp [P_shear_2D] at h
  exact h
lemma plug_flow_algebra (v_rot r_val c_val P_c_val k_val : ℝ)
    (hr : r_val ≠ 0) (_hPc : P_c_val > 0) (_hk : k_val ≥ 0) (hv : v_rot ≥ 0) (hc : c_val > 0)
    (h_accel : v_rot^2 / r_val = (c_val^2 / (2 * P_c_val)) * (k_val / r_val)) :
    v_rot = c_val * Real.sqrt (k_val / (2 * P_c_val)) := by
  have h1 : (v_rot^2 / r_val) * r_val = ((c_val^2 / (2 * P_c_val)) * (k_val / r_val)) * r_val :=
    congrArg (· * r_val) h_accel
  have h2 : (v_rot^2 / r_val) * r_val = v_rot^2 := div_mul_cancel₀ (v_rot^2) hr
  have h3 : ((c_val^2 / (2 * P_c_val)) * (k_val / r_val)) * r_val = c_val^2 * (k_val / (2 * P_c_val)) := by
    calc ((c_val^2 / (2 * P_c_val)) * (k_val / r_val)) * r_val
      _ = (c_val^2 / (2 * P_c_val)) * (k_val * (r_val / r_val)) := by ring
      _ = (c_val^2 / (2 * P_c_val)) * k_val := by rw [div_self hr, mul_one]
      _ = c_val^2 * (k_val / (2 * P_c_val)) := by ring
  rw [h2, h3] at h1
  have h4 : Real.sqrt (v_rot^2) = Real.sqrt (c_val^2 * (k_val / (2 * P_c_val))) := congrArg Real.sqrt h1
  rw [Real.sqrt_sq hv] at h4
  have h5 : Real.sqrt (c_val^2 * (k_val / (2 * P_c_val))) =
            Real.sqrt (c_val^2) * Real.sqrt (k_val / (2 * P_c_val)) :=
    Real.sqrt_mul (sq_nonneg c_val) (k_val / (2 * P_c_val))
  rw [h5, Real.sqrt_sq (le_of_lt hc)] at h4
  exact h4
-- Theorem 76: Macroscopic Bingham Plug Flow Plateau (v_rot = c √(k / 2P_c), Manuscript Section 11.6.6)
theorem kinematic_plateau_extraction (v_rot r : ℝ)
    (hr : r ≠ 0) (hk : k_shear ≥ 0) (hv : v_rot ≥ 0)
    (h_accel : v_rot^2 / r = (c^2 / (2 * P_c)) * (k_shear / r)) :
    v_rot = c * Real.sqrt (k_shear / (2 * P_c)) := by
  exact plug_flow_algebra v_rot r c P_c k_shear hr P_c_pos hk hv c_pos h_accel
-- Theorem 77: 2D Shear Amplitude from Transition-Radius Boundary Matching (Manuscript Section 11.6.7)
theorem shear_amplitude_from_boundary_matching (v_rot : ℝ)
    (h_plug : v_rot^2 = (c^2 / (2 * P_c)) * k_shear)
    (h_match : v_rot^2 = Real.sqrt (a_0 * G * M_bar)) :
    k_shear = (2 * P_c / c^2) * Real.sqrt (a_0 * G * M_bar) ∧
    k_shear = rho_tau * Real.sqrt (a_0 * G * M_bar) := by
  have hc : c ≠ 0 := c_ne_zero
  have hPc : P_c ≠ 0 := Pc_non_zero
  have hk1 : k_shear = (2 * P_c / c^2) * Real.sqrt (a_0 * G * M_bar) := by
    have h_eq : (c^2 / (2 * P_c)) * k_shear = Real.sqrt (a_0 * G * M_bar) := by
      rw [←h_plug, h_match]
    calc k_shear = (2 * P_c / c^2) * ((c^2 / (2 * P_c)) * k_shear) := by field_simp
      _ = (2 * P_c / c^2) * Real.sqrt (a_0 * G * M_bar) := by rw [h_eq]
  refine ⟨hk1, ?_⟩
  rw [hk1]
  dsimp [P_c]
  field_simp
lemma tully_fisher_algebra (v_rot a_0 G_val M_bar : ℝ)
    (ha : a_0 > 0) (hG : G_val > 0) (hM : M_bar ≥ 0) (_hv : v_rot ≥ 0)
    (h : v_rot^2 = a_0 * Real.sqrt (G_val * M_bar / a_0)) :
    v_rot^4 = a_0 * G_val * M_bar := by
  have h1 : (v_rot^2)^2 = (a_0 * Real.sqrt (G_val * M_bar / a_0))^2 := congrArg (·^2) h
  have h2 : (v_rot^2)^2 = v_rot^4 := by ring
  have h3 : (a_0 * Real.sqrt (G_val * M_bar / a_0))^2 = a_0^2 * (Real.sqrt (G_val * M_bar / a_0))^2 :=
    mul_pow a_0 _ 2
  rw [h2, h3] at h1
  have h_inside : G_val * M_bar / a_0 ≥ 0 := div_nonneg (mul_nonneg (le_of_lt hG) hM) (le_of_lt ha)
  rw [Real.sq_sqrt h_inside] at h1
  have h4 : a_0^2 * (G_val * M_bar / a_0) = a_0 * G_val * M_bar := by
    calc a_0^2 * (G_val * M_bar / a_0) = (a_0 * a_0 * G_val * M_bar) / a_0 := by ring
      _ = (a_0 * G_val * M_bar) * (a_0 / a_0) := by ring
      _ = a_0 * G_val * M_bar := by rw [div_self (ne_of_gt ha), mul_one]
  rw [h4] at h1
  exact h1
-- Theorem 78: Derivation of the Baryonic Tully-Fisher Relation (v_rot^4 = a_0 G M_bar, Manuscript Section 11.6.7)
theorem baryonic_tully_fisher_derivation (v_rot : ℝ)
    (ha : a_0 > 0) (hM : M_bar ≥ 0) (_hv : v_rot ≥ 0)
    (h_plateau : v_rot^2 = a_0 * Real.sqrt (G * M_bar / a_0)) :
    v_rot^4 = a_0 * G * M_bar := by
  exact tully_fisher_algebra v_rot a_0 G M_bar ha G_pos hM _hv h_plateau
-- Theorem 79: Radial Shear Pressure Ratio Profile (P_shear^2D(r) / P_c = 2(v_rot^2/c^2) ln(R_max/r), Manuscript Section 11.6.8)
theorem shear_pressure_ratio_profile (v_rot r : ℝ)
    (h_k : k_shear = 2 * P_c * (v_rot^2 / c^2)) :
    (P_shear_2D k_shear R_max r) / P_c = 2 * (v_rot^2 / c^2) * Real.log (R_max / r) := by
  dsimp [P_shear_2D]
  rw [h_k]
  have h1 : (2 * P_c * (v_rot^2 / c^2) * Real.log (R_max / r)) / P_c =
            (2 * (v_rot^2 / c^2) * Real.log (R_max / r)) * (P_c / P_c) := by ring
  rw [h1, div_self Pc_non_zero, mul_one]

-- ======================================================================
-- SECTION 12: THE NON-LINEAR AFFINE CONNECTION (EINSTEIN-CARTAN ISOMORPHISM)
-- ======================================================================
-- Dimensional Audit: Longitudinal acceleration ((1 / rho_tau) * grad_P = a_coord) and Einstein-Cartan Lagrangian density (Force * Curvature = Pressure):
theorem unit_section12_affine_connection_and_cartan :
    (u_dimless / u_rho_tau) * u_grad_P = u_accel ∧
    u_Force * u_Curvature = u_P_c := by
  constructor <;> rfl
-- ----------------------------------------------------------------------
-- 12.1 Connection Decomposition
-- ----------------------------------------------------------------------
/-- General spacetime affine connection `Γ^λ_μν`. -/
abbrev AffineConnection := SpaceTime → Fin 4 → Fin 4 → Fin 4 → ℝ
/-- Symmetric (Levi-Civita / Christoffel) part of an affine connection: `Γ^λ_(μν)`. -/
noncomputable def symConnection (Gamma : AffineConnection) : AffineConnection :=
  fun x lam μ ν => (Gamma x lam μ ν + Gamma x lam ν μ) / 2
/-- Antisymmetric Torsion tensor of an affine connection: `T^λ_μν = Γ^λ_μν - Γ^λ_νμ`. -/
noncomputable def torsionTensor (Gamma : AffineConnection) : AffineConnection :=
  fun x lam μ ν => Gamma x lam μ ν - Gamma x lam ν μ
-- Theorem 80: Affine Connection Symmetric-Torsion Decomposition (Γ^λ_μν = Γ^λ_(μν) + 1/2 T^λ_μν, Manuscript Section 12.1)
theorem connection_torsion_decomposition (Gamma : AffineConnection) (x : SpaceTime) (lam μ ν : Fin 4) :
    Gamma x lam μ ν = symConnection Gamma x lam μ ν + (1 / 2) * torsionTensor Gamma x lam μ ν := by
  dsimp [symConnection, torsionTensor]
  ring
-- Theorem 81: Torsion-Free Reduction to the Symmetric Levi-Civita Connection (Manuscript Section 12.1)
theorem torsion_free_iff_symmetric_connection (Gamma : AffineConnection) (x : SpaceTime) (lam μ ν : Fin 4) :
    torsionTensor Gamma x lam μ ν = 0 ↔ Gamma x lam μ ν = symConnection Gamma x lam μ ν := by
  dsimp [torsionTensor, symConnection]
  constructor <;> intro h <;> linarith
/-- Full covariant divergence of a contravariant rank-2 tensor field:
    `∇_μ U^μν = ∂_μ U^μν + Γ^μ_μλ U^λν + Γ^ν_μλ U^μλ`. -/
noncomputable def covariant_metric_divergence (Gamma : AffineConnection) (U : MetricField) (x : SpaceTime) : V4 :=
  fun ν => metric_divergence U x ν +
    ∑ μ : Fin 4, ∑ lam : Fin 4, (Gamma x μ μ lam * U x lam ν + Gamma x ν μ lam * U x μ lam)
-- Theorem 82: Weak-Field Flat-Connection Divergence Reduction (Manuscript Sections 5.0 & 12.1)
theorem flat_connection_divergence_limit (Gamma : AffineConnection) (U : MetricField) (x : SpaceTime)
    (h_flat : ∀ lam μ ν, Gamma x lam μ ν = 0) :
    covariant_metric_divergence Gamma U x = metric_divergence U x := by
  ext ν
  dsimp [covariant_metric_divergence]
  have h_sum_zero : (∑ μ : Fin 4, ∑ lam : Fin 4, (Gamma x μ μ lam * U x lam ν + Gamma x ν μ lam * U x μ lam)) = 0 := by
    apply Finset.sum_eq_zero
    intro μ _
    apply Finset.sum_eq_zero
    intro lam _
    rw [h_flat μ μ lam, h_flat ν μ lam]
    ring
  rw [h_sum_zero, add_zero]
-- ----------------------------------------------------------------------
-- 12.2 The Symmetric Connection (Gravitational Acceleration)
-- ----------------------------------------------------------------------
-- Theorem 83: Longitudinal Transport Acceleration (a_grav = (1 / ρ_τ) ∇P_dyn, Manuscript Section 12.2)
theorem longitudinal_transport_acceleration (a_coord : V_3D)
    (h_grad : grad_P_static = - grad_P_dyn)
    (h_a : a_coord = - (1 / rho_tau) • grad_P_static) :
    a_coord = (1 / rho_tau) • grad_P_dyn := by
  have h1 : - (1 / rho_tau) • grad_P_static = - (1 / rho_tau) • (- grad_P_dyn) := by rw [h_grad]
  have h2 : - (1 / rho_tau) • (- grad_P_dyn) = (- (1 / rho_tau) * -1) • grad_P_dyn := by
    have h_neg_vec : - grad_P_dyn = (-1 : ℝ) • grad_P_dyn := (neg_one_smul ℝ grad_P_dyn).symm
    rw [h_neg_vec, smul_smul]
  have h3 : (- (1 / rho_tau) * -1) • grad_P_dyn = (1 / rho_tau) • grad_P_dyn := by
    have h_scalar : (- (1 / rho_tau) * -1) = 1 / rho_tau := by ring
    rw [h_scalar]
  rw [h_a, h1, h2, h3]
-- ----------------------------------------------------------------------
-- 12.3 Spacetime Torsion
-- ----------------------------------------------------------------------
/-- Spacetime torsion generated by the gradient of the Clebsch vorticity 2-form (Manuscript Section 12.3):
    `T^λ_μν = α t_p ∂^λ (dλ_Ω ∧ dβ_Ω)_μν`. -/
noncomputable def clebsch_torsion_tensor (alpha_val t_p_val : ℝ) (lambda_f beta_f : ScalarField) : AffineConnection :=
  fun x lam μ ν => alpha_val * t_p_val * partial_deriv (fun y => Omega_clebsch_field lambda_f beta_f y μ ν) lam x
-- ----------------------------------------------------------------------
-- 12.4 Mapping Clebsch Vorticity to Torsion
-- ----------------------------------------------------------------------
/-- Spin angular momentum density tensor `s^λ_μν = (c^4 / 8πG) T^λ_μν` (Manuscript Section 12.4). -/
noncomputable def spin_angular_momentum_density (T_torsion : AffineConnection) : AffineConnection :=
  fun x lam μ ν => (c^4 / (8 * Real.pi * G)) * T_torsion x lam μ ν
-- Theorem 84: Mapping Clebsch Wedge Vorticity to Spin Angular Momentum Density (Manuscript Section 12.4)
theorem clebsch_vorticity_to_torsion_spin_density
    (alpha_val : ℝ) (lambda_f beta_f : ScalarField) (x : SpaceTime) (lam μ ν : Fin 4) :
    spin_angular_momentum_density (clebsch_torsion_tensor alpha_val t_p lambda_f beta_f) x lam μ ν =
    (c^4 / (8 * Real.pi * G)) * alpha_val * t_p *
      partial_deriv (fun y => wedge_covec (d_scalar_field lambda_f y) (d_scalar_field beta_f y) μ ν) lam x := by
  dsimp [spin_angular_momentum_density, clebsch_torsion_tensor, Omega_clebsch_field, omega_clebsch_2form]
  ring
-- ----------------------------------------------------------------------
-- 12.5 The Macroscopic Torsion Boundary (Decay Limit)
-- ----------------------------------------------------------------------
-- [Manuscript Section Placeholder: Exponential confinement decay of torsion outside the defect core
--  (T^λ_μν ∝ exp(-r/r_c) → 0 for r ≫ r_c), reducing Γ^λ_μν to the Levi-Civita connection].
-- ----------------------------------------------------------------------
-- 12.6 The Riemann Curvature Expansion
-- ----------------------------------------------------------------------
variable (L_Tot L_EH L_Spin tension_limit R_tilde K_trace_1 K_trace_2 : ℝ)
-- Theorem 85: The Einstein-Cartan Lagrangian Partition (L_Tot = L_EH + L_spin, Manuscript Section 12.6)
theorem einstein_cartan_lagrangian
    (h_L_Tot : L_Tot = tension_limit * (R_tilde + K_trace_1 - K_trace_2))
    (h_L_EH : L_EH = tension_limit * R_tilde)
    (h_L_Spin : L_Spin = tension_limit * (K_trace_1 - K_trace_2)) :
    L_Tot = L_EH + L_Spin := by
  have h1 : tension_limit * (R_tilde + K_trace_1 - K_trace_2) =
            tension_limit * R_tilde + tension_limit * (K_trace_1 - K_trace_2) := by ring
  rw [h_L_Tot, h1, ←h_L_EH, ←h_L_Spin]

-- ======================================================================
