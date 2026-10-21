/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Tactic

/-!
# Fundamental bedrock axioms, dimensional audit layer, kinematics, and thermodynamic relations

Module of Binyamin's v5.7 formalization. Declarations retained verbatim
from the author's single-file development.
-/

@[expose] public section

open Real BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars true

namespace AsymmetricTensor
-- ======================================================================
-- SECTION 0: FUNDAMENTAL BEDROCK AXIOMS & EMERGENT CONSTANTS
-- ======================================================================

-- 0.1 Concrete positive definitions (SI numerical values; locked as irreducible below)
noncomputable def c    : ℝ := 299792458 -- m/s per c
noncomputable def l_p  : ℝ := 1616255 * 10 ^ (-41 : ℤ) -- m per l_p
noncomputable def hbar : ℝ := 1054571817 * 10 ^ (-43 : ℤ) -- J*s per hbar

-- Positivity bounds are proven theorems rather than axioms:
theorem c_pos    : 0 < c    := by unfold c; positivity
theorem l_p_pos  : 0 < l_p  := by unfold l_p; positivity
theorem hbar_pos : 0 < hbar := by unfold hbar; positivity

-- Lock c, l_p, and hbar as irreducible so they remain purely symbolic in all downstream proofs:
attribute [irreducible] c l_p hbar

-- 0.2 Geometric Curvature Ceilings & Emergent Vacuum Constants (Definitions)
noncomputable def t_p     : ℝ := l_p / c
noncomputable def k_p     : ℝ := 1 / l_p              -- Spatial curvature ceiling (m^-1)
noncomputable def Omega_p : ℝ := c / l_p              -- Temporal curvature ceiling (s^-1)
noncomputable def E_P     : ℝ := (hbar * c) / l_p     -- Constitutive energy stiffness ceiling (J)
noncomputable def M_P     : ℝ := hbar / (l_p * c)
noncomputable def G       : ℝ := (l_p^2 * c^3) / hbar
noncomputable def rho_tau : ℝ := hbar / (2 * Real.pi * l_p^4 * c)
noncomputable def P_c     : ℝ := (1 / 2) * rho_tau * c^2

-- ======================================================================
-- SECTION 0.3: GEOMETRIC CURVATURE DIMENSIONAL LATTICE (K, Omega, E)
-- ======================================================================

/-- Tracks physical dimensions on the Geometric Curvature Lattice `⟨K, Omega, E⟩ ∈ ℤ³`:
    - `K`: Spatial Curvature exponent (`k_p = 1 / l_p`, `∇^K`; negative `K` is length `l_p^{-K}`),
    - `Omega`: Temporal Curvature exponent (`Omega_p = 1 / t_p`, `∂_t^Omega`; negative `Omega` is
      time `t_p^{-Omega}`),
    - `E`: Constitutive Stiffness exponent (`E_P = hbar * Omega_p`; `0` = unweighted geometry, `+1`
      = stress/load, `-1` = compliance). -/
structure UnitDim where
  K     : ℤ := 0  -- Spatial Curvature (k_p = 1 / l_p)
  Omega : ℤ := 0  -- Temporal Curvature (Omega_p = 1 / t_p)
  E     : ℤ := 0  -- Constitutive Energy Stiffness (E_P = hbar * Omega_p)
  deriving DecidableEq, Repr

instance : Mul UnitDim where
  mul a b := ⟨a.K + b.K, a.Omega + b.Omega, a.E + b.E⟩

instance : Div UnitDim where
  div a b := ⟨a.K - b.K, a.Omega - b.Omega, a.E - b.E⟩

instance : HPow UnitDim ℤ UnitDim where
  hPow a n := ⟨a.K * n, a.Omega * n, a.E * n⟩

-- 1. Tier 1 Fundamental Curvature & Stiffness Ceilings ⟨K, Omega, E⟩
def u_dimless : UnitDim := ⟨0, 0, 0⟩
def u_k_p     : UnitDim := ⟨1, 0, 0⟩   -- Spatial Curvature Ceiling (k_p = 1 / l_p, ∇)
def u_omega   : UnitDim := ⟨0, 1, 0⟩   -- Temporal Curvature Ceiling (Omega_p = 1 / t_p, ∂_t)
def u_Energy  : UnitDim := ⟨0, 0, 1⟩   -- Constitutive Energy Stiffness Ceiling (E_P)

-- 2. Extensive Space-Time & Tier 2 Emergent Couplings (Length, Time, Velocity, Action)
def u_l_p     : UnitDim := u_dimless / u_k_p     -- ⟨-1, 0, 0⟩  (Extensive Length l_p = 1 / k_p)
def u_t_p     : UnitDim := u_dimless / u_omega   -- ⟨0, -1, 0⟩  (Extensive Time t_p = 1 / Omega_p)
def u_c       : UnitDim := u_omega / u_k_p
-- ⟨-1, 1, 0⟩  (Phase Velocity c = Omega_p / k_p = l_p / t_p)
def u_hbar    : UnitDim := u_Energy / u_omega
-- ⟨0, -1, 1⟩  (Action Stiffness hbar = E_P / Omega_p = E_P * t_p)

-- 3. Emergent Continuum & Defect Units
def u_M_P     : UnitDim := u_hbar / (u_l_p * u_c)
-- ⟨2, -2, 1⟩   (Defect Mass m_0 = E_P / c^2)
def u_G       : UnitDim := (u_l_p^(2:ℤ) * u_c^(3:ℤ)) / u_hbar
-- ⟨-5, 4, -1⟩  (Gravitational Compliance G)
def u_rho_tau : UnitDim := u_hbar / (u_l_p^(4:ℤ) * u_c)
-- ⟨5, -2, 1⟩   (3D Mass Density rho_tau = P_c / c^2)
def u_P_c     : UnitDim := u_rho_tau * (u_c^(2:ℤ))
-- ⟨3, 0, 1⟩    (3D Bulk Pressure Stiffness P_c = E_P * k_p^3)

-- 4. Derived Mechanical & Differential Curvature Units
def u_accel       : UnitDim := (u_c^(2:ℤ)) / u_l_p
-- ⟨-1, 2, 0⟩   (Acceleration a = v^2 / r = c^2 * k_p)
def u_Mom         : UnitDim := u_hbar / u_l_p
-- ⟨1, -1, 1⟩   (Momentum p = hbar * k_p = E_P / c)
def u_Force       : UnitDim := (u_hbar * u_c) / (u_l_p^(2:ℤ))
-- ⟨1, 0, 1⟩    (1D Force / Tension F = E_P * k_p)
def u_SurfTension : UnitDim := u_Energy * (u_k_p^(2:ℤ))
-- ⟨2, 0, 1⟩    (2D Surface Tension sigma = E_P * k_p^2)
def u_Viscosity   : UnitDim := u_P_c / u_omega
-- ⟨3, -1, 1⟩   (Dynamic Viscosity / Spin mu = P_c * t_p)
def u_Area        : UnitDim := u_l_p^(2:ℤ)
-- ⟨-2, 0, 0⟩   (2D Area l_p^2 = k_p^-2)
def u_Volume      : UnitDim := u_l_p^(3:ℤ)
-- ⟨-3, 0, 0⟩   (3D Volume l_p^3 = k_p^-3)
def u_Phi         : UnitDim := u_c^(2:ℤ)
-- ⟨-2, 2, 0⟩   (Gravitational potential G M / r = v^2)
def u_Curvature   : UnitDim := u_dimless / (u_l_p^(2:ℤ))
-- ⟨2, 0, 0⟩    (2D Gaussian Curvature k_p^2 = 1 / l_p^2, Lambda)
def u_grad_P      : UnitDim := u_P_c / u_l_p
-- ⟨4, 0, 1⟩    (3D Force Density -∇P = E_P * k_p^4)
def u_Laplacian   : UnitDim := u_dimless / (u_l_p^(2:ℤ))
-- ⟨2, 0, 0⟩    (Laplace operator ∇^2 = k_p^2)
def u_Biharmonic  : UnitDim := u_dimless / (u_l_p^(4:ℤ))
-- ⟨4, 0, 0⟩    (Biharmonic operator ∇^4 = k_p^4)
def u_C_isochoric : UnitDim := u_c * (u_l_p^(2:ℤ))
-- ⟨-3, 1, 0⟩   (Isochoric flow constant C = v r^2)

-- 5. Automated Dimensional Verification on the ⟨K, Omega, E⟩ Lattice (Proven by `rfl`)
theorem unit_emergent_time :
    u_t_p = ⟨0, -1, 0⟩ ∧
    u_t_p = u_l_p / u_c ∧
    u_dimless / u_t_p = u_omega ∧
    u_c = u_omega / u_k_p ∧
    u_hbar = u_Energy / u_omega := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem unit_spatial_ladder :
    u_Force = u_Energy * u_k_p ∧
    u_SurfTension = u_Force * u_k_p ∧
    u_P_c = u_SurfTension * u_k_p ∧
    u_grad_P = u_P_c * u_k_p ∧
    u_Force = u_Energy / u_l_p ∧
    u_P_c = u_Force / u_Area ∧
    u_P_c = u_Energy / u_Volume := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem unit_relativistic_ladder :
    u_Mom = u_M_P * u_c ∧ u_Energy = u_M_P * (u_c^(2:ℤ)) := by
  constructor <;> rfl

theorem unit_newtonian_gravity :
    (u_G * u_M_P * u_M_P) / (u_l_p^(2:ℤ)) = u_Force := by rfl

theorem unit_tensor_vorticity_dimensionless :
    u_dimless * u_t_p * u_omega = u_dimless := by rfl

theorem dimensional_closure :
    u_k_p = ⟨1, 0, 0⟩ ∧
    u_omega = ⟨0, 1, 0⟩ ∧
    u_Energy = ⟨0, 0, 1⟩ ∧
    u_l_p = ⟨-1, 0, 0⟩ ∧
    u_t_p = ⟨0, -1, 0⟩ ∧
    u_c = ⟨-1, 1, 0⟩ ∧
    u_hbar = ⟨0, -1, 1⟩ ∧
    u_M_P = ⟨2, -2, 1⟩ ∧
    u_G = ⟨-5, 4, -1⟩ ∧
    u_rho_tau = ⟨5, -2, 1⟩ ∧
    u_P_c = ⟨3, 0, 1⟩ ∧
    u_Force = ⟨1, 0, 1⟩ ∧
    u_SurfTension = ⟨2, 0, 1⟩ ∧
    u_Viscosity = ⟨3, -1, 1⟩ ∧
    u_Mom = ⟨1, -1, 1⟩ ∧
    u_accel = ⟨-1, 2, 0⟩ ∧
    u_Laplacian = ⟨2, 0, 0⟩ ∧
    u_grad_P = ⟨4, 0, 1⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Unimodular GL(3, ℤ) Basis Isomorphism: Legacy ⟨L, V, S⟩ ↔ Geometric Curvature ⟨K, Omega, E⟩
theorem unit_basis_isomorphism_LVS_KOE (L V S : ℤ) :
    (u_l_p ^ L) * (u_c ^ V) * (u_hbar ^ S) = ⟨-(L + V), V - S, S⟩ := by
  dsimp [u_l_p, u_c, u_hbar, u_dimless, u_k_p, u_omega, u_Energy]
  change UnitDim.mk ((-1 * L) + (-1 * V) + (0 * S))
                    ((0 * L) + (1 * V) + (-1 * S))
                    ((0 * L) + (0 * V) + (1 * S)) =
         UnitDim.mk (-(L + V)) (V - S) S
  congr 1 <;> ring

-- ======================================================================
-- SECTION 0.4: POSITIVITY & FUNDAMENTAL CONSTANT IDENTITIES
-- ======================================================================
lemma k_p_pos : 0 < k_p := by
  dsimp [k_p]
  exact div_pos (by norm_num : (0 : ℝ) < 1) l_p_pos

lemma Omega_p_pos : 0 < Omega_p := by
  dsimp [Omega_p]
  exact div_pos c_pos l_p_pos

lemma E_P_pos : 0 < E_P := by
  dsimp [E_P]
  exact div_pos (mul_pos hbar_pos c_pos) l_p_pos

lemma G_pos : 0 < G := by
  dsimp [G]
  have h1 : (0 : ℝ) < l_p^2 := pow_pos l_p_pos 2
  have h2 : (0 : ℝ) < c^3 := pow_pos c_pos 3
  exact div_pos (mul_pos h1 h2) hbar_pos

lemma rho_tau_pos : 0 < rho_tau := by
  dsimp [rho_tau]
  have h1 : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos
  have h2 : (0 : ℝ) < l_p^4 := pow_pos l_p_pos 4
  have h3 : (0 : ℝ) < 2 * Real.pi * l_p^4 := mul_pos h1 h2
  have h4 : (0 : ℝ) < 2 * Real.pi * l_p^4 * c := mul_pos h3 c_pos
  exact div_pos hbar_pos h4

lemma M_P_pos : 0 < M_P := by
  dsimp [M_P]
  exact div_pos hbar_pos (mul_pos l_p_pos c_pos)

lemma M_P_sq_eq_hbar_c_div_G : M_P^2 = hbar * c / G := by
  dsimp [M_P, G]
  have hl_ne : l_p ≠ 0 := ne_of_gt l_p_pos
  have hc_ne : c ≠ 0 := ne_of_gt c_pos
  have hbar_ne : hbar ≠ 0 := ne_of_gt hbar_pos
  field_simp

lemma c_ne_zero : c ≠ 0 := ne_of_gt c_pos
lemma l_p_ne_zero : l_p ≠ 0 := ne_of_gt l_p_pos
lemma hbar_ne_zero : hbar ≠ 0 := ne_of_gt hbar_pos
lemma k_p_ne_zero : k_p ≠ 0 := ne_of_gt k_p_pos
lemma Omega_p_ne_zero : Omega_p ≠ 0 := ne_of_gt Omega_p_pos
lemma E_P_ne_zero : E_P ≠ 0 := ne_of_gt E_P_pos
lemma t_p_ne_zero : t_p ≠ 0 := div_ne_zero l_p_ne_zero c_ne_zero
lemma M_P_ne_zero : M_P ≠ 0 := ne_of_gt M_P_pos
lemma G_ne_zero : G ≠ 0 := ne_of_gt G_pos
lemma rho_tau_ne_zero : rho_tau ≠ 0 := ne_of_gt rho_tau_pos

lemma P_c_pos : 0 < P_c := by
  dsimp [P_c]
  exact mul_pos (mul_pos (by norm_num) rho_tau_pos) (pow_pos c_pos 2)

lemma Pc_non_zero : P_c ≠ 0 := ne_of_gt P_c_pos

lemma t_p_mul_c : t_p * c = l_p := by
  dsimp [t_p]
  exact div_mul_cancel₀ l_p c_ne_zero

lemma M_P_mul_l_p_c : M_P * l_p * c = hbar := by
  dsimp [M_P]
  have h_assoc : (hbar / (l_p * c)) * l_p * c = (hbar / (l_p * c)) * (l_p * c) := by ring
  rw [h_assoc]
  exact div_mul_cancel₀ hbar (mul_ne_zero l_p_ne_zero c_ne_zero)

lemma G_mul_hbar : G * hbar = l_p^2 * c^3 := by
  dsimp [G]
  exact div_mul_cancel₀ (l_p^2 * c^3) hbar_ne_zero

lemma rho_tau_mul : rho_tau * (2 * Real.pi * l_p^4 * c) = hbar := by
  dsimp [rho_tau]
  have ha : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hb : l_p^4 ≠ 0 := pow_ne_zero 4 l_p_ne_zero
  have h_denom : 2 * Real.pi * l_p^4 * c ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) c_ne_zero
  exact div_mul_cancel₀ hbar h_denom

lemma c4_div_G_eq_planck_force : c^4 / G = (hbar * c) / l_p^2 := by
  dsimp [G]
  have step1 : c^4 / ((l_p^2 * c^3) / hbar) = (c^4 * hbar) / (l_p^2 * c^3) := by rw [div_div_eq_mul_div]
  rw [step1]
  have step2 : (c^4 * hbar) / (l_p^2 * c^3) = (hbar * c * c^3) / (l_p^2 * c^3) := by
    have h_num : c^4 * hbar = hbar * c * c^3 := by ring
    rw [h_num]
  rw [step2]
  have step3 : (hbar * c * c^3) / (l_p^2 * c^3) = ((hbar * c) / l_p^2) * (c^3 / c^3) := by ring
  rw [step3, div_self (pow_ne_zero 3 c_ne_zero), mul_one]

-- Geometric Curvature Ceiling Identities (Linking k_p, Omega_p, E_P to c, hbar, Force, P_c, M_P)
lemma curvature_ceiling_identities :
    Omega_p / k_p = c ∧
    E_P / Omega_p = hbar ∧
    E_P * k_p = c^4 / G ∧
    P_c = (E_P * k_p^3) / (4 * Real.pi) ∧
    M_P = E_P * (k_p / Omega_p)^2 := by
  have hl : l_p ≠ 0 := l_p_ne_zero
  have hc : c ≠ 0 := c_ne_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [Omega_p, k_p]
    field_simp
  · dsimp [E_P, Omega_p]
    field_simp
  · rw [c4_div_G_eq_planck_force]
    dsimp [E_P, k_p]
    ring
  · dsimp [P_c, rho_tau, E_P, k_p]
    field_simp
    ring
  · dsimp [M_P, E_P, k_p, Omega_p]
    field_simp

-- ======================================================================
-- SECTION 1: KINEMATIC PARAMETRIZATION (CLEBSCH VARIABLES)
-- ======================================================================
abbrev V4 := Fin 4 → ℝ
abbrev T2 := Matrix (Fin 4) (Fin 4) ℝ

-- Spatial vector space (used in Sections 5.2, 6.4, 10.5, 12.2, 13.1)
variable {V_3D : Type} [AddCommGroup V_3D] [Module ℝ V_3D]

-- Graded differential form spaces (0-forms, 1-forms, 2-forms)
variable {Forms_0D : Type} [AddCommGroup Forms_0D] [Module ℝ Forms_0D]
variable {Forms_1D : Type} [AddCommGroup Forms_1D] [Module ℝ Forms_1D]
variable {Forms_2D : Type} [AddCommGroup Forms_2D] [Module ℝ Forms_2D]

-- Exterior derivative operators (d : Ω^0 → Ω^1 and d : Ω^1 → Ω^2)
variable (d0 : Forms_0D →ₗ[ℝ] Forms_1D)
variable (d1 : Forms_1D →ₗ[ℝ] Forms_2D)

-- Scalar multiplication of a 0-form on 1-forms and 2-forms: (λ, ω) ↦ λ • ω
variable (smul_form  : Forms_0D → Forms_1D → Forms_1D)
variable (smul_2form : Forms_0D → Forms_2D → Forms_2D)

-- Antisymmetric exterior wedge product: (α, β) ↦ α ∧ β
variable (wedge : Forms_1D →ₗ[ℝ] Forms_1D →ₗ[ℝ] Forms_2D)

/-- Irrotational longitudinal phase 1-form: `dh`. -/
noncomputable def grad_h (h : Forms_0D) : Forms_1D :=
  d0 h

/-- Internal rotational Clebsch phase 1-form: `λ_Ω dβ_Ω`. -/
noncomputable def curl_phase (lambda_Omega beta_Omega : Forms_0D) : Forms_1D :=
  smul_form lambda_Omega (d0 beta_Omega)

/-- Total macroscopic velocity 1-form (Manuscript Eq. 1):
    `v(x, t) = dh + v_⊥ + λ_Ω dβ_Ω`. -/
noncomputable def v_macro (h lambda_Omega beta_Omega : Forms_0D) (v_perp : Forms_1D) : Forms_1D :=
  grad_h d0 h + v_perp + curl_phase d0 smul_form lambda_Omega beta_Omega

/-- Internal topological vorticity 2-form (Manuscript Eq. 2):
    `Ω = d(λ_Ω dβ_Ω)`. -/
noncomputable def Omega (lambda_Omega beta_Omega : Forms_0D) : Forms_2D :=
  d1 (curl_phase d0 smul_form lambda_Omega beta_Omega)

-- Theorem 1: Irrotational Phase Nullification (d(dh) = 0, Manuscript Section 1)
theorem irrotational_phase_null (h : Forms_0D)
    (d_squared_zero : ∀ (f : Forms_0D), d1 (d0 f) = 0) :
    d1 (grad_h d0 h) = 0 :=
  d_squared_zero h

-- Theorem 2: Clebsch Vorticity 2-Form Extraction (Ω = dλ_Ω ∧ dβ_Ω, Manuscript Eq. 2)
theorem clebsch_vorticity_extraction (lambda_Omega beta_Omega : Forms_0D)
    (d_squared_zero : ∀ (f : Forms_0D), d1 (d0 f) = 0)
    (smul_2form_zero : ∀ (f : Forms_0D), smul_2form f 0 = 0)
    (leibniz_rule : ∀ (lam_val bet_val : Forms_0D),
      d1 (smul_form lam_val (d0 bet_val)) =
      wedge (d0 lam_val) (d0 bet_val) + smul_2form lam_val (d1 (d0 bet_val))) :
    Omega d0 d1 smul_form lambda_Omega beta_Omega = wedge (d0 lambda_Omega) (d0 beta_Omega) := by
  dsimp [Omega, curl_phase]
  rw [leibniz_rule]
  rw [d_squared_zero]
  rw [smul_2form_zero]
  exact add_zero _

-- Theorem 3: Macroscopic Velocity Exterior Derivative Decomposition (Manuscript Eqs. 1–2)
theorem macroscopic_vorticity_decomposition (h lambda_Omega beta_Omega : Forms_0D) (v_perp : Forms_1D)
    (d_squared_zero : ∀ (f : Forms_0D), d1 (d0 f) = 0)
    (smul_2form_zero : ∀ (f : Forms_0D), smul_2form f 0 = 0)
    (leibniz_rule : ∀ (lam_val bet_val : Forms_0D),
      d1 (smul_form lam_val (d0 bet_val)) =
      wedge (d0 lam_val) (d0 bet_val) + smul_2form lam_val (d1 (d0 bet_val))) :
    d1 (v_macro d0 smul_form h lambda_Omega beta_Omega v_perp) =
    d1 v_perp + wedge (d0 lambda_Omega) (d0 beta_Omega) := by
  dsimp [v_macro, grad_h]
  rw [map_add, map_add]
  rw [d_squared_zero h, zero_add]
  exact congrArg (d1 v_perp + ·)
    (clebsch_vorticity_extraction d0 d1 smul_form smul_2form wedge lambda_Omega beta_Omega
      d_squared_zero smul_2form_zero leibniz_rule)

-- ======================================================================
-- SECTION 2: THE THERMODYNAMIC BUDGET (ENERGY CONSERVATION)
-- ======================================================================
variable (v_esc : ℝ)
variable (v_parallel v_perp_mag v_circ : ℝ)

-- Dimensional Audit: Dynamic pressure (1/2 * rho_tau * v^2) and compliance ratios are dimensionally exact:
theorem unit_section2_thermodynamic_budget :
    u_rho_tau * (u_c^(2:ℤ)) = u_P_c ∧
    u_P_c / u_P_c = u_dimless ∧
    (u_c^(2:ℤ)) / (u_c^(2:ℤ)) = u_dimless := by
  refine ⟨rfl, rfl, rfl⟩

/-- Scalar dynamic pressure `P_dyn(v) = (1/2) ρ_τ v^2`. -/
noncomputable def P_dyn_scalar (v : ℝ) : ℝ :=
  (1 / 2) * rho_tau * v^2

/-- Macroscopic gravitational/cosmological baseline load `ΔP_macro(v_0) = (1/2) ρ_τ v_0^2`. -/
noncomputable def P_g (v_esc_val : ℝ) : ℝ := P_dyn_scalar v_esc_val

/-- Orthogonal 3-component dynamic pressure (Manuscript Eq. 5):
    `P_dyn = (1/2) ρ_τ (v_∥^2 + v_⊥^2 + v_↻^2)`. -/
noncomputable def P_dyn_components (v_parallel_val v_perp_mag_val v_circ_val : ℝ) : ℝ :=
  (1 / 2) * rho_tau * (v_parallel_val^2 + v_perp_mag_val^2 + v_circ_val^2)

-- Theorem 4: Emergent Critical Vacuum Pressure (P_c = 1/2 ρ_τ c^2, Manuscript Section 2)
theorem emergent_critical_pressure :
    P_c = (1 / 2) * rho_tau * c^2 := by
  rfl

lemma cancel_fraction_rho (v_val : ℝ) :
  (((1 / 2) * rho_tau * v_val^2) / ((1 / 2) * rho_tau * c^2)) = (v_val^2 / c^2) := by
  have hrho_ne_zero : rho_tau ≠ 0 := ne_of_gt rho_tau_pos
  have hc_ne_zero : c^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt c_pos)
  have h1 : (((1 / 2) * rho_tau * v_val^2) / ((1 / 2) * rho_tau * c^2)) =
            (((1 / 2) * rho_tau) / ((1 / 2) * rho_tau)) * (v_val^2 / c^2) := by ring
  rw [h1]
  have h_cancel : ((1 / 2) * rho_tau) / ((1 / 2) * rho_tau) = 1 :=
    div_self (mul_ne_zero (by norm_num) hrho_ne_zero)
  rw [h_cancel]
  ring

-- Theorem 5: Gravitational Compliance Equivalence (α_g^2 = (P_c - ΔP_macro)/P_c = 1 - v_0^2/c^2, Manuscript Eq. 4)
theorem compliance_equivalence (v_esc_val : ℝ) :
    ((P_c - P_g v_esc_val) / P_c) = 1 - (v_esc_val^2 / c^2) := by
  have h_Pc_sub : P_c = (1 / 2) * rho_tau * c^2 := rfl
  have h_Pg_sub : P_g v_esc_val = (1 / 2) * rho_tau * v_esc_val^2 := rfl
  rw [h_Pc_sub, h_Pg_sub]
  have hc_ne_zero : c ≠ 0 := ne_of_gt c_pos
  have h1 : (((1 / 2) * rho_tau * c^2 - (1 / 2) * rho_tau * v_esc_val^2) / ((1 / 2) * rho_tau * c^2)) =
            (((1 / 2) * rho_tau * c^2) / ((1 / 2) * rho_tau * c^2)) -
            (((1 / 2) * rho_tau * v_esc_val^2) / ((1 / 2) * rho_tau * c^2)) := by ring
  rw [h1]
  have h_cancel_esc : (((1 / 2) * rho_tau * v_esc_val^2) / ((1 / 2) * rho_tau * c^2)) = (v_esc_val^2 / c^2) :=
    cancel_fraction_rho v_esc_val
  rw [h_cancel_esc]
  have h2 : (((1 / 2) * rho_tau * c^2) / ((1 / 2) * rho_tau * c^2)) = (c^2 / c^2) :=
    cancel_fraction_rho c
  rw [h2]
  have h3 : c^2 / c^2 = 1 := div_self (pow_ne_zero 2 hc_ne_zero)
  rw [h3]

-- Theorem 6: The Nested Ledger Identity (P_ambient = P_c * α_g^2, Manuscript Eqs. 3–4)
theorem nested_ledger_compliance (P_ambient alpha_g_sq v_0 : ℝ)
    (h_amb : P_ambient = P_c - P_g v_0)
    (h_alpha_g : alpha_g_sq = 1 - v_0^2 / c^2) :
    P_ambient = P_c * alpha_g_sq := by
  have h_eq := compliance_equivalence v_0
  rw [← h_amb, ← h_alpha_g] at h_eq
  calc P_ambient = (P_ambient / P_c) * P_c := (div_mul_cancel₀ P_ambient Pc_non_zero).symm
    _ = alpha_g_sq * P_c := by rw [h_eq]
    _ = P_c * alpha_g_sq := by ring

end AsymmetricTensor
