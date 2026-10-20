import AsymmetricTensor
import ProofAudit

/-! Current matrix/contraction interfaces, with test-local component witnesses.
No action integral, variation, or field equation is asserted here. -/

open AsymmetricTensor BigOperators

namespace V45MatrixRegression

def sampleMatrix : T2 := fun i j => if i = 0 ∧ j = 1 then 2 else 0

example : symPart sampleMatrix 0 1 = 1 := by norm_num [symPart, sampleMatrix]
example : antiPart sampleMatrix 0 1 = 1 := by norm_num [antiPart, sampleMatrix]
example : antiPart sampleMatrix 1 0 = -1 := by norm_num [antiPart, sampleMatrix]
example : sampleMatrix = symPart sampleMatrix + antiPart sampleMatrix :=
  matrix_decomposition sampleMatrix

-- Test-local basis tensors keep the production API surface unchanged.
def electric (e : ℝ) : T2 := fun i j =>
  if i = 0 ∧ j = 1 then e else if i = 1 ∧ j = 0 then -e else 0

def magnetic (b : ℝ) : T2 := fun i j =>
  if i = 1 ∧ j = 2 then b else if i = 2 ∧ j = 1 then -b else 0

example : tensor_contract (electric 1) (electric 1) = 2 := by
  norm_num [tensor_contract, electric]
example : lorentzian_contract (electric 1) (electric 1) = -2 := by
  norm_num [lorentzian_contract, electric]
example : lorentzian_contract (magnetic 1) (magnetic 1) = 2 := by
  norm_num [lorentzian_contract, magnetic]
example : lorentzian_contract (electric 2 + magnetic 3)
    (electric 2 + magnetic 3) = 10 := by
  norm_num [lorentzian_contract, electric, magnetic]
example : tensor_contract (electric 2 + magnetic 3)
    (electric 2 + magnetic 3) = 26 := by
  norm_num [tensor_contract, electric, magnetic]

-- The retained generic raising API agrees with the new explicit component API.
theorem contraction_bridge (A B : T2) :
    contract2 eta_metric A B = lorentzian_contract A B := by
  simp [contract2, raiseBoth, eta_metric, Fin.sum_univ_succ, lorentzian_contract]
  ring

theorem arbitrary_sym_anti (A B : T2) :
    lorentzian_contract (symPart A) (antiPart B) = 0 := by
  dsimp [lorentzian_contract, symPart, antiPart]
  ring

example (s a vx vy vz tp : ℝ) (d_lambda d_beta : V4) :
    lorentzian_contract (U_hat s a vx vy vz d_lambda d_beta tp)
        (U_hat s a vx vy vz d_lambda d_beta tp) =
      lorentzian_contract (U_sym s a vx vy vz d_lambda d_beta tp)
        (U_sym s a vx vy vz d_lambda d_beta tp) +
      lorentzian_contract (U_anti s a vx vy vz d_lambda d_beta tp)
        (U_anti s a vx vy vz d_lambda d_beta tp) :=
  lorentzian_action_separation s a vx vy vz d_lambda d_beta tp

-- The v4.5 comoving bundle retains normalization, projector and slip constraints.
example : u_comoving 0 = -1 := by simp [u_comoving]

example (vx vy vz : ℝ) (ν : Fin 4) :
    (∑ μ : Fin 4, ∑ α : Fin 4, eta_metric μ α * u_comoving μ * u_comoving α) = -1 ∧
    (∑ μ : Fin 4, ∑ α : Fin 4,
      eta_metric μ α * u_comoving μ * h_projector u_comoving α ν) = 0 ∧
    (∑ μ : Fin 4, ∑ α : Fin 4,
      eta_metric μ α * u_comoving μ * v_perp_covec vx vy vz α) = 0 :=
  comoving_orthogonality_relations vx vy vz ν

-- Spatial gradients have no time-space wedge components. This hypothesis is
-- essential: arbitrary four-gradients do not have the old spatial omega API.
theorem comoving_vorticity_orthogonal (lx ly lz bx by_ bz : ℝ) (ν : Fin 4) :
    (∑ μ : Fin 4, ∑ α : Fin 4,
      eta_metric μ α * u_comoving μ *
        omega_clebsch_2form (v_perp_covec lx ly lz) (v_perp_covec bx by_ bz) α ν) = 0 := by
  fin_cases ν <;>
    norm_num [Fin.sum_univ_succ, eta_metric, u_comoving,
      omega_clebsch_2form, wedge_covec, v_perp_covec]

example (s a vx vy vz lx ly lz bx by_ bz tp : ℝ) :
    U_covariant s a c tp u_comoving (v_perp_covec vx vy vz)
        (v_perp_covec lx ly lz) (v_perp_covec bx by_ bz) =
      U_hat s a vx vy vz (v_perp_covec lx ly lz) (v_perp_covec bx by_ bz) tp :=
  U_hat_eq_comoving_U_covariant s a vx vy vz lx ly lz bx by_ bz tp

-- A time-space Clebsch wedge is retained by U_covariant but omitted by the
-- spatial-component U_hat. Thus the spatial restriction above is observable.
theorem nonspatial_comoving_counterexample :
    U_covariant 1 1 c 1 u_comoving (v_perp_covec 0 0 0)
        (fun i => if i = 0 then 1 else 0) (v_perp_covec 1 0 0) ≠
      U_hat 1 1 0 0 0 (fun i => if i = 0 then 1 else 0) (v_perp_covec 1 0 0) 1 := by
  intro h
  have h01 := congrArg (fun A : T2 => A 0 1) h
  norm_num [U_covariant, U_hat, u_comoving, v_perp_covec, h_projector,
    eta_metric, wedge_covec, omega_clebsch_2form] at h01

-- Positive Omega_z=w uses d_lambda=(0,0,1,0), d_beta=(0,w,0,0).
def zLambda : V4 := v_perp_covec 0 1 0
def zBeta (w : ℝ) : V4 := v_perp_covec w 0 0

theorem z_vorticity_orientation (w : ℝ) :
    Omega_x_clebsch zLambda (zBeta w) = 0 ∧
    Omega_y_clebsch zLambda (zBeta w) = 0 ∧
    Omega_z_clebsch zLambda (zBeta w) = w := by
  simp [Omega_x_clebsch, Omega_y_clebsch, Omega_z_clebsch,
    omega_clebsch_2form, wedge_covec, zLambda, zBeta, v_perp_covec]

-- Equal electric and magnetic terms give a null contraction in Eq. 123.
example : lorentzian_contract (U_anti 2 1 c 0 0 zLambda (zBeta 1) 1)
    (U_anti 2 1 c 0 0 zLambda (zBeta 1) 1) = 0 := by
  rw [lorentzian_antisymmetric_trace_eq123, (z_vorticity_orientation _).1,
    (z_vorticity_orientation _).2.1, (z_vorticity_orientation _).2.2]
  field_simp [c_ne_zero]
  ring

-- Nonunit slip, vorticity, and time scale guard the factors and signs.
example : lorentzian_contract (U_anti 2 3 c 0 0 zLambda (zBeta 2) 4)
    (U_anti 2 3 c 0 0 zLambda (zBeta 2) 4) = 1134 := by
  rw [lorentzian_antisymmetric_trace_eq123, (z_vorticity_orientation _).1,
    (z_vorticity_orientation _).2.1, (z_vorticity_orientation _).2.2]
  field_simp [c_ne_zero]
  ring

#audit_theorem V45MatrixRegression.comoving_vorticity_orthogonal custom []
#audit_theorem V45MatrixRegression.nonspatial_comoving_counterexample custom []
#audit_theorem V45MatrixRegression.z_vorticity_orientation custom []
#audit_theorem AsymmetricTensor.comoving_orthogonality_relations custom []
#audit_theorem AsymmetricTensor.U_hat_eq_comoving_U_covariant custom []
#audit_theorem V45MatrixRegression.contraction_bridge custom []
#audit_theorem V45MatrixRegression.arbitrary_sym_anti custom []
#audit_theorem AsymmetricTensor.lorentzian_contract_sym_anti_proven custom []
#audit_theorem AsymmetricTensor.lorentzian_action_separation custom []
#audit_theorem AsymmetricTensor.lorentzian_antisymmetric_trace_eq123 custom []

end V45MatrixRegression

-- Audit this test module's retained declarations for completeness, too.
#audit_current_module declared []
