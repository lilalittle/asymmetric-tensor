import AsymmetricTensor
import ProofAudit

-- All declarations owned by the production root and its submodules, including
-- private declarations and declarations outside the AsymmetricTensor namespace.
-- v4.5: covariant_conservation is Binyamin's seventh axiom (physical postulate).
#audit_root AsymmetricTensor declared [AsymmetricTensor.c, AsymmetricTensor.l_p,
  AsymmetricTensor.hbar, AsymmetricTensor.c_pos, AsymmetricTensor.l_p_pos,
  AsymmetricTensor.hbar_pos, AsymmetricTensor.covariant_conservation]

-- These SELECTIVE per-result checks pin the actual v4.5 dependencies.
-- The coordinate postulate applies only to U_hat_dynamic; the two projections
-- inherit it, while divergence expansion and conditional geometric algebra do not.
-- tests/V45*.lean add focused exact checks for the current replacement APIs.
-- Changing it or any expected set requires review. See docs/verification.md.
#audit_theorem AsymmetricTensor.matrix_decomposition custom []
#audit_theorem AsymmetricTensor.tensor_decomposition_proven custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.contract_sym_anti_proven custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.unified_action_separation custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.bernoulli_energy_conservation custom [AsymmetricTensor.c,
  AsymmetricTensor.l_p, AsymmetricTensor.covariant_conservation]
#audit_theorem AsymmetricTensor.navier_stokes_momentum_conservation custom [AsymmetricTensor.c,
  AsymmetricTensor.l_p, AsymmetricTensor.covariant_conservation]
#audit_theorem AsymmetricTensor.divergence_expansion custom [AsymmetricTensor.c,
  AsymmetricTensor.l_p]
#audit_theorem AsymmetricTensor.geometric_navier_stokes custom [AsymmetricTensor.c,
  AsymmetricTensor.l_p, AsymmetricTensor.hbar, AsymmetricTensor.c_pos,
  AsymmetricTensor.l_p_pos, AsymmetricTensor.hbar_pos]
#audit_theorem AsymmetricTensor.baryonic_tully_fisher_derivation custom [AsymmetricTensor.c,
  AsymmetricTensor.l_p, AsymmetricTensor.hbar, AsymmetricTensor.c_pos,
  AsymmetricTensor.l_p_pos, AsymmetricTensor.hbar_pos]
