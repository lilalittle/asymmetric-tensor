import AsymmetricTensor
import ProofAudit

-- All declarations owned by the production root and its submodules, including
-- private declarations and declarations outside the AsymmetricTensor namespace.
-- v5.0: covariant_conservation is the sole declared custom axiom.
#audit_root AsymmetricTensor declared [AsymmetricTensor.covariant_conservation]

-- v5.0 positivity is proved without any custom axioms.
#audit_theorem AsymmetricTensor.c_pos custom []
#audit_theorem AsymmetricTensor.l_p_pos custom []
#audit_theorem AsymmetricTensor.hbar_pos custom []

-- These SELECTIVE per-result checks pin the v5.0 custom-axiom dependencies.
-- The coordinate postulate applies only to U_hat_dynamic; the two projections
-- inherit it, while divergence expansion and conditional geometric algebra do not.
-- tests/V45*.lean add focused exact checks for the current replacement APIs.
-- Changing it or any expected set requires review. See docs/verification.md.
#audit_theorem AsymmetricTensor.matrix_decomposition custom []
#audit_theorem AsymmetricTensor.tensor_decomposition_proven custom []
#audit_theorem AsymmetricTensor.contract_sym_anti_proven custom []
#audit_theorem AsymmetricTensor.unified_action_separation custom []
#audit_theorem AsymmetricTensor.bernoulli_energy_conservation custom [AsymmetricTensor.covariant_conservation]
#audit_theorem AsymmetricTensor.navier_stokes_momentum_conservation custom [AsymmetricTensor.covariant_conservation]
#audit_theorem AsymmetricTensor.divergence_expansion custom []
#audit_theorem AsymmetricTensor.geometric_navier_stokes custom []
#audit_theorem AsymmetricTensor.baryonic_tully_fisher_derivation custom []
