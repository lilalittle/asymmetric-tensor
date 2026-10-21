import AsymmetricTensor
import ProofAudit

-- All declarations owned by the production root and its submodules, including
-- private declarations and declarations outside the AsymmetricTensor namespace.
-- v5.7: the on-shell field bundle replaces the last declared custom axiom.
#audit_root AsymmetricTensor declared []

-- v5.0 positivity is proved without any custom axioms.
#audit_theorem AsymmetricTensor.c_pos custom []
#audit_theorem AsymmetricTensor.l_p_pos custom []
#audit_theorem AsymmetricTensor.hbar_pos custom []

-- These SELECTIVE per-result checks pin the v5.7 custom-axiom dependencies.
-- Conservation applies to U_hat_dynamic, projected from the on-shell bundle.
-- Its explicit witness and conservation projections require no custom axiom.
-- tests/V45*.lean add focused exact checks for the current replacement APIs.
-- Changing it or any expected set requires review. See docs/verification.md.
#audit_theorem AsymmetricTensor.matrix_decomposition custom []
#audit_theorem AsymmetricTensor.tensor_decomposition_proven custom []
#audit_theorem AsymmetricTensor.contract_sym_anti_proven custom []
#audit_theorem AsymmetricTensor.unified_action_separation custom []
#audit_theorem AsymmetricTensor.homogeneous_vacuum_is_divergence_free custom []
#audit_theorem AsymmetricTensor.covariant_conservation custom []
#audit_theorem AsymmetricTensor.bernoulli_energy_conservation custom []
#audit_theorem AsymmetricTensor.navier_stokes_momentum_conservation custom []
#audit_theorem AsymmetricTensor.divergence_expansion custom []
#audit_theorem AsymmetricTensor.geometric_navier_stokes custom []
#audit_theorem AsymmetricTensor.baryonic_tully_fisher_derivation custom []
#audit_theorem AsymmetricTensor.schwinger_zero_slip_aligned_bridge custom []
#audit_theorem AsymmetricTensor.tensor_four_effects_unification custom []
