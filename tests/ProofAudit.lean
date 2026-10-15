import AsymmetricTensor
import ProofAudit

-- All declarations owned by the production root and its submodules, including
-- private declarations and declarations outside the AsymmetricTensor namespace.
#audit_root AsymmetricTensor declared [AsymmetricTensor.c, AsymmetricTensor.l_p,
  AsymmetricTensor.hbar, AsymmetricTensor.c_pos, AsymmetricTensor.l_p_pos,
  AsymmetricTensor.hbar_pos]

-- This file lists eleven SELECTIVE per-result axiom checks.
-- tests/LorentzianAction.lean retains seventeen additional exact action checks.
-- Changing it or any expected set requires review. See docs/verification.md.
#audit_theorem AsymmetricTensor.matrix_decomposition custom []
#audit_theorem AsymmetricTensor.tensor_decomposition_proven custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.contract_sym_anti_proven custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.unified_action_separation custom [AsymmetricTensor.c]
#audit_theorem AsymmetricTensor.constant_coordinate_conserved custom []
#audit_theorem AsymmetricTensor.exists_coordinate_conserved custom []
#audit_theorem AsymmetricTensor.coordinate_field_not_conserved custom []
#audit_theorem AsymmetricTensor.bernoulli_energy_conservation custom []
#audit_theorem AsymmetricTensor.navier_stokes_momentum_conservation custom []
#audit_theorem AsymmetricTensor.geometric_navier_stokes custom [AsymmetricTensor.c,
  AsymmetricTensor.l_p, AsymmetricTensor.hbar, AsymmetricTensor.c_pos,
  AsymmetricTensor.l_p_pos, AsymmetricTensor.hbar_pos]
#audit_theorem AsymmetricTensor.baryonic_tully_fisher_derivation custom [AsymmetricTensor.c,
  AsymmetricTensor.l_p, AsymmetricTensor.hbar, AsymmetricTensor.c_pos,
  AsymmetricTensor.l_p_pos, AsymmetricTensor.hbar_pos]
