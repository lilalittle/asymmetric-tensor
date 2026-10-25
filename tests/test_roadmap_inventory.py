#!/usr/bin/env python3
"""Mutation regressions for lexical inventory and current conditional scope.

Zero h_target binders is a naming fact, not completion of the physical roadmap.
The historical ten-target inventory and current model premises remain explicit.
"""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / "scripts"))
from check_module_source import source_files
from roadmap_inventory import (declaration_signatures, has_named_binder,
                               target_binder_declarations)


class TargetInventory(unittest.TestCase):
    def targets(self, text):
        return target_binder_declarations([text])

    def test_comment_cannot_attach_to_preceding_theorem(self):
        text = """theorem mott : True := by trivial
-- Next item has a TARGET PLACEHOLDER `h_target`.
theorem actual (h_target : True) : True := h_target
"""
        self.assertEqual(self.targets(text), {"actual"})

    def test_nested_block_comments_and_fake_declarations(self):
        text = """/- outer /- theorem fake (h_target : True) : True := h_target -/ -/
theorem clean : True := by trivial
/- Following h_target commentary must not change the preceding theorem. -/
"""
        self.assertEqual(self.targets(text), set())

    def test_proof_local_name_is_not_an_assumption(self):
        text = """theorem clean : True := by
  have h_target : True := True.intro
  exact h_target
"""
        self.assertEqual(self.targets(text), set())

    def test_strings_are_not_tokens_or_declarations(self):
        text = 'def text : String := "(h_target : True) -- /- fake -/"\n'
        self.assertEqual(self.targets(text), set())

    def test_explicit_implicit_and_grouped_binders(self):
        text = """theorem explicit (h_target : True) : True := h_target
theorem implicit {h_target : True} : True := h_target
theorem grouped (first h_target last : True) : True := h_target
"""
        self.assertEqual(self.targets(text), {"explicit", "implicit", "grouped"})

    def test_similarly_named_binder_does_not_match(self):
        self.assertEqual(self.targets(
            "theorem other (h_target_extra : True) : True := h_target_extra\n"), set())

    def test_default_value_does_not_end_signature(self):
        self.assertEqual(self.targets(
            "theorem actual (n : Nat := 0) (h_target : True) : True := h_target\n"),
            {"actual"})

    def test_forall_binder_in_signature(self):
        self.assertEqual(self.targets(
            "theorem actual : ∀ h_target : True, True := fun h => h\n"), {"actual"})

    def test_primed_binders_are_different_identifiers(self):
        text = """theorem other (h_target' : True) : True := h_target'
theorem grouped (x h_target'' : True) : True := x
theorem quantified : ∀ h_target' : True, True := fun h => h
"""
        self.assertEqual(self.targets(text), set())

    def test_result_type_ascription_is_not_a_binder(self):
        self.assertEqual(self.targets(
            "theorem reference : (h_target : Prop) := proof\n"), set())

    def test_parameter_type_reference_is_not_a_binder(self):
        self.assertEqual(self.targets(
            "theorem reference (x : (h_target : Prop)) : True := by trivial\n"), set())

    def test_forall_body_ascription_is_not_a_binder(self):
        self.assertEqual(self.targets(
            "theorem reference : ∀ (x : True), (h_target : Prop) := proof\n"), set())

    def test_private_protected_and_attributed_declarations(self):
        text = """private theorem hidden (h_target : True) : True := h_target
protected theorem guarded {h_target : True} : True := h_target
@[simp] private theorem attributed (h_target : True) : True := h_target
"""
        self.assertEqual(self.targets(text), {"hidden", "guarded", "attributed"})

    def test_primed_declaration_name_is_preserved(self):
        self.assertEqual(self.targets(
            "private theorem hidden' (h_target : True) : True := h_target\n"),
            {"hidden'"})

    def test_multiline_string_cannot_introduce_declaration(self):
        text = '''def text : String := "a multiline string
private theorem fake (h_target : True) : True := h_target
end of string"
theorem clean : True := by trivial
'''
        self.assertEqual(self.targets(text), set())

    def test_parenthesized_and_grouped_forall_binders(self):
        text = """theorem outer : (∀ (x h_target : True), True) := proof
theorem nested : ∀ (x : True), ∀ {h_target : True}, True := proof
"""
        self.assertEqual(self.targets(text), {"outer", "nested"})

    def test_empty_comment_preserves_identifier_boundary(self):
        text = "theorem clean (h_/--/target : True) : True := target\n"
        self.assertEqual(self.targets(text), set())

    def test_forall_in_parameter_type_or_default_is_not_a_target(self):
        text = """theorem defaulted (p : Prop := ∀ h_target : True, True) : True := True.intro
theorem supplied (p : ∀ h_target : True, True) : True := True.intro
"""
        self.assertEqual(self.targets(text), set())

    def test_current_inventory_is_exact(self):
        sources = [path.read_text() for path in source_files(ROOT)]
        self.assertEqual(target_binder_declarations(sources), set())

    def test_historical_target_inventory_is_preserved(self):
        archived = (ROOT / "docs/equation-baseline-source.lean.txt").read_text()
        self.assertEqual(target_binder_declarations([archived]), {
            "alpha_decay_wkb_mapping", "optimal_transport_minimization",
            "gravitoelectromagnetism_mapping", "poynting_vector_convection",
            "entanglement_contextuality", "helicity_orbital_arrest",
            "almansi_finite_strain", "su3_mass_gap_transition",
            "lorentz_force_magnus_mapping", "wake_detachment_stabilization",
        })

    def test_quoted_target_binder_is_detected(self):
        self.assertEqual(self.targets(
            "theorem quoted («h_target» : True) : True := «h_target»\n"), {"quoted"})

    def test_target_reference_in_proof_does_not_replace_signature(self):
        text = "theorem conditional (h_wkb : True) : True := h_target\n"
        self.assertEqual(self.targets(text), set())
        signature = dict(declaration_signatures(text))["conditional"]
        self.assertTrue(has_named_binder(signature, "h_wkb"))
        self.assertFalse(has_named_binder(signature, "h_target"))

    def test_current_model_premises_are_still_explicit(self):
        # Reviewed v4.5 signature premises, including all conditional Section 16
        # declarations. These are lexical scope guards, not a substitute for
        # elaborated API-type comparison or a judgment of physical completeness.
        expected = {
            "lemaitre_tolman_bondi_compliance": ["h_admittance"],
            "volumetric_admittance_scaling": ["h_alpha_s"],
            "holographic_bound_area_scaling": ["h_area", "h_bekenstein"],
            "casimir_pressure_scaling": ["hd", "h_B4", "h_EM", "h_Delta_U", "h_P", "h_F"],
            "wakefield_cavitation_gradient": ["h_conservation", "h_Pc_const"],
            "alpha_decay_wkb_mapping": ["h_alpha_s", "h_wkb"],
            "optimal_transport_minimization": ["h_alpha_s"],
            "michelson_morley_invariance": [
                "h_alpha_pos", "_hc", "h_L_arm", "h_v_light", "h_t_par", "h_t_perp"],
            "shapiro_delay_refraction": ["h_alpha_pos", "h_n"],
            "inertia_conservation": [
                "h_fore_aft_sym", "h_bernoulli_fore", "h_bernoulli_aft", "h_net_force"],
            "action_reaction_equilibrium": ["h_total", "h_conserved"],
            "mott_scattering_cross_section": ["h_mott"],
            "entanglement_contextuality": ["h_distinct_angle", "h_nonvanishing_vorticity"],
            "cp_violation_energy_shift": ["h_E_CP"],
            "coulomb_bernoulli_superposition_and_deficit": ["h_flux", "hv1", "hv2", "h_alpha_s"],
            "coulomb_phase_flux_and_force_constant": ["hr", "h_alpha", "h_force_eq", "h_K_def"],
            "rydberg_energy_quantization": ["hn", "hr1", "h_radii", "h_circulation"],
            "kinematic_origin_of_charge": [
                "hr", "heps", "he_nonneg", "h_transduction", "h_force_eq"],
            "dirac_moment_and_magnetic_anomaly": ["h_bohr", "h_anomaly", "h_true"],
            "almansi_finite_strain": ["ha_s", "h_compliance"],
            "su3_mass_gap_transition": ["h_im_pos", "h_solid_regime", "h_De_def"],
            "z_pinch_sausage_instability": ["h_conservation", "h_P_dyn_zero"],
            "acoustic_covariance_volume": ["_h_gamma_ne", "h_L", "h_V_0", "h_V"],
            "wake_detachment_stabilization": ["h_alpha_s"],
            "u1_gauge_invariance": ["h_v"],
            "viscoelastic_phase_angle_reduction": ["h_alpha_s"],
            "electromagnetic_decoupling_ratio": ["ha_s", "hc", "ht_p", "h_Omega", "h_E", "h_M"],
            "fourier_curvature_decomposition": ["ha_s", "h_on_shell"],
            "born_infeld_general_determinant_isomorphism": ["ha_s"],
        }
        signatures = dict(declaration_signatures(
            (ROOT / "AsymmetricTensor/FutureTargets.lean").read_text()))
        for theorem, premises in expected.items():
            with self.subTest(theorem=theorem):
                self.assertIn(theorem, signatures)
                for premise in premises:
                    self.assertTrue(has_named_binder(signatures[theorem], premise),
                                    f"Review changed model premise: {theorem}.{premise}")


if __name__ == "__main__":
    unittest.main()
