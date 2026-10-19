#!/usr/bin/env python3
"""Check the actual module inventory and bounded split-context mutations."""
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from check_module_context import check, ROOT


class ModuleContext(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        shutil.copytree(ROOT / "AsymmetricTensor", self.root / "AsymmetricTensor")
        (self.root / "scripts").mkdir()
        shutil.copy(ROOT / "scripts/module-context-baseline.json", self.root / "scripts")

    def replace(self, relative, before, after):
        path = self.root / "AsymmetricTensor" / relative
        source = path.read_text()
        self.assertIn(before, source)
        path.write_text(source.replace(before, after, 1))

    def assert_rejected(self, diagnostic):
        errors = check(self.root)
        self.assertTrue(any(diagnostic in error for error in errors), errors)

    def test_current_source(self):
        # This real-tree check makes this script the single aggregate gate.
        self.assertEqual(check(ROOT), [])

    def test_clean_copy(self):
        self.assertEqual(check(self.root), [])

    def test_missing_import(self):
        self.replace("FieldCalculus.lean", "public import AsymmetricTensor.MatrixAlgebra\n", "")
        self.assert_rejected("missing first-party public import")

    def test_changed_import(self):
        self.replace("Applications/MechanicsMass.lean", "public import AsymmetricTensor.MatrixAlgebra",
                     "public import AsymmetricTensor.FieldCalculus")
        self.assert_rejected("changed first-party public import")

    def test_additional_import(self):
        self.replace("MatrixAlgebra.lean", "public import AsymmetricTensor.Model",
                     "public import AsymmetricTensor.Model\npublic import AsymmetricTensor.FieldCalculus")
        self.assert_rejected("additional first-party public import")

    def test_missing_context(self):
        self.replace("MatrixAlgebra.lean", "variable (M : ℝ)\n", "")
        self.assert_rejected("missing section-context command")

    def test_changed_context(self):
        self.replace("Applications/WavesForces.lean", "variable (v_val : ℝ)",
                     "variable (v_val : ℚ)")
        self.assert_rejected("changed section-context command")

    def test_additional_context(self):
        self.replace("FieldCalculus.lean", "namespace AsymmetricTensor",
                     "namespace AsymmetricTensor\nvariable (new_field : ℝ)")
        self.assert_rejected("additional section-context command")

    def test_missing_typeclass_context(self):
        self.replace("Applications/Geometry.lean", " [Module ℝ V_3D]", "")
        self.assert_rejected("changed section-context command")

    def test_missing_omit(self):
        self.replace("MatrixAlgebra.lean", "omit [Module ℝ V_3D] [Module ℝ Forms_2D] in\n", "")
        self.assert_rejected("missing section-context command")

    def test_additional_include(self):
        self.replace("MatrixAlgebra.lean", "variable (M : ℝ)",
                     "variable (M : ℝ)\ninclude M")
        self.assert_rejected("additional section-context command")

    def test_reordered_context(self):
        self.replace("MatrixAlgebra.lean", "variable (M : ℝ)\n", "")
        self.replace("MatrixAlgebra.lean", "variable (Phi : ℝ)",
                     "variable (Phi : ℝ)\nvariable (M : ℝ)")
        self.assert_rejected("section-context command")

    def test_missing_future_force_import(self):
        self.replace("FutureTargets.lean",
                     "public import AsymmetricTensor.Applications.WavesForces\n", "")
        self.assert_rejected("missing first-party public import")

    def test_reordered_forms_operators(self):
        self.replace("Applications/WavesForces.lean",
                     "variable (d0 : Forms_0D →ₗ[ℝ] Forms_1D)\n"
                     "variable (d1 : Forms_1D →ₗ[ℝ] Forms_2D)",
                     "variable (d1 : Forms_1D →ₗ[ℝ] Forms_2D)\n"
                     "variable (d0 : Forms_0D →ₗ[ℝ] Forms_1D)")
        self.assert_rejected("section-context command")

    def test_reordered_velocity_pressure_context(self):
        self.replace("Applications/WavesForces.lean", "variable (v_val : ℝ)\n", "")
        self.replace("Applications/WavesForces.lean",
                     "variable (lambda_D L_0 P_dyn_val : ℝ)",
                     "variable (lambda_D L_0 P_dyn_val : ℝ)\nvariable (v_val : ℝ)")
        self.assert_rejected("section-context command")

    def test_comments_strings_and_spacing(self):
        self.replace("MatrixAlgebra.lean", "variable (M : ℝ)",
                     "variable   (M : ℝ) -- retained context\n"
                     "/- outer /- nested -/\nvariable (fake : ℝ)\n-/\n"
                     'def contextText := "text\nvariable (also_fake : ℝ)\n"')
        self.assertEqual(check(self.root), [])

    def test_multiline_context_needs_review(self):
        self.replace("MatrixAlgebra.lean", "variable (M : ℝ)",
                     "variable (M : ℝ)\n  (extra : ℝ)")
        self.assert_rejected("unsupported multiline context command")

    def test_additional_module(self):
        (self.root / "AsymmetricTensor/NewModule.lean").write_text("")
        self.assert_rejected("additional module needs a reviewed context inventory")


if __name__ == "__main__":
    unittest.main()
