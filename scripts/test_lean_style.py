#!/usr/bin/env python3
"""Small mutation regressions for the module/style gate (no Lean installation needed)."""
import contextlib
import io
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from check_lean_style import check, ROOT


class StyleGate(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        shutil.copytree(ROOT / "AsymmetricTensor", self.root / "AsymmetricTensor")
        shutil.copy(ROOT / "AsymmetricTensor.lean", self.root)
        (self.root / "scripts").mkdir()
        shutil.copy(ROOT / "scripts/lean-style-baseline.json", self.root / "scripts")

    def errors(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return check(self.root)

    def test_clean(self):
        self.assertEqual(self.errors(), [])

    def test_new_long_line(self):
        with (self.root / "AsymmetricTensor/Model.lean").open("a") as file:
            file.write("\n-- " + "x" * 101 + "\n")
        self.assertTrue(any("unreviewed long line" in error for error in self.errors()))

    def test_global_suppression(self):
        with (self.root / "AsymmetricTensor/Model.lean").open("a") as file:
            file.write("\nset_option linter.unusedSectionVars false\n")
        self.assertTrue(any("unreviewed unused-section-variable" in error
                            for error in self.errors()))

    def test_unimported_module(self):
        shutil.copy(self.root / "AsymmetricTensor/Model.lean",
                    self.root / "AsymmetricTensor/Orphan.lean")
        self.assertTrue(any("unreachable from the umbrella" in error for error in self.errors()))


if __name__ == "__main__":
    unittest.main()
