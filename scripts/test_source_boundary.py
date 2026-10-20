#!/usr/bin/env python3
"""Mutate the draft boundary without changing the working tree's source."""
import contextlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace

sys.dont_write_bytecode = True
from check_author_drafts import check_one
from check_lean_style import check as style
from check_module_context import check as context
from check_module_source import source_files
from check_public_api import inventory
from check_source_boundary import check as boundary, ROOT
from report_author_drafts import validate
from source_boundary import author_drafts, is_author_draft, production_sources


class SourceBoundary(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ["AsymmetricTensor", "scripts", "tests"]:
            shutil.copytree(ROOT / name, self.root / name)
        for name in ["AsymmetricTensor.lean", "ProofAudit.lean"]:
            shutil.copy(ROOT / name, self.root)

    def test_exact_scope(self):
        self.assertTrue(is_author_draft("AsymmetricTensor/Asymmetric Tensor v5.0.lean"))
        self.assertTrue(is_author_draft("AsymmetricTensor/Asymmetric Tensor v12.3.4.lean"))
        for path in ["AsymmetricTensor.lean", "AsymmetricTensor/Bad Name.lean",
                     "AsymmetricTensor/Applications/Asymmetric Tensor v5.0.lean",
                     "AsymmetricTensor/Asymmetric Tensor v5.0.lean.bak"]:
            self.assertFalse(is_author_draft(path), path)

    def test_broken_author_uploads_are_isolated_from_every_inventory(self):
        before = inventory(self.root)
        paths = author_drafts(self.root) + [self.root / "AsymmetricTensor/Asymmetric Tensor v99.0.lean"]
        for path in paths:
            path.write_text('/- UNTERMINATED COMMENT\ninvalid Lean syntax!\ntheorem bad : False := by sorry')
        self.assertEqual(inventory(self.root), before)
        self.assertEqual(source_files(self.root), production_sources(self.root))
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(style(self.root), [])
        self.assertEqual(context(self.root), [])
        self.assertEqual(boundary(self.root), [])

    def test_unrelated_spaced_file_is_not_exempt(self):
        (self.root / "AsymmetricTensor/Bad Name.lean").write_text("broken!")
        self.assertTrue(style(self.root))
        self.assertTrue(context(self.root))

    def test_missing_stable_module_fails(self):
        (self.root / "AsymmetricTensor/Model.lean").unlink()
        self.assertTrue(style(self.root))
        self.assertTrue(context(self.root))

    def test_root_is_not_an_author_scratch_file(self):
        (self.root / "AsymmetricTensor.lean").write_text("broken root!")
        self.assertTrue(style(self.root))

    def test_escaped_draft_import_rejected(self):
        for relative in ["AsymmetricTensor.lean", "ProofAudit.lean", "tests/Boundary.lean"]:
            with (self.root / relative).open("a") as output:
                output.write('\nimport AsymmetricTensor.«Asymmetric Tensor v5.0»\n')
        self.assertEqual(len(boundary(self.root)), 3)

    def test_multiline_draft_import_rejected(self):
        with (self.root / "AsymmetricTensor.lean").open("a") as output:
            output.write('\nimport Mathlib\n  AsymmetricTensor.«Asymmetric Tensor v5.0»\n')
        self.assertTrue(boundary(self.root))

    def test_report_rejects_missing_crashed_or_tool_failed_diagnostics(self):
        output = self.root / "diagnostics"
        output.mkdir()
        expected = ["AsymmetricTensor/Asymmetric Tensor v5.0.lean"]
        with self.assertRaises(RuntimeError):
            validate(output, expected)
        (output / "summary.md").write_text("summary")
        (output / "draft.log").write_text("compiler log")
        for status, code, accepted in [("COMPILED", 0, True), ("COMPILE_FAILED", 1, True),
                                       ("TIMEOUT", None, True), ("TOOL_FAILURE", -9, False),
                                       ("COMPILED", 1, False), ("BOGUS", 0, False)]:
            (output / "results.json").write_text(json.dumps([
                {"path": expected[0], "status": status, "exit_code": code, "log": "draft.log"}]))
            if accepted:
                self.assertEqual(validate(output, expected)[0]["status"], status)
            else:
                with self.assertRaises(RuntimeError):
                    validate(output, expected)
        (output / "results.json").write_text("[]")
        with self.assertRaises(RuntimeError):
            validate(output, expected)

    def test_diagnostic_outcomes(self):
        path = author_drafts(self.root)[0]
        log = self.root / "diagnostic.log"
        for code, status in [(0, "COMPILED"), (1, "COMPILE_FAILED"), (-9, "TOOL_FAILURE")]:
            def runner(*args, **kwargs):
                return SimpleNamespace(returncode=code)
            self.assertEqual(check_one(path, self.root, log, 2, runner)["status"], status)
        for exception, status in [(FileNotFoundError("lake"), "TOOL_FAILURE"),
                                  (subprocess.TimeoutExpired("lake", 2), "TIMEOUT")]:
            def runner(*args, **kwargs):
                raise exception
            self.assertEqual(check_one(path, self.root, log, 2, runner)["status"], status)


if __name__ == "__main__":
    unittest.main()
