#!/usr/bin/env python3
"""Fail-closed reference isolation/hash/API guard regressions; no Lean required."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from check_public_api import differences, parse_snapshot
from check_v57_reference import (
    LOCK_FILES, ROOT, SOURCE_COMMIT, SOURCE_PATH, SUMMARY_AFTER, SUMMARY_BEFORE,
    check_locks, prepare_reference, validate_source, validate_upload,
)


class V57ReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = subprocess.check_output(
            ["git", "show", f"{SOURCE_COMMIT}:{SOURCE_PATH}"], cwd=ROOT)

    def test_exact_source_and_single_authorized_comment_change(self):
        validate_source(self.source)
        corrected = self.source.replace(SUMMARY_BEFORE, SUMMARY_AFTER, 1)
        validate_upload(self.source, corrected)
        with self.assertRaises(RuntimeError):
            validate_source(self.source + b"\n")
        with self.assertRaises(RuntimeError):
            validate_upload(self.source, corrected + b"\n")
        with self.assertRaises(RuntimeError):
            validate_upload(self.source, self.source)

    def test_reference_never_reuses_first_party_build_or_split_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root, reference = Path(directory) / "candidate", Path(directory) / "reference"
            root.mkdir()
            reference.mkdir()
            for name in LOCK_FILES:
                (root / name).write_bytes(f"fixture {name}\n".encode())
            (root / ".lake/packages/mathlib").mkdir(parents=True)
            (root / ".lake/build").mkdir()
            (root / ".lake/build/AsymmetricTensor.olean").write_bytes(b"must not reuse")
            (root / "AsymmetricTensor").mkdir()
            (root / "AsymmetricTensor/Model.lean").write_text("must not copy")
            prepare_reference(root, reference, self.source)
            self.assertEqual((reference / "AsymmetricTensor.lean").read_bytes(), self.source)
            self.assertEqual((reference / ".lake/packages").resolve(),
                             (root / ".lake/packages").resolve())
            self.assertFalse((reference / ".lake/build").exists())
            self.assertFalse((reference / "AsymmetricTensor").exists())
            locks = {name: (root / name).read_bytes() for name in LOCK_FILES}
            check_locks(root, reference, locks)
            (reference / "lake-manifest.json").write_text("changed")
            with self.assertRaises(RuntimeError):
                check_locks(root, reference, locks)

    def test_generated_api_changes_are_not_hidden_by_lexical_inventory(self):
        named = {"AsymmetricTensor.witness"}
        before = {
            "AsymmetricTensor.witness": ("definition", "[]", "state"),
            "AsymmetricTensor.DynamicClebschFields.mk": ("constructor", "[]", "all fields"),
            "AsymmetricTensor.UnitDim.K": ("definition", "[]", "UnitDim -> Int"),
            "AsymmetricTensor.instMulUnitDim": ("definition", "[]", "Mul UnitDim"),
        }
        self.assertFalse(any(differences(named, named, before, before).values()))
        after = dict(before)
        del after["AsymmetricTensor.UnitDim.K"]
        after["AsymmetricTensor.UnitDim.L"] = ("definition", "[]", "UnitDim -> Int")
        after["AsymmetricTensor.DynamicClebschFields.mk"] = ("constructor", "[]", "lost field")
        after["AsymmetricTensor.instMulUnitDim"] = ("opaque", "[]", "Mul UnitDim")
        delta = differences(named, named, before, after)
        self.assertEqual(delta["Removed compiled declaration"], ["AsymmetricTensor.UnitDim.K"])
        self.assertEqual(delta["Added compiled declaration"], ["AsymmetricTensor.UnitDim.L"])
        self.assertEqual(delta["Changed kind/type/universes"],
                         ["AsymmetricTensor.DynamicClebschFields.mk", "AsymmetricTensor.instMulUnitDim"])

    def test_universes_and_missing_source_target_are_checked(self):
        before = {"AsymmetricTensor.f": ("theorem", "[u]", "full type")}
        after = {"AsymmetricTensor.f": ("theorem", "[v]", "full type")}
        delta = differences({"AsymmetricTensor.f", "AsymmetricTensor.missing"},
                            {"AsymmetricTensor.f"}, before, after)
        self.assertEqual(delta["Changed kind/type/universes"], ["AsymmetricTensor.f"])
        self.assertEqual(delta["Missing elaborated source declaration"], ["AsymmetricTensor.missing"])

    def test_snapshot_parser_rejects_empty_and_duplicate_reports(self):
        line = "API|AsymmetricTensor.f|theorem|[]|full type"
        self.assertEqual(parse_snapshot(line)["AsymmetricTensor.f"], ("theorem", "[]", "full type"))
        with self.assertRaises(RuntimeError):
            parse_snapshot("no declarations")
        with self.assertRaises(RuntimeError):
            parse_snapshot(line + "\n" + line)


if __name__ == "__main__":
    unittest.main()
