#!/usr/bin/env python3
"""Fail-closed reference isolation/hash/API guard regressions; no Lean required."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from check_public_api import (
    certificate_source, differences, parse_snapshot, public_comparison,
)
from check_v59_reference import (
    LOCK_FILES, ROOT, SOURCE_COMMIT, SOURCE_PATH, STABLE_COMMIT, STABLE_TREE,
    check_locks, migration_inventory, prepare_reference, prepare_stable_reference,
    stable_sources, validate_source, validate_upload,
)


class V59ReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = subprocess.check_output(
            ["git", "show", f"{SOURCE_COMMIT}:{SOURCE_PATH}"], cwd=ROOT)

    def test_exact_immutable_source_and_upload_bytes(self):
        validate_source(self.source)
        validate_upload(self.source, self.source)
        with self.assertRaises(RuntimeError):
            validate_source(self.source + b"\n")
        with self.assertRaises(RuntimeError):
            validate_upload(self.source, self.source + b"\n")
        # Even an overview-only repair is not authorized for this source snapshot.
        overview = "Lorentz boost symmetry breaking".encode()
        self.assertIn(overview, self.source)
        with self.assertRaises(RuntimeError):
            validate_upload(self.source, self.source.replace(overview, b"Changed overview", 1))

    def test_previous_stable_identity_and_dependency_pins(self):
        self.assertNotEqual(STABLE_COMMIT, SOURCE_COMMIT)
        tree = subprocess.check_output(
            ["git", "rev-parse", f"{STABLE_COMMIT}^{{tree}}"], cwd=ROOT, text=True).strip()
        self.assertEqual(tree, STABLE_TREE)
        for name in LOCK_FILES:
            before = subprocess.check_output(
                ["git", "show", f"{STABLE_COMMIT}:{name}"], cwd=ROOT)
            raw = subprocess.check_output(
                ["git", "show", f"{SOURCE_COMMIT}:{name}"], cwd=ROOT)
            self.assertEqual(before, raw, name)

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

    def test_reference_rejects_absent_dependency_packages(self):
        with tempfile.TemporaryDirectory() as directory:
            root, reference = Path(directory) / "candidate", Path(directory) / "reference"
            root.mkdir()
            reference.mkdir()
            for name in LOCK_FILES:
                (root / name).write_bytes(b"fixture configuration")
            with self.assertRaisesRegex(RuntimeError, "Pinned dependency packages are absent"):
                prepare_reference(root, reference, self.source)

    def test_reference_rejects_preexisting_split_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root, reference = Path(directory) / "candidate", Path(directory) / "reference"
            root.mkdir()
            reference.mkdir()
            for name in LOCK_FILES:
                (root / name).write_bytes(b"fixture configuration")
            (root / ".lake/packages").mkdir(parents=True)
            (reference / "AsymmetricTensor").mkdir()
            with self.assertRaisesRegex(RuntimeError, "without split source"):
                prepare_reference(root, reference, self.source)

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

    def test_auxiliary_class_requires_theorem_kind_and_not_source_name(self):
        helper = "AsymmetricTensor.f._proof_1"
        for kind in ("definition", "axiom", "opaque", "constructor", "recursor", "inductive"):
            entry = {helper: (kind, "[]", "proposition")}
            report = public_comparison(set(), set(), entry, {})
            self.assertEqual(report["differences"]["Removed compiled declaration"], [helper])
        theorem = {helper: ("theorem", "[]", "proposition")}
        report = public_comparison({helper}, {helper}, theorem, {})
        self.assertIn(helper, report["differences"]["Removed compiled declaration"])
        for name in ("AsymmetricTensor.f.eq_1", "AsymmetricTensor.f._proof_x",
                     "AsymmetricTensor.f._proof_1.nested", "AsymmetricTensor.UnitDim.mk"):
            report = public_comparison(set(), set(), {name: ("theorem", "[]", "P")}, {})
            self.assertEqual(report["differences"]["Removed compiled declaration"], [name])

    def test_proof_reference_normalization_requires_exact_proposition_and_universes(self):
        old_helper = "AsymmetricTensor.a._proof_1"
        new_helper = "AsymmetricTensor.b._proof_1"
        equation = "AsymmetricTensor.f.eq_1"
        def fixture(helper, proposition="P", kind="theorem", levels="[]"):
            return {helper: (kind, levels, proposition), equation: ("theorem", "[]",
                    f"full type (Lean.Expr.const `{helper} [])")}
        before, after = fixture(old_helper), fixture(new_helper)
        report = public_comparison(set(), set(), before, after)
        self.assertFalse(any(report["differences"].values()))
        self.assertEqual(report["kernel_certificates_required"], [equation])
        for mutated in (fixture(new_helper, proposition="Q"),
                        fixture(new_helper, kind="axiom"),
                        fixture(new_helper, kind="definition"),
                        fixture(new_helper, levels="[u]")):
            report = public_comparison(set(), set(), before, mutated)
            self.assertIn(equation, report["differences"]["Changed kind/type/universes"])
        after[equation] = ("theorem", "[]", after[equation][2] + " genuine type change")
        report = public_comparison(set(), set(), before, after)
        self.assertIn(equation, report["differences"]["Changed kind/type/universes"])

    def test_equation_certificate_uses_unmodified_raw_type_and_actual_constant(self):
        name = "AsymmetricTensor.f.eq_1"
        raw = "Lean.Expr.app\\n  (Lean.Expr.const `AsymmetricTensor.a [])\\n  (Lean.Expr.const `True [])"
        text = certificate_source([name], {name: ("theorem", "[]", raw)})
        self.assertIn("let rawType : Expr :=\n    Lean.Expr.app\n"
                      "      (Lean.Expr.const `AsymmetricTensor.a [])\n"
                      "      (Lean.Expr.const `True [])", text)
        self.assertIn(f"value := mkConst `{name} (levelParams.map Level.param)", text)
        self.assertIn("toKernelEnv.addDecl options declaration", text)
        self.assertIn("setBool `debug.skipKernelTC false", text)
        self.assertNotIn("PROOF_OF_EXACT_RECORDED_TYPE", text)

    def test_stable_baseline_is_immutable_modules_with_independent_outputs(self):
        sources = stable_sources(ROOT)
        self.assertEqual(len(sources), 10)
        self.assertIn("AsymmetricTensor/Model.lean", sources)
        self.assertNotIn(SOURCE_PATH, sources)
        with tempfile.TemporaryDirectory() as directory:
            root, stable = Path(directory) / "candidate", Path(directory) / "stable"
            root.mkdir()
            stable.mkdir()
            for name in LOCK_FILES:
                (root / name).write_bytes(f"fixture {name}\n".encode())
            (root / ".lake/packages").mkdir(parents=True)
            (root / ".lake/build").mkdir()
            (root / ".lake/build/AsymmetricTensor.olean").write_bytes(b"candidate cache")
            prepare_stable_reference(root, stable, sources)
            for name, contents in sources.items():
                self.assertEqual((stable / name).read_bytes(), contents)
            self.assertFalse((stable / ".lake/build").exists())
            self.assertEqual((stable / ".lake/packages").resolve(),
                             (root / ".lake/packages").resolve())

    def test_migration_records_generated_deltas_but_rejects_missing_evidence(self):
        old = {"AsymmetricTensor.UnitDim.L": ("definition", "[]", "UnitDim -> Int"),
               "AsymmetricTensor.conservation": ("axiom", "[]", "conserved")}
        new = {"AsymmetricTensor.UnitDim.K": ("definition", "[]", "UnitDim -> Int"),
               "AsymmetricTensor.conservation": ("theorem", "[]", "conserved"),
               "AsymmetricTensor.DynamicClebschFields.mk": ("constructor", "[]", "full fields")}
        named = {"AsymmetricTensor.conservation"}
        report = migration_inventory(named, named, old, new)
        self.assertEqual(report["stable"], old)
        self.assertEqual(report["integrated"], new)
        self.assertEqual(report["differences"]["Removed compiled declaration"],
                         ["AsymmetricTensor.UnitDim.L"])
        self.assertEqual(report["differences"]["Changed kind/type/universes"],
                         ["AsymmetricTensor.conservation"])
        with self.assertRaises(RuntimeError):
            migration_inventory(named, named, {}, new)
        with self.assertRaises(RuntimeError):
            migration_inventory(named | {"AsymmetricTensor.missing"}, named, old, new)


if __name__ == "__main__":
    unittest.main()
