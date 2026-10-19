"""Regression/mutation checks for the fixed v9 / #9+#33 evidence ledger.

These tests exercise accounting and stale-evidence guards, not the correctness
of the human mathematical mapping. Reproduce the kernel audit separately with
the commands in docs/equation-coverage.md.
"""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('equation_ledger', ROOT / 'scripts/equation_ledger.py')
ledger = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ledger)


class LedgerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.mapping = json.loads((ROOT / 'docs/equation-map.json').read_text())
        cls.audit = json.loads((ROOT / 'docs/declaration-audit.json').read_text())
        cls.source = (ROOT / 'docs/equation-baseline-source.lean.txt').read_text()
        cls.inventory, cls.sections = ledger.equation_inventory(ROOT / 'papers/asymmetric-metric-tensor.pdf')
        cls.tmp = tempfile.TemporaryDirectory(prefix='equation-ledger-test-')
        cls.fixture = Path(cls.tmp.name)
        paths = set(cls.mapping['snapshot']['files']) | {
            'scripts/equation_ledger.py', 'docs/equation-map.json',
            'docs/declaration-audit.json', 'docs/equation-coverage.json',
            'docs/equation-coverage.md', *ledger.ARCHIVED_FILES.values(),
        }
        for path in paths:
            target = cls.fixture / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / path, target)
        # The live-success fixture deliberately reconstructs the accepted snapshot.
        # Never restore old source or dependencies into the production checkout.
        for path, archive in ledger.ARCHIVED_FILES.items():
            shutil.copyfile(cls.fixture / archive, cls.fixture / path)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def validate_mapping(self, mapping):
        return ledger.validate_mapping(mapping, self.inventory, self.audit, self.source)

    def validate_audit(self, audit):
        return ledger.validate_audit(audit, self.source, self.mapping['snapshot'])

    def cli(self, *args):
        return subprocess.run(
            [sys.executable, str(self.fixture / 'scripts/equation_ledger.py'), *args],
            capture_output=True, text=True, check=False,
        )

    def changed_file(self, path, action):
        target = self.fixture / path
        original = target.read_bytes()
        try:
            target.write_bytes(original + b'\n')
            action()
        finally:
            target.write_bytes(original)

    def assert_cli_failure(self, *args, contains):
        result = self.cli(*args)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(contains, result.stderr)

    def test_snapshot_and_generated_artifacts_match(self):
        for mode in [('--check',), ('--check', '--historical')]:
            with self.subTest(mode=mode):
                result = self.cli(*mode)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('239 numbered equations, 40 unnumbered claims, 240 audited declarations', result.stdout)
        self.assertEqual(len(self.inventory), 239)
        self.assertEqual(self.audit['source_declaration_count'], 214)

    def test_every_snapshot_file_is_hash_guarded(self):
        for path in self.mapping['snapshot']['files']:
            with self.subTest(path=path):
                self.changed_file(path, lambda: self.assert_cli_failure('--check', contains='Stale reviewed snapshot'))

    def test_live_fixture_is_explicitly_the_archived_snapshot(self):
        for path, archive in ledger.ARCHIVED_FILES.items():
            with self.subTest(path=path):
                self.assertEqual((self.fixture / path).read_bytes(), (ROOT / archive).read_bytes())
                self.assertEqual(ledger.digest(self.fixture / path), self.mapping['snapshot']['files'][path])

    def test_current_checkout_is_validated_as_historical_evidence(self):
        result = subprocess.run(
            [sys.executable, str(ROOT / 'scripts/equation_ledger.py'), '--check', '--historical'],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.startswith('HISTORICAL ARCHIVE ONLY:'))

    def test_historical_mode_explicitly_ignores_later_live_source(self):
        def check():
            self.assert_cli_failure('--check', contains='Stale reviewed snapshot')
            result = self.cli('--check', '--historical')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(result.stdout.startswith('HISTORICAL ARCHIVE ONLY:'))
        self.changed_file('AsymmetricTensor.lean', check)

    def test_historical_mode_explicitly_ignores_later_live_manifest(self):
        def check():
            self.assert_cli_failure('--check', contains='Stale reviewed snapshot: lake-manifest.json')
            changed_manifest = (self.fixture / 'lake-manifest.json').read_bytes()
            result = self.cli('--check', '--historical')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(result.stdout.startswith('HISTORICAL ARCHIVE ONLY:'))
            self.assertEqual((self.fixture / 'lake-manifest.json').read_bytes(), changed_manifest)
        self.changed_file('lake-manifest.json', check)

    def test_historical_mode_preserves_later_live_audit_program(self):
        def check():
            self.assert_cli_failure('--check', contains='Stale reviewed snapshot: tests/EquationAxioms.lean')
            changed_audit = (self.fixture / 'tests/EquationAxioms.lean').read_bytes()
            result = self.cli('--check', '--historical')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(result.stdout.startswith('HISTORICAL ARCHIVE ONLY:'))
            self.assertEqual((self.fixture / 'tests/EquationAxioms.lean').read_bytes(), changed_audit)
        self.changed_file('tests/EquationAxioms.lean', check)

    def test_archives_are_guarded_even_when_live_snapshot_matches(self):
        for path, archive in ledger.ARCHIVED_FILES.items():
            with self.subTest(path=path):
                def check():
                    self.assert_cli_failure('--check', contains=f'Archived snapshot evidence changed: {path}')
                    self.assert_cli_failure('--check', '--historical', contains=f'Stale reviewed snapshot: {path}')
                self.changed_file(archive, check)

    def test_historical_mode_still_guards_nonarchived_snapshot_files(self):
        for path in self.mapping['snapshot']['files'].keys() - ledger.ARCHIVED_FILES.keys():
            with self.subTest(path=path):
                self.changed_file(path, lambda: self.assert_cli_failure(
                    '--check', '--historical', contains=f'Stale reviewed snapshot: {path}'))

    def test_historical_mode_cannot_import_an_unbound_live_audit(self):
        for mode in ['--check', '--write']:
            with self.subTest(mode=mode):
                self.assert_cli_failure(mode, '--historical', '--audit-log', '/not-a-baseline-log',
                                        contains='Historical mode checks committed baseline evidence only')

    def test_deterministic_outputs_reject_edits(self):
        for path in ['docs/equation-coverage.json', 'docs/equation-coverage.md', 'docs/declaration-audit.json']:
            with self.subTest(path=path):
                self.changed_file(path, lambda: self.assert_cli_failure('--check', contains='Stale generated artifact'))

    def test_missing_numbered_equation_rejected(self):
        m = deepcopy(self.mapping)
        m['entries'] = [r for r in m['entries'] if r['id'] != 239]
        with self.assertRaisesRegex(ValueError, 'Numbered coverage'):
            self.validate_mapping(m)

    def test_duplicate_entry_rejected(self):
        m = deepcopy(self.mapping)
        m['entries'].append(deepcopy(m['entries'][0]))
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            self.validate_mapping(m)

    def test_missing_foundational_or_roadmap_claim_rejected(self):
        for claim in ['U1.exterior_closure', 'S16.1.holographic_bound']:
            with self.subTest(claim=claim):
                m = deepcopy(self.mapping)
                m['entries'] = [r for r in m['entries'] if r['id'] != claim]
                with self.assertRaisesRegex(ValueError, 'unnumbered inventory'):
                    self.validate_mapping(m)

    def test_unknown_status_declaration_or_empty_scope_rejected(self):
        for field, value in [('status', 'fully_proven'), ('declarations', ['AsymmetricTensor.no_such_theorem']),
                             ('topic', ''), ('note', '')]:
            with self.subTest(field=field):
                m = deepcopy(self.mapping)
                m['entries'][0][field] = value
                with self.assertRaises(ValueError):
                    self.validate_mapping(m)

    def test_proved_identity_requires_evidence(self):
        m = deepcopy(self.mapping)
        r = next(r for r in m['entries'] if r['status'] == 'proved_identity')
        r['declarations'] = []
        with self.assertRaisesRegex(ValueError, 'requires declaration evidence'):
            self.validate_mapping(m)

    def test_exact_target_cannot_be_promoted_to_proof(self):
        m = deepcopy(self.mapping)
        for row in m['entries']:
            if row['status'] == 'specification_target':
                row['status'] = 'proved_identity'
        with self.assertRaisesRegex(ValueError, 'Unlabelled exact-target'):
            self.validate_mapping(m)

    def test_wrong_pdf_page_or_section_rejected(self):
        for field, value in [('page', 56), ('section', '16.1')]:
            with self.subTest(field=field):
                m = deepcopy(self.mapping)
                m['entries'][0][field] = value
                with self.assertRaisesRegex(ValueError, 'Wrong'):
                    ledger.render(m, self.inventory, deepcopy(self.sections), self.audit, self.source)

    def test_missing_source_declaration_rejected(self):
        a = deepcopy(self.audit)
        i = next(i for i, d in enumerate(a['declarations']) if not d['generated'])
        del a['declarations'][i]
        a['declaration_count'] -= 1
        with self.assertRaisesRegex(ValueError, 'Missing source declaration'):
            self.validate_audit(a)

    def test_unreviewed_axiom_and_sorry_rejected(self):
        for axiom in ['AsymmetricTensor.universal_conservation', 'sorryAx']:
            with self.subTest(axiom=axiom):
                a = deepcopy(self.audit)
                a['declarations'][0]['axioms'].append(axiom)
                a['declarations'][0]['custom_axioms'].append(axiom)
                with self.assertRaisesRegex(ValueError, 'Unreviewed transitive axioms'):
                    self.validate_audit(a)

    def test_empty_or_elided_type_rejected(self):
        for signature in ['', '∀ (x : ℝ), ⋯']:
            with self.subTest(signature=signature):
                a = deepcopy(self.audit)
                a['declarations'][0]['type'] = signature
                with self.assertRaisesRegex(ValueError, 'Missing or abbreviated elaborated type'):
                    self.validate_audit(a)

    def test_source_links_and_generated_owners_are_checked(self):
        for generated in [False, True]:
            with self.subTest(generated=generated):
                a = deepcopy(self.audit)
                d = next(d for d in a['declarations'] if d['generated'] == generated)
                d['source_line'] += 1
                with self.assertRaisesRegex(ValueError, 'Stale'):
                    self.validate_audit(a)

    def test_complete_audit_log_round_trip_and_truncation(self):
        records = []
        for d in self.audit['declarations']:
            records.append({k: v for k, v in d.items()
                            if k not in {'source_line', 'source_kind', 'source_parent', 'generated'}})
        log = '\n'.join('EQUATION_AXIOM ' + json.dumps(r) for r in records)
        full = log + '\nEQUATION_AXIOM_COUNT ' + str(len(records))
        result = ledger.audit_from_log(full, self.source, self.mapping['snapshot'])
        self.assertEqual(result, self.audit)
        with self.assertRaisesRegex(ValueError, 'Incomplete Lean axiom output'):
            ledger.audit_from_log(log, self.source, self.mapping['snapshot'])
        with self.assertRaisesRegex(ValueError, 'Incomplete Lean axiom output'):
            ledger.audit_from_log(full.replace('EQUATION_AXIOM_COUNT 240', 'EQUATION_AXIOM_COUNT 241'),
                                  self.source, self.mapping['snapshot'])


if __name__ == '__main__':
    unittest.main()
