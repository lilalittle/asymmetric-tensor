#!/usr/bin/env python3
"""Historical pinned v5.7 inventory; not a replacement for current Lean audits.

The bounded declaration scanner omits structures and anonymous instances, so
their reviewed inventory is checked separately here. Elaborated generated API,
declaration types, and proof dependencies are checked by the Lean audits and
reference API comparison. These historical assertions read immutable v5.7
stable module bytes, never the evolving production checkout.
"""
from pathlib import Path
import re
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_module_source import declarations, strip_comments
from check_module_context import inventory
from source_boundary import is_author_draft

STABLE_COMMIT = "8ad507caa6625c810507a01c031040833af9c318"
STABLE_TREE = "3e0a27fb8d5e095e6f0b9b65b4fa19b4815fcba5"


class V57Inventory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        tree = subprocess.check_output(
            ['git', 'rev-parse', f'{STABLE_COMMIT}^{{tree}}'], cwd=ROOT, text=True).strip()
        if tree != STABLE_TREE:
            raise RuntimeError('Historical v5.7 stable tree differs from its pinned identity')
        paths = subprocess.check_output(
            ['git', 'ls-tree', '-r', '--name-only', STABLE_COMMIT],
            cwd=ROOT, text=True).splitlines()
        selected = [p for p in paths if p == 'AsymmetricTensor.lean' or (
            p.startswith('AsymmetricTensor/') and p.endswith('.lean')
            and not is_author_draft(p))]
        cls.historical_sources = {
            p: subprocess.check_output(
                ['git', 'show', f'{STABLE_COMMIT}:{p}'], cwd=ROOT).decode()
            for p in selected}

    def setUp(self):
        self.sources = self.historical_sources
        self.text = strip_comments('\n'.join(self.sources.values()))

    def test_declaration_inventory(self):
        self.assertEqual(len(self.sources), 10)
        self.assertEqual(len(declarations(self.sources.values())), 466)
        self.assertEqual(len(re.findall(r'^theorem\s+', self.text, re.M)), 241)
        self.assertEqual(len(re.findall(r'^lemma\s+', self.text, re.M)), 50)
        self.assertEqual(len(re.findall(r'^(?:noncomputable )?def\s+', self.text, re.M)), 167)
        self.assertEqual(len(re.findall(r'^abbrev\s+', self.text, re.M)), 7)
        self.assertEqual(re.findall(r'^(?:noncomputable )?opaque\s+(\w+)', self.text, re.M),
                         ['dyn_state'])
        self.assertEqual(re.findall(r'^axiom\s+(\w+)', self.text, re.M), [])
        self.assertCountEqual(re.findall(r'^structure\s+(\w+)', self.text, re.M),
                              ['UnitDim', 'DynamicClebschFields'])
        self.assertEqual(re.findall(r'^instance\s*:\s*([^\n]+?)\s+where', self.text, re.M),
                         ['Mul UnitDim', 'Div UnitDim', 'HPow UnitDim ℤ UnitDim'])
        self.assertNotRegex(self.text, r'\b(?:sorry|admit)\b')

    def test_conservative_foundations(self):
        model = self.sources['AsymmetricTensor/Model.lean']
        for name in ['c', 'l_p', 'hbar']:
            self.assertRegex(model, rf'(?m)^noncomputable def {name}\s+: ℝ :=')
            self.assertRegex(model, rf'(?m)^theorem {name}_pos\s+:')
        self.assertIn('attribute [irreducible] c l_p hbar', model)

    def test_dependency_moves(self):
        matrix = self.sources['AsymmetricTensor/MatrixAlgebra.lean']
        field = self.sources['AsymmetricTensor/FieldCalculus.lean']
        for name in ['quadratic_gravitational_lagrangian_trace', 'cauchy_strain',
                     'partial_deriv2', 'saint_venant_inc', 'linearized_riemann']:
            self.assertNotIn(name, declarations([matrix]))
            self.assertIn(name, declarations([field]))
        self.assertIn('variable (M : ℝ)', matrix)

    def test_import_graph_acyclic(self):
        graph = {}
        for path, source in self.sources.items():
            commands, errors = inventory(source)
            self.assertEqual(errors, [])
            graph[path[:-5].replace('/', '.')] = [c.split()[-1] for c in commands['imports']]
        visited, active = set(), set()
        def visit(module):
            self.assertNotIn(module, active, f'import cycle at {module}')
            if module in visited:
                return
            self.assertIn(module, graph)
            active.add(module)
            for dependency in graph[module]:
                visit(dependency)
            active.remove(module)
            visited.add(module)
        visit('AsymmetricTensor')
        self.assertEqual(visited, set(graph))


if __name__ == '__main__':
    unittest.main()
