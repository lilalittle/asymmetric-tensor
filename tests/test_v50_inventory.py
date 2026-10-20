#!/usr/bin/env python3
"""Lexical v5.0 integration regressions; not a replacement for Lean audits."""
from pathlib import Path
import re
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_module_source import declarations, source_files, strip_comments
from check_module_context import inventory


class V50Inventory(unittest.TestCase):
    def setUp(self):
        self.sources = {p.relative_to(ROOT).as_posix(): p.read_text()
                        for p in source_files(ROOT)}
        self.text = strip_comments('\n'.join(self.sources.values()))

    def test_declaration_inventory(self):
        self.assertEqual(len(self.sources), 10)
        self.assertEqual(len(declarations(self.sources.values())), 431)
        self.assertEqual(len(re.findall(r'^(?:theorem|lemma)\s+', self.text, re.M)), 268)
        self.assertEqual(len(re.findall(r'^(?:noncomputable )?def\s+', self.text, re.M)), 147)
        self.assertEqual(re.findall(r'^axiom\s+(\w+)', self.text, re.M),
                         ['covariant_conservation'])
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
