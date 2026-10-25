#!/usr/bin/env python3
"""Historical lexical v5.8 regressions against the pinned prior stable; not a replacement for Lean audits.

The bounded declaration scanner omits structures and anonymous instances, so
their reviewed inventory is checked separately here. Elaborated generated API,
declaration types, and proof dependencies are checked by the Lean audits and
reference API comparison.
"""
from collections import Counter
from pathlib import Path
import re
import sys
import subprocess
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_module_source import declarations, docstrings, source_files, strip_comments
from check_module_context import inventory
from check_v58_reference import SOURCE_COMMIT, SOURCE_PATH, stable_sources, validate_source
from check_v59_reference import stable_sources as v58_sources


def structural_commands(sources):
    """Bounded current-syntax tokens omitted by the named-declaration scanner.

    This supplements, never replaces, the complete compiled API comparison.
    """
    commands = Counter()
    for source in sources:
        text = strip_comments(source)
        for match in re.finditer(r'^(?:structure|instance)\b[^\n]*', text, re.M):
            end = re.search(r'\n(?=[^\s])', text[match.end():])
            stop = match.end() + end.start() if end else len(text)
            tokens = re.findall(r'"(?:\\.|[^"\\])*"|\w+|[^\w\s]', text[match.start():stop])
            commands[tuple(tokens)] += 1
    return commands


class V58Inventory(unittest.TestCase):
    def setUp(self):
        # Preserve all v5.8 assertions against its immutable stable modules.
        # A v5.9 candidate must not be zero-difference compared with v5.8.
        self.sources = {name: contents.decode()
                        for name, contents in v58_sources(ROOT).items()}
        self.text = strip_comments('\n'.join(self.sources.values()))

    def test_declaration_inventory(self):
        self.assertEqual(len(self.sources), 10)
        self.assertEqual(sum(docstrings(self.sources.values()).values()), 75)
        self.assertEqual(len(declarations(self.sources.values())), 473)
        self.assertEqual(len(re.findall(r'^theorem\s+', self.text, re.M)), 246)
        self.assertEqual(len(re.findall(r'^lemma\s+', self.text, re.M)), 51)
        self.assertEqual(len(re.findall(r'^(?:noncomputable )?def\s+', self.text, re.M)), 168)
        self.assertEqual(len(re.findall(r'^abbrev\s+', self.text, re.M)), 7)
        self.assertEqual(re.findall(r'^(?:noncomputable )?opaque\s+(\w+)', self.text, re.M),
                         ['dyn_state'])
        self.assertEqual(re.findall(r'^axiom\s+(\w+)', self.text, re.M), [])
        self.assertCountEqual(re.findall(r'^structure\s+(\w+)', self.text, re.M),
                              ['UnitDim', 'DynamicClebschFields'])
        self.assertEqual(re.findall(r'^instance\s*:\s*([^\n]+?)\s+where', self.text, re.M),
                         ['Mul UnitDim', 'Div UnitDim', 'HPow UnitDim ℤ UnitDim'])
        self.assertNotRegex(self.text, r'\b(?:sorry|admit)\b')

    def test_inventory_is_derived_from_immutable_v58_source(self):
        raw = subprocess.check_output(
            ['git', 'show', f'{SOURCE_COMMIT}:{SOURCE_PATH}'], cwd=ROOT)
        validate_source(raw)
        source = raw.decode()
        text = strip_comments(source)
        self.assertEqual(len(declarations([source])), 473)
        self.assertEqual(sum(docstrings([source]).values()), 75)
        self.assertEqual(len(re.findall(r'^theorem\s+', text, re.M)), 246)
        self.assertEqual(len(re.findall(r'^lemma\s+', text, re.M)), 51)
        self.assertEqual(len(re.findall(r'^(?:noncomputable )?def\s+', text, re.M)), 168)
        self.assertEqual(len(re.findall(r'^abbrev\s+', text, re.M)), 7)
        self.assertEqual(re.findall(r'^structure\s+(\w+)', text, re.M),
                         ['UnitDim', 'DynamicClebschFields'])
        self.assertEqual(re.findall(r'^instance\s*:\s*([^\n]+?)\s+where', text, re.M),
                         ['Mul UnitDim', 'Div UnitDim', 'HPow UnitDim ℤ UnitDim'])
        # Source and split production must independently agree, not just have
        # equal declaration totals. Structures/generated APIs remain a separate
        # full compiled-reference contract, not covered by this lexical scanner.
        before, after = declarations([source]), declarations(self.sources.values())
        self.assertEqual([name for name in sorted(before.keys() | after.keys())
                          if before.get(name) != after.get(name)], [])
        self.assertEqual(docstrings([source]), docstrings(self.sources.values()))
        structural = structural_commands([source])
        self.assertEqual(sum(structural.values()), 5)
        self.assertEqual(structural, structural_commands(self.sources.values()))
        previous = [contents.decode() for contents in stable_sources(ROOT).values()]
        self.assertEqual(structural, structural_commands(previous))

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
