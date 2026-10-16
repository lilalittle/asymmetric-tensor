#!/usr/bin/env python3
"""Mutation checks for the deliberately narrow source-migration comparator."""
import sys
import unittest
sys.dont_write_bytecode = True
from check_module_source import declarations, docstrings, strip_comments


class SourceMigration(unittest.TestCase):
    def test_comments_and_whitespace(self):
        a = 'theorem t : True := by\n  trivial\n'
        b = '/- outer /- inner -/ -/\ntheorem t : True := by\n  -- proof\n  trivial\n'
        self.assertEqual(declarations([a]), declarations([b]))

    def test_body_change(self):
        self.assertNotEqual(declarations(['def x : Nat := 1\n']),
                            declarations(['def x : Nat := 2\n']))

    def test_attributes_and_aliases(self):
        a = '@[simp] theorem t : True := by\n  trivial\nalias old_t := t\n'
        self.assertEqual(set(declarations([a])), {'t', 'old_t'})
        self.assertNotEqual(declarations([a]), declarations([a.replace('@[simp] ', '')]))

    def test_duplicate_rejected(self):
        with self.assertRaises(ValueError):
            declarations(['axiom x : Nat\n', 'axiom x : Nat\n'])

    def test_docstring_preservation(self):
        self.assertEqual(docstrings(['/-- A useful\n contract. -/']),
                         docstrings(['/-- A useful contract. -/']))
        self.assertNotEqual(docstrings(['/-- A useful contract. -/']), docstrings(['']))

    def test_comment_markers_in_strings(self):
        self.assertEqual(strip_comments('def x := "-- /- text -/"\n'),
                         'def x := "-- /- text -/"\n')
        self.assertNotEqual(declarations(['def x := "a b"\n']),
                            declarations(['def x := "ab"\n']))


if __name__ == '__main__':
    unittest.main()
