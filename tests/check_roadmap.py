#!/usr/bin/env python3
"""Validate the roadmap inventory and independently check its finite contract.

Uses only Python's standard library. Exact symbolic/rational checks are a
specification sanity check, not a Lean proof of the proposed targets.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / "scripts"))
from check_module_source import declarations, source_files
from roadmap_inventory import mask_comments, target_binder_declarations

# Scan production only, never generated files or test declarations. Lexical
# extraction distinguishes actual binders from proof-local names and comments.
sources = [path.read_text() for path in source_files(ROOT)]
source = "\n".join(mask_comments(text) for text in sources)
roadmap = (ROOT / "docs/formalization-roadmap.md").read_text()
spec = mask_comments((ROOT / "tests/RoadmapTargets.lean").read_text())

known = set(declarations(sources))
inventory = set()
for names in re.findall(r"<!-- declarations: (.*?) -->", roadmap):
    inventory.update(names.split())
assert inventory <= known, f"Unknown declarations: {sorted(inventory - known)}"
placeholders = target_binder_declarations(sources)
# The author's v4.5 source has no binder named h_target. This syntactic fact
# does not establish the physical interpretations: h_wkb, h_on_shell and other
# substantive model premises remain, checked separately by the scope regressions.
assert placeholders == set(), f"Unexpected h_target declarations: {placeholders}"
assert source.count("section FutureWork") == 1
assert source.count("end FutureWork") == 1
future = source.split("section FutureWork", 1)[1].split("end FutureWork", 1)[0]
future_names = set(re.findall(r"^theorem\s+(\w+)", future, re.M))
future_defs = set(re.findall(r"^(?:noncomputable )?def\s+(\w+)", future, re.M))
assert len(future_names) == 39, f"Review changed Section 16 theorem inventory: {future_names}"
assert len(future_defs) == 28, f"Review changed Section 16 definition inventory: {future_defs}"
assert future_names <= inventory, f"Missing Section 16 results: {future_names - inventory}"
assert len(re.findall(r"^def \w+Target : Prop", spec, re.M)) == 9
assert not re.search(r"^\s*(?:axiom|theorem|lemma)\b|\b(?:sorry|admit)\b", spec, re.M)
print(f"PASS inventory: {len(placeholders)} h_target binders, "
      f"{len(future_names)} Section 16 theorems, {len(future_defs)} Section 16 definitions, "
      f"{len(inventory)} valid declaration references; conditional physical scope remains")

# Check library candidates against the pinned, locally materialized dependency.
mathlib = ROOT / ".lake/packages/mathlib"
assert mathlib.is_dir(), "Materialize the pinned Mathlib checkout before this check"
paths = set(re.findall(r"`(Mathlib/[^`]+\.lean)`", roadmap))
assert paths
for path in sorted(paths):
    assert (mathlib / path).is_file(), f"Missing library candidate: {path}"
print(f"PASS {len(paths)} Mathlib candidate paths exist")

# Independent formal Laurent-polynomial expansion by the Leibniz formula.
# Variables are a,b,v,w,t,k with k=1/c. Negative a powers are valid only for a!=0.
# This does not assume that the repository's definition equals our matrix;
# the Lean target retains the actual U_hat specialization for that bridge.
ZERO = (0,) * 6

def mono(coef=1, **exponents):
    powers = tuple(exponents.get(x, 0) for x in "abvwtk")
    return {powers: Q(coef)} if coef else {}


def add(p, q):
    out = Counter(p)
    for powers, coef in q.items():
        out[powers] += coef
    return {powers: coef for powers, coef in out.items() if coef}


def mul(p, q):
    out = {}
    for pp, pc in p.items():
        for qp, qc in q.items():
            powers = tuple(x + y for x, y in zip(pp, qp))
            out[powers] = out.get(powers, Q(0)) + pc * qc
    return {powers: coef for powers, coef in out.items() if coef}


def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))


z = {}
m = [[mono(-1, a=2), mono(-1, b=1, v=1, k=1), z, z],
     [mono(b=1, v=1, k=1), mono(a=-2), mono(-1, b=1, t=1, w=1), z],
     [z, mono(b=1, t=1, w=1), mono(a=-2), z],
     [z, z, z, mono(a=-2)]]
actual = {}
for p in permutations(range(4)):
    term = mono(sign(p))
    for i in range(4):
        term = mul(term, m[i][p[i]])
    actual = add(actual, term)
expected = add(add(mono(-1, a=-4), mono(-1, b=2, t=2, w=2)),
               mono(a=-4, b=2, v=2, k=2))
assert actual == expected, (actual, expected)
print("PASS symbolic 4x4 determinant: complete 24-permutation Laurent expansion")


def det(m):
    result = Q(0)
    for p in permutations(range(len(m))):
        term = Q(sign(p))
        for i in range(len(m)):
            term *= m[i][p[i]]
        result += term
    return result


def matrix(a, b, v, w, t, c):
    assert a != 0 and c != 0
    e, q, d = b * v / c, b * t * w, 1 / a**2
    return [[-a*a, -e, Q(0), Q(0)], [e, d, -q, Q(0)],
            [Q(0), q, d, Q(0)], [Q(0), Q(0), Q(0), d]]


cases = [
    ("vacuum", (1, 0, 0, 0, 1, 2), Q(-1)),
    ("pure electric", (1, 1, 1, 0, 1, 2), Q(-3, 4)),
    ("pure rotational counterexample", (1, 1, 0, 1, 1, 2), Q(-2)),
    ("mixed", (1, 1, 1, 1, 1, 2), Q(-7, 4)),
    ("nonunit zero shear", (2, 0, 0, 0, 1, 2), Q(-1, 16)),
    ("nonunit mixed", (2, 1, 1, 1, 1, 2), Q(-67, 64)),
    ("negative nonzero admittance", (-2, 1, 1, 1, 1, 2), Q(-67, 64)),
]
for name, params, desired in cases:
    a, b, v, w, t, c = map(Q, params)
    m = matrix(a, b, v, w, t, c)
    result = det(m)
    assert result == desired, (name, result, desired)
    assert result == -1/a**4 - (b*t*w)**2 + (b*v/c)**2/a**4
    anti = [[(m[i][j] - m[j][i])/2 for j in range(4)] for i in range(4)]
    sym = [[(m[i][j] + m[j][i])/2 for j in range(4)] for i in range(4)]
    assert sum(anti[i][i] for i in range(4)) == 0
    assert all(anti[i][j] == -anti[j][i] for i in range(4) for j in range(4))
    assert det(sym) == -1/a**4
    spatial = [row[1:] for row in sym[1:]]
    assert spatial == [[1/a**2 if i == j else Q(0) for j in range(3)] for i in range(3)]
    assert det(spatial) == 1/a**6
    if a > 0:
        # Unique nonnegative square-root witnesses, without floating arithmetic.
        assert 1/a**3 > 0 and (1/a**3)**2 == det(spatial)
        assert 1/a**2 > 0 and (1/a**2)**2 == abs(det(sym))
    if a == 1:
        assert (result == -1) == ((b*v/c)**2 == (b*t*w)**2)
    print(f"PASS exact rational example: {name}; det={result}")
print("ROADMAP_CHECK_OK (specification checks; no production determinant proof claimed)")
