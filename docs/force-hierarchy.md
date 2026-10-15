# Electromagnetic baseline and the force hierarchy

The reference is manuscript v9 (September 25, 2026),
[Eq. (223), p. 47, and Eq. (224), p. 48](../papers/asymmetric-metric-tensor.pdf#page=48).
The published PDF is unchanged.

The manuscript uses the same fundamental-force function at two different radii:

- `F_fund(r) = ℏ c / r²`
- `Lcrit = α ℏ / (m_e c)`
- `a₀ = ℏ / (α m_e c)`

The exact manuscript correspondence is:

| Lean theorem | Statement |
| --- | --- |
| `interaction_hierarchy_strong` | `F_fund(Lcrit) = m_e² c³ / (α² ℏ)` (223) |
| `interaction_hierarchy_em` | `F_fund(a₀) = α² m_e² c³ / ℏ` (224) |
| `interaction_hierarchy_em_strong_ratio` | `F_fund(a₀) / F_fund(Lcrit) = α⁴` (text immediately after 224) |

The hypotheses require `m_e ≠ 0` and `α ≠ 0`; the existing axioms provide
`c > 0` and `ℏ > 0`. These conditions keep both substituted radii and the
strong-force denominator nonzero. Positive mass and coupling are a special case.
The proof is an algebraic consequence of the stated force and radius formulas;
it does not independently establish the physical model. In particular, Lean's
convention `x / 0 = 0` must not be read as defining a physical zero-radius limit.

## Separately retained algebra

Before this correction, `interaction_hierarchy_em` asserted
`α * F_fund(a₀) = α³ m_e² c³ / ℏ`. The identity is valid but its left-hand side
is not the baseline in Eq. (224).

That identity is now named `interaction_hierarchy_em_scaled_algebra` and follows
by multiplying the baseline theorem by `α`. Its companion
`interaction_hierarchy_em_scaled_strong_ratio` gives `α⁵`. These are optional
algebraic rescalings only. No separately coupled physical force is defined or
claimed, and no new physical coupling convention is added to the manuscript.
Callers that relied on the old theorem statement should use the explicitly
scaled name.

## Regression checks

After `lake build`, run:

```sh
lake env lean tests/ForceHierarchy.lean
```

The checks cover Eq. (224), both symbolic ratios, a nonunit coupling where
`α⁴ = 1/16` and `α⁵ = 1/32` are distinct, and the degenerate zero-mass case that
explains why the ratio theorem retains its nonzero-mass domain.
