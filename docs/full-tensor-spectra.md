# Aligned full-tensor spectra

This is the mathematical repair and a **proposed manuscript correction** for
[issue #20](https://github.com/lilalittle/asymmetric-tensor/issues/20).
It does not amend the author's PDF or supply author approval. The reference is
v9, September 25, 2026, sections 9.1–9.7, equations 130–142, and the
cross-reference to section 8.3. The archived equation ledger remains unchanged.

## Matrix and proved polynomial

Set `a = alpha_s`, `d = 1/a²`, `x = alpha*vx/c`, `y = alpha*vy/c`, and
`r = alpha*t_p_val*Omega_z`. The alignment is `vz = Omega_x = Omega_y = 0`;
both transverse slips are retained. `U_hat_aligned_eq` identifies the actual
`U_hat` specialization with

```text
[-a², -x, -y, 0]
[  x,  d, -r, 0]
[  y,  r,  d, 0]
[  0,  0,  0, d]
```

The production module `Applications.Spectra` proves, from the matrix definitions,

```text
charpoly(U)(X) = (X-d) [(X+a²)((X-d)²+r²) + (x²+y²)(X-d)]
det(U) = -1/a⁴ - r² + (x²+y²)/a⁴                  (a ≠ 0)
```

`aligned_matrix_shift_det` also computes `det(U - z I)` directly. Dimension four
makes its determinant agree with `det(z I - U)`. The polynomial with explicit
`1/a²` entries is valid even for Lean's totalized zero input; the simplified
nonzero-admittance determinant is not. No singular limit, finite-volume law,
gauge symmetry, or dynamical evolution follows from this calculation.

The real characteristic polynomial records the full coupled spectrum. Its
longitudinal root `d` is independent of slip. The cubic factor evaluated at `d`
is `(a²+d)r²`. For `a ≠ 0`, `a²+d > 0`, so the cubic shares that root exactly
when `r = 0`. This is the justified degeneracy statement. Inferring `Omega_z = 0`
also requires `alpha ≠ 0` and `t_p_val ≠ 0`; it is not a general stability theorem.

## Block eigenvalues versus full eigenvalues

The isolated complexified transverse block is `[[d,-r],[r,d]]`. Explicit nonzero
vectors `(1,-i)` and `(1,i)` satisfy the eigenvector equations with eigenvalues
`d+ri` and `d-ri`. They are not merely matrix-entry identities.

`transverse_plane_invariant_iff` proves that its embedding `(0,u,v,0)` intertwines
the block and full matrix actions exactly when `x=y=0`. Under this condition the
circular vectors lift to full eigenvectors. The longitudinal vector `(0,0,0,1)`
works even with slip; the temporal vector `(1,0,0,0)` works when slip is zero.
`schwinger_limit_eigenvalues` now states actual complex eigenvector relations for
`complexify (U_hat ...)`, restricted to aligned zero slip, `alpha_s=1`, and
`alpha*t_p_val*Omega_z=1`. Its type intentionally replaces the old diagonal-entry
conjunction. The legacy `transverse_eigenvalues_are_real_iff_no_spin` likewise now
states reality of the two explicit block roots, not a claim about all full roots.

At `a=r=1`, insertion of `1+i` in the full determinant gives `-(x²+y²)`. In
particular, the production counterexample is

```text
[-1, -1/2,  0, 0]
[1/2,   1, -1, 0]
[  0,   1,  1, 0]
[  0,   0,  0, 1]
```

Its shifted determinant is exactly `-1/4`, so `1+i` is not an eigenvalue.
`nonzero_slip_example_from_U_hat` identifies it with the actual tensor at
`vx=c/2`, `alpha_s=alpha=t_p_val=Omega_z=1` and all other components zero.

## Proposed manuscript changes and downstream consequences

- Equations 131–133: retain the aligned matrix and coupled polynomial, with the
  nonzero-admittance domain explicit when simplifying inverse powers. Cancellation
  of mixed terms shows dependence on `x²+y²`; it alone does not establish an
  `O(2)` gauge theory.
- Section 9.3 / equation 135: retain the shared-root criterion `r=0` for nonzero
  admittance. State the extra nonzero factors before concluding zero vorticity.
  Withdraw the inference that all coupled transverse eigenvalues are nonreal
  whenever rotation is nonzero.
- Section 9.4 / equation 137: the actual determinant formula is proved here.
  `det(U)=-1` remains an independent condition, not a consequence of trace-free
  additive shear. Choosing a physical volume measure and proving a volume law
  remain in [issue #21](https://github.com/lilalittle/asymmetric-tensor/issues/21).
- Section 9.5 / equation 138: replace the unrestricted `1±i` full-spectrum claim
  by the zero-slip restriction, or explicitly describe only the isolated block.
  The numerical identity `|(1+lambda)/(1-lambda)|=sqrt(5)` at these two numbers
  is only complex arithmetic. In equation 134 the two terms cancel at these
  roots, giving `x²+y²=0`; the coefficient ratio is not thereby an electric/
  magnetic amplitude ratio or a physical impedance. Withdraw the claimed
  impedance shift, `U(1)` breaking, and birefringence derivation pending a new
  justified model. Restricting the eigenvalues alone does not rescue them.
- Section 9.6 / equations 139–140: retain the block eigenvectors and distinguish
  the invariant-plane condition. Their normalized coefficient `1/sqrt(2)` is
  a choice of vector length, not a derived Tresca yield criterion, physical
  half-load partition, or mass bound. Remove the claimed derivation of the
  section 8.3 yield rule from these eigenvectors. Independent scalar mass
  identities elsewhere are unchanged; their physical premises remain separate.
- Appendix 16.3: remove the claim that these roots force a glass transition or
  establish a Yang–Mills mass gap. The vector-space decomposition into symmetric
  and imaginary antisymmetric matrices does not supply the omitted dynamics,
  threshold, or spectral-gap proof; the existing `su3_mass_gap_transition` is
  explicitly a target-returning specification.
- Section 9.7: the aligned determinant-collapse algebra is justified only for
  `a ≠ 0`; substitution of `a=0`, phase transitions and radiation conclusions
  require separate arguments. See the independently scoped limit repair.

These are proposed corrections for author review, not a new physical model.
No empirical Schwinger threshold, polarization dynamics, mass yield, or
unitary group action has been formalized here.

## Verification

`tests/FullTensorSpectra.lean` checks actual determinant/characteristic-polynomial
specializations, complex eigenvector equations, decoupling, the nonzero-slip
counterexample, and exact transitive custom-axiom sets. The aggregate
`scripts/verify.sh` imports the production module through `Electromagnetism`,
so the whole-module completeness and six-axiom inventory checks cover it.

## v3 review-branch integration

This repair is based on modular main `9cc32ea7e141a7a1a039494d47e655fcc7f545e8`.
It has not been built on top of the separate
[v3 review vehicle, PR #61](https://github.com/lilalittle/asymmetric-tensor/pull/61)
at `2fa2e6ad`. That proposal replaces the module tree with a monolith and changes
some surrounding API conventions, including global time-scale use. Retaining
the same aligned matrix entries does not establish source compatibility.

The generic `alignedMatrix` determinant, characteristic-polynomial, invariant-plane
and complex eigenvector proofs are reusable mathematical components. Porting
requires an explicit choice of integration layout, imports, and `U_hat` bridge
arguments, followed by the focused and complete regression/audit gates on the
chosen revision. The v3 branch's existing same-named scalar theorem is not this
spectral repair. Neither this note nor the local verification approves merging
that review branch or bypasses the author's required code review.

For that specific v3 interface, the normalized counterexample would use
`alpha=1` and `Omega_z=1/t_p`, proving `t_p ≠ 0` from `l_p_pos` and `c_pos`,
or retain the product hypothesis `alpha*t_p*Omega_z=1`. It cannot independently
set a time-scale argument to one. Since v3 defines `t_p=l_p/c`, its actual
`U_hat` bridge dependencies include `l_p` as well as `c`; the concrete normalized
example additionally needs the corresponding positivity axioms. Any v3 audit
must review those exact dependencies afresh, not reuse this branch's `c`-only
bridge allowlists. Global time scale and real-exponent conventions must also be
handled explicitly at the port boundary.

Local validation on 2026-10-16, on the modular-main repair candidate, passed
`bash scripts/verify.sh`: all thirteen Lean regressions, 411-declaration
completeness and transitive-axiom checks, the unchanged six declared axioms,
22 new exact spectral checks, inherited audits, roadmap checks, and mutation
regressions. `git diff --check` and the production style gate also passed.
The pinned setup, PDF and archived equation evidence were unchanged. This used
the restored pinned Mathlib cache; it does not certify a v3 port, a combined
repair stack, author approval, or hosted CI on a future published revision.
