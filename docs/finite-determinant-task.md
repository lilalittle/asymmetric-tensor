# Derive the finite aligned determinant and distinguish volume densities

Current progress: the [spectral repair](full-tensor-spectra.md) supplies the
aligned determinant formula from the actual `U_hat` via `U_hat_aligned_det`
(set its second transverse slip to zero for the specialization below).
The volume-density results and physical interpretation below remain separate
work; the retained target propositions are specifications, not proof records.

Implementation contract for the mathematical part of the existing finite-volume
finding. This is a proposed implementation scope, not a claim that the following
results are already proved in the production library.

## Purpose

Replace a premise about an expanded scalar determinant with a theorem about the
actual `U_hat` matrix. Show precisely why trace-free additive shear does not imply
finite volume preservation. Keep any physical isochoric condition explicit.

## Definitions and precise targets

Use `a = α_s`, `b = α`, `v = v_x`, `w = Ω_z`, `t = t_p_val` and define

```lean
noncomputable def alignedU_hat (a b v w t : ℝ) : T2 :=
  U_hat a b v 0 0 0 0 w t
```

The name means a coordinate specialization with electric slip along the x-axis
and vorticity along the z-axis; those two vectors are perpendicular, not parallel.
It is not the determinant formula for arbitrary six-component slip/vorticity.
The matrix is

```text
[ -a²   -b(v/c)       0       0 ]
[ b(v/c)  1/a²     -b(tw)     0 ]
[   0      b(tw)     1/a²     0 ]
[   0        0         0     1/a² ]
```

Prove the following from this matrix, without an expanded determinant premise:

1. For all real `a b v w t`, with `a ≠ 0`,

   `det(alignedU_hat a b v w t) = -1/a⁴ - (b*t*w)² + (b*(v/c))²/a⁴`.

2. At `a = 1`,

   `det(alignedU_hat 1 b v w t) = -1 ↔ (b*(v/c))² = (b*t*w)²`.

   Thus equality of the two squared terms follows only when the determinant
   constraint is separately supplied. It is not a consequence of antisymmetry.

3. For all real matrices `U : T2`,

   `(antiPart U)ᵀ = -antiPart U` and `trace(antiPart U) = 0`.

   Specialize to `W = alignedU_hat 1 1 0 1 1` and prove

   `trace(antiPart W) = 0`, `(antiPart W)ᵀ = -antiPart W`, and `det W = -2`.

   In particular, state `det W ≠ -1`. The example uses zero electric slip and
   unit rotational shear; it does not depend on the numerical value of `c`.

4. With `a ≠ 0`, prove the actual symmetric spacetime determinant

   `det(symPart(alignedU_hat a b v w t)) = -1/a⁴`.

   Define the spatial symmetric block as

   `spatialS a = Matrix.diagonal (fun _ : Fin 3 => 1/a²)`.

   Prove that it equals the spatial block of `symPart(alignedU_hat a b v w t)`
   under the index embedding `i ↦ i.succ`. Prove

   `det(spatialS a) = 1/a⁶`.

   For `a > 0`, prove

   `sqrt(det(spatialS a)) = 1/a³` and
   `sqrt(abs(det(symPart(alignedU_hat a b v w t)))) = 1/a²`.

   Name these as algebraic densities of the indicated symmetric matrices. Do not
   call `sqrt(abs(det U))` the physical metric density without selecting that model.

The exact well-typed candidate propositions are in
[`tests/RoadmapTargets.lean`](../tests/RoadmapTargets.lean). They are specifications,
not axioms or placeholder theorems. Their elaboration does not prove them.
A separate [proved counterexample regression](../tests/RoadmapCounterexample.lean)
checks item 3 for the explicit rotational example. It is evidence that the bounded
task is tractable, not an implementation of the general determinant/density targets.

## Implementation boundaries

- Preserve `U_hat` and the existing public algebraic lemmas; introduce a theorem
  linking `Matrix.det` to them rather than silently changing their hypotheses.
- Use `a ≠ 0` in the general finite theorem. Do not interpret the totalized `a = 0`
  matrix as a singular limit or a post-yield phase.
- Keep the `a = 1` determinant condition explicit. Do not add a physical axiom or
  assert the condition for arbitrary parameters.
- A characteristic polynomial, full spectra, matrix exponential deformation,
  connection, and physical constitutive model are outside this finite task.
- The manuscript correction must distinguish infinitesimal trace, finite
  determinant, symmetric spacetime density and spatial density. Choosing a
  physical volume law or publishing a replacement manuscript requires the author.
  The mathematical results do not by themselves complete that paper work.

## Acceptance and validation

- [ ] All targets above are theorems about the actual matrices, with no `h_det`
  expansion or assumed target equality.
- [ ] The general determinant theorem is tested on zero shear, pure electric,
  pure rotational, mixed, and positive nonunit-admittance examples.
- [ ] At the vacuum `a = 1, b = 0`, determinant is `-1`; the pure rotation example
  above is `-2`. A nonunit zero-shear example has determinant `-1/a⁴`, so the
  classical `-1` condition is not silently extended to all admittances.
- [ ] The antisymmetric part is proved skew and trace-free from its definition.
- [ ] The spatial-block bridge and the `a⁻⁶` determinant versus `a⁻³` density are
  proved, with positivity used where a square-root sign requires it.
- [ ] Full `lake build` and a dedicated regression test run on the pinned toolchain.
- [ ] No new axiom, `sorry`, `admit`, target-returning proof, or use of the universal
  conservation axiom. Print and review the new theorems' transitive axiom lists.
  Dependence on the existing scalar `c` in the general definition is expected;
  conservation is not. The zero-electric counterexample should not require `c_pos`.
- [ ] Update the equation/scope documentation to explain which former scalar
  assumptions now have matrix bridges and which physical choices remain open.

Stop after the finite algebra, documentation and regressions. No unbounded claim
about finite deformations, empirical physics or singular limits is part of this
implementation contract.
