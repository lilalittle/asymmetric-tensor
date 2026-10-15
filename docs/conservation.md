# Coordinate-conservation repair

Issue [#9](https://github.com/lilalittle/asymmetric-tensor/issues/9) records a
contradiction in revision `9f69988`: the axiom `covariant_conservation` asserted
zero divergence for every matrix-valued function on ℝ⁴. The field
`U x μ ν = x 0` has zeroth divergence component equal to one, so the axiom
implied `1 = 0`. The issue retains the historical reproducer; no theorem of
`False` belongs in the repaired library.

The repair removes that axiom. `CoordinateConserved U` is the proposition
`∀ x, metric_divergence U x = 0`, supplied explicitly by callers. The two
component-projection theorems now require an `hU : CoordinateConserved U`
argument immediately after `U`. They do not select a new physical law or prove
that a proposed physical field satisfies the constraint.

`constant_coordinate_conserved` proves every constant component matrix is a
solution, and `exists_coordinate_conserved` exhibits a nonempty solution class.
`coordinate_field_not_conserved` proves the original linear field is not one.
These statements do not rely on the physical constants or their positivity.

The operation is a fixed-coordinate partial divergence. No connection terms,
index-raising convention, constitutive law, mass-continuity equation, or momentum
PDE is supplied by this repair. For a classical derivative interpretation the
fields need suitable differentiability; Lean's total `fderiv` is used here.
In particular, neither component projection alone establishes a Bernoulli or
Navier–Stokes equation. Those stronger interpretations remain separate work.

## Validation

With the committed toolchain and dependency manifest, fetch the Mathlib cache
and run:

```sh
lake exe cache get
lake build
lake env lean tests/Conservation.lean
```

The test file checks witnesses and the changed calling convention, and prints
transitive axioms for the five conservation statements and two unaffected
headline algebraic results. Inspect the printed lists: the conservation
statements should use only ordinary Lean logical axioms (`propext`,
`Classical.choice`, `Quot.sound`, as needed), without `sorryAx` or any custom
conservation axiom. The algebraic results may retain physical-constant premises
or axioms according to their statements. This focused report is not a
whole-library axiom allowlist or an empirical validation of the manuscript.
