/-
Copyright (c) 2026 Binyamin Tsadik Bair-Mosheh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Binyamin Tsadik Bair-Mosheh
-/
module

public import AsymmetricTensor.Model
public import AsymmetricTensor.MatrixAlgebra
public import AsymmetricTensor.FieldCalculus
public import AsymmetricTensor.Applications.MechanicsMass
public import AsymmetricTensor.Applications.Electromagnetism
public import AsymmetricTensor.Applications.Geometry
public import AsymmetricTensor.Applications.WavesForces
public import AsymmetricTensor.Applications.Optics
public import AsymmetricTensor.FutureTargets

/-!
# The Asymmetric Metric-Tensor companion library

Compatibility umbrella: importing `AsymmetricTensor` continues to expose every
existing `AsymmetricTensor` declaration. Import a submodule to work on a smaller
part of the development. See `docs/modules.md` for the module map and naming policy.

This library supplies a coordinate-matrix research prototype, algebraic lemmas,
finite-path integral results, and conditional statements. Physical names and
section headings do not assert complete manuscript coverage. See
`docs/formalization-status.md` for implemented objects, assumptions and open work.

The historical universal `covariant_conservation` axiom was inconsistent and
has been removed. Conservation is an explicit `CoordinateConserved` premise,
with constant-field witnesses and a linear-field counterexample. The library
also includes the fixed-chart rank-two Lie derivative, Minkowski action
contractions, base-10 distance moduli, finite optical-path inequalities, and the
corrected electromagnetic baseline. These results retain explicit domains and
model assumptions; they do not supply a general covariant connection, derive
the physical momentum PDE, or validate the manuscript empirically.
Section 16 still contains ten `exact h_target` specifications that assume
their conclusions. Kernel checking does not itself prove consistency of all
model assumptions or establish scientific correspondence.
-/
