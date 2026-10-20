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
# The Asymmetric Metric-Tensor library (v5.0)

Compatibility umbrella: importing `AsymmetricTensor` exposes every
`AsymmetricTensor` declaration. Import a submodule to work on a smaller
part of the development.

This is the modular layout of Binyamin Tsadik Bair-Mosheh's v5.0
formalization, mechanically split from his single-file development with
no changes to any declaration. Section headings and physical names are
the author's; they do not assert complete manuscript coverage.
-/
