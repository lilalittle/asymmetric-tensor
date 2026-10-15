# asymmetric-tensor

Lean 4 formalization of the **asymmetric metric-tensor and the thermodynamic
equation of state**, by Binyamin Tsadik Bair-Mosheh.

`AsymmetricTensor.lean` (2,203 lines) formalizes sections 1–16 of the work:
kinematic parametrization, the thermodynamic budget, metric-tensor assembly
(`U_hat`/`U_sym`/`U_anti`), the field equation, the equation of motion,
the unified action, conformal symmetry, the mass mechanism (VEV → Planck
mass → yield), gauge theory, tensor covariance / CPT, galactic kinematics
(Tully-Fisher), the Einstein–Cartan isomorphism, wave mechanics, pressure
dynamics, lensing, and future-work corollaries. The 8-commit history on the
`binyamin/formalization` branch records one version per draft of the working
document, in order.

## Building

Requires [elan](https://elan.lean-lang.org):

```
lake update          # pins Lean + Mathlib (see lean-toolchain, lake-manifest.json)
lake exe cache get   # fetch prebuilt Mathlib oleans (~6 GB); do NOT build Mathlib from source
lake build           # elaborates AsymmetricTensor.lean
```

CI (`.github/workflows/lean_action_ci.yml`) does the same via
`leanprover/lean-action`, which fetches the Mathlib cache automatically.

## Verification status

Verified 2026-10-15: Lean 4.35.0 + Mathlib `aa35a481e5f0` —
full kernel elaboration, **0 errors, 0 `sorry`**.

One mechanical note: the source document placed the `/-!` module docstring
*before* the `import` lines, which Lean ≥ 4.35 rejects
(`invalid 'import' command, it must be used in the beginning of the file`).
The docstring has been moved below the imports; nothing else was changed.

## What "compiles" does and doesn't mean

A successful build means every definition and proof term checks against
Lean's kernel, Mathlib, and the file's 7 stated axioms
(`c`, `l_p`, `hbar`, their positivity, `covariant_conservation`).
It does not prove the physics from first principles — the physical content
lives in those axioms and in the theorems' hypotheses.

## License

Apache-2.0 — see `LICENSE`. Copyright 2026 Binyamin Tsadik Bair-Mosheh.
