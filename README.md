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

Requires [elan](https://lean-lang.org/install/):

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

## Published versions

The author's published manuscripts, mirrored here one version per commit under `papers/`:

| Version | Published | Zenodo record | Paper |
|---|---|---|---|
| v0 | 2026-07-12 | [zenodo.21321265](https://doi.org/10.5281/zenodo.21321265) | `papers/v0/GfX.pdf` |
| v1 | 2026-07-13 | [zenodo.21339079](https://doi.org/10.5281/zenodo.21339079) | `papers/v1/GfX.pdf` |
| v2 | 2026-07-20 | [zenodo.21455277](https://doi.org/10.5281/zenodo.21455277) | `papers/v2/GfX.pdf` |
| v3 | 2026-07-23 | [zenodo.21505034](https://doi.org/10.5281/zenodo.21505034) | `papers/v3/GfX.pdf` |
| v4 | 2026-08-03 | [zenodo.21780517](https://doi.org/10.5281/zenodo.21780517) | `papers/v4/unified tensor.pdf` |
| v5 | 2026-08-31 | [zenodo.22212278](https://doi.org/10.5281/zenodo.22212278) | `papers/v5/Unified Tensor.pdf` |
| v6 | 2026-09-09 | [zenodo.22675546](https://doi.org/10.5281/zenodo.22675546) | `papers/v6/Asymmetric Metric Tensor.pdf` |
| v7 | 2026-09-17 | [zenodo.22813082](https://doi.org/10.5281/zenodo.22813082) | `papers/v7/Asymmetric Metric Tensor.pdf` |
| v8 | 2026-09-19 | [zenodo.22847830](https://doi.org/10.5281/zenodo.22847830) | `papers/v8/A Tensor.pdf` |
| v9 | 2026-09-25 | [zenodo.22953897](https://doi.org/10.5281/zenodo.22953897) | `papers/v9/A Tensor.pdf` |

All versions live at the concept DOI: https://doi.org/10.5281/zenodo.21321264

Copyright Binyamin Tsadik Bair-Mosheh — [CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/).
