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
Lean's kernel, Mathlib, and the file's 6 stated axioms
(`c`, `l_p`, `hbar`, and their positivity). Coordinate conservation is an
explicit `CoordinateConserved U` hypothesis, not a universal axiom. The
component-projection theorems do not derive Bernoulli or Navier–Stokes PDEs.
See [the conservation repair](docs/conservation.md) for the counterexample,
nonempty solution class, API change, and focused axiom-audit commands.
It does not prove the physics from first principles — the physical content
lives in those axioms and in the theorems' hypotheses.

## License

The Lean software is licensed under **Apache-2.0** — see [`LICENSE`](LICENSE).
The published manuscripts in `papers/` are licensed under **CC-BY-4.0** — see
[`papers/LICENSE`](papers/LICENSE). Copyright 2026 Binyamin Tsadik Bair-Mosheh.
These are separate licenses for separate artifacts; the manuscript's license
does not replace the software license.

## Citation

`CITATION.cff` describes the **Lean software** at the top level, with its repository
URL and Apache-2.0 license. Its `preferred-citation` describes the **manuscript**:
the DOI, v9 version, September 25, 2026 date, and CC-BY-4.0 license in that section
belong to the paper. The manuscript metadata and abstract retain the provenance
of the original Zenodo citation export, available in this repository's git history.

To cite the manuscript currently included in this checkout:

> Binyamin Tsadik Bair-Mosheh (2026). *Formalization of the Asymmetric Metric-Tensor
> and the Thermodynamic Equation of State* (v9). Zenodo.
> https://doi.org/10.5281/zenodo.22953897

If you use or discuss the Lean implementation, also cite the software revision:

> Binyamin Tsadik Bair-Mosheh. *asymmetric-tensor: Lean 4 companion to the Asymmetric
> Metric-Tensor manuscript* [Software]. https://github.com/lilalittle/asymmetric-tensor,
> commit FULL_COMMIT_SHA.

Replace `FULL_COMMIT_SHA` with the full output of `git rev-parse HEAD` in the
checkout you used, and link to
`https://github.com/lilalittle/asymmetric-tensor/tree/FULL_COMMIT_SHA` with that same
SHA. Describe any uncommitted changes separately. If you use a different paper
version, cite its version-specific DOI from the table below. A paper version and a
software revision need not match.

No software DOI or archived software release is claimed here. The manuscript DOI
identifies the paper; it is not evidence that a particular software revision was
archived.

## Published versions

The author's published manuscripts (Zenodo, CC-BY-4.0). The latest version is always at `papers/asymmetric-metric-tensor.pdf`; each published version replaced the previous one, so older versions are recoverable from this repo's git history:

| Version | Published | Zenodo record |
|---|---|---|
| v0 | 2026-07-12 | [zenodo.21321265](https://doi.org/10.5281/zenodo.21321265) |
| v1 | 2026-07-13 | [zenodo.21339079](https://doi.org/10.5281/zenodo.21339079) |
| v2 | 2026-07-20 | [zenodo.21455277](https://doi.org/10.5281/zenodo.21455277) |
| v3 | 2026-07-23 | [zenodo.21505034](https://doi.org/10.5281/zenodo.21505034) |
| v4 | 2026-08-03 | [zenodo.21780517](https://doi.org/10.5281/zenodo.21780517) |
| v5 | 2026-08-31 | [zenodo.22212278](https://doi.org/10.5281/zenodo.22212278) |
| v6 | 2026-09-09 | [zenodo.22675546](https://doi.org/10.5281/zenodo.22675546) |
| v7 | 2026-09-17 | [zenodo.22813082](https://doi.org/10.5281/zenodo.22813082) |
| v8 | 2026-09-19 | [zenodo.22847830](https://doi.org/10.5281/zenodo.22847830) |
| v9 | 2026-09-25 | [zenodo.22953897](https://doi.org/10.5281/zenodo.22953897) |

All versions live at the concept DOI: https://doi.org/10.5281/zenodo.21321264

Copyright Binyamin Tsadik Bair-Mosheh — [CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/).
