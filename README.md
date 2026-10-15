# asymmetric-tensor

Lean 4 formalization of the **asymmetric metric-tensor and the thermodynamic
equation of state**, by Binyamin Tsadik Bair-Mosheh.

`AsymmetricTensor.lean` formalizes sections 1–16 of the work:
kinematic parametrization, the thermodynamic budget, metric-tensor assembly
(`U_hat`/`U_sym`/`U_anti`), the field equation, the equation of motion,
the unified action, conformal symmetry, the mass mechanism (VEV → Planck
mass → yield), gauge theory, tensor covariance / CPT, galactic kinematics
(Tully-Fisher), the Einstein–Cartan isomorphism, wave mechanics, pressure
dynamics, lensing, and future-work corollaries. The 8-commit history on the
`binyamin/formalization` branch records one version per draft of the working
document, in order.

## Building the committed version

Requires Git, Bash, Python 3, and [elan](https://lean-lang.org/install/), with
`lake` on your `PATH`. Run the following from a new project directory:

```sh
git clone https://github.com/lilalittle/asymmetric-tensor.git
cd asymmetric-tensor
lake exe cache get       # fetch the prebuilt Mathlib dependencies
./scripts/verify.sh      # build, audit, and run regression checks
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

Elan selects Lean 4.35.0 from `lean-toolchain`, installing it if needed.
`lake-manifest.json` records the exact dependency commits; `lakefile.toml`
also pins Mathlib to `aa35a481e5f0cdb3b04a899ead15d6ca7305a624`.
Lake fetches missing dependencies at those recorded revisions. The cache
command avoids compiling Mathlib from source; let it finish successfully
before running the verification script. The final command should
produce no diff and exit successfully: normal setup must not change the
committed toolchain or dependency selection.

Do not run `lake update` for normal reproduction. It is an upgrade operation
that can rewrite the manifest and toolchain. Keep the committed manifest
rather than deleting or regenerating it to troubleshoot a cache download.

### Intentional dependency upgrades

In a separate branch, choose the desired Mathlib commit and change its `rev`
in `lakefile.toml`. Then run:

```sh
lake update mathlib
lake exe cache get
lake build AsymmetricTensor
git diff -- lean-toolchain lakefile.toml lake-manifest.json
```

`lake update mathlib` resolves the selected revision and its dependencies,
and may update `lean-toolchain` to match. Review every dependency/toolchain
change and resolve any build failures before committing the new selection.
For the update behavior, see the
[Lake manual](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

The electromagnetic force-hierarchy regression checks run with
`lake env lean tests/ForceHierarchy.lean` after `lake build`. See
[the force-hierarchy correspondence](docs/force-hierarchy.md) for the exact
manuscript baseline, its domain, and the separately named algebraic rescaling.

## Verification status

The checked-in [Lean proof-audit workflow](.github/workflows/lean_action_ci.yml)
runs on pushes and pull requests. It preserves the dependency pins, obtains the
Mathlib cache, builds the advertised target, rejects incomplete first-party
proofs, checks eleven general and seventeen action-specific theorem axiom sets,
and exercises the checked-in regressions and failure mutations.
Existing module-system/style warnings remain visible and nonfatal; proof errors
and detected `sorryAx` dependencies fail verification independently.

The repaired candidate passed local checks on 2026-10-15. The exact published
head `6b667bbc6e3657cc8727bd7565fd3aa0509299b6` also passed its
[hosted proof-audit run](https://github.com/subtleGradient/asymmetric-tensor/actions/runs/38788710791).
That is evidence for this identified revision, not for a later merged combination;
check the revision-specific workflow result after subsequent changes.

The [verification contract](docs/verification.md) lists every selectively audited
theorem, its exact allowed custom axioms, and the separate production-module
completeness coverage. This is not a whole-library custom-axiom audit.
`FutureWork` statements that simply return `h_target` are explicitly classified
there as target specifications, not completed physical derivations.

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

## Next mathematical contribution

The [formalization roadmap](docs/formalization-roadmap.md) inventories target
specifications and simplified models, records open modeling decisions, and selects
a [bounded finite-determinant task](docs/finite-determinant-task.md).

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
