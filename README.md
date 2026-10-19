# asymmetric-tensor

Lean 4 research companion to **The Asymmetric Metric-Tensor and the
Thermodynamic Equation of State**, by Binyamin Tsadik Bair-Mosheh.

The repository contains a real 4×4 coordinate-matrix model, algebraic lemmas,
a fixed-chart tensor Lie derivative, Lorentzian contraction identities, finite
optical-path integrals, and conditional statements motivated by the manuscript.
Its headings follow topics 1–16 of the paper; they do **not** mean those sections
are fully formalized. Several geometric objects and physical derivations remain
open, and ten specification targets simply return their assumed conclusions.

## What is implemented?

Start with the [formalization status map](docs/formalization-status.md):

- [Section-by-section coverage, objects, and assumptions](docs/formalization-status.md#section-by-section-status)
- [Custom assumptions and unspecified model symbols](docs/formalization-status.md#assumptions-and-unspecified-symbols)
- [All ten assumed targets](docs/formalization-status.md#the-ten-exact-h_target-cases)
- [Current dispositions of the 22 reviewed findings](docs/formalization-status.md#review-findings-and-dispositions)
- [Historical v9 equation ledger: 239 equations and 40 unnumbered claims](docs/equation-coverage.md)
- [Historical #9/#33 declaration types and transitive axiom audit](docs/declaration-audit.json)

The equation ledger preserves the exact reviewed #9/#33 source and dependency
snapshot. Its 240-declaration audit and equation labels are historical evidence;
current-source equation remapping remains open. Validate the archive with
`python3 scripts/equation_ledger.py --check --historical` (requires Poppler
`pdftotext`). The current proof-audit workflow below checks a different scope.

Useful entry points exposed by [AsymmetricTensor.lean](AsymmetricTensor.lean) are
`matrix_decomposition` (matrix algebra), `constant_coordinate_conserved`
(a proved nonempty conservation constraint), `lorentzian_action_separation`
(an explicit Minkowski contraction), and `optical_distance_gt` (a finite
integral inequality for a specified ansatz). The [entry-point guide](docs/formalization-status.md#where-to-start)
explains each result's scope. The [module map](docs/modules.md) locates their
implementations and describes the unchanged public namespace and import policy.

The historical universal conservation axiom has been removed; the current
[coordinate-conservation interface](docs/conservation.md) requires an explicit
`CoordinateConserved` premise. The [action](docs/lorentzian-action.md),
[Lie-derivative](docs/lie-derivative.md), [optical-path](docs/optical-path.md), and
[force-hierarchy](docs/force-hierarchy.md) notes describe the other bounded
mathematical repairs and the physical questions they leave open.

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

## Verification and scope

The checked-in [Lean proof-audit workflow](.github/workflows/lean_action_ci.yml)
runs on pushes and pull requests. It preserves the dependency pins, obtains the
Mathlib cache, builds the advertised target, checks all production declarations
for incomplete proofs, checks eleven general and seventeen action-specific
theorem axiom sets, and exercises the regressions and failure mutations.
Existing module-system/style warnings remain visible and nonfatal; proof errors
and detected `sorryAx` dependencies fail verification independently.

The [status map](docs/formalization-status.md#reviewed-snapshot-and-validation)
records the mathematical source identity, unchanged manuscript hash, and local
validation of this rebased combination. Historical CI-only head
`6b667bbc6e3657cc8727bd7565fd3aa0509299b6` passed its
[hosted proof-audit run](https://github.com/subtleGradient/asymmetric-tensor/actions/runs/38788710791).
That run does not cover this combined source; no hosted result for the rebased
combination is recorded here. Local existing-cache validation, clean setup, and
revision-specific hosted checks are distinct evidence.

The [verification contract](docs/verification.md) distinguishes whole-production
proof-completeness checking from the selected exact theorem dependency audits.
The selected lists are not a whole-library custom-axiom audit. The ten
`FutureWork` statements returning `h_target` remain target specifications.

Lean checks formal statements against their hypotheses and dependencies. It
does not check whether a physical name matches its implemented objects, whether
an assumed law is empirically true, or whether the manuscript is fully represented.
The source has six explicit `axiom` declarations for physical constants and their
positivity, plus nine body-less `opaque` field declarations. Those counts are a
source inventory, **not** a transitive dependency audit. Removing the historical
conservation contradiction does not prove consistency of every remaining model
assumption. The component-projection results do not derive Bernoulli or
Navier–Stokes PDEs, and the action results do not supply an action variation.

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
| v10 | 2026-10-19 | [zenodo.23472554](https://doi.org/10.5281/zenodo.23472554) |

All versions live at the concept DOI: https://doi.org/10.5281/zenodo.21321264

Copyright Binyamin Tsadik Bair-Mosheh — [CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/).

## Contributing and API navigation

Start with [the contributor guide](CONTRIBUTING.md) and its checked matrix example.
Core definitions and headline results have declaration docstrings describing
their mathematical contracts and limitations. The guide links the repaired
Lie, action, optical, and force interfaces and their focused regression files.
