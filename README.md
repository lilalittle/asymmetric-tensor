# asymmetric-tensor

Lean 4 research companion to **The Asymmetric Metric-Tensor and the
Thermodynamic Equation of State**, by Binyamin Tsadik Bair-Mosheh.

The current implementation is the author's **v5.7 formalization**, organized into
nine topic modules. It contains real 4×4 matrix algebra, Clebsch-gradient exterior
products, fixed-chart field operators, Lorentzian contraction identities, and
conditional statements motivated by the manuscript. Physical names and section
headings do not establish full manuscript coverage or empirical validity.

## Author updates versus the verified library

Binyamin can freely edit the current single-file draft at
[`AsymmetricTensor/Asymmetric Tensor v5.7.lean`](AsymmetricTensor/Asymmetric%20Tensor%20v5.7.lean).
Versioned author uploads have separate **advisory compiler diagnostics** and do
not alter the stable library or its strict proof checks. A green stable check
means the integrated library at that revision passed, not that an uploaded draft has
been accepted. The root `AsymmetricTensor.lean` remains the stable import umbrella.
See [the authoring lane and promotion rules](CONTRIBUTING.md#binyamins-single-file-authoring-lane).

## What is implemented?

Use the [current API and regression coverage report](docs/regression-coverage.md),
[module map](docs/modules.md), and [verification contract](docs/verification.md)
for this revision. The public entry point remains `import AsymmetricTensor`, but
v5.7 changes the v5.0 dimensional and dynamic-field APIs. See the
[migration and source record](docs/v5.7-integration.md).

- `matrix_decomposition` splits any real 4×4 matrix into symmetric and
  antisymmetric parts. `U_hat` now takes two four-component Clebsch gradients;
  `omega_clebsch_2form` constructs their exterior wedge.
- `lie_derivative` includes transport and both covariant-index terms in a fixed
  chart. `is_translationally_symmetric` accepts an arbitrary vector field in this
  version; its name does not restrict that field to a constant translation.
- `lorentzian_contract` and `lorentzian_action_separation` give explicit
  background-Minkowski contraction algebra. They do not construct or vary an
  action integral.
- `covariant_conservation` is a theorem about the selected `U_hat_dynamic`.
  `DynamicClebschFields` bundles fields with a conservation condition; a
  homogeneous vacuum witnesses that this structure is inhabited, and opaque
  `dyn_state` supplies the active configuration. This does not prove conservation
  for arbitrary fields or establish a nontrivial physical solution. Conditional
  momentum identities still take continuity, product-rule, balance, or
  constitutive relations as hypotheses.
- `UnitDim` uses the integer exponents `K`, `Omega`, and `E` in place of
  `L`, `V`, and `S`. The Schwinger eigenvector bridge requires explicit zero slip
  and axial alignment; the four-effects optical theorem distinguishes
  pressure-only refraction from the combined-admittance tensor.
- `refractive_index_substitution` is pointwise optical algebra. The finite-path
  integral and strict optical-delay APIs from the older repair are absent.
  `optical_path_retardation` instead assumes an average index greater than one
  and a distance-product relation. `log10` and `magnitude_anomaly_log10_pos`
  provide a base-10 magnitude identity and strict positivity under explicit
  distance, redshift, and modulus hypotheses; the older natural-log identities
  remain alongside them.
- `interaction_hierarchy_em` returns the unscaled `α²` force expression, the
  scaled `α³` expression, and the unscaled `α⁴` strong-force ratio, given the
  radius formulas and nonzero mass and coupling. The scaled `α⁵` ratio is
  checked separately in test-local regressions. These are algebraic consequences
  of the stated formulas, not independent validation of the physical model.

Section 16 no longer contains the ten old `h_target` premises. Its replacement
statements prove particular algebraic conclusions, often under explicit physical
or constitutive assumptions. Removing `h_target` does not establish the broader
physical claims suggested by their names.

### Historical material

The [v9 equation ledger](docs/equation-coverage.md) and
[declaration audit](docs/declaration-audit.json) preserve the reviewed #9/#33
source and dependency snapshot. Their 240-declaration audit and equation labels
are historical evidence; a current-source equation mapping remains open.
Validate that archive with `python3 scripts/equation_ledger.py --check --historical`
(requires Poppler `pdftotext`). This is separate from the current proof audit.

The older [status map](docs/formalization-status.md),
[conservation](docs/conservation.md), [Lie derivative](docs/lie-derivative.md),
[action](docs/lorentzian-action.md), [optical-path](docs/optical-path.md), and
[force-hierarchy](docs/force-hierarchy.md) notes retain earlier API descriptions
and validation records. Read them as historical documentation, alongside the
[current coverage differences](docs/regression-coverage.md), rather than as
contracts for v5.7. The seven archived Lean test files are preserved but are not
executed by the current aggregate verifier.

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

## Verification and scope

The [Lean proof-audit workflow](.github/workflows/lean_action_ci.yml) runs the
aggregate verifier on pushes and pull requests. It builds the library and audit
support, executes all top-level `tests/*.lean`, checks production proof completeness
and exact declared axioms, checks selected theorem dependencies, and exercises
failure mutations. Warnings remain visible and nonfatal; elaboration errors and
transitive `sorryAx` dependencies fail independently.

The v5.7 source declares no custom axioms or `sorry`/`admit` holes. The
three physical constants remain irreducible noncomputable definitions with
proved positivity bounds. Eight scalar-field definitions now project from the
witness-backed opaque `dyn_state`. The strict declared and transitive custom-axiom
policies are empty; the ordinary logical axioms `propext`, `Classical.choice`,
and `Quot.sound` remain permitted. These checks do not establish empirical
validity or a universal-field conservation law.

The [v5.7 integration record](docs/v5.7-integration.md) identifies the exact
author source, approved changes and current validation status. The aggregate
also builds an independent monolithic reference and compares source tokens,
docstrings and elaborated APIs, including the changed structure and instance
interfaces. Reference fidelity and intentional migration from v5.0 are separate
checks. Local Lean was unavailable during preparation; hosted results must be
recorded for the exact candidate before claiming verification. Historical green
runs do not certify this candidate.

`lake build` alone does not run the regression suite. For a focused iteration
after building, run `lake env lean tests/V45FieldCalculus.lean`,
`lake env lean tests/V45MatrixAction.lean`, or
`lake env lean tests/V45OpticsForces.lean` as appropriate. Use the aggregate
verifier before reporting a complete local pass.

## Contributing and API navigation

Start with [the contributor guide](CONTRIBUTING.md) and the current test files it
links. Keep scientific assumptions, test-local recovered properties, production
APIs, and outstanding analytical work distinct. The older
[formalization roadmap](docs/formalization-roadmap.md) is a revision-pinned
planning record; recheck current source and upstream work before adopting a task.

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
