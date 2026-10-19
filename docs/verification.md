# Verification contract

The [workflow](../.github/workflows/lean_action_ci.yml) installs the committed
Lean toolchain, obtains the pinned Mathlib cache, and runs
[`scripts/verify.sh`](../scripts/verify.sh) on pushes, pull requests and manual
runs. GitHub actions are pinned to commits, and GitHub first-party build caching
is disabled. A configured workflow is not evidence that a revision passed.

## Reproduction without upgrading dependencies

Use Git, Bash, Python 3 and [elan](https://lean-lang.org/install/). From the root:

```sh
lake exe cache get
bash scripts/verify.sh
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

Lean is pinned to 4.35.0 and Mathlib to
`aa35a481e5f0cdb3b04a899ead15d6ca7305a624`. Keep all transitive revisions in the
committed manifest. Do not delete it or run `lake update` for reproduction.
The script compares configuration-file bytes with its entry state; CI also
checks for changes relative to the checkout. Intentional upgrades need a separate
review of dependency/toolchain changes.

## What the aggregate executes

The aggregate runs production style/source-parser regressions and the bounded
import/context guard, builds `AsymmetricTensor` and `ProofAudit`, executes every
top-level `tests/*.lean`, checks the roadmap inventory and its regressions, and
runs proof-audit acceptance/rejection fixtures. A build alone does not run the
regressions. Warnings stay visible and nonfatal; elaboration errors or failed
checks stop the script. Transitive `sorryAx` checking is independent of warnings.

The current top-level Lean files are:

- `ApiSnapshot.lean`: elaborated signatures used by the separate reference comparison
- `EquationAxioms.lean`: complete first-party transitive custom-axiom policy
- `ProofAudit.lean`: production completeness/inventory and selected exact dependencies
- `RoadmapCounterexample.lean`: finite matrix counterexample and Clebsch orientation
- `RoadmapTargets.lean`: proposed determinant/volume proposition types, not their proofs
- `V45FieldCalculus.lean`: coordinate calculus, scoped conservation, Lie and continuity checks
- `V45MatrixAction.lean`: contraction signs, Clebsch/frame restrictions and action algebra
- `V45OpticsForces.lean`: natural-log/scaled-force contracts and test-local recovered algebra

The glob is nonrecursive. Seven files in
[`tests/archive/v2`](../tests/archive/v2/README.md) are preserved but not executed.
Their historical results, including seventeen action-specific dependency checks,
are not current coverage. [The coverage report](regression-coverage.md) accounts
for each archived file, current replacements, and remaining losses.

## Distinct proof checks

1. **Build:** Lean elaborates definitions and proofs. Success alone does not
   exclude admitted proofs or custom axioms.
2. **Production completeness and declared axioms:** `#audit_root AsymmetricTensor`
   examines declarations owned by the umbrella and its first-party modules,
   including private/generated declarations, regardless of namespace. It rejects
   transitive `sorryAx` and any change to the exact declared-axiom inventory. This
   command alone is not a whole-library imported custom-axiom allowlist.
3. **Selective exact dependencies:** `tests/ProofAudit.lean` and the `V45*` tests
   pin reviewed custom-axiom sets for selected results. Missing/extra dependencies
   or missing declarations fail. The ordinary logical axioms `propext`,
   `Classical.choice`, and `Quot.sound` are permitted. Each new `V45*` module also
   checks all its retained declarations with `#audit_current_module declared []`.
4. **Current-source transitive inventory:** `tests/EquationAxioms.lean` examines
   every first-party declaration, permitting only the seven custom names below
   and those three logical axioms transitively. Its machine-readable output is
   not an equation mapping and must not replace the historical audit JSON.

All names below belong to `AsymmetricTensor`.

| Selected production theorem | Exact custom axioms in `tests/ProofAudit.lean` |
|---|---|
| `matrix_decomposition` | none |
| `tensor_decomposition_proven` | `c` |
| `contract_sym_anti_proven` | `c` |
| `unified_action_separation` | `c` |
| `bernoulli_energy_conservation` | `c`, `l_p`, `covariant_conservation` |
| `navier_stokes_momentum_conservation` | `c`, `l_p`, `covariant_conservation` |
| `divergence_expansion` | `c`, `l_p` |
| `geometric_navier_stokes` | `c`, `l_p`, `hbar`, `c_pos`, `l_p_pos`, `hbar_pos` |
| `baryonic_tully_fisher_derivation` | `c`, `l_p`, `hbar`, `c_pos`, `l_p_pos`, `hbar_pos` |

The seven explicit axioms are `c`, `l_p`, `hbar`, `c_pos`, `l_p_pos`, `hbar_pos`,
and `covariant_conservation`. The first six declare constants and positivity.
The seventh states exactly `∀ x : SpaceTime, metric_divergence U_hat_dynamic x = 0`.
`V45FieldCalculus.lean` pins the axiom kind and definitional type of all seven
names. Its scoped-postulate guard rejects broadening conservation to arbitrary
fields, even if its name remains allowlisted. Eight body-less opaque scalar
fields are additional unspecified inputs; their regularity and physical laws
are not established merely by declaring them.

The temporal/spatial projections inherit the scoped postulate. Generic coordinate
calculus and its nonconserved-field counterexample do not. The conditional
material-acceleration, field-continuity, and Eulerian-balance identities have no
custom axioms in their selected audits, but still assume the displayed
product-rule, continuity, or balance hypotheses. `geometric_navier_stokes`
assumes its zero-divergence sum and does not inherit the postulate.

Expected sets are reviewed policy, not automatically learned from output.
An allowlist does not establish consistency or empirical validity.
`ProofAudit.lean` uses Lean's `collectAxioms`, including dependencies through
bodies, types and imports. It is not independent kernel certification or an
audit of every Mathlib declaration. See
[Lean's proof-validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

## Failure regressions

`scripts/test_proof_audit.py` creates temporary fixtures under `.lake`, compiles
imported dependencies, and requires the intended diagnostic and a nonzero exit.
A malformed fixture or unrelated missing import does not count as rejection
coverage. Cases include completed-proof acceptance; direct `sorry` and `admit`;
unfinished imported/private proofs; unexpected imported or unreferenced
first-party axioms; and missing theorem/module targets. Temporary fixtures and
compiled files are removed afterward.

Style, source-token parser, context-inventory and roadmap regressions exercise
their own bounded contracts. None substitutes for complete elaboration and the
independent built-reference API comparison. In particular, the context guard
cannot establish declaration placement or arbitrary Lean semantics.

## Current validation boundary

The PR #70 repair targets integration head
`10158f3b5336ca15a78d98221c5531dd55a578b5`, based on the author's raw v4.5 commit
`5a84e0c52b71295a678dcc1c50f80d430e5475f2`. It preserves the preceding import
fixes and trace-theorem relocation, restores twelve remaining section-context
identifiers in ten production lines, and migrates meaningful regressions without
restoring the whole historical API. [Module evidence](modules.md#compatibility-checks)
records the baseline source hash and the source-comparison limits.

Fresh local checks on 2026-10-19 for this repaired source/test tree established:

- Both the raw v4.5 reference and repaired production library build.
- Source comparison retains 377 inventoried named declaration token sequences
  and 54 declaration docstrings. Full built-reference API comparison retains
  all 377 elaborated types, universes and binder order.
- The root audit checks 517 compiled production declarations, exactly seven
  declared axioms and no transitive `sorryAx`; nine root-result exact dependency
  checks pass. This compiled count includes generated declarations and differs
  from the bounded 377-name source inventory.
- The focused field, matrix and optics/force files pass, with respectively
  12, 10 and 8 exact dependency checks and completeness checks over their
  16, 23 and 12 retained test declarations. All seven axiom kinds/types are pinned.
- The roadmap counterexample and its six exact dependency checks pass.

These focused results are not a final aggregate or hosted result. Final aggregate
and hosted status belong to the exact-head evidence on
[PR #70](https://github.com/lilalittle/asymmetric-tensor/pull/70), identifying the
tested revision and outcome. This document records the bounded checks above;
an older successful run does not certify a later commit.

A completed validation record should identify the exact candidate revision/tree,
reference revision, commands and outcomes for:

- The aggregate, including every current top-level Lean regression and negative fixture
- All production declarations, the seven-axiom inventory and transitive dependency checks
- The seven axiom kind/type guards and test-module completeness checks
- Source-token/docstring and full elaborated API comparisons with the built raw reference
- Preservation of toolchain, dependency files and archived ledger evidence
- Hosted CI for the exact published repair commit

Existing-cache local validation, fresh setup and hosted execution are separate
evidence. The historical ledger checks require Poppler and remain separate:
`python3 scripts/equation_ledger.py --check --historical` and
`python3 tests/test_equation_ledger.py`. The ledger concerns the reviewed #9/#33
snapshot; current `EquationAxioms.lean` output has a different source and policy.
The separate historical check and all 23 ledger regression/mutation tests passed
locally on 2026-10-19 with accepted archive hashes retained. These results do not
add Poppler-dependent checks to the hosted aggregate.

No current Section 16 declaration has an `h_target` binder. Its algebraic
corollaries still contain physical hypotheses. For example, exponential WKB
transmission is assumed, and positive kinetic energy does not prove an optimal
transport minimum. Neither proof completeness nor a restricted dependency set
turns these statements into the broader physical theories named in their titles.

## Historical validation records

The following pre-v4.5 records are retained for provenance only. Their old API,
declaration counts, six-axiom inventory, test counts and successful runs do not
certify the current candidate. Linked historical scope pages have the same limit.

Historical candidate validation on 2026-10-15 passed the production build,
conservation regressions, 240-declaration completeness/inventory check, eleven
exact theorem axiom checks, and mutation suite. The exact published head
`6b667bbc6e3657cc8727bd7565fd3aa0509299b6` also passed the
[hosted proof-audit run](https://github.com/subtleGradient/asymmetric-tensor/actions/runs/38788710791),
including lock preservation and negative regression checks. Later source or merge
revisions require their own successful run; this pinned result does not certify
them. Neither a green local run nor a green hosted run validates empirical physics
or manuscript coverage.

The CI-only rebased candidate on main `94c49e59d796fdbec846d59c6cbfa45f0304d598` had a
separate local validation on 2026-10-15: production/support builds, all eight
inherited Lean regression files plus `tests/ProofAudit.lean`, the then-current
360-declaration completeness/inventory check, eleven general and seventeen
action-specific exact theorem axiom checks, the roadmap inventory and
finite-contract checks, and the mutation suite. Its production source was
byte-identical to that main revision. Later scope/API documentation stacks and
their additional examples are recorded in the
[scope validation snapshot](formalization-status.md#reviewed-snapshot-and-validation). The historical hosted run above does not
cover this combined source or the expanded regression gate; the new published
revision requires its own hosted result.

The module-split stack has a separate local validation on 2026-10-15: all ten
production modules, the audit support library, all eleven Lean regression files,
the 364-declaration completeness check with the same six declared axioms, eleven
general and seventeen action-specific exact dependency checks, roadmap checks,
and proof-audit and style mutation regressions pass. The increase from 360 to 364
is compiler-generated implementation detail; the 304 source-declared public
names and their full types/universes are unchanged. All 78 API declaration
docstrings and the scope text are retained. See [module evidence](modules.md).
This local result uses the existing shared Mathlib cache; it does not certify
hosted CI or a fresh checkout of the final published revision.

The later historical-ledger integration was validated separately on 2026-10-15:
`./scripts/verify.sh` passed all twelve Lean regression files, including
`tests/EquationAxioms.lean`. That added current-source audit enumerates all 364
production declarations and permits only the six named custom axioms plus
`propext`, `Classical.choice` and `Quot.sound` transitively. It does not establish
a current equation-to-declaration map or replace the archived 240-declaration
#9/#33 audit. The [historical ledger](equation-coverage.md) also passed its
explicit `--check --historical` validation and all 22 Python regression/mutation
tests; the default live check rejected the changed current source as intended.
The historical source, mapping, coverage JSON, audit JSON and accepted hashes
were preserved. These separate Python ledger checks require Poppler `pdftotext`
and are not part of the hosted workflow; the Lean declaration check is part
of its normal `tests/*.lean` gate.
