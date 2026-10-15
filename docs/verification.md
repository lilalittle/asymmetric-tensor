# Verification contract

The workflow at [`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml)
runs on pushes, pull requests, and manual dispatch. It installs the toolchain
from `lean-toolchain`, obtains Mathlib's cache using the committed manifest,
and runs `scripts/verify.sh`. Both GitHub actions are pinned to commit SHAs.
GitHub `.lake` build caching is disabled so first-party source is elaborated
for the candidate. The Mathlib cache is still used.

## Reproduction without upgrading dependencies

Install [elan](https://lean-lang.org/install/) and use Git, Bash, and Python 3.
From a clean checkout:

```sh
lake exe cache get
./scripts/verify.sh
git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json
```

Lean is pinned to 4.35.0. Mathlib is pinned in both the package requirement and
manifest to `aa35a481e5f0cdb3b04a899ead15d6ca7305a624`. All transitive packages
use the manifest's recorded revisions. Do not delete the manifest or run
`lake update` during reproduction. `lake update mathlib` belongs on a separate
intentional-upgrade branch after selecting a new `rev`; review and commit the
resulting toolchain and manifest changes together.

`verify.sh` builds the advertised `AsymmetricTensor` target and the separate
`ProofAudit` support library, runs every checked-in `tests/*.lean` regression
(including the production audit), checks the roadmap inventory with
`tests/check_roadmap.py`, and runs temporary mutation regressions. It verifies
that the three lock and configuration files keep exactly the bytes they had when
the script began.
CI additionally requires no changes to those files relative to the checkout.
A missing cache, elaboration error, failed audit, or failed regression is fatal.

## Three distinct proof checks

1. **Build:** Lean elaborates the production definitions and proofs. A successful
   build alone does not exclude admitted proofs or custom axioms.
2. **Completeness and declared-axiom inventory:** `#audit_root AsymmetricTensor`
   examines every declaration owned by the root module and its imported
   `AsymmetricTensor.*` submodules, regardless of declaration namespace. This
   includes private/generated declarations, and currently covers 360 declarations.
   Each declaration's transitive axiom set must exclude `sorryAx`. Every axiom
   declared in those modules must be one of exactly the six listed below.
   This is whole-production-module completeness coverage, not a whole-library
   allowlist of imported custom axioms. Modules outside that root are not covered.
3. **Selective transitive axiom audit:** the following eleven theorems in
   `tests/ProofAudit.lean` have exact reviewed custom-axiom sets. The three ordinary
   Lean logical axioms `propext`,
   `Classical.choice`, and `Quot.sound` are deliberately permitted. Any other
   dependency, including `sorryAx`, `Lean.ofReduceBool`, or an unexpected imported
   custom axiom, fails. Missing theorems and changed custom sets also fail.

All names below are in the `AsymmetricTensor` namespace. `none` means no custom
axioms; ordinary logical axioms still apply.

| Theorem | Exact custom axioms |
|---|---|
| `matrix_decomposition` | none |
| `tensor_decomposition_proven` | `c` |
| `contract_sym_anti_proven` | `c` |
| `unified_action_separation` | `c` |
| `constant_coordinate_conserved` | none |
| `exists_coordinate_conserved` | none |
| `coordinate_field_not_conserved` | none |
| `bernoulli_energy_conservation` | none |
| `navier_stokes_momentum_conservation` | none |
| `geometric_navier_stokes` | `c`, `l_p`, `hbar`, `c_pos`, `l_p_pos`, `hbar_pos` |
| `baryonic_tully_fisher_derivation` | `c`, `l_p`, `hbar`, `c_pos`, `l_p_pos`, `hbar_pos` |

The inherited `tests/LorentzianAction.lean` regression additionally enforces these
seventeen exact custom-axiom sets, with the same three ordinary logical axioms
permitted. The aggregate verifier runs this file too. These are existing reviewed
checks from the Lorentzian-action repair; the rebase does not expand either
allowlist.

| Action theorem | Exact custom axioms |
|---|---|
| `raiseBoth_minkowskiInv` | none |
| `minkowskiInv_sq` | none |
| `lorentzian_sym_anti_orthogonality` | none |
| `lorentzian_matrix_action_separation` | none |
| `pure_electric_negative` | none |
| `pure_magnetic_positive` | none |
| `rest_frame_constraints` | none |
| `restSpatialMetric_eq_background_projector` | none |
| `rest_symmetric_covariant_form` | `c` |
| `rest_antisymmetric_covariant_form` | `c` |
| `symmetric_action_eq121` | `c` |
| `antisymmetric_action_eq123` | `c` |
| `lorentzian_action_separation` | `c` |
| `symmetricMetricInv_left_inverse` | `c` |
| `mixed_electric_measurement` | `c` |
| `mixed_magnetic_measurement` | `c` |
| `kinematic_lagrangian_separation` | `c`, `l_p`, `hbar` |

The six physical axioms declare three real constants and their strict positivity.
They are explicit assumptions, not experimentally established facts. The allowed
logical axioms are the standard extensionality, classical choice, and quotient
soundness assumptions. The lists are policy reviewed in source, not learned from
the current output automatically. Review changes to either audit file along with
changes to theorem statements; an allowlist is not a consistency proof.

`ProofAudit.lean` uses Lean 4.35's `Lean.collectAxioms`, including dependencies
through theorem bodies, definition bodies, types, and imported modules. See
[Lean's proof-validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
This is not independent kernel certification or an audit of all Mathlib axioms.

## Conservation dependency

This candidate includes the [#9 conservation repair](conservation.md). The original
`covariant_conservation` axiom is removed and is never allowlisted. The coordinate
witness and nonempty solution-class proofs are checked. The two component
projections require `CoordinateConserved U`; the theorem named
`geometric_navier_stokes` separately assumes its displayed zero-divergence sum.
The audited legacy `unified_action_separation` is the Frobenius algebraic identity;
the separately named `lorentzian_action_separation` is checked by the inherited
action audit above. These checks establish neither a covariant connection nor a
Bernoulli/Navier–Stokes PDE derivation.

## Target specifications are not completed derivations

No unfinished proof is exempted from completeness checking. Intentional future
research targets are instead conditional statements that take their own target
as a hypothesis. The declarations in the `AsymmetricTensor` namespace and
`FutureWork` section
`alpha_decay_wkb_mapping`, `optimal_transport_minimization`,
`gravitoelectromagnetism_mapping`, `poynting_vector_convection`,
`entanglement_contextuality`, `helicity_orbital_arrest`, `almansi_finite_strain`,
`su3_mass_gap_transition`, `lorentz_force_magnus_mapping`, and
`wake_detachment_stabilization` simply return `h_target`.
These are target specifications, not derivations of the named physical results.
They are not among the eleven headline axiom-audited results. Their proof
completeness does not change that classification. Likewise, opaque field inputs
in Section 5 do not establish equations of motion or regularity.

## Warning policy

Warnings remain visible and nonfatal. In particular, the existing
legacy/module-system import warnings and cosmetic/style/unused-variable warnings
are not grounds for rejecting a mathematically complete candidate. CI does not
use a blanket `--wfail` and does not disable or filter warnings. Elaborator errors
are fatal. A `sorry` warning cannot sneak through this policy because the
compiled transitive `sorryAx` check independently fails, even for a private
unreferenced declaration. This separates proof regressions from a module/style
migration; it is not a claim of full Mathlib lint compliance.

## Failure regressions and status

`scripts/test_proof_audit.py` generates temporary fixtures under `.lake`, compiles
imported dependencies, and requires the intended audit error marker and a nonzero
exit. A malformed fixture or missing import does not count as successful rejection.
It checks acceptance of a completed proof and rejection of:

- A direct `sorry` and a direct `admit`.
- An unfinished proof reached through a compiled imported theorem.
- An unreferenced private unfinished proof in a different namespace.
- An unexpected custom axiom reached through a compiled import.
- An unreferenced unexpected first-party axiom.
- A missing theorem and a missing production module.

Temporary mutations and their compiled files are deleted after the run. No
mutation is installed in the production source. During local validation, an
additional private unfinished theorem and an unreferenced custom axiom were
also temporarily inserted into `AsymmetricTensor.lean`: each compiled, then
failed the production audit with its intended diagnostic. Both were removed
and the restored source was rebuilt and rechecked.

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
inherited Lean regression files plus `tests/ProofAudit.lean`, the current
360-declaration completeness/inventory check, eleven general and seventeen
action-specific exact theorem axiom checks, the roadmap inventory and
finite-contract checks, and the mutation suite. Its production source was
byte-identical to that main revision. Later scope/API documentation stacks and
their additional examples are recorded in the
[scope validation snapshot](formalization-status.md#reviewed-snapshot-and-validation). The historical hosted run above does not
cover this combined source or the expanded regression gate; the new published
revision requires its own hosted result.
