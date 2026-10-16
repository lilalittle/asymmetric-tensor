# Modules, naming, and style

This is an organizational refactor of the current repaired library and scope/API/CI stack.
It preserves the existing public declarations and their mathematical statements.
The manuscript's topic labels are retained for navigation; they do not establish
that the named physical theories have been derived.

## Finding and importing a result

`import AsymmetricTensor` remains the compatibility entry point. It publicly
imports all nine implementation modules. Every declaration remains in namespace
`AsymmetricTensor`; a filename does not add a namespace segment. In particular,
`FutureWork` is a section, not a namespace.

| Module below `AsymmetricTensor` | Main contents | First-party dependency |
|---|---|---|
| `Model` | Six assumptions, constants, positivity, `V4`/`T2`, scalar budgets | none |
| `MatrixAlgebra` | `symPart`/`antiPart`, matrix assembly, contractions, `VolAvg`, action identity | `Model` |
| `FieldCalculus` | Fixed-chart fields, partial derivatives, conditional conservation, field inputs | `MatrixAlgebra` |
| `Applications.MechanicsMass` | Cavitation, conditional field equations, boost-symmetry constraint, dressing, mass relations | `FieldCalculus` |
| `Applications.Electromagnetism` | Eigenvalue/contraction identities and cavitation limits | `MatrixAlgebra` |
| `Applications.Geometry` | Frame transformations, galactic relations, affine-connection target | `Model` |
| `Applications.WavesForces` | Wave, pressure, and force relations | `Model` |
| `Applications.Optics` | Conditional redshift, finite optical-path integrals, base-10 magnitude relations | `Model`; explicit Mathlib interval-integral import |
| `FutureTargets` | Section 16 algebraic corollaries and explicitly hypothesis-driven targets | `Model` |

For example, a matrix-only contribution can start with:

```lean
import AsymmetricTensor.MatrixAlgebra

example (U : AsymmetricTensor.T2) :
    U = AsymmetricTensor.symPart U + AsymmetricTensor.antiPart U :=
  AsymmetricTensor.matrix_decomposition U
```

Implementation modules currently range from 232 to 520 lines. The split does not
claim that all assumptions have been isolated from all reusable mathematics:
`Model` still holds both basic types and the existing scalar theory. Moving those
again is worth doing only when a concrete contributor needs that boundary.

## Public API and module conventions

Production files use the Lean 4.35 module system, an Apache-2.0 copyright header,
explicit `public import`s, and `@[expose] public section` for the existing exposed
API. Keep source attribution and the manuscript's separate licensing intact.
Use `autoImplicit false` to catch accidental implicit parameters.

All **304 source-declared public names** were compared with the pre-split repaired scope/API/CI
library. Their fully elaborated types and universe parameters are identical after
removing only generated binder hygiene scopes and elaborator metadata. This
preserves user-written binder names, implicit/instance binder kinds, constants,
and argument order. The compiler's auxiliary proof names are implementation
details and change with module elaboration; those are covered by the completeness
audit, rather than advertised as stable API.

To repeat the comparison with a built baseline checkout using the same dependency
pins, run from this checkout after building both libraries:

```sh
python3 scripts/check_public_api.py /path/to/built-baseline-checkout
```

The script uses `tests/ApiSnapshot.lean`. Its source-name inventory supports this
project's current single-namespace declaration syntax, including attributes and
aliases; extend it deliberately if
introducing structures, nested namespaces, or other declaration forms. This is a
migration check of names and types, not a proof that definition bodies are equal.

## Deliberate naming policy

- Keep existing scientific notation and public names in this change, including
  `V4`, `T2`, `U_hat`, `U_sym`, `U_anti`, `M_P`, `rho_tau`, and `P_c`.
- For new generic definitions, prefer descriptive `lowerCamelCase` names, as in
  `symPart`, `antiPart`, and `raiseBoth`; types use `UpperCamelCase`.
- New theorem names should describe the actual mathematical conclusion using
  `snake_case`. Avoid upgrading a conditional algebraic identity into a claimed
  physical derivation through its name.
- Rename existing declarations only in a focused change with a reason and a
  migration note. Preserve an old name with an appropriate alias/deprecation
  when downstream use warrants it, and test both names. No renames are necessary
  to make this module split usable.
- Add declaration docstrings for new reusable APIs: define the objects, explain
  nonzero/positivity hypotheses, and state what the result does not establish.

[Mathlib style](https://leanprover-community.github.io/contribute/style.html) and
[naming conventions](https://leanprover-community.github.io/contribute/naming.html)
are reference points. This prototype does not claim full Mathlib admission.

## Lint and long-line baseline

`linter.unusedSectionVars` is enabled in every implementation module. Five
individual theorems keep a documented declaration-local exception:

- `dressing_field_invariance`
- `equivalence_principle_gradients`
- `gravitoelectromagnetism_mapping`
- `poynting_vector_convection`
- `u1_gauge_invariance`

Their pre-existing typeclass parameters are unnecessary for the proof, but
removing them would change the established public signatures. The exceptions
cover only those declarations, not their surrounding files. Revisit them with a
separately reviewed API migration; do not use a file-wide linter suppression.
Unused hypotheses already named with `_` remain explicit parts of their theorem
statements. Keeping them does not establish their physical necessity.

New or edited production lines should fit within 100 characters. The initial
baseline records the **exact text and multiplicity of 189 inherited long lines**
in `scripts/lean-style-baseline.json` from the current repaired source. It permits those
existing lines and their removal, but rejects a new or changed overlong line,
even if the total count decreases. Wrap touched lines instead of automatically
refreshing the baseline. This is a maintenance baseline, not a claim to have reformatted all proofs.
New API docstrings are wrapped without changing their text.

`scripts/check_lean_style.py` also checks headers, module directives, explicit
public import structure, the five exact linter exceptions, whitespace, and that
every production source is reachable from the umbrella. Four mutation regressions
check clean acceptance and rejection of a new long line, broad linter suppression,
and an unimported module. `scripts/verify.sh` runs both scripts before Lean checks.
This small gate is intentionally narrower than the full Mathlib style linter.

## Compatibility evidence

The baseline is the current mathematical main `94c49e59d796fdbec846d59c6cbfa45f0304d598`
with the independently reviewed CI, scope, and API changes stacked on it.
The reproducible migration commands are:

```sh
python3 scripts/check_module_source.py /path/to/pre-split-api-checkout
python3 scripts/check_public_api.py /path/to/built-pre-split-api-checkout
```

The first compares all 304 declaration attribute/statement/body token sequences
and retains all 78 declaration docstrings up to whitespace. It deliberately
supports this repository's present syntax, rather than claiming to parse arbitrary
Lean. Its six mutation tests cover comments, body edits, declaration attributes,
aliases, duplicates, docstrings, and string literals. The second checks all 304
fully elaborated types and universe parameters, including binder kinds and names.
Section-variable context is validated by that elaborated comparison.

A separate elaborated-expression inspection expands generated first-party helpers
and removes binder hygiene scopes and metadata. It finds 289 of 298 declaration
values structurally identical. The other eight theorem proofs differ in generated
proof terms; `VolAvg` differs only in its proof fields, while its function and
non-proof parameters agree. These are proof-irrelevance/compiler elaboration
differences, not changes to scientific statements or computational definitions.
No claim is made that all raw compiled proof expressions are byte-identical.
All source proof tokens are unchanged, and the complete audit still rejects
transitive `sorryAx` and preserves the declared-axiom inventory.

The scope paragraphs remain in the compatibility umbrella; implementation modules
retain all declaration contracts. The obsolete monolithic manuscript abstract is
not used as a coverage claim. README, contribution guidance, and revision-specific
verification records point to this module map.

## Import discipline

The broad public `Mathlib.Tactic` import is retained for downstream compatibility.
The finite optical-path module explicitly imports
`Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`; the newer boost-symmetry
proof makes `Applications.MechanicsMass` depend on `FieldCalculus`. The module map
reflects these current dependencies. No historical import-count or warm-run timing
is presented as a measurement of this revised source.

## Verification

```sh
./scripts/verify.sh
python3 scripts/check_public_api.py /path/to/built-baseline-checkout
python3 scripts/check_module_source.py /path/to/pre-split-api-checkout
git diff --check
```

The default build reaches all ten production modules, including the umbrella.
The completeness audit checks 364 declarations after this split, including private
and compiler-generated declarations, retains the six-axiom inventory, and rejects
all transitive `sorryAx` uses. All eleven reviewed per-theorem custom-axiom checks
and all proof-audit mutation regressions still pass. The count differs from the
360-declaration monolith because auxiliary declarations change under the module
system; the 304 source-declared public signatures are unchanged.

See [the verification contract](verification.md) for exact coverage, limitations,
and the requirement to verify hosted CI on the final published revision.
