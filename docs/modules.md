# Modules, naming, and style

This is the modular layout of Binyamin Tsadik Bair-Mosheh's v4.6 formalization.
The public umbrella and namespace remain `AsymmetricTensor`; preservation of
that import path does not imply compatibility with the older repaired APIs.
Section headings follow manuscript topics and do not establish full coverage.

## Finding and importing a result

`import AsymmetricTensor` publicly imports nine implementation modules.
A filename does not add a namespace segment. In particular, `FutureWork` is a
section inside `AsymmetricTensor`, not a namespace.

| Module below `AsymmetricTensor` | Main contents | Direct first-party dependencies |
|---|---|---|
| `Model` | Six constant/positivity axioms, dimensions, `V4`/`T2`, abstract forms and scalar budgets | none |
| `MatrixAlgebra` | Matrix assembly, Clebsch wedge, comoving frame, Frobenius and Lorentzian contractions, cavitation and conditional scalar-operator relations | `Model` |
| `FieldCalculus` | Stress, `VolAvg`, fixed-chart derivatives, dynamic Clebsch fields, scoped conservation axiom, conditional momentum identities, Lie derivative and dressing | `Model`, `MatrixAlgebra` |
| `Applications.MechanicsMass` | Spatial compliance, conditional Lagrangian, defect and mass relations | `Model`, `MatrixAlgebra` |
| `Applications.Electromagnetism` | Electromagnetic component identities, planar scalar eigenvalue relations and cavitation limits | `Model`, `MatrixAlgebra` |
| `Applications.Geometry` | Frame relations, galactic algebra and conditional connection identities | `Model`, `FieldCalculus` |
| `Applications.WavesForces` | Wave/abstract-form identities, pressure and scaled force relations | `Model` |
| `Applications.Optics` | Redshift and pointwise refraction, natural-log magnitude identities | `Model` |
| `FutureTargets` | Section 16 algebraic corollaries and additional dimensional identities | `Model`, `MatrixAlgebra`, `Applications.Electromagnetism`, `Applications.WavesForces` |

For example:

```lean
import AsymmetricTensor.MatrixAlgebra

example (U : AsymmetricTensor.T2) :
    U = AsymmetricTensor.symPart U + AsymmetricTensor.antiPart U :=
  AsymmetricTensor.matrix_decomposition U
```

`quadratic_gravitational_lagrangian_trace` lives in `FieldCalculus`, with its
`I_2_vac` dependency. Its statement and proof tokens are unchanged from the raw
author source. Keeping it in `MatrixAlgebra` would require a forward dependency
on `FieldCalculus`, which itself uses the matrix definitions.

## Public API and naming conventions

Production files use Lean 4.35's module system, the author's Apache-2.0 copyright
header, explicit `public import`s, `@[expose] public section`, and
`set_option autoImplicit false`. Keep attribution and manuscript licensing intact.
The broad `Mathlib.Tactic` import remains; the current optical module does not
import an interval-integral implementation or expose the old finite-path API.

Preserve existing scientific notation and public names during a layout repair.
Use descriptive `lowerCamelCase` for new generic definitions, `UpperCamelCase`
for types, and `snake_case` for theorems. A theorem name should not upgrade
conditional algebra into a completed physical derivation. An intentional API
change needs a migration note and tests of changed assumptions and boundaries.
Add docstrings explaining objects, domains, and nonzero/positivity hypotheses.

[Mathlib style](https://leanprover-community.github.io/contribute/style.html) and
[naming conventions](https://leanprover-community.github.io/contribute/naming.html)
are useful reference points; this prototype does not claim full Mathlib admission.

## Style and import/context guards

`linter.unusedSectionVars` is enabled in all implementation modules. The current
style policy has no declaration-local suppression exceptions. The five exceptions
and 189-line baseline recorded for the older split are not current measurements.

New or edited production lines should fit within 100 characters.
`scripts/lean-style-baseline.json` records the exact text and multiplicity of
inherited long lines. Removing an inherited line is allowed; a new or changed
overlong line is not. Wrap touched lines rather than automatically refreshing the
baseline. `check_lean_style.py` also checks headers, module/public-import directives,
whitespace, linter settings, and reachability of every production module.

`check_module_context.py` checks the reviewed first-party import and
`variable`/`include`/`omit` inventories in `module-context-baseline.json`.
It supports line-leading, single-line commands, ignores comments and strings,
and preserves inventory order. It does not track section boundaries or command
positions relative to declarations. It neither parses arbitrary Lean nor proves
source or type preservation. The aggregate runs the context and style guards
through their acceptance/rejection tests as well as the actual build.

## Compatibility checks

This repair targets PR #70's `integrate/v4.5` branch at integration head
`10158f3b5336ca15a78d98221c5531dd55a578b5`. The author baseline is raw v4.5 commit
`5a84e0c52b71295a678dcc1c50f80d430e5475f2`, whose monolithic Lean source has SHA-256
`7edb09326bcb05c4444645cc1ec645c238dd509b77ca96e7f791bba33728b136`.
The repair preserves the preceding import fixes and unchanged trace-theorem
relocation, then restores twelve remaining section-context identifiers. The
reviewed context baseline also retains the existing unused Matrix Forms/wedge
context and direct FutureTargets-to-MatrixAlgebra import; compiled API comparison
checks that these inherited details do not change authored declaration types.

The bounded source comparison retains all **377 inventoried named declarations**
and **54 declaration docstrings**, up to whitespace in docstrings. This parser
covers the repository's supported `def`/`abbrev`/`opaque`/`axiom`/`lemma`/`theorem`/
`alias` syntax; it does not inventory structures, instances, every generated
declaration, or surrounding section context. Do not interpret 377 as the full
compiled declaration count.

Use a separate reference checkout containing the author's monolith as
`AsymmetricTensor.lean`, with no stale split source directory, the committed
pins, and an independently completed reference build:

```sh
python3 scripts/check_module_source.py /path/to/author-reference-checkout
python3 scripts/check_public_api.py /path/to/built-author-reference-checkout
bash scripts/verify.sh
git diff --check
```

The elaborated API comparison retains full types, binder names/kinds/order,
constant references and universe parameters after normalizing binder hygiene and
metadata. Identical declaration tokens alone cannot establish this: section
variables can change a declaration's parameters without changing its body text.
A whole-type regression for `isochoric_velocity_scaling` specifically guards
its inherited argument order.

These are separate checks: source-token/docstring preservation, elaborated API
compatibility, and whole-production proof completeness. They do not assert
byte-identical compiled proof terms or empirical validity. Historical comparisons
of 304 declarations and 78 docstrings describe the older library only. See
[verification](verification.md#current-validation-boundary) for the exact-head
validation boundary and [regression coverage](regression-coverage.md) for semantic changes
from that older API.
