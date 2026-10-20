# The stable Lean library and its authoring boundary

Draft for discussion. Not an activated policy or authorization to act.

Scope: the stable import umbrella, production modules, verification support, tests, and the boundary with raw author uploads. Source authority is owned by [authority](authority.ok.md).

### lean-01
The stable library elaborates and its applicable aggregate verifier passes with the committed toolchain and dependency locks, without verification rewriting those locks. A dependency upgrade is an explicit reviewed change, not a side effect of reproduction.

Check: exact-revision aggregate result and lock invariance. Focused tests or historical green runs are not substitutes for the aggregate.

### lean-02
The current production audit rejects transitive admitted proofs and unapproved axiom-dependency changes throughout its declared coverage, including private/generated first-party declarations. Its accepted inventory and selected exact theorem dependency contracts are reviewed inputs, never automatically learned to make a failure disappear.

Check: live completeness/dependency audit and negative regression cases that fail for the intended reason. This specifies an auditable boundary, not zero axioms or an independent proof of model consistency.

### lean-03
Raw author uploads are explicitly classified and independently diagnosed, cannot enter the stable import closure unnoticed, and do not become certified production code merely by compiling. A malformed recognized draft may fail advisory compilation while the unchanged stable library remains valid; infrastructure failures are not hidden as ordinary draft diagnostics.

Check: source-boundary inventory, import/isolation regressions, separate draft outcomes and stable checks. Filename spaces alone do not create an exemption.

### lean-04
A changed public mathematical/API contract has meaningful regression evidence for the affected quantities, hypotheses, signs, normalization, and relevant nontrivial or degenerate cases, or an explicit bounded coverage gap. Test-local recovered facts and archived tests are never described as current production APIs or executed coverage.

Check: production types, current test execution, regression report, and linked coverage gap. A source-inventory count is not independent mathematical coverage. Disclosing a gap does not waive an applicable mandatory acceptance criterion; any bounded exception requires its responsible authority's approval.

### lean-05
Promotion of a raw draft to the stable library is a separately accepted integration with the preservation evidence required by authority-02, current production audits, relevant regression disposition, and exact-candidate hosted evidence. An upload event does not itself promote the draft or refresh proof baselines.

Check: integration contract, raw-reference identity, comparison/audit reports, and accepted exceptions.
