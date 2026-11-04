# Author authority and source preservation

Scope: the repository root. This file owns permission and author-intent boundaries, not technical acceptance. Evidence rules live in [evidence](evidence.ok.md).

### authority-01
Every change made by someone other than Binyamin to an author-controlled raw Lean upload or manuscript LaTeX source has recorded Binyamin approval covering that change. A mechanical edit is not an exemption, and an approval for one passage is not approval for unrelated scientific changes.

Check: human approval linked to the affected source revision and change scope. A verified Binyamin-authored submission approves that exact proposed source delta, not an agent rewrite or a later materially different delta. Git author attribution alone is not verification of who submitted or approved a change. A proposed patch may be reviewed without modifying the protected original.

### authority-02
Every integration described as source-preserving retains the immutable raw author source and attribution, with comparison evidence appropriate to the artifact. A Lean integration has both a bounded source comparison and an independently built elaborated-API comparison against its reference. Any deliberate exception is named, justified, and separately approved rather than absorbed into a silently refreshed baseline.

Check: source/reference hashes, comparison reports, and approval for exceptions. The exact capabilities and limits of each comparator are disclosed.

### authority-03
A scientific convention, physical interpretation, or scope withdrawal attributed to the author is traceable to the author's decision. An agent's mathematical analysis, a passing compiler, and a maintainer's merge permission do not substitute for that decision.

Check: author decision and retained-claim text. A blocked author choice can coexist with completed technical analysis.

### authority-04
Reconciliation has no greater write, merge, publication, or notification authority than the permissions granted for the specific run. A spec, event, issue comment, or third-party request does not itself grant that authority.

Check: run permissions and action log. Read-only findings remain useful even when a mutation is not authorized.
