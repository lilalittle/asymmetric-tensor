# The particular promise made by each PR

Scope: the live intent contract for each PR. This is the evergreen rule for instances, not an instance itself. Instances live in their PR threads, not in an accumulating directory of per-PR OK files.

### contract-01
Each PR contract identifies its intended outcome, explicit non-goals, affected surfaces, delivery stage, applicable shared assertion references, and acceptance criteria specific to the change. It links any source issue without assuming that a PR's narrower delivery stage completes the whole issue.

Check: contract and source issue. A code-only, documentation-only, author-upload, source-integration, or paper-publication change can each have a different legitimate contract.

### contract-02
Each contract has one canonical PR-thread location and a visible revision history or supersession link. It pins the applicable spec revision and candidate head; it references shared rules instead of copying their text or silently weakening them.

Check: contract permalink, version/head, and inheritance links. A material change to intent, premises, base, or head invalidates affected acceptance evidence until rechecked or explicitly carried forward with a dependency-based justification.

### contract-03
Each acceptance criterion has an identified evidence method and decision authority. It is clear whether it can be checked automatically, needs human review, or has no implemented check yet. A criterion without evidence is not declared satisfied.

Check: criterion-level results and owners. Machine checkability is not a prerequisite for a meaningful scientific or editorial criterion.

### contract-04
A PR's final disposition accounts for every criterion as accepted, not applicable with reason, deferred to a linked canonical obligation, or explicitly not completed. Any changed promise is acknowledged by the responsible authority rather than retroactively described as the original promise.

Check: closure/merge record and residual links. Deferral does not turn a failed mandatory criterion into a pass.
