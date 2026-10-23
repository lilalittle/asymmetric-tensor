# Shared pull-request acceptance

Scope: every proposed repository change. This file owns shared readiness and merge acceptance; [PR contracts](pr-contracts.ok.md) owns the change-specific promise.

### prs-01
Every PR marked ready for review has a current, discoverable intent contract that references the applicable shared OK assertions and adds only its change-specific outcome, exclusions, and acceptance criteria.

Check: the PR body or its single linked contract comment. Draft research uploads may remain exploratory, provided that status and their current limits are explicit.

### prs-02
A PR reported ready to merge has passing current evidence for its applicable mandatory checks and explicit approvals for its protected changes. Advisory diagnostics and unknown checks are named separately; their success is not used to replace a required gate, and a configured workflow is not treated as a completed run.

Check: exact candidate head, current target/base relevance, required-check results, protected-change approvals, and disposition of blocking findings. The applicable checks must be verified against the current repository configuration; this contract does not infer which checks GitHub branch protection enforces.

### prs-03
A blocking PR finding identifies an applicable acceptance violation, whether it is introduced, inherited or of unknown origin, its evidence, severity rationale, and a testable remedy or author decision. Inherited main-branch defects are linked to their issue and are not silently added to this PR's scope unless the change depends on fixing them or the reviewer explicitly explains the new risk.

Check: compare base and candidate. An inherited mandatory gate failure can block acceptance without silently making its repair part of the PR's promise. “Not introduced here” does not excuse a new claim that relies on the inherited defect.

### prs-04
Every PR-local gap and work order is canonical in that PR's conversation or review thread, with one index to the live items. Repeated review runs update or supersede that index, and a resolved review thread is not by itself evidence that the underlying gap passed acceptance.

Check: thread permalinks and current dispositions. Inline discussion remains evidence; it is not duplicated into an independently managed issue merely to satisfy a template.

### prs-05
Every merged or abandoned PR leaves a truthful disposition for its contract and findings. Any unresolved obligation that still applies to main has a canonical issue linked from the PR; only an explicit authorized withdrawal can remove the obligation, while deferral cannot. Candidate-only problems from an abandoned change are not misreported as main defects.

Check: merge or closure reconciliation against the actual resulting main revision. PR merge is an event, not automatic proof that every linked issue's acceptance criteria were met.
