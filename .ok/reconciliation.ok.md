# Reconciliation integrity

Draft for discussion. Not an activated policy or authorization to act.

Scope: the process that compares these ideals to observed repository state. Event definitions and execution steps belong to the companion runbook, not in the ideal-state files.

### reconcile-01
Each run has exactly one declared focus root, a bounded observed revision or PR candidate, applicable spec revision, trigger, permissions and check budget. Its result says what was checked, what was not checked, and what remains unknown.

Check: run snapshot. Repository scope does not imply every check must run on every event.

### reconcile-02
Each observed gap has a stable identity, its violated assertion or explicit new goal, evidence, affected scope, canonical location, owner/unclaimed state, next action, and acceptance test. Main-branch gaps are canonical in GitHub issues; PR-local gaps and work orders are canonical in the PR thread. Applicability that is still unknown is not asserted as a main defect.

Check: canonical record and dated observation. Gap identity is independent of the latest commit hash or display equation number.

### reconcile-03
Reconciliation is idempotent and preserves valid commitments: it searches existing active/closed records before creating one, records only material changes, and never treats local task archival as permission to close or erase live GitHub work. Repeated unchanged observations produce no duplicate comments or issues.

Check: dedupe key, latest record and mutation outcome. Uncertain writes are inspected before any retry.

### reconcile-04
Every work order has a bounded deliverable and verification method, and its dependency graph is acyclic. Human blockers attach only to atomic low-level tasks, with the precise question and decision authority; parent tasks depend on those leaves. Canonical blocked work stays live when another run starts, even though its local execution mirror may be archived or marked stale during native DotOK regeneration.

Check: task links and blocker evidence. In native DotOK YAML, pending/in-progress/done/stale remain the only statuses and dependencies use blocked_by.

### reconcile-05
Every resolution is rechecked at its acceptance revision and scope. New relevant source, base, dependency, spec, author decision or artifact evidence invalidates affected prior observations until rerun or justified carry-forward; recurrence is reopened under the existing identity when the obligation is the same.

Check: current evidence and lifecycle record, including post-merge routing. Archived snapshots preserve what was true then without certifying what is true now.
