# Reconciliation runbook

The `.ok` files define desired state; this file defines when and how it is checked. No trigger grants write permission.

## 1. Start one bounded run

Pin FOCUS_ROOT to the repository root, the evaluated main commit or PR number/head/base, the spec commit, and relevant artifact/input hashes. Record the trigger, intended check scope, permissions and budget. Read all applicable assertions before deciding whether the evidence says pass, fail or unknown.

Freeze the spec revision for the run. If two assertions conflict, cite both, pause only the conflicting work and ask the responsible human for a resolution. Do not silently choose the easier rule or weaken a baseline. A proposed spec amendment is separately reviewed intent, not a repair that changes the test to pass.

A candidate's GitHub head and the tested synthetic merge revision, if any, are different identifiers; record both. Re-check head/base and canonical status immediately before any consequential write or final acceptance claim.

## 2. Events and relevant checks

These are logical event definitions, not a promise that a connector/webhook currently supports them. Implementation must verify support before enabling a trigger.

- **PR opened or marked ready:** establish/update the short intent contract; classify changed surfaces and author-controlled files; identify existing issue links; run the applicable cheap checks and acceptance plan. Draft author uploads remain in the advisory lane.
- **PR head, target branch, base, or scope changes:** invalidate only affected observations and reviews, then evaluate the new candidate. Full merge acceptance still refers to the exact current head. A bounded author's approval for unchanged content can remain applicable across unrelated changes, such as a docs-only head movement, even when whole-candidate build evidence must be refreshed. A verified Binyamin-authored submission approves its exact source delta; Git author attribution alone or an agent-generated rewrite does not establish that approval.
- **CI completion or rerun:** ingest the run ID, attempt, head/tested merge identity, result and logs; distinguish mandatory, advisory, infrastructure failure, cancellation and unknown. Do not keep posting the same failure.
- **Review or author-decision changes:** update the exact affected criterion/hold. A generic comment, unrelated approval or checkbox tick does not resolve a protected-source decision.
- **Push/merge to main:** evaluate the changed dependency closure, reconcile linked issues against the actual resulting main commit, and route surviving obligations out of a now-closed PR. Do not inherit a branch's verdict blindly.
- **Author source or companion manuscript received:** identify its provenance, compare relevant claims and open work; do not assume incorporation, promotion, or permission to edit it. Raw Lean compilation is advisory; new boundary leaks are not.
- **TeX or build-input changes:** check affected manuscript consistency, reference integrity and source-to-output claims; mark advertised source/PDF correspondence unknown or stale as evidence warrants.
- **PDF/Zenodo/release artifact changes:** verify the actual document/version/hash and affected passages, citations, licenses and linked issue acceptance. A new filename or record is not proof a particular correction is present.
- **Issue/PR closure or acceptance request:** compare each criterion with its evidence and declared delivery stage, resolve duplicates and identify residual work. A closure event is not evidence of success.
- **Spec or dependency/toolchain policy changes:** invalidate affected judgments; do not silently reinterpret historical results under new requirements.
- **Explicit audit or later agreed low-frequency drift sweep:** find gaps missed by event routes. This is optional and unscheduled; do not invent constant polling merely because ideal state is evergreen.

## 3. Observe, attribute, then route

1. Read relevant current records, including closed issues and prior PR findings, before creating anything.
2. Gather the minimum sufficient evidence. Cheap structural checks may precede expensive builds or scientific review. Missing tools/logs produce an unknown observation and a bounded evidence-acquisition action, not a fabricated code failure.
3. Compare the candidate and pinned main separately when defect origin matters.
4. Route the live record:
   - **Confirmed on main:** one canonical GitHub issue, even if discovered during a PR review. The PR links that issue and records only its own plan/acceptance impact.
   - **Candidate-only:** the PR conversation or existing inline review thread owns the gap and work order. A single contract/index comment links all live findings; do not copy every inline discussion into it.
   - **Applicability unknown during a PR review:** keep the candidate finding and diagnostic work in that PR, explicitly unresolved. Do not label it a main regression until tested.
   - **Repository-wide evidence gap found outside a PR:** an issue may own the evidence-acquisition goal, labeled as unknown evidence rather than a proven defect in mathematics.
   - **Raw draft diagnostic only:** retain the diagnostic for that exact draft; do not create a stable-library bug when isolation is working. A broken report or production leak is a different gap.
5. If a GitHub write is not authorized or fails, retain an explicitly unpublished local observation artifact and report the blocker. Do not call it captured in the canonical backlog or silently switch the durable source of truth to `.tasks`.

## 4. Stable identities and deduplication

Use a semantic key consisting of repository + owning assertion/goal + stable affected subject (including the particular manuscript/artifact identity) + failure mode. Example: `gap-tensor-manuscript-equation-destinations`, not `gap-pr77-head2c07-line683`. A source SHA, page number or equation display number belongs in evidence, not in the enduring identity. Preserve earlier aliases when a finding already has an issue ID or review marker.

Maintain event-delivery idempotency separately from gap identity: the same event can be retried, and different events can discover the same gap. Before posting, search the canonical issue/PR index and closed history; update an existing record when the obligation matches. A different acceptance obligation gets a new linked identity, not a misleading reopen.

One gap can have successive observations and several work orders, but only one canonical live location. Work on an existing main issue inside a PR is a PR-local implementation work order linked to the issue, not a second copy of the issue's mutable gap state.

When moving a gap from PR to main: first verify or create/reuse the destination issue, then link it from the old record and mark the former PR location as historical/redirected. Preserve the stable gap identity. Do not declare transfer complete until the destination is verified. If a write outcome is uncertain, read the target before retrying.

## 5. Work orders and human holds

Most contributors need only a short outcome, owner, next action, dependencies and evidence checklist in the canonical thread. Native YAML is optional serialization for agents, not mandatory user paperwork.

A work order has one bounded deliverable, applicable OK/gap references, authority, dependencies, expected verification and a result link. Split only when work has independently useful acceptance or a different owner/authority. Use the native hierarchy as needed: high outcome blocked by medium components; medium components blocked by low atomic actions. Do not invent extra tasks solely to fill three levels.

The optional YAML schema is exactly DotOK's:

```yaml
---
id: task-example-unique-slug
level: low
status: pending
blocked_by: []
ok_refs: ["manuscript-source.ok.md#tex-03"]
gap_refs: ["gap-tensor-tex-equation-destinations"]
---
```

`id`, `level`, `status`, and `blocked_by` retain native meanings. `ok_refs` and `gap_refs` are optional. Valid statuses are only `pending`, `in-progress`, `done`, `stale`; a blocked task remains pending or in-progress and identifies blockers in `blocked_by`. Owner, canonical URL, head/base, evidence and next action stay in the Markdown body, not invented required schema fields.

Only low-level tasks may directly depend on `task-needs-attention-YYYY-MM-DD`. Exactly one derived daily file at `.tasks/blocked-by-user/needs-attention-YYYY-MM-DD.md` consolidates questions and links their canonical issue/PR locations. The human-facing checklist is a digest, not a second task database. An answer resolves only its particular question; verified applicable approval is required before removing that dependency. The agent checking a box does not create author approval.

A completed technical task does not automatically close its wider gap. Conversely a closed GitHub issue does not prove every mirrored task succeeded: the closure may be duplicate, declined, or deliberately narrowed. Record the actual disposition.

## 6. Native local scratch without a second backlog

If `.tasks` is used, acquire one reconciliation lock per FOCUS_ROOT. Serialize runs at the same root so a main run cannot archive a PR run's active tasks. Coalesce queued events for the same subject to the latest revision while preserving any unresolved material decision.

- `.tasks/artifacts/gaps-snapshot-<UTC timestamp>-<context>.md` contains immutable point-in-time observations, with canonical links and tested identities.
- `.tasks/artifacts/reconciliation-<UTC timestamp>-<context>.canvas` is a required fresh generated graph for every full native OODA run, using the installed JSON Canvas skill. It is not a source of new acceptance rules.
- `.tasks/*.md` contains only current execution mirrors using native task YAML. Each mirror names its canonical GitHub source in the body.
- `.tasks/archive/<run>/` keeps stale/completed local execution plans. A new loop archives local plans, rereads GitHub, then regenerates only still-relevant work. Archival is not a GitHub state transition.
- `.tasks/blocked-by-user/` contains only the consolidated daily view described above.

No committed `ASKS.md`, `GAPS.md`, or per-PR backlog is introduced. A local evidence snapshot is not a centralized current gaps database. Canonical GitHub records win if mirrors disagree; conflicting or newer human instructions are reconciled before action.

## 7. Freshness and lifecycle

Observations refer to immutable tested subjects. Head/base movement, relevant dependencies, a changed spec, new source/paper artifacts or an author decision can make an observation stale. Keep the old result as historical evidence; do not change “passed at A” into “failed at A” because B appeared.

Carry-forward is possible only when the relevant complete dependency set is shown unchanged and the report says it is reused evidence, not a new run. Whole-candidate hosted gates still follow their exact-revision requirements. Inaccessible or expired evidence becomes unknown, not automatically false.

Before resolution, rerun the acceptance test or inspect valid scoped evidence on the acceptance revision. If unchanged obligations recur, reopen/reuse their canonical record. If the desired outcome changes, record an authorized scope decision, preserve old evidence, and link any residual obligation. Do not close merely because a task aged out, a graph was regenerated, or a PR merged.

After a merge, confirm the fix is in the actual resulting main and examine unresolved PR findings. Main-applicable residuals belong in existing/new issues; candidate-only discarded alternatives can retire. After an unmerged closure, do not promote nonexistent candidate regressions to main, but retain independently demonstrated main defects in their issues.

## 8. Noise and resource budget

Suggested initial mode: advisory, event-driven and delta-only. Coalesce rapid updates; reuse equivalent evidence where justified; run expensive builds only for relevant input changes, readiness/acceptance gates, or explicit audit. Stop a check at its declared timeout and report unknown/infrastructure failure rather than cycling forever.

Before enabling automation, agree on numerical limits for run time, concurrent jobs, retries and notification frequency. Per-run limits are recorded in its snapshot. Existing CI limits are evidence about today's implementation, not new limits silently imposed by this proposal.

Update one canonical summary when a blocker appears/resolves, acceptance materially changes, ownership is needed, or an event changes what the user should do. Do not append “still failing” comments for unchanged evidence. Consolidate non-urgent author questions into the single daily digest; raise a genuinely blocking/time-sensitive decision promptly. Do not automatically assign humans, merge, publish, close issues or post external comments unless that action is authorized for the run.
