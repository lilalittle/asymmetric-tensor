# An evergreen contract for asymmetric-tensor

## Recommendation

Keep ten small OK files, grouped into three concerns. They contain 45 binary, testable assertions, not a backlog. Each assertion has one owning file; other files link to it.

**Work and change acceptance**
- `.ok/issues.ok.md`: the ideal main-branch work record.
- `.ok/pull-requests.ok.md`: shared PR readiness, review and final disposition.
- `.ok/pr-contracts.ok.md`: what a particular PR must promise. Each actual instance stays in the PR thread, using `templates/pr-contract.md`; no permanent `.ok/pr-77.ok.md` forest.

**Artifact contracts**
- `.ok/lean.ok.md`: stable proof/API contracts and the isolated authoring lane.
- `.ok/documentation.ok.md`: usable and accurate current/historical docs, reproduction and citations.
- `.ok/manuscript-source.ok.md`: source buildability, internal consistency and reliable references.
- `.ok/paper-artifacts.ok.md`: artifact identity, source/publication provenance, currency and reader-visible integrity.

**Cross-cutting boundaries the initial surface split misses**
- `.ok/authority.ok.md`: author decisions, protected-source edits, source-preserving integration and permission limits.
- `.ok/evidence.ok.md`: revision-specific evidence and the limits of mathematical/scientific claims.
- `.ok/reconciliation.ok.md`: canonical gap ownership, freshness, idempotency and valid resolution.

The shared PR file answers “may this change be accepted?” The contract file answers “what exactly did this change promise?” The instance answers that question for one PR and has that PR's lifetime. This is the one place where “a spec for every PR” should not mean another evergreen file for every PR.

## Scope and DotOK compatibility

FOCUS_ROOT is the root directory of `lilalittle/asymmetric-tensor`, not the user's other projects. OK_DIR is `<FOCUS_ROOT>/.ok`; TASKS_DIR is `<FOCUS_ROOT>/.tasks`.

The user explicitly requested Markdown `.ok/*.ok.md`, so DotOK's default-to-canvas capture rule does not apply. DotOK requires binary Markdown assertions but prescribes no Markdown frontmatter schema; these files therefore use ordinary headings and stable heading IDs rather than an invented `.ok` schema.

Important distinctions:
- **Ideal/goal:** what should remain true, owned by an OK assertion. A new one-off desired capability may instead be a scoped issue goal.
- **Observation:** a dated comparison of an identified state with an assertion; report pass, fail or unknown, with applicability separately recorded.
- **Gap:** a supported mismatch, or explicitly a missing-evidence gap rather than a claim the mathematics is false.
- **Work order:** a bounded action and its acceptance test, not the goal itself.
- **Hold:** a reason execution or acceptance must wait, such as author approval or missing infrastructure. “Hold” is descriptive, not a new DotOK task status.
- **Event:** a reason to observe again, not an assertion that anything is wrong and not permission to act.

GitHub-canonical work is an explicit project adapter to native DotOK. Native DotOK defaults to local `.tasks` files; the user's instruction instead makes PR threads and main-branch issues authoritative. `.tasks` can hold disposable, regenerated execution mirrors and evidence snapshots, never a second durable backlog. Archiving them does not archive or close GitHub commitments. The runbook defines this adaptation and preserves the exact native task YAML enums and `blocked_by` linkage.

## Why these boundaries survive Hyperslice

We started with the whole project, then tested independent binary cuts rather than sorting file extensions:

1. **Ideal versus observation.** A rule survives future revisions; “PR 77 has two blockers” does not. Put the latter in a dated example or live thread.
2. **Main-applicable versus candidate-only.** A defect found in PR review may already be on main. Route by reproduced scope, not discovery location. Unknown applicability is an observation limit, not a third kind of ideal.
3. **Author-controlled versus integration-controlled.** Two `.lean` files can have opposite valid failure policies: a broken raw draft is permitted in its advisory lane while broken stable code is not. Authority cuts across Lean and TeX.
4. **Evidence sufficient versus insufficient.** A theorem may be true but not proved here. Conversely a completed proof can establish only an assumed implication. Unknown is not false and green is not empirical validation.
5. **Source intent versus delivered artifact.** Correct author text, merged TeX, a compiled review PDF and a published PDF are four distinct deliverables. This justifies separate source and paper contracts.
6. **Current versus historical evidence.** An old successful result can be valuable and honest, yet insufficient for today's head. “Old” is not inherently bad; falsely advertised currency is.
7. **Shared acceptance versus particular intent.** Repeating boilerplate in every PR creates drift; omitting a PR's unique purpose makes a green check meaningless. Inheritance plus a short instance handles both.
8. **Capability versus authority.** Being able to fix a formula is not permission to choose the author's physics or edit protected source.

Adversarial inversions: a red draft check can be healthy; an open issue can be healthy; a closed issue can conceal unresolved main work; a successful TeX build can still contain duplicate equation numbers; a valid old PDF need not match current TeX. Each defeats a simplistic “all green/all closed/all files match” ideal.

These are separable dimensions, not a demand for every combination to become a directory. Ten small files preserve the user's discoverable surfaces while giving authority, evidence and reconciliation one owner each. They can be combined later without changing the assertions if navigation proves too granular.

## What is already checked, and what would be new

This proposal was grounded in an immutable source snapshot at `d2931e8dcdcfc6de768eda5a2c272cab1abf0e04`, and fresh issue/PR reads on 2026-10-20. It does not claim a new full Lean or TeX verification run.

Existing automated evidence includes the stable aggregate `scripts/verify.sh`, source/import isolation checks, proof and axiom audits, current regressions, deliberate negative tests, and separately reported advisory author-upload diagnostics. Source-preservation and built-reference API comparisons are additional integration evidence, not automatically equivalent to the aggregate. Hosted workflow presence does not establish which branch-protection gates are enforced.

Currently human-reviewed or only partly automated: whether a theorem matches a manuscript claim; whether a changed premise needs author approval; whether an issue's accepted outcome actually closes its full scope; rendered PDF usability; equation/reference integrity across build outputs.

Proposed new capabilities, not implemented by these files: event-driven reconciliation, canonical gap indexing/dedupe, criterion/evidence tracking, source-to-PDF build manifests, automatic citation/link drift checks, and any new required CI or branch-protection gate. Installing a skill or writing a razor does not create those capabilities.

## Accepted policy

**Source/PDF lag:** source may move ahead of the published PDF, as [confirmed in PR #82](https://github.com/lilalittle/asymmetric-tensor/pull/82#issuecomment-6296369344). The artifact relationship must remain explicit, and any accepted publication obligation remains visible. A source correction is not described as published until the intended PDF contains it. See `paper-03`.

## Remaining implementation choices

1. **Enforcement rollout:** should these begin as advisory reviews using existing checks, then promote reliable automated razors to required gates? Recommendation: yes; scientific/editorial judgments stay explicitly human-reviewed.
2. **Notification budget:** when work is automated, what cadence is useful for non-urgent drift and consolidated author questions? Recommendation: event-driven material updates, one consolidated human-question digest per day, and no routine “still unchanged” comments. No schedule is installed by these files.

There is no need to ask where the canonical tasks live: the user already chose GitHub issues for main and PR threads for PR-local work. Likewise, raw-author edit authority is not being reopened as a new preference.

See `reconciliation-runbook.md` for events, routing and lifecycle; `examples/2026-10-20.md` for #27, #44 and #77; and `templates/` for the lightweight records.
