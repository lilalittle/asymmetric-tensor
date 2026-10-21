---
name: binyamin-ingest
description: Review and integrate Binyamin's asymmetric-tensor author uploads while preserving exact source, authorship, mathematical contracts, and strict stable verification. Use for new drops, source review, or an approved draft's promotion.
---

# Binyamin ingest

Deliver a traceable author-source review and, when approved, a verified integration
into the stable library. East stewards the outcome. Use tools and independent
reviewers capable of the work; no particular machine, account, installation,
publisher, or execution client is required.
For status-only or focused repair requests, perform the relevant checks below
without expanding the task into publication, full ingestion or promotion.

Read [CONTRIBUTING](../../../CONTRIBUTING.md) for the author/stable boundary and
scientific contracts. Use the current repository instructions and committed pins.
This skill grants no security/access changes, purchases, or paid actions. Follow
the task's publication and merge authority; a draft-only task stays draft.

## Anchor the source once

Review an existing versioned author upload **in place at an immutable commit**.
For an external drop, preserve the exact received bytes and source locator/revision
(including the selected document tab, when relevant) in a versioned upload before
review. Verify extraction against the source, not merely plausible line counts.
Keep existing author commit history; credit author content to the verified author
identity and mechanical changes to their actual contributor. Do not invent identity
metadata or attribute steward repairs to the author.
Preserve line origin through copies and splits. Before acceptance, verify blame
on representative authored, repaired and genuinely new lines using the
[source-provenance procedure](../../../docs/source-provenance.md); retain the
original history and report tracing exceptions. Ignore only reviewed, wholly
mechanical commits, never mixed or novel content.
Check original path/line content for repaired and restored lines; a matching
author name or a "mechanical" commit label alone is not provenance evidence.

Use one durable source-review record in an existing relevant PR or issue (create
one if needed within the task's authority). Record:

- Source commit, path, Git blob and SHA-256, source provenance and prior version.
- Review base, prior findings, changed declarations/contracts, and diagnostic links.
- Independent reviewer, exact reviewed source, verdict, surviving blockers and
  author decisions; later link the separate integration PR and its exact head/tree.

Do not create a duplicate root-copy PR: replacing the stable umbrella merely to
review a draft needlessly breaks stable CI. A disposable monolithic checkout for
reference builds is still useful; it is not a second publication or review record.
An authoring file may evolve, but the reviewed snapshot must remain retrievable.
New bytes require a new pinned revision and a review of the delta and carried
findings. Preserve the historical reviews [#86](https://github.com/lilalittle/asymmetric-tensor/pull/86)
and [#87](https://github.com/lilalittle/asymmetric-tensor/pull/87); their unresolved
semantic findings survive compilation, newer uploads, and workflow migration.

## Obtain an independent source verdict

Have **Astra** independently review the pinned source: challenge assumptions,
axioms, proof holes, APIs and scientific claims; test counterexamples; then try
to refute each proposed finding before returning an evidence-backed **APPROVE**
or **REQUEST_CHANGES**. Keep the review manifest and prosecution/defense evidence;
publish only the supported verdict and relevant evidence, without private paths
or internal notes. Give the reviewer the actual source and previous findings,
not a desired conclusion. If independent Astra review is unavailable, record the
blocker rather than substituting the implementer's self-review.

Unresolved semantic blockers stop promotion. Intended assumptions, physical-model
choices, changed conclusions and proof obligations belong to the author. Obtain
explicit author approval of the exact semantic change and renew the source review;
do not manufacture a bridge, weaken a statement or add axioms/`sorry` to force green.
Approval permits integration work within existing authority; it is not merge evidence.

Minor mechanical syntax/reference repairs, including author Lean or TeX files,
may proceed without waiting for promotion approval when meaning, assumptions and
proof requirements are unchanged. Retain
the original snapshot, make a small attributed patch, run relevant compiler/reference
checks, and report it briefly. Ambiguous repairs need an author decision. A repair
neither clears unrelated semantic blockers nor makes an unchanged PDF verified.

## Integrate the approved source faithfully

Start a separate integration branch/PR from freshly fetched main. Pin the approved
source and compare it with both the preceding source and current stable library.
Reassess previous repairs against current code; preserve their purpose without
blindly replaying patches or rebuilding an obsolete fixed module layout.

Preserve declarations, docstrings, imports, section-variable context and public
APIs unless the exact change has author approval. Keep source import/copy history
distinct from formatting, modularization and repairs. Update affected tests,
module/roadmap documentation and inventories; do not refresh proof baselines just
to silence failures. [Module compatibility and dependency guidance](../../../docs/modules.md#compatibility-checks)
records the maintained compiler/context and import-cycle lessons.

Compare source tokens **and full elaborated types** against a separately built
reference of the pinned source with the same dependency pins. The existing
comparators cover bounded named declarations, not every structure, constructor,
projection, instance or generated API. Explicitly inventory and compare those
affected APIs and add elaborated call-site/migration regressions; matching scanner
counts is insufficient. For example, `UnitDim.L/V/S` becoming `K/Omega/E` needs an
explicit migration contract. Compare source-to-integration fidelity separately
from intentional prior-stable-to-new-source changes. Document any approved delta
and reference repair; never silently alter the baseline to make comparison pass.

## Verify the candidate and completion

Use the [verification contract](../../../docs/verification.md) and
[regression coverage](../../../docs/regression-coverage.md), not a copied command
inventory or historical green run. Run `bash scripts/verify.sh`, source/reference
API comparisons, affected migration checks and `git diff --check`. The complete
strict stable gate includes proof completeness, declared and transitive axiom
policy, context/style/source-boundary guards and all regressions. `lake build`
alone is insufficient. Report unavailable checks as unverified.

Keep draft diagnostics visible in their separate advisory lane. Report compiler
failures/timeouts with logs; distinguish them from missing reports, toolchain,
lock-file or other infrastructure failures. An advisory failure alone does not
fail an unchanged stable library or authorize promotion. COMPILED is neither proof
completeness, API compatibility nor empirical validation.

Obtain **independent Astra final integration review** of the exact candidate
head/tree, source mapping, approved changes and full verification evidence. Before
any authorized merge, re-fetch base and head, reconcile concurrent work without
discarding it, rerun affected checks plus the full stable gate on the reconciled
candidate, and renew final review when the reviewed candidate changes. Require
successful hosted CI for that exact head with no failing required checks and
valid visible diagnostics; older-head results do not transfer.

When merge is authorized, preserve author/integration history (no squash), verify
the resulting main commit and hosted checks after merge, and report the merge SHA,
review/check links and remaining gaps. Pending or failed post-merge verification
is not completion. Update relevant issue status only with evidence and authority;
do not close scientific or publication obligations merely because code compiles.
