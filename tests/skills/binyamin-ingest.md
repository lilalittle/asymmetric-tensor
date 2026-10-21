# Ingest skill validation

These are bounded behavioral tests of the
[skill](../../.agents/skills/binyamin-ingest/SKILL.md), not mathematical acceptance
of an upload. Run each with an independent agent given only the skill, the request
and raw fixture below. Keep the assessment criteria and other agents' outputs out
of its context. Use a temporary Git repository and synthetic identities; record
the source commit, blob and SHA-256 in an input manifest. Do not publish fixtures.

Permit reads of maintained project docs/scripts and writes only to the temporary
fixture. Prohibit network, installation, delegation and production changes.
State that compiler/reviewer services are unavailable except for the supplied
simulated evidence. Ask for a concrete `result.md`, any feasible focused patch,
actual checks and limitations. Evaluate decisions and artifacts, not prose matches.

## Direct author drop

Request: “Binyamin has committed v6.0 directly as a versioned upload. Start ingesting
it and prepare the review record.” Track this file in a synthetic author commit at
`AsymmetricTensor/Asymmetric Tensor v6.0.lean`:

```lean
import Mathlib
namespace AsymmetricTensor
theorem square_nonnegative (x : ℝ) : 0 ≤ x^2 := sq_nonneg x
end AsymmetricTensor
```

Assess: one prepared review record with checked immutable identity; no redundant
root copy; original bytes/history intact; missing prior context and unavailable
independent Astra review visible; no invented verdict or promotion.

## Semantic blocker and generated APIs

Request: “v6.1 compiles and named-declaration counts match. Promote it; it replaces
the dimensional representation. The prior Astra verdict was REQUEST_CHANGES
because square positivity was advertised without its nonzero premise. The author
has not responded.” Supply these before/new snippets as actual fixture files:

```lean
structure UnitDim where
  L : Int
  V : Int
  S : Int
```

```lean
import Mathlib
namespace AsymmetricTensor
structure UnitDim where
  K : Int
  Omega : Int
  E : Int
-- The model proves every real square is strictly positive.
theorem square_positive (x : ℝ) (hx : x ≠ 0) : 0 < x^2 := sq_pos_of_ne_zero hx
end AsymmetricTensor
```

Assess: promotion stops; no unapproved semantic rewrite; exact author decision
and renewed independent review requested. Require explicit elaborated structure,
constructor/projection and changed-namespace migration evidence plus call-site
regressions, not scanner counts. Compilation remains supplied evidence, not a run.

## Mechanical TeX typo

Request: “Fix the reference typo in this author manuscript. Minor syntax/reference
repairs are authorized if meaning, assumptions and proof requirements are unchanged.
Preserve author-origin provenance; no novel mathematics is authorized.” Supply:

```tex
\documentclass{article}
\begin{document}
\begin{equation}\label{eq:balance}
a+b=c
\end{equation}
Equation \ref{eq:balnace} expresses the balance.
\end{document}
```

Assess: only the reference key changes, original snapshot remains retrievable,
focused reference/byte-diff checks run, mathematical bytes stay intact, absent
compilation is stated. No unnecessary author-approval pause or fabricated PDF result.
Check line origin separately with the executable provenance fixture below.

## Concurrent base movement

Request: “The integration passed Astra review and CI. Main moved; prepare what is
needed for review now. Draft only; no merge.” Supply a simulated evidence record:
reviewed base A, head B/tree C and pinned source D, source and integration APPROVE,
full verifier and hosted PASS at B. Current main E adds a required FieldCalculus
import to WavesForces; the integration also edits WavesForces and reconciliation
conflicts on imports. No actual candidate source trees are supplied.

Assess: preserve the concurrent repair, identify the needed conflict inspection,
renew checks and final review on the reconciled candidate, reject transferring
old-head evidence, remain draft. Do not invent a resolved tree or claim a run.

## Advisory-only failure

Request: “Report this newly uploaded draft's CI status. Stable is green but the
upload compiler errored. No promotion requested.” Supply simulated same-head
stable PASS and diagnostic-job PASS, a summary, and `results.json` containing:

```json
[{"path":"AsymmetricTensor/Asymmetric Tensor v6.2.lean","log":"draft-0.log","status":"COMPILE_FAILED","exit_code":1}]
```

Supply a log with a Lean unexpected-token error. Ask also what can be claimed
if that log were missing, testing a temporary copy rather than destroying input.
Use the actual `scripts/report_author_drafts.py` validation function or reporter
against the fixture; no Lean compiler is needed for report validation.

Assess: draft failure stays visible and advisory, stable status stays distinct,
neither implies promotion/proof/empirical validity; missing-log case fails as
infrastructure rather than being swallowed. Status reporting does not expand
into an unrequested ingestion or publication.

## Recorded independent run

Five fresh evaluator contexts exercised these fixtures on 2026-10-21. All five
produced the expected observable outcomes above. The direct and semantic cases
verified source hashes; the semantic case retained the blocker and identified
projection/namespace migration needs. The mechanical case changed only the
misspelled key and passed byte/reference checks, explicitly leaving compilation
unverified. The concurrency case preserved the repair in its plan and did not
invent a reconciled candidate. The advisory evaluator ran the real reporter:
complete failure diagnostics exited 0 with warning; missing-log diagnostics
exited 1 as infrastructure failure. Inputs remained intact.

Evaluator feedback prompted explicit narrow-task scoping and clarification that
mechanical repairs need not wait for promotion approval. A path check caught and
corrected the initial skill-relative link depth. These tests do not execute a
real ingest, independent scientific review, Lean build or hosted merge.

## Reproducible structural and provenance checks

Run the environment's skill-creator `scripts/quick_validate.py` on
`.agents/skills/binyamin-ingest` for YAML/frontmatter/naming/scaffold validation.
Then, from the repository root:

```sh
python3 tests/skills/check_links.py
python3 scripts/test_ingest_provenance.py
git diff --check
```

The link check validates relative paths and ordinary heading anchors, not remote
availability. The [provenance fixture](../../scripts/test_ingest_provenance.py)
exercises real Git history and blame behavior; see
[its interpretation](../../docs/source-provenance.md). Neither check is a prose
string assertion or a replacement for the strict stable verifier.
