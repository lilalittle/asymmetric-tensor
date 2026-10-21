# Source and line provenance

An integration must retain Binyamin's source commits and make his mathematical
lines traceable to that source. Credit genuinely new contributor text to its
actual author. Commit author and committer are different roles; neither should
be falsified to make a blame display look better.

Keep the exact author upload and its commit/blob/hash record. Preserve its history
when merging; do not squash or reconstruct it under the integrator's identity.
Separate unchanged copies, moves and deletion-only splits from formatting,
mechanical repairs and genuinely new content. New wrappers, tests, documentation
and mathematical changes are not automatically author content. A byte-identical
author-content copy may retain that author's attribution with the actual steward
as committer; verify it contains no new steward-authored lines. Preserve the
original source commit as well, not just the display name on a later copy.

## Verify attribution on the candidate

For each affected author block, record the original commit/path/line range and
its destination. Check the actual candidate's history and blame, including changed
lines, module boundaries and genuinely new lines. The acceptance evidence must
show author-origin lines tracing to Binyamin and new contributor lines remaining
with that contributor; unexplained reassignment needs correction or an explicit
source mapping and limitation. Do not claim success from a sample that omits the
transformed lines.

From the repository root, inspect the ordinary view and then the provenance view:

```sh
git blame HEAD -- path/to/module.lean
git -c blame.markIgnoredLines=true -c blame.markUnblamableLines=true \
  blame -w -M -C -C -C --ignore-revs-file .git-blame-ignore-revs \
  HEAD -- path/to/module.lean
```

If no reviewed ignore file exists, omit `--ignore-revs-file` and its argument.
`-w` ignores whitespace changes; `-M` detects moved blocks within a file; repeated
`-C` extends cross-file copy detection, with three occurrences searching any
commit. These are heuristics with similarity thresholds, not proof of authorship.
Do not lower thresholds merely to obtain a preferred attribution. Use
`--line-porcelain` for machine-readable commit/author/original-filename evidence.
See `git help blame` for the installed Git's semantics.

Default blame and a hosting site's display may stop at a copy or repair commit.
An ignore file does not guarantee that every transformed line reaches the original
source. In a Git 2.49.0 experiment, unchanged copied theorem lines traced correctly,
but a later reference-spelling repair stopped at the intervening copy commit even
with that repair ignored. Keep the pinned source mapping and repair diff in such
cases; do not misattribute novel content or rewrite honest history to hide a
heuristic limitation.

## Maintain mechanical exclusions deliberately

When a reviewed, wholly mechanical commit merits exclusion, maintain its full
commit ID in a tracked `.git-blame-ignore-revs`, with a short reason and review
reference. Add the ID in a later commit; a commit cannot contain its own final ID.
Do not list mixed commits that also add wrappers, tests, explanatory text or
semantic changes. Split those changes before committing when practical. Never
bulk-ignore historical integration commits without reviewing their full diffs.
Calling a commit "mechanical" is not sufficient: verify each affected line's
original path and line content, including restored lines, before accepting an
exclusion. Separate repairs with reliable mappings from additions or restorations
that need their own attribution evidence.

An ignored revision is still in history. Git may attribute its changed lines to
nearby older lines: `?` marks reassignment through an ignored revision, and `*`
marks a line Git could not attribute elsewhere when the settings above are used.
Inspect both kinds against source evidence; a mark is not an authorship verdict.
The absence of an unblamable marker does not establish a correct mapping.
No real historical commits are added to an ignore list by this redesign.

## Real acceptance example

The [PR #88 attribution audit](https://github.com/lilalittle/asymmetric-tensor/pull/88)
tested ignoring the original manuscript-repair commit
`d2792fb4d23829054ee9847edd21f3203474ee32`. Ten inherited formula/reference lines
then traced to Binyamin's text, while the restored `\end{document}` incorrectly
traced to an unrelated historical list item. No unblamable marker appeared.
The old file contained a real terminator elsewhere; the selected original line
was nevertheless wrong. This was not a successful whole-commit exclusion.

For this class of repair, keep existing-line changes, terminator restoration and
ignore-file metadata in separate commits. Test the precise repair revision before
listing it; retain the restoration's honest change history and explicit source
mapping when tracing is ambiguous. Acceptance requires checking content and line
origin, not merely seeing the expected author's name. This example records the
original audit and does not certify a later PR head or authorize its merge.

## Reproduce the fixture

Run `python3 scripts/test_ingest_provenance.py`. It creates temporary repositories
with synthetic author/steward identities and checks that the original source
commit and blob survive a two-module split, file move, mechanical whitespace
change and separately committed steward explanation. It compares plain,
copy-aware and ignore-aware blame: copied and whitespace-repaired lines reach the
original author, while the novel explanation remains with the steward. A separate
non-whitespace reference-spelling repair exercises revision ignoring itself. Its
result distinguishes a verified original trace from an explicit tracing exception
with a retained source mapping; a passing test must not turn that exception into
a successful provenance claim. It changes no project author files and performs no
Lean or scientific verification. Repeat provenance checks on the real integration;
this small fixture does not certify arbitrary rewrites.
