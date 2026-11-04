# GitHub issues as the main-branch work record

Scope: durable goals and gaps affecting the main branch, plus repository-wide research work. PR-local work is governed by [pull requests](pull-requests.ok.md) and [reconciliation](reconciliation.ok.md).

### issues-01
Each open issue has one intelligible outcome, a declared scope and delivery stage, and observable acceptance criteria. It distinguishes a desired capability from an observed failure; a reported failure includes evidence against an identified main revision and relevant OK assertion, or states that main applicability is still unknown.

Check: an unfamiliar contributor can tell what would close the issue and what would not. Mixed code/manuscript work may share an outcome but has separately owned acceptance leaves.

### issues-02
Each main-branch gap has exactly one canonical active record. Related issues, umbrella checklists, PRs, and historical reports link to that record instead of maintaining independently mutable copies of its status or work orders.

Check: canonical URL, stable gap identity, and duplicate search. An umbrella may coordinate several independently closable gaps without claiming to own them again.

### issues-03
Each active outcome has a next action, an owner or explicit unclaimed state, and a stated blocker when progress depends on a person, decision, tool, or other task. Assignment is not falsely reported as acceptance of responsibility, and author-only leaves remain distinguishable from contributor work.

Check: the issue's current summary and linked work orders. A blocked item remains visible; it is not recategorized as completed to clear the queue.

### issues-04
Every closure states its actual reason and delivery stage, links acceptance evidence for any completed claim, and links any remaining independently necessary work. Author handoff, merged source, verified integration, and published paper are distinct outcomes; completion of one does not imply the others.

Check: closure record. Duplicate, declined, or superseded issues are not reported as scientifically or technically resolved.

### issues-05
A closed finding that recurs on a later main revision is re-evaluated under the same identity when its acceptance obligation is unchanged; a genuinely different obligation is linked as new work. Age or an old green result alone never proves a current gap is closed.

Check: revision-specific reopening or supersession evidence, preserving the earlier valid outcome rather than rewriting history.
