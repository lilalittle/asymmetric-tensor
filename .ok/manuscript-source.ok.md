# Manuscript source integrity

Draft for discussion. Not an activated policy or authorization to act.

Scope: each manuscript's LaTeX source and required build inputs, including companion manuscripts. Source approval belongs to [authority](authority.ok.md); the output artifact belongs to [paper artifacts](paper-artifacts.ok.md).

### tex-01
Each manuscript identified as buildable has an identified source entry point and complete input set with a documented build method that produces its intended document. Missing inputs or unavailable reproduction evidence are explicit gaps, not inferred success from a different manuscript's build.

Check: source/input identities, engine and dependency information, command, and build log. Compilation is separate from mathematical acceptance.

### tex-02
A manuscript represented as internally consistent uses the same quantity definitions, hypotheses and domains across each claimed derivation, or explicitly distinguishes the alternatives. A formula imported from Lean is not said to follow from manuscript definitions when the Lean theorem merely assumes it.

Check: targeted human mathematical review of changed claims and their dependencies, using evidence-02 and evidence-03.

### tex-03
In a manuscript revision accepted for reading, equation identifiers and references unambiguously identify their intended expressions in the compiled document, with no unresolved references/citations or duplicate destinations that misdirect readers. Historical numbering, when retained, has a coherent unique scheme rather than colliding isolated manual tags.

Check: source labels, repeated-pass build diagnostics, resolved auxiliary references and rendered/text inspection. A zero exit code alone is insufficient. An exploratory raw upload may be diagnosed as not yet satisfying this acceptance contract without being rejected from the authoring lane.

### tex-04
Every manuscript revision presented for acceptance has an accompanying disposition that distinguishes new author-approved corrections, inherited limitations, and deferred scientific questions. A correction in a companion manuscript or posted paragraph is not described as incorporated into this manuscript until its actual source contains it.

Check: source diff, PR/release disposition and author-approved correction evidence; the disposition need not edit the protected source. Wider research questions need not be solved to accept an honestly bounded local correction.
