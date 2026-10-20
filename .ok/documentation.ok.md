# Reader-facing documentation

Draft for discussion. Not an activated policy or authorization to act.

Scope: README, contributor guidance, API/scope explanations, examples, citation instructions, and generated documentation. This file owns reader usability and truthful current-versus-historical presentation; mathematical correspondence belongs to [evidence](evidence.ok.md).

### docs-01
Every document presenting itself as current points to existing entry points, declarations, commands, and artifacts with the stated behavior. Historical material names its snapshot and does not use an unqualified moving link to imply that old evidence certifies the present revision.

Check: links and examples against the named revision, plus human review of scope language. Historical documents may remain unchanged when their historical status is clear at the point of use.

### docs-02
The reproduction instructions identify prerequisites and committed dependency selection, distinguish build, focused tests, aggregate verification and hosted results, and do not prescribe an unintended upgrade or baseline reset as routine setup.

Check: a clean-room or equivalent documented reproduction and command-to-check mapping. Tool unavailability is reported, not substituted with an unperformed pass.

### docs-03
Current citation instructions and machine-readable citation metadata agree with the artifact they claim to describe, including paper version/DOI/date versus software revision, author attribution, and the applicable separate licenses. Historical citations remain usable and explicitly historical.

Check: README, citation metadata, paper manifest, checked artifact identity and licenses. A paper DOI is not silently represented as a software DOI.

### docs-04
A generated report names its inputs and generation method, and either reproduces from those inputs or is explicitly retained as immutable historical evidence. Documentation does not silently present known losses in API or test coverage as restored capabilities.

Check: generation provenance and current coverage links. A report may link the canonical issue rather than become another task-status database.
