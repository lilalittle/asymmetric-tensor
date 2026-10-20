#!/usr/bin/env python3
"""Prove Lake does not build raw author uploads as stable dependencies.

Add an unmistakably malformed versioned upload, rebuild the real stable targets,
and require success. The normal proof-audit mutation suite independently proves
that production sorry/admit/undeclared axioms stay blocking.
"""
from pathlib import Path
import json
import tempfile
import subprocess
import uuid

from check_author_drafts import check_one
from report_author_drafts import validate

ROOT = Path(__file__).resolve().parents[1]
# Numeric version, unique and exclusive so no checked-in author file is touched.
path = ROOT / "AsymmetricTensor" / f"Asymmetric Tensor v{uuid.uuid4().int}.lean"
created = False
try:
    with path.open("x") as output:
        created = True
        output.write("/- Deliberately unterminated: this author draft cannot compile.\n")
    with tempfile.TemporaryDirectory(prefix="draft-negative-", dir=ROOT / ".lake") as directory:
        output = Path(directory)
        relative = path.relative_to(ROOT).as_posix()
        result = {"path": relative, "log": "draft.log",
                  **check_one(path, ROOT, output / "draft.log", 60)}
        assert result["status"] == "COMPILE_FAILED", result
        (output / "results.json").write_text(json.dumps([result]))
        (output / "summary.md").write_text("Negative fixture: compiler failure is advisory.\n")
        validate(output, [relative])
        print("DRAFT_DIAGNOSTIC_ADVISORY: real malformed source rejected without a tooling failure.")
    subprocess.run(["lake", "build", "AsymmetricTensor", "ProofAudit"],
                   cwd=ROOT, check=True, timeout=300)
    print("DRAFT_BUILD_ISOLATED: malformed author upload did not enter the stable build.")
finally:
    if created:
        path.unlink(missing_ok=True)
