#!/usr/bin/env python3
"""Compile temporary mutations and require specific audit failures.

No intentionally incomplete Lean source is retained in the project. A malformed
fixture, missing import, or unrelated Lean error is a test failure, not evidence
that the audit rejected the intended mutation.
"""

from __future__ import annotations

import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def lake_output(*args: str) -> str:
    return subprocess.check_output(["lake", "env", *args], cwd=ROOT, text=True).strip()


def main() -> None:
    lean = Path(lake_output("lean", "--print-prefix")) / "bin" / "lean"
    lean_path = lake_output("printenv", "LEAN_PATH")
    with tempfile.TemporaryDirectory(prefix="proof-audit-", dir=ROOT / ".lake") as name:
        temp = Path(name)
        env = dict(os.environ, LEAN_PATH=str(temp) + os.pathsep + lean_path)

        def run(module: str, source: str, *, compile: bool = False,
                reject: str | None = None) -> None:
            path = temp / f"{module}.lean"
            path.write_text(source, encoding="utf-8")
            command = [str(lean), f"--root={temp}", str(path)]
            if compile:
                command += ["-o", str(temp / f"{module}.olean")]
            result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    timeout=120)
            if reject is None:
                if result.returncode != 0:
                    raise RuntimeError(f"{module} did not compile:\n{result.stdout}")
            else:
                if result.returncode == 0:
                    raise RuntimeError(f"{module}: mutation unexpectedly passed")
                if reject not in result.stdout:
                    raise RuntimeError(
                        f"{module}: failed for an unrelated reason, expected {reject}:\n"
                        f"{result.stdout}")
                print(f"PASS {module}: rejected with {reject}")

        run("CleanFixture", "theorem clean : True := True.intro\n", compile=True)
        run("CleanAudit", """import CleanFixture
import ProofAudit
#audit_root CleanFixture declared []
#audit_theorem clean custom []
""")
        print("PASS CleanAudit: complete proof accepted")

        for tactic in ("sorry", "admit"):
            run(f"Unfinished_{tactic}", f"""import ProofAudit
theorem unfinished : True := by {tactic}
#audit_theorem unfinished custom []
""", reject="PROOF_AUDIT_INCOMPLETE")

        # Compiled dependency: no unfinished-proof token occurs in the audited reader.
        run("ImportedHole", "theorem hiddenHole : True := by sorry\n", compile=True)
        run("ImportedHoleAudit", """import ImportedHole
import ProofAudit
theorem headline : True := hiddenHole
#audit_theorem headline custom []
""", reject="PROOF_AUDIT_INCOMPLETE")

        # Private and unreferenced, outside the production root namespace.
        run("PrivateHole", "namespace DifferentNamespace\n"
            "private theorem unadvertised : True := by sorry\n"
            "end DifferentNamespace\n", compile=True)
        run("PrivateHoleAudit", """import PrivateHole
import ProofAudit
#audit_root PrivateHole declared []
""", reject="PROOF_AUDIT_INCOMPLETE")

        run("UnexpectedAxiom", "axiom unexpected : True\n", compile=True)
        run("UnexpectedAxiomAudit", """import UnexpectedAxiom
import ProofAudit
theorem headline : True := unexpected
#audit_theorem headline custom []
""", reject="PROOF_AUDIT_AXIOMS")
        run("UnexpectedInventoryAudit", """import UnexpectedAxiom
import ProofAudit
#audit_root UnexpectedAxiom declared []
""", reject="PROOF_AUDIT_INVENTORY")

        run("MissingTargetAudit", """import ProofAudit
#audit_theorem noSuchTheorem custom []
""", reject="PROOF_AUDIT_TARGET")
        run("MissingModuleAudit", """import ProofAudit
#audit_root NoSuchModule declared []
""", reject="PROOF_AUDIT_MODULE")

    print("All proof-audit regressions passed; temporary mutation files removed.")


if __name__ == "__main__":
    main()
