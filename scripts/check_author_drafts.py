#!/usr/bin/env python3
"""Compile author uploads independently; report failures without changing source.

Nonzero exits are intentional: only this step is advisory in the workflow.
Compilation is not a proof-completeness audit or acceptance of the draft theory.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from source_boundary import author_drafts

ROOT = Path(__file__).resolve().parents[1]


def check_one(path, root, log, timeout, runner=subprocess.run):
    with log.open("w") as output:
        try:
            result = runner(["lake", "env", "lean", str(path.relative_to(root))],
                            cwd=root, stdout=output, stderr=subprocess.STDOUT,
                            timeout=timeout, check=False)
            status = ("COMPILED" if result.returncode == 0 else
                      "TOOL_FAILURE" if result.returncode < 0 else "COMPILE_FAILED")
            return {"status": status, "exit_code": result.returncode}
        except subprocess.TimeoutExpired:
            output.write("\nDraft compilation exceeded the time limit.\n")
            return {"status": "TIMEOUT", "exit_code": None}
        except OSError as exc:
            output.write(f"\nUnable to run Lean: {exc}\n")
            return {"status": "TOOL_FAILURE", "exit_code": None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/author-diagnostics")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    results = []
    for index, path in enumerate(author_drafts(ROOT)):
        log = args.output / f"draft-{index}.log"
        result = {"path": path.relative_to(ROOT).as_posix(), "log": log.name,
                  **check_one(path, ROOT, log, args.timeout)}
        results.append(result)
        print(f"{result['status']}: {result['path']} (see {log})")
    (args.output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    summary = ["## Author-source diagnostics (advisory)", "",
               "These versioned uploads are NOT the verified library. "
               "COMPILED means Lean accepted the file, not that it is sorry-free, "
               "axiom-audited, API-compatible, or scientifically validated.", ""]
    for result in results:
        summary.append(f"- `{result['path']}`: **{result['status']}** "
                       f"(exit {result['exit_code']}; `{result['log']}`)")
    if not results:
        summary.append("No versioned author uploads found; no draft was checked.")
    summary += ["", "Only the stable `verify` job certifies the integrated library. "
                "Logs and machine-readable results are in the author-diagnostics artifact."]
    (args.output / "summary.md").write_text("\n".join(summary) + "\n")
    return int(any(item["status"] != "COMPILED" for item in results))


if __name__ == "__main__":
    sys.exit(main())
