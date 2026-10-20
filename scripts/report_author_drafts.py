#!/usr/bin/env python3
"""Keep author compile failures advisory, but fail on broken diagnostics tooling."""
import json
import os
from pathlib import Path
import sys

from source_boundary import author_drafts

ROOT = Path(__file__).resolve().parents[1]


def validate(output, expected):
    try:
        results = json.loads((output / "results.json").read_text())
        if not isinstance(results, list):
            raise ValueError("results must be a list")
        if sorted(item["path"] for item in results) != sorted(expected):
            raise ValueError("results do not cover exactly the current author uploads")
        if not (output / "summary.md").is_file():
            raise ValueError("summary missing")
        for item in results:
            status, code, log = item["status"], item["exit_code"], item["log"]
            if not isinstance(log, str) or Path(log).name != log or not (output / log).is_file():
                raise ValueError("diagnostic log missing or malformed")
            if status == "TOOL_FAILURE":
                raise ValueError(f"tool failure while checking {item['path']}")
            valid = ((status == "COMPILED" and type(code) is int and code == 0) or
                     (status == "COMPILE_FAILED" and type(code) is int and code > 0) or
                     (status == "TIMEOUT" and code is None))
            if not valid:
                raise ValueError("unknown or inconsistent diagnostic outcome")
        return results
    except (OSError, ValueError, KeyError, TypeError) as exc:
        raise RuntimeError(f"Author diagnostics infrastructure failed: {exc}") from exc


def main():
    output = ROOT / ".lake/author-diagnostics"
    try:
        results = validate(output, [p.relative_to(ROOT).as_posix() for p in author_drafts(ROOT)])
        summary = (output / "summary.md").read_text()
        failed = False
    except RuntimeError as exc:
        summary = f"## Author diagnostics unavailable\n\n{exc}\nNo draft verification is claimed.\n"
        results, failed = [], True
    print(summary)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a") as report:
            report.write(summary)
    if any(item["status"] != "COMPILED" for item in results):
        print("::warning::Author uploads have compile failures or timeouts; see the diagnostic logs. "
              "Stable verification is independent.")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
