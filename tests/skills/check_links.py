#!/usr/bin/env python3
"""Check local Markdown destinations in the ingest skill and its changed docs.

This checks file containment/existence and ordinary heading anchors, not remote
URL availability or arbitrary Markdown syntax. Pass other Markdown files as args.
"""
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[2]
DEFAULTS = [
    ".agents/skills/binyamin-ingest/SKILL.md",
    "CONTRIBUTING.md",
    "docs/source-provenance.md",
    "tests/skills/binyamin-ingest.md",
]


def check(paths):
    checked = 0
    for path in paths:
        for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", path.read_text()):
            url = urlsplit(target.strip("<>"))
            if url.scheme or url.netloc:
                continue
            dest = (path.parent / unquote(url.path)).resolve() if url.path else path
            if not dest.is_relative_to(ROOT) or not dest.is_file():
                raise ValueError(f"{path.relative_to(ROOT)}: missing/outside path {target}")
            if url.fragment:
                headings = re.findall(r"^#+\s+(.+)$", dest.read_text(), re.MULTILINE)
                anchors = {re.sub(r"[^\w\- ]", "", h.lower()).replace(" ", "-")
                           for h in headings}
                if unquote(url.fragment) not in anchors:
                    raise ValueError(f"{path.relative_to(ROOT)}: missing anchor {target}")
            checked += 1
    return checked


if __name__ == "__main__":
    paths = [(ROOT / item).resolve() for item in (sys.argv[1:] or DEFAULTS)]
    try:
        count = check(paths)
    except (OSError, ValueError) as exc:
        sys.exit(str(exc))
    print(f"PASS: {count} local Markdown paths and anchors")
