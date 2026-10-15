#!/usr/bin/env python3
"""Compare moved declaration tokens/docstrings with a pre-split source checkout.

This intentionally supports this project's current single-namespace syntax,
including inline declaration attributes and aliases; it is not a Lean parser.
Section variables/imports are checked separately through elaborated API types.
"""
from collections import Counter
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(
    r"^(?:@\[[^\]\n]*\][ \t]*)?(?:noncomputable[ \t]+)?"
    r"(?:def|abbrev|opaque|axiom|lemma|theorem|alias)[ \t]+([^\s(:]+)", re.M)


def strip_comments(source):
    result, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            result.append("\n" if source[i] == "\n" else " ")
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            end = i + 1
            while end < len(source):
                if source[end] == "\\":
                    end += 2
                elif source[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
            result.append(source[i:end])
            i = end
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise ValueError("Unterminated block comment")
    return "".join(result)


def declarations(sources):
    result = {}
    for source in sources:
        text = strip_comments(source)
        for match in DECL.finditer(text):
            # Current declarations have indented continuations. An unindented
            # command starts the next declaration or a section/context directive.
            end = re.search(r"\n(?=[^\s])", text[match.end():])
            stop = match.end() + end.start() if end else len(text)
            body = text[match.start():stop]
            if match[1] in result:
                raise ValueError(f"Duplicate declaration: {match[1]}")
            result[match[1]] = re.findall(r'"(?:\\.|[^"\\])*"|\w+|[^\w\s]', body)
    return result


def source_files(root):
    return [root / "AsymmetricTensor.lean", *sorted((root / "AsymmetricTensor").rglob("*.lean"))]


def docstrings(sources):
    # Current declaration docstrings contain no nested block comments.
    return Counter(" ".join(comment.split()) for source in sources
                   for comment in re.findall(r"/--(.*?)-/", source, re.S))


def main():
    if len(sys.argv) != 2:
        sys.exit("Usage: python3 scripts/check_module_source.py BASELINE_CHECKOUT")
    baseline = Path(sys.argv[1]).resolve()
    before = [path.read_text() for path in source_files(baseline)]
    after = [path.read_text() for path in source_files(ROOT)]
    a, b = declarations(before), declarations(after)
    failures = [name for name in sorted(a.keys() | b.keys()) if a.get(name) != b.get(name)]
    for name in failures:
        print(f"Changed declaration tokens: {name}")
    missing_docs, added_docs = docstrings(before) - docstrings(after), docstrings(after) - docstrings(before)
    if missing_docs or added_docs:
        print(f"Changed declaration docstrings: {sum(missing_docs.values())} removed, "
              f"{sum(added_docs.values())} added")
    if failures or missing_docs or added_docs:
        sys.exit(1)
    print(f"SOURCE_COMPATIBLE: {len(a)} declarations have identical attributes, statements, "
          f"and body tokens; {sum(docstrings(before).values())} declaration docstrings retained "
          "up to whitespace.")


if __name__ == "__main__":
    main()
