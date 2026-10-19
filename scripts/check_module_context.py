#!/usr/bin/env python3
"""Check the hand-reviewed v4.5 module import and section-context inventory.

This deliberately checks only line-leading, single-line first-party public
imports and variable/include/omit commands in the nine implementation modules.
Comments and strings are ignored; whitespace is normalized and command order
within each inventory is retained. New modules or changed inventories require
intentional review of module-context-baseline.json; there is no refresh option.

This is not a Lean parser, a source-preservation check, or a semantic proof. It
does not track namespace/section boundaries or positions relative to declarations,
and does not inventory structures, instances, or bodies. Keep the production
build, proof audits and built-reference elaborated API comparison separately.
"""
from difflib import SequenceMatcher
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
from roadmap_inventory import mask_comments, TOKEN

ROOT = Path(__file__).resolve().parents[1]
CONTEXT = re.compile(r"^[ \t]*(?:variable|include|omit)\b")
PUBLIC_IMPORT = re.compile(r"^[ \t]*public[ \t]+import\b")


def inventory(source):
    """Read the supported command forms, rejecting their multiline variants."""
    text = mask_comments(source)
    masked = list(text)
    for token in TOKEN.finditer(text):
        if token[0].startswith(('"', "'")):
            for i in range(token.start(), token.end()):
                if masked[i] != "\n":
                    masked[i] = " "
    lines = "".join(masked).splitlines()
    result = {"imports": [], "context": []}
    errors = []
    for i, line in enumerate(lines):
        command = " ".join(line.split())
        if CONTEXT.match(line):
            kind = "context"
        elif PUBLIC_IMPORT.match(line) and any(
                name == "AsymmetricTensor" or name.startswith("AsymmetricTensor.")
                for name in command.split()[2:]):
            kind = "imports"
        else:
            continue
        result[kind].append(command)
        following = next((other for other in lines[i + 1:] if other.strip()), "")
        if following[:1].isspace():
            errors.append(f"line {i + 1}: unsupported multiline {kind} command; "
                          "review the bounded guard before changing command syntax")
    return result, errors


def differences(expected, actual, label):
    errors = []
    for operation, a, b, c, d in SequenceMatcher(
            a=expected, b=actual, autojunk=False).get_opcodes():
        if operation == "equal":
            continue
        if operation == "replace":
            errors.append(f"changed {label}: expected {expected[a:b]!r}; found {actual[c:d]!r}")
        elif operation == "delete":
            errors.append(f"missing {label}: {expected[a:b]!r}")
        else:
            errors.append(f"additional {label}: {actual[c:d]!r}")
    return errors


def check(root):
    baseline = json.loads((root / "scripts/module-context-baseline.json").read_text())
    if baseline.get("version") != 1:
        return ["module context baseline: unsupported manifest version"]
    modules = baseline["modules"]
    # Skip Binyamin's direct raw uploads (spaces in filename = not a valid Lean module name).
    # These are his source material, not production modules.
    actual = {path.relative_to(root).as_posix()
              for path in (root / "AsymmetricTensor").rglob("*.lean")
              if " " not in path.name}
    errors = [f"{path}: missing reviewed module" for path in sorted(modules.keys() - actual)]
    errors.extend(f"{path}: additional module needs a reviewed context inventory"
                  for path in sorted(actual - modules.keys()))
    for path in sorted(actual & modules.keys()):
        commands, syntax_errors = inventory((root / path).read_text())
        errors.extend(f"{path}: {error}" for error in syntax_errors)
        for kind, label in [("imports", "first-party public import"),
                            ("context", "section-context command")]:
            errors.extend(f"{path}: {error}" for error in
                          differences(modules[path][kind], commands[kind], label))
    return errors


if __name__ == "__main__":
    failures = check(ROOT)
    for failure in failures:
        print(failure, file=sys.stderr)
    if not failures:
        print("MODULE_CONTEXT_OK: nine reviewed v4.5 module inventories unchanged.")
    sys.exit(bool(failures))
