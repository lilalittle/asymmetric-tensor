"""Inspect named target binders in this repository's declaration signatures.

Local lexical extraction handles nested comments, string literals, visibility
modifiers and primed identifiers while preserving token boundaries. Parameter groups
and explicit forall binders are distinguished from type ascriptions/references.
This is an inventory check for the project's syntax, not Lean elaboration.
"""
import re

# Quoted strings/characters are indivisible tokens. In particular, identifier
# primes must stay attached: h_target' is a different name from h_target.
LITERAL = r'"(?:\\.|[^"\\])*"|' + r"'(?:\\.|[^'\\])'"
IDENTIFIER = r"(?:«[^»]+»|\w[\w']*(?:\.\w[\w']*)*)"
TOKEN = re.compile(rf"{LITERAL}|{IDENTIFIER}|:=|[^\w\s]", re.S)
DECLARATION = re.compile(
    rf"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?"
    rf"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    rf"(?:def|abbrev|opaque|axiom|lemma|theorem)\s+(?P<name>{IDENTIFIER})", re.M)
OPEN = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
CLOSE = set(OPEN.values())


def mask_comments(source):
    """Replace comment characters with whitespace, preserving strings and primes."""
    result, i, depth = list(source), 0, 0
    literal = re.compile(LITERAL, re.S)
    identifier = re.compile(IDENTIFIER)
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            result[i:i + 2] = "  "
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            result[i:i + 2] = "  "
            i += 2
        elif depth:
            if source[i] != "\n":
                result[i] = " "
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result[i:end] = " " * (end - i)
            i = end
        else:
            token = literal.match(source, i) or identifier.match(source, i)
            i = token.end() if token else i + 1
    if depth:
        raise ValueError("Unterminated block comment")
    return "".join(result)


def declaration_header(tokens):
    """Exclude a top-level declaration value, retaining parameter defaults."""
    depth = 0
    for i, token in enumerate(tokens):
        if depth == 0 and token in (":=", "where"):
            return tokens[:i]
        if token in OPEN:
            depth += 1
        elif token in CLOSE:
            depth -= 1
    return tokens


def declaration_signatures(source):
    text = mask_comments(source)
    # Preserve line positions while preventing fake declaration starts inside
    # multiline strings. Tokenization, rather than a separate quote regex, keeps
    # a trailing identifier prime from being mistaken for a character literal.
    masked = list(text)
    for token in TOKEN.finditer(text):
        if token[0].startswith(('"', "'")):
            for i in range(token.start(), token.end()):
                if masked[i] != "\n":
                    masked[i] = " "
    matches = list(DECLARATION.finditer("".join(masked)))
    for i, match in enumerate(matches):
        stop = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        tokens = TOKEN.findall(text[match.end():stop])
        yield match["name"], declaration_header(tokens)


def group_end(tokens, start):
    stack = []
    for i in range(start, len(tokens)):
        token = tokens[i]
        if token in OPEN:
            stack.append(OPEN[token])
        elif token in CLOSE:
            if not stack or stack.pop() != token:
                return None
            if not stack:
                return i
    return None


def binder_names(tokens):
    """Read only names before the binder's type, never names inside that type."""
    names = []
    for token in tokens:
        if token in (":", ":=", ","):
            break
        if re.fullmatch(IDENTIFIER, token) is None:
            return []
        names.append(token[1:-1] if token.startswith("«") else token)
    return names


def has_named_binder(tokens, name):
    header = declaration_header(tokens)
    # Declaration parameter groups precede the top-level result-type colon.
    i = 0
    while i < len(header) and header[i] != ":":
        if header[i] in OPEN:
            end = group_end(header, i)
            if end is None:
                break
            if name in binder_names(header[i + 1:end]):
                return True
            i = end + 1
        else:
            i += 1

    # Inspect quantifiers in the actual result type, not inside a parameter's
    # type/default. Parentheses alone remain ascriptions/applications.
    result_start = i + 1 if i < len(header) and header[i] == ":" else len(header)
    for i, token in enumerate(header[result_start:], start=result_start):
        if token not in ("∀", "forall"):
            continue
        j = i + 1
        while j < len(header) and header[j] in OPEN:
            end = group_end(header, j)
            if end is None:
                break
            if name in binder_names(header[j + 1:end]):
                return True
            j = end + 1
        if j < len(header) and name in binder_names(header[j:]):
            return True
    return False


def target_binder_declarations(sources):
    result, seen = set(), set()
    for source in sources:
        for name, signature in declaration_signatures(source):
            if name in seen:
                raise ValueError(f"Duplicate declaration: {name}")
            seen.add(name)
            if has_named_binder(signature, "h_target"):
                result.add(name)
    return result
