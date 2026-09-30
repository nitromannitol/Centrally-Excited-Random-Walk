"""Reading Lean source safely, without a Lean parser.

Two hazards this module exists to handle, both observed in the surveyed repos:

1. Ordinary prose in a header comment that happens to begin a line with the
   word `theorem` was read as a declaration by the regex-based discovery in
   `check_axioms.py`. So comments are masked before any declaration scan, and
   the masker is nesting-aware because Lean's `/- -/` nests.
2. A declaration name that is an ASCII truncation of a non-ASCII identifier
   (`e` for `e₁`) silently matched the wrong declaration in Manhattan's copy.
   So name comparison is exact on the full identifier, and a truncation is a
   hard error rather than a match.
"""

from __future__ import annotations

import re

from .config import BEGIN, END

# Declaration heads. `example` is deliberately absent: it has no name.
_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque)\s+"
    r"([^\s:{(\[]+)",
    re.M,
)

# Identifier characters Lean allows beyond ASCII word chars.
_IDENT_OK = re.compile(r"^[A-Za-z_À-￿][A-Za-z0-9_.'!?À-￿]*$")


def mask_comments(src: str) -> str:
    """Replace comment bodies with spaces, preserving newlines and offsets.

    Handles nested `/- -/` and line comments. Keeps the string the same length
    so that byte offsets and line numbers computed on the result still point
    at the original file.
    """
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if src.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and src[i] != "\n":
            out[i] = " "
        i += 1
    return "".join(out)


def frozen_blocks(src: str) -> list[tuple[int, int]]:
    """Offsets of every (begin_end, end_start) marker pair, in order.

    Markers are located in the raw text: a marker inside a comment would be
    pathological, and masking first would hide a real one.
    """
    spans, pos = [], 0
    while True:
        i = src.find(BEGIN, pos)
        if i < 0:
            return spans
        j = src.find(END, i)
        if j < 0:
            spans.append((i + len(BEGIN), -1))
            return spans
        spans.append((i + len(BEGIN), j))
        pos = j + len(END)


def block_body(src: str, span: tuple[int, int]) -> str:
    """The hashed bytes: strictly between the markers, one leading newline dropped."""
    body = src[span[0]: span[1]]
    return body[1:] if body.startswith("\n") else body


def declarations(text: str) -> list[str]:
    """Declaration names in `text`, comments masked, in source order."""
    return [m.group(2) for m in _DECL.finditer(mask_comments(text))]


def is_truncation(recorded: str, actual: str) -> bool:
    """True when `recorded` is a strict ASCII-ish prefix of `actual`.

    `e` vs `e₁`: the manifest would pass a prefix match while naming a
    different declaration. Callers treat this as a hard error.
    """
    return recorded != actual and actual.startswith(recorded)


def line_of(src: str, offset: int) -> int:
    return src.count("\n", 0, offset) + 1


def token_hits(src: str, tokens) -> list[tuple[str, int]]:
    """(token, line) for each banned token outside comments.

    Whole-identifier matching on both sides. Without the trailing boundary,
    `axiom` matches inside `#print axioms`, which is a legitimate line in
    every `Certificate.lean` and `Meta/AxiomsAudit.lean`; that false positive
    produced 226 spurious failures in Manhattan-Transience on first run.
    """
    masked = mask_comments(src)
    hits = []
    for tok in tokens:
        pat = r"(?<![A-Za-z0-9_'!?])" + re.escape(tok) + r"(?![A-Za-z0-9_'!?])"
        for m in re.finditer(pat, masked):
            hits.append((tok, line_of(masked, m.start())))
    return sorted(hits, key=lambda t: t[1])


def axiom_declarations(src: str) -> list[int]:
    """Lines declaring an `axiom`, as opposed to mentioning one.

    `#print axioms Foo` is how every certificate asks Lean for a closure and
    must stay legal; `axiom foo : T` is the thing the protocol bans.
    """
    masked = mask_comments(src)
    return [
        line_of(masked, m.start())
        for m in re.finditer(r"(?m)^\s*axiom\s+", masked)
    ]
