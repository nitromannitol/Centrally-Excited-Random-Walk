"""Compare every exponent in a paper statement with those in its Lean statement.

Exponents like `2/3` and `1/3` (or `-2/3` and `-1/3`) carry the actual
content of a scaling theorem, and swapping `2/3` for `1/3` is a
transposition that no Lean type error would ever catch — both sides still
type-check as `ℝ`. So exponents are compared directly, as multisets rather
than as sets: every exponent occurrence is extracted from the paper's line
range and from the frozen Lean statement (plus the bodies of any `def` the
block names, since a paper's `h(t)` is often a named Lean definition rather
than a literal formula in the statement), and a paper exponent occurrence
with no matching occurrence on the Lean side is reported.

A *multiplicity* difference is reported as a note, not a failure. The paper
writes `|R_t| = c t^{2/3} + o(t^{2/3})`, naming the exponent twice, while any
faithful Lean rendering names it once; failing on that fires on a universal
idiom and pushes the reviewer toward a blanket waiver, which would cost the
real check. An exponent the Lean never mentions at all is the failure.

Three kinds of difference are expected and are recorded per node, in
`readings.yaml['exponents']` (see `readings.py` for the schema), rather than
silently ignored or hand-waved in a comment here:

  notation    the paper writes `\\gamma`, Lean writes `γ`
  general     the paper writes the `d = 2` case as `2/3` and `1/3`; Lean
              carries the general `d/(d+1)` and `1/(d+1)`, which agree at `d = 2`
  split       one paper theorem is split across several manifest nodes, so a
              node's own display does not contain every exponent in its
              theorem's full line range
  context     the exponent occurs only in surrounding prose or in the proof,
              not in the statement this node claims
  definition  the exponent lives inside a named Lean definition under a
              different literal spelling that still matches the paper

A node's waiver is a *list* (a node can have more than one independent
expected difference) and, if present and non-empty, suppresses every
currently-missing exponent occurrence for that node — see `readings.py` for
why the waiver is granted at the node level rather than keyed by the exact
exponent spelling, which is where the vendored version of this checker kept
it. Waivers are printed on every run whenever a node has one recorded.

`DECORATION`, `SET_BASE` and `GREEK` (below) filter out superscripts that
are not really exponents at all: a rescaling label `f^{(R)}`, a lattice name
`\\Z^d`, a transpose `A^\\top`. `top_level_sum()` and `canon()` decide when a
wrapping parenthesis after a unary minus is redundant (`-(x)` == `-x`) versus
load-bearing (`-(2-d/2)` != `-2-d/2`), so the two sides can be compared after
one canonical spelling rather than by fragile textual equality.

The paper's basename and the library directory searched for named
definitions come from `cfg.paper_path`/`cfg.paper_stem`/`cfg.lib_dir`, never
from a literal — the same `rotor\\.tex`-shaped bug that made `check_clauses`
inspect 0 nodes in two repos would do the same thing here.

    python3 -m leanform_tools.check_exponents <repo>
"""

from __future__ import annotations

import re
import sys
from collections import Counter

from . import lean_source as ls
from . import readings as rd
from .config import RepoConfig, load
from .gate import Result, run

# Superscripts that are not exponents of a quantity: set names like `ℤ^d`,
# the inverse in `Δ^{-1}`, summation limits, and `θ`-expressions written
# with `Real.exp` rather than `^` on the Lean side. This is the shared
# floor; each repo adds its own vocabulary under `noise:` in
# ledger/readings.yaml, because which bare symbols are decorative is a
# property of the paper (ORRW's `c`, `M`, `R`, `d` are named constants).
NOISE = {"2", "+", "-1", "\\Z", "\\R", "\\infty", "\\ast", "\\star",
         "j", "n", "m", "k", "i"}

# A superscript that decorates a symbol instead of raising it to a power:
# a rescaling label `f^{(R)}`, a density label `\sigma^{(\rho)}`, roman
# decorations `g^{\rm BM}` and `\P^{\rm tr}`, and the transpose star.
DECORATION = re.compile(
    r"^(\\(rm|mathrm|mathbf|mathcal|text|operatorname).*"
    r"|\((\\rho|\\rho\'|R|T|\\varepsilon)\)"
    r"|\*|\\ast|\\star|\\top|\\dagger|\\prime|\'|\\|)$")

# Bases whose superscript is a dimension or a set name, never a power of a
# quantity: `\Z^d`, `\R^d`, `\N^d`, `\T^d`.
SET_BASE = re.compile(r"(\\(Z|R|N|T|mathbb\{[A-Za-z]\})|\bC_{\\rm loc}|\bH)\s*$")

GREEK = {"\\alpha": "α", "\\beta": "β", "\\gamma": "γ", "\\delta": "δ",
         "\\theta": "θ", "\\kappa": "κ", "\\lambda": "λ", "\\rho": "ρ",
         "\\sigma": "σ", "\\tau": "τ", "\\varepsilon": "ε", "\\eta": "η"}


def top_level_sum(e: str) -> bool:
    """True when `e` has a `+` or `-` outside every bracket, so that
    dropping a wrapping parenthesis after a minus sign would change what it
    means."""
    depth = 0
    for j, ch in enumerate(e):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch in "+-" and depth == 0 and j > 0:
            return True
    return False


def canon(e: str) -> str:
    """One spelling for an exponent, applied to the paper and to Lean alike.

    `-(2 - d/2)` and `-2 - d/2` are different numbers, so the parenthesis
    after a minus sign is kept whenever the operand is itself a sum; it is
    dropped only when it is redundant, which is what makes the two sides
    comparable.
    """
    for k, v in GREEK.items():
        e = e.replace(k, v)
    e = re.sub(r"\\(cdot|times|,|!|;|\s)", "", e)
    e = re.sub(r"[\s*]", "", e)
    # `\frac{d}{d+1}` and Lean's `d/(d+1)` are the same exponent. ORRW's own
    # checker carried a \frac normalizer; without it every fractional
    # exponent in that repo reads as "present in the paper, absent in Lean".
    # Parenthesize a compound denominator so `\frac{d}{d+1}` becomes
    # `d/(d+1)` and not `d/d+1`, which would be a different number.
    for _ in range(3):
        m = re.search(r"\\[dt]?frac\{([^{}]*)\}\{([^{}]*)\}", e)
        if not m:
            break
        num, den = m.group(1), m.group(2)
        den = f"({den})" if top_level_sum(den) else den
        e = e[: m.start()] + f"{num}/{den}" + e[m.end():]
    for _ in range(3):
        # Drop a type ascription whatever the type: `(3 : ℕ)` must compare
        # equal to the paper's `3`, not to the string `3:ℕ`.
        e = re.sub(r":[^()]*$", "", e) if re.search(r":(ℝ|ℕ|ℤ|ℚ|ℂ)\)?$", e) else e
        m = re.fullmatch(r"\((.*)\)", e)
        if m and not top_level_sum(m.group(1)):
            e = m.group(1)
        if e.startswith("-(") and e.endswith(")") and not top_level_sum(e[2:-1]):
            e = "-" + e[2:-1]
    return e


def balanced(s: str, i: int, op: str, cl: str) -> str | None:
    depth = 0
    for j in range(i, len(s)):
        if s[j] == op:
            depth += 1
        elif s[j] == cl:
            depth -= 1
            if depth == 0:
                return s[i + 1:j]
    return None


DECL_START = re.compile(
    r"^(noncomputable\s+)?(private\s+|protected\s+)?"
    r"(def|abbrev|theorem|lemma|instance|structure|inductive|class|namespace|end|open|variable|@\[|/-)")


def definition_bodies(cfg: RepoConfig) -> dict[str, str]:
    """Every `def` under `cfg.lib_dir`, by fully qualified and short name.

    An exponent of a paper statement often sits in a definition the
    statement names rather than in the statement's own text, so the text a
    statement is compared against is the frozen block together with the
    bodies of the definitions it mentions.
    """
    bodies: dict[str, str] = {}
    if not cfg.lib_dir.exists():
        return bodies
    for path in sorted(cfg.lib_dir.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        i = 0
        while i < len(lines):
            m = re.match(r"^(noncomputable\s+)?def\s+([A-Za-z_][A-Za-z0-9_.']*)", lines[i])
            if not m:
                i += 1
                continue
            name = m.group(2)
            j = i + 1
            while j < len(lines) and not DECL_START.match(lines[j]):
                j += 1
            bodies[name] = "\n".join(lines[i:j])
            bodies[name.split(".")[-1]] = bodies[name]
            i = j
    return bodies


def with_definitions(blk: str, bodies: dict[str, str]) -> str:
    """The frozen block plus the body of each definition it names."""
    out = [blk]
    for name in sorted(set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", blk))):
        body = bodies.get(name) or bodies.get(name.split(".")[-1])
        if body is not None and body not in out:
            out.append(body)
    return "\n".join(out)


def paper_exponents(seg: str, extra_noise: set[str] | None = None) -> tuple[Counter, bool]:
    """The exponent multiset of the segment, and whether it has an exponential.

    A superscript is not an exponent when its base is a set name (`\\Z^d` is
    a lattice, not a power) and when it decorates rather than raises
    (`f^{(R)}`). A superscript on `e` is an exponential: Lean writes it
    `Real.exp`, not `^`, so it is reported separately and checked by name.
    """
    out, exponential = [], False
    for m in re.finditer(r"\^", seg):
        i = m.end()
        if i >= len(seg):
            continue
        if seg[i] == "{":
            g = balanced(seg, i, "{", "}")
            if g is None:
                continue
        else:
            g = seg[i]
        base = seg[:m.start()]
        if SET_BASE.search(base):
            continue
        if re.search(r"(^|[^A-Za-z\\])e\s*$", base):
            exponential = True
            continue
        out.append(g)
    cleaned = []
    for e in out:
        e = re.sub(r"\s|\\,|\\!|\\bigl|\\bigr", "", e)
        while e.startswith("{") and e.endswith("}"):
            e = e[1:-1]
        if e and not DECORATION.match(e):
            cleaned.append(canon(e))
    counts = Counter(cleaned)
    # Which bare symbols are decorative rather than genuine exponents is a
    # property of the paper, not of the tooling: ORRW writes `n^c`, `2^M` and
    # `\cdot^R` with `c`, `M`, `R` as named constants its Lean statement
    # binds differently, and its own checker listed exactly those four in
    # NOISE. So the vocabulary is per-repo data in ledger/readings.yaml,
    # unioned with the shared default — never a literal edited into shared code.
    for noise in NOISE | (extra_noise or set()):
        counts.pop(noise, None)
    return counts, exponential


def lean_exponents(blk: str) -> Counter:
    """The exponent multiset of a Lean statement (plus named definitions)."""
    out = []
    for m in re.finditer(r"\^\s*", blk):
        i = m.end()
        if i >= len(blk):
            continue
        if blk[i] == "(":
            g = balanced(blk, i, "(", ")")
            if g is not None:
                out.append(g)
        else:
            g = re.match(r"[A-Za-zγβ0-9]+", blk[i:])
            if g:
                out.append(g.group(0))
    cleaned = []
    for e in out:
        e = re.sub(r"\(\s*([a-zA-Zβγ])\s*:\s*ℝ\s*\)", r"\1", e)
        e = re.sub(r"\(\s*(\d+)\s*:\s*ℝ\s*\)", r"\1", e)
        cleaned.append(canon(e))
    counts = Counter(cleaned)
    counts.pop("2", None)
    return counts


def _frozen_block(cfg: RepoConfig, node) -> tuple[str | None, str | None]:
    if not node.file:
        return None, f"{node.id}: no file: recorded"
    path = cfg.root / node.file
    if not path.exists():
        return None, f"{node.id}: file {node.file} does not exist"
    src = path.read_text(encoding="utf-8")
    spans = ls.frozen_blocks(src)
    if len(spans) != 1 or spans[0][1] < 0:
        return None, f"{node.id}: expected exactly one frozen block in {node.file}, found {len(spans)}"
    return ls.block_body(src, spans[0]), None


def _missing(pe: Counter, le: Counter) -> tuple[list[str], list[str]]:
    """Split the shortfall into (absent, fewer-occurrences).

    An exponent the Lean statement never mentions is the defect this gate
    exists for: `2/3` written where the paper says `1/3` is a transposition
    no type error would catch.

    A *multiplicity* shortfall is not that. The paper writes
    `|R_t| = c t^{2/3} + o(t^{2/3})`, which names the exponent twice, and any
    faithful Lean rendering — one `Tendsto (… / t ^ (2/3))` — names it once.
    Treating that as a failure fires on a universal idiom and would push the
    reviewer toward silencing the gate with a waiver, which costs the real
    check. So it is reported, not failed.
    """
    absent, fewer = [], []
    for exp, pc in sorted(pe.items()):
        lc = le.get(exp, 0)
        if lc == 0:
            absent.append(exp if pc == 1 else f"{exp} (x{pc})")
        elif pc > lc:
            fewer.append(f"{exp} (paper {pc}x, Lean {lc}x)")
    return absent, fewer


def check(res: Result, cfg: RepoConfig) -> None:
    res.total = len(cfg.nodes)
    _readings = rd.load_readings(cfg)
    exp_waivers = _readings.get("exponents", {})
    extra_noise = set(_readings.get("noise") or [])
    bodies = definition_bodies(cfg)

    paper_lines: list[str] | None = None
    if cfg.paper_path.exists():
        paper_lines = cfg.paper_path.read_text(encoding="utf-8").splitlines()
    else:
        res.fail(
            f"{cfg.paper_rel} does not exist; exponents cannot be extracted "
            "from the paper for any node"
        )

    for node in cfg.nodes:
        nid = node.id
        block, err = _frozen_block(cfg, node)
        if err:
            res.fail(err)
            continue
        res.count()

        waiver_entries = exp_waivers.get(nid) or []
        for w in waiver_entries:
            kind = w.get("kind", "context") if isinstance(w, dict) else "context"
            detail = w.get("detail", "") if isinstance(w, dict) else str(w)
            print(f"  {nid}: waiver [{kind}] {detail}")

        m = cfg.source_re.match(node.source or "") if node.source else None
        if not m or paper_lines is None:
            if m is None:
                res.note(
                    f"{nid}: source {node.source!r} does not name a "
                    f"`{cfg.paper_stem}:<a>-<b>` range; exponent comparison skipped"
                )
            continue

        a, b = int(m["a"]), int(m["b"])
        seg = "\n".join(paper_lines[a - 1:b])
        full_block = with_definitions(block, bodies)
        pe, pexp = paper_exponents(seg, extra_noise)
        le = lean_exponents(full_block)

        missing, fewer = _missing(pe, le)
        if pexp and not re.search(r"Real\.exp|rexp|Real\.log", full_block):
            missing.append(
                "e^{...} (the paper has an exponential; no Real.exp/Real.log "
                "in the Lean statement or its named definitions)"
            )

        print(f"  {nid:24s} paper {dict(sorted(pe.items()))}")
        print(f"  {'':24s} lean  {dict(sorted(le.items()))}")

        if fewer:
            res.note(
                f"{nid}: exponent stated more often in the paper than in Lean "
                f"{fewer} — usually the `c·t^a + o(t^a)` idiom; read once, not a defect"
            )

        if missing:
            if waiver_entries:
                res.note(
                    f"{nid}: exponent occurrence(s) with no Lean counterpart "
                    f"{missing}; waived by {len(waiver_entries)} reading(s) above"
                )
            else:
                res.fail(
                    f"{nid}: paper exponent(s) with no Lean counterpart: "
                    f"{missing}"
                )


def main(argv: list[str]) -> int:
    root = argv[1] if len(argv) > 1 else "."
    cfg = load(root)
    return run("check_exponents", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
