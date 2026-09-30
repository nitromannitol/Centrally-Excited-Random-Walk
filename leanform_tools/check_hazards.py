"""Probability lints on frozen blocks — BEST_PRACTICES.md §3, new gate 6.

A junk value is what a Lean function returns on input the paper never
considers. `sInf ∅ = 0` in the reals, `Set.ncard` of an infinite set is `0`,
`ENat.toNat ⊤ = 0`, a non-summable `tsum` is `0`, `a / 0 = 0`, a singular
`Matrix.inv` is `0`, a non-integrable Bochner integral is `0`. Each of these
can make a statement vacuously true, and at least one of them has made a
statement outright *false*: `Set.ncard` reading `0` on an infinite set turned
"the symmetric difference has at most two elements" into a claim satisfied by
an infinite symmetric difference — vacuous in exactly the case it existed to
exclude.

This gate does not decide whether a hazard is a defect. That is a
mathematical judgement and it belongs to a human. What it does is make every
hazard **declared**: each one is either guarded by a clause in the same
block, absorbed by the carrier type, or written down in
`ledger/readings.yaml` with a reason. An undeclared hazard fails.

So it is a `REVIEWED` obligation, in the sense §3 asks for: not "this is
wrong", but "nobody has said why this is right".

Matching is whole-identifier. A naive substring scan for `sInf` also matches
`IsInfPath`, `HasInfLivePath` and `HasInfiniteComponent`; measured over the
574 frozen blocks in this fleet that was 12 false positives out of 54 for the
affected classes — a 22% noise rate that would have buried the real hits.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from . import lean_source as ls
from .config import RepoConfig, load
from .gate import Result, run

# Each hazard: (name, pattern, what the junk value is).
# Patterns are whole-identifier or genuine operator characters, never bare
# substrings. `⁻¹` and `∫` are symbols and cannot collide with an identifier.
HAZARDS: list[tuple[str, str, str]] = [
    ("sInf", r"(?<![A-Za-z0-9_])sInf(?![A-Za-z0-9_])", "sInf ∅ = 0 in a conditionally complete lattice"),
    ("iInf", r"(?<![A-Za-z0-9_])iInf(?![A-Za-z0-9_])|⨅", "infimum over an empty index"),
    ("sSup", r"(?<![A-Za-z0-9_])sSup(?![A-Za-z0-9_])", "sSup ∅ = 0, and sSup of an unbounded set = 0"),
    ("iSup", r"(?<![A-Za-z0-9_])iSup(?![A-Za-z0-9_])|⨆", "supremum over an empty or unbounded index"),
    ("ncard", r"(?<![A-Za-z0-9_])Set\.ncard(?![A-Za-z0-9_])|(?<![A-Za-z0-9_])\.ncard(?![A-Za-z0-9_])",
     "Set.ncard of an infinite set = 0; Set.encard (ℕ∞) is the safe form"),
    ("toNat", r"(?<![A-Za-z0-9_])ENat\.toNat(?![A-Za-z0-9_])|(?<![A-Za-z0-9_])\.toNat(?![A-Za-z0-9_])",
     "ENat.toNat ⊤ = 0"),
    ("toReal", r"(?<![A-Za-z0-9_])ENNReal\.toReal(?![A-Za-z0-9_])|(?<![A-Za-z0-9_])\.toReal(?![A-Za-z0-9_])",
     "ENNReal.toReal ⊤ = 0"),
    ("tsum", r"(?<![A-Za-z0-9_])tsum(?![A-Za-z0-9_])|∑'", "a non-summable tsum = 0"),
    ("intdiv", r"(?<![A-Za-z0-9_])Int\.ediv(?![A-Za-z0-9_])|(?<![A-Za-z0-9_])Int\.fdiv(?![A-Za-z0-9_])|⌊|⌋",
     "integer division truncates; Int.ediv rounds toward -∞"),
    ("inv", r"⁻¹", "x⁻¹ = 0 at x = 0; Matrix.inv of a singular matrix = 0"),
    # `∫⁻` is a lintegral valued in ℝ≥0∞ and is total; only the Bochner `∫`
    # can return the junk value 0 on a non-integrable function.
    ("bochner", r"∫(?!⁻)", "a Bochner integral of a non-integrable function = 0"),
    ("choose", r"(?<![A-Za-z0-9_])Classical\.choice(?![A-Za-z0-9_])|(?<![A-Za-z0-9_])\.choose(?![A-Za-z0-9_])",
     "a choice term is unconstrained outside its specification"),
]

# A clause anywhere in the same block that plausibly rules the junk case out.
# Deliberately generous: this gate's job is to find the UNDECLARED hazard, and
# a false "guarded" here is recoverable (a human still reads the block),
# whereas a false alarm on every bounded integral makes the gate ignored.
GUARDS = [
    r"(?<![A-Za-z0-9_])Integrable(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])IntegrableOn(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])Summable(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])BddAbove(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])BddBelow(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])IsLUB(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])IsGLB(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])Set\.Finite(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])Set\.Nonempty(?![A-Za-z0-9_])",
    r"\.Nonempty",
    r"≠\s*0", r"0\s*<", r"0\s*≠", r"≠\s*⊤", r"<\s*⊤", r"≠\s*∅",
]

# Carrier types that absorb the hazard outright.
CARRIERS = [
    r"(?<![A-Za-z0-9_])ℕ∞(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])ℝ≥0∞(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])ENNReal(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])ENat(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])WithTop(?![A-Za-z0-9_])",
    r"(?<![A-Za-z0-9_])Set\.encard(?![A-Za-z0-9_])",
    r"∫⁻",  # lintegral: total on ℝ≥0∞, not a Bochner integral
]


def _declared(readings: dict, node_id: str, hazard: str) -> str | None:
    """A written reason in ledger/readings.yaml, if any."""
    entry = (readings.get("hazards") or {}).get(node_id)
    if not entry:
        return None
    if isinstance(entry, str):
        return entry
    if isinstance(entry, dict):
        return entry.get(hazard) or entry.get("all")
    return None


def _load_readings(cfg: RepoConfig) -> dict:
    p = cfg.root / "ledger" / "readings.yaml"
    if not p.exists():
        return {}
    try:
        import yaml

        return yaml.safe_load(p.read_text(encoding="utf-8")) or {}
    except Exception:
        return {}


# `(2 : ℂ)⁻¹`, `(3:ℝ)⁻¹`, `2⁻¹` — the inverse of a numeric literal is never
# the junk value, because the literal is never zero. Manhattan-Transience has
# five hits of exactly this shape and two independent model lanes called all
# five unguarded; all five are harmless. Excluded here rather than waived
# one-by-one in readings.yaml, because it is a property of the syntax.
_LITERAL_INV = re.compile(r"(?:\(\s*[0-9]+(?:\.[0-9]+)?\s*(?::[^)]*)?\)|(?<![A-Za-z0-9_])[0-9]+)$")


def _is_literal_inverse(body: str, start: int) -> bool:
    return bool(_LITERAL_INV.search(body[:start]))


def scan_block(body: str) -> list[tuple[str, int, str]]:
    """(hazard, line-within-block, quoted line) for each whole-identifier hit."""
    hits = []
    lines = body.splitlines()
    for name, pat, _why in HAZARDS:
        for m in re.finditer(pat, body):
            if name == "inv" and _is_literal_inverse(body, m.start()):
                continue
            line_no = body.count("\n", 0, m.start()) + 1
            line = lines[line_no - 1].strip() if 0 < line_no <= len(lines) else ""
            hits.append((name, line_no, line))
    return sorted(set(hits), key=lambda t: (t[1], t[0]))


def classify(body: str, hazard: str) -> str:
    """GUARDED / CARRIER / UNGUARDED, from the block alone."""
    if any(re.search(p, body) for p in CARRIERS):
        # A carrier only excuses the hazards a carrier can excuse.
        if hazard in {"sInf", "iInf", "sSup", "iSup", "ncard", "toNat", "toReal", "tsum"}:
            return "CARRIER"
    if any(re.search(p, body) for p in GUARDS):
        return "GUARDED"
    return "UNGUARDED"


def check(res: Result, cfg: RepoConfig) -> None:
    readings = _load_readings(cfg)
    res.total = len(cfg.nodes)
    counts = {"GUARDED": 0, "CARRIER": 0, "UNGUARDED": 0, "DECLARED": 0}

    for node in cfg.nodes:
        if not node.file:
            continue
        p = cfg.root / node.file
        if not p.exists():
            continue
        src = p.read_text(encoding="utf-8")
        spans = ls.frozen_blocks(src)
        if len(spans) != 1 or spans[0][1] < 0:
            continue
        res.count()
        body = ls.block_body(src, spans[0])
        for hazard, line_no, line in scan_block(body):
            reason = _declared(readings, node.id, hazard)
            if reason:
                counts["DECLARED"] += 1
                continue
            verdict = classify(body, hazard)
            counts[verdict] += 1
            if verdict == "UNGUARDED":
                res.fail(
                    f"{node.id}: undeclared `{hazard}` at block line {line_no}\n"
                    f"        {line[:100]}\n"
                    f"        No clause in this block rules the junk case out, and "
                    f"ledger/readings.yaml has no entry. Add a guard to the statement, "
                    f"or record why it is safe under hazards.{node.id}.{hazard}."
                )

    res.note(
        "hazards: {GUARDED} guarded by a clause, {CARRIER} absorbed by the carrier "
        "type, {DECLARED} declared in readings.yaml, {UNGUARDED} undeclared".format(**counts)
    )


def main(argv: list[str]) -> int:
    cfg = load(argv[1] if len(argv) > 1 else ".")
    return run("check_hazards", check, cfg)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
