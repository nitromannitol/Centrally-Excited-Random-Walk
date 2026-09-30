# leanform_tools

The deterministic gates for the `lean-form` protocol, in one package, shared
by every paper repository instead of vendored per repo.

## Why this exists

Each repository used to carry its own copy of roughly a dozen checkers. The
copies drifted, and the drift was invisible, because a checker whose regex no
longer matches its repo does not fail — it passes, having inspected nothing.
Measured on 2026-09-23 across the fleet:

- **nine checkers in four repositories exited 0 having inspected zero items**,
  two of those repositories being released work. `Parking-Sharpness`'s
  citation checker reported `0 correct, 0 stale` over 426 real citations,
  because line 37 still read `re.compile(r"rotor\.tex:(\d+)…")`.
- **four repositories' axiom gate failed open**: no return-code check, so a
  Lean probe that crashed read as a clean axiom closure.
- two repositories' entire `REVIEWED` audit table still held **another
  paper's node ids** — 26 of 26 foreign.

So the rule this package enforces on itself: **no paper name, library name or
`Frozen/` path may appear as a literal anywhere in it.** Every one of those is
derived from `ledger/manifest.yaml`.

## The meta-check

`gate.Result.done()` fails a checker that processed nothing:

```
paper_citations: META-CHECK FAILED — processed 0 items of 426 available.
A checker that inspects nothing does not pass.
```

Exit codes are `0` pass, `1` a real failure, **`2` vacuous**. Code 2 is
separate on purpose: in a CI log, "inspected nothing" and "clean" must not
look alike. A checker with genuinely nothing to do declares it in code
(`res.vacuous_ok = "this repo has no FROZEN nodes"`) and says so in its
output.

## Use

```bash
python3 -m leanform_tools.verify <repo>              # the whole pipeline
python3 -m leanform_tools.verify <repo> --skip-lake  # pure-Python gates only
python3 -m leanform_tools.check_manifest <repo>      # one gate
```

`verify` runs unit tests first (a broken checker must not issue a verdict),
then the pure-Python gates, then the three that invoke Lake, and
short-circuits: once the hash gate fails there is no point auditing exponents.

## The gates

| module | asks | Lake |
|---|---|---|
| `check_manifest` | one block per file, hash matches, declarations match, one owner per frozen file, `sorry` only as a registered draft, no banned token, paper pinned | no |
| `check_axioms` | every export's axiom closure ⊆ {`propext`, `Classical.choice`, `Quot.sound`}, `sorryAx` only for a registered draft | **yes** |
| `check_warnings` | the build's warning multiset is exactly one sorry-warning per `DRAFT_SORRY` node | **yes** |
| `check_coverage` | every labelled statement in the paper is claimed by a node; an unlabelled one is a hard error | no |
| `check_clauses` | every node has a written reading against the paper | no |
| `check_constants` | an existential constant is bound before every parameter it must not depend on | no |
| `check_exponents` | the paper's and Lean's exponent multisets agree | no |
| `check_hazards` | every junk-value hazard is guarded, absorbed by the carrier, or declared | no |
| `check_progress` | a change may close holes; it may not open them | no |
| `paper_anchors` / `paper_citations` | recorded line ranges still match the labels | no |
| `sync_docs` / `assumptions` / `certificate` | every number in prose is generated, not restated | certificate |
| `linkcheck` | no Markdown link points at a deleted file | no |
| `freeze` | register a node and hash its block | no |

## Per-repo data

Anything paper-specific lives in the repo, never here:

- `ledger/manifest.yaml` — `source_pin.file` gives the paper; `library:` gives
  the Lean library when it cannot be inferred from the exports.
- `ledger/readings.yaml` — clause readings, constant waivers, exponent
  waivers, hazard declarations, and the paper's `noise` vocabulary.
- `ledger/holes.json` — the hole baseline for `check_progress`.

`python3 -m leanform_tools.readings --extract <repo>` recovers
`readings.yaml` from an incumbent `tools/` directory by parsing it as a syntax
tree, never importing it. It **refuses** any entry whose key is not a node of
that repo's own manifest, and says how many it refused — which is what stops a
migration from importing another paper's readings wholesale.

## Tests

```bash
python3 -m unittest discover -s leanform_tools/tests -t .
```

159 tests. Most encode a specific false success observed in the fleet: a
checker that inspected nothing, an axiom probe that crashed and read as clean,
`Set.ncard` on an infinite set, a manifest name that is an ASCII truncation of
a non-ASCII identifier, a certificate that overwrote a good file on failure.
