# Freeze of the statements of the revised paper

**The author's rulings.** The work was authorized under gates G1–G8, and batches were to be frozen
under G7's standing approval.
- **G1:** the statements are declared final, and the revised text is pinned as
  `paper/limit-shapes.tex`, with its sha256 in `source_pin`.
- **G2:** the eight first-version nodes are relabelled.
- **G3:** of the four lemmas stated "on the event", `lem:crossing` and `lem:outer-crossing` are
  read deterministically, and `lem:contact` and `lem:separated-brackets` as probability bounds.
- **G4:** Theorem 1.3 is split into four parts.
- **G5:** the two Externals are those of the plan, after the sources were checked.
- **G7:** the batches are frozen under standing approval and presented in HANDOFF.md.

## What is frozen

- **The pin.** `source_pin` is `paper/limit-shapes.tex`. Every one of its 27 labelled theorem-like
  environments is claimed by a node (`check_coverage`).
- **Theorem nodes.** There are 30, one file each under `CERW/Frozen/`:
  - one per environment;
  - Theorem 1.3 as four nodes, `thm-sharp-radii`, `thm-sharp-radii-lil`, `thm-sharp-bulk` and
    `thm-sharp-width`, one per part.
- **Two Externals** under `CERW/External/`, state FROZEN:
  - `ext-martingale-clt`, Hall–Heyde Corollary 3.1 for one martingale with deterministic
    normalizers;
  - `ext-stout-lil`, Stout (1970), with a predictable bound on the increments.
- **The relabelled first-version nodes (G2).** Their frozen text is unchanged; only the ids change,
  and their `source:` now cites `paper/cerw-flat.tex` by line, with no label:
  - `thm-shape` → `ball-shape`;
  - `thm-fluctuations` → `fluctuation-bounds`;
  - `eq-hausdorff` → `hausdorff-bound`;
  - `lem-local` → `local-time-potential`;
  - `lem-geometry` → `potential-geometry`;
  - `lem-radial` → `radial-test`;
  - `prop-coarse` → `coarse-bounds`.

## Evidence before the freeze

- **Readings.** Four independent refute-first readings covered all 32 nodes:
  - `ledger/audits/prefreeze-reading-introduction.md`;
  - `ledger/audits/prefreeze-reading-norm-setup.md`;
  - `ledger/audits/prefreeze-reading-norm-shape.md`;
  - `ledger/audits/prefreeze-reading-limit-laws.md`.

  Two DEFECTs were found and fixed before the freeze. Both were the same parenthesization of the
  scaled cell set in the volume clauses of Theorem 1.2 and Proposition 6.1.
- **The Externals.** The source check is `ledger/audits/external-sources.md`, and both verdicts are
  "implied, with a remark":
  - the Hall–Heyde special case with a non-trivial `ℱ 0`;
  - Stout's `K_n = B_n u_n / s_n`.
- **NL twins:** `ledger/nl/<id>.tex`.
- **Non-vacuity:**
  - `CERW.Support.Main.exists_norm_realization`: the walk with norm `Ψ` exists for every norm and
    every choice of subgradients;
  - `CERW.Support.Main.euclidean_norm_hypotheses`: the Euclidean norm meets the norm hypotheses;
  - `CERW.Support.Drift.exists_isDriftCERW`.
- **Consumption.** Every frozen theorem is proved from, or reduces to, the `Prop` of the same
  statement in `CERW/Support/Statements.lean`, which Support proofs assume and discharge.

## State at the freeze

- **13 theorem nodes are SEALED**, each by a Support proof:
  - `thm-shape`, `lem-freedman`, `lem-geometry`, `lem-crossing`, `lem-cap`, `lem-near-far`;
  - `lem-ballpotential`, `lem-layer`, `lem-radial`, `lem-exp-deviation`, `thm-sharp-width`;
  - `lem-outer-crossing`, `lem-cell`.
- **The rest are DRAFT_SORRY.** The hole baseline records their registered `sorry`s
  (`ledger/holes.json`).
