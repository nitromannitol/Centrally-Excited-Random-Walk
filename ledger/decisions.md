# The author's rulings on the revised surface

Each entry records one ruling of the author, what it changed, and the evidence the change was
landed on. The earlier rulings are recorded in `ledger/approval/`.

## D1 (2026-10-01). Erratum: `thm-sharp-width` is re-frozen as version 2

**The author's ruling.** Re-freeze `thm-sharp-width` (`CERW.Frozen.sharp_width`,
`CERW/Frozen/SharpWidth.lean`) as version 2, with the split drafted and proved in
`scratch/Frozen/SharpWidthSplit.lean`:
- part (a), the polynomial lower bound, is unconditional;
- part (b), the iterated logarithm, alone takes `CERW.External.StoutLIL` as a hypothesis.

**Why.** Version 1 carried `hLIL : CERW.External.StoutLIL.{u}` as a hypothesis of the conjunction
(a) ∧ (b), but only (b) uses it (paper line 1647). So (a) was formally conditional, while the
paper's (a) is not. The proved-gate audit graded this CONCERN (`ledger/audits/proved-gate-audit.md`);
the proposal is in the supervisor record.

**What changed.**
- The frozen block. The binder `(hLIL : CERW.External.StoutLIL.{u})` is deleted, and the second
  conjunct begins with `CERW.External.StoutLIL.{u} →`. Every other byte is unchanged.
- The proof. Part (a) is `CERW.Support.Lower.sharp_width_poly_of`, which needs no law of the iterated
  logarithm. Part (b) is the second conjunct of `CERW.Support.Lower.sharp_width_of`.
- The manifest. The node is now version 2 with `frozen_sha256`
  `33c8d67f92937c4993df7f3a5cf0fa8c7871390124e8971eab54adbd076f20da`, registered with the vendored
  `leanform_tools.freeze`. The entry keeps its place in the manifest.
- The consumers. The guard `CERW.Support.Guards.sharp_width_applies` takes the new form. The draft
  Prop `CERW.Support.Statements.sharp_width` stays in its version 1 form, because
  `sharp_width_of` proves it. Its docstring now says so.
- The documents. README, PROOF, CORRESPONDENCE, `ledger/readings.yaml` and CERTIFICATE now
  describe `hLIL` as the premise of part (b) only.

**Version 2 is at least as strong as version 1.** `scratch/SharpWidthV2ImpliesV1.lean` derives the
version 1 statement, verbatim, from the version 2 theorem.

**Evidence.**
- `lake build` passes, with no error and no warning.
- `#print axioms CERW.Frozen.sharp_width` gives `[propext, Classical.choice, Quot.sound]`.
- `python3 tools/verify.py` exits 0, with all 15 gates passing.

## D2 (2026-10-01). P5: the 30 statements of the revised paper are promoted from SEALED to PROVED

**The author's ruling.** P5 is approved. The 30 SEALED nodes of the revised surface are promoted to
PROVED. Every one of them has been independently audited.

**What changed.** Only the `state:` field changed, from `SEALED` to `PROVED`, for all 30 nodes. The
frozen bytes, their hashes and the versions stay as they are. The manifest now has 37 `PROVED` nodes
(the seven first-version statements of G8 and these 30) and 2 `FROZEN` Externals, the martingale
CLT and Stout's LIL. CERTIFICATE, CORRESPONDENCE, README and PROOF are regenerated, and
`ledger/FRONTIER.md` and STATUS are updated.

**The audits behind it.**
- The four pre-freeze readings (`ledger/audits/prefreeze-reading-*.md`).
- The post-seal audit of the first 18 sealed nodes (`ledger/audits/postseal-revised-audit.md`),
  which found no defect.
- The pre-landing audit of the Support theorems behind the last seals
  (`ledger/audits/prelanding-audit.md`).
- The audit of the Theorem 1.2 and Proposition 7.1 proofs (`ledger/audits/outer-radius-audit.md`).
- The refute-first audit of all 30 nodes (`ledger/audits/proved-gate-audit.md`): 29 PASS, 1 CONCERN,
  0 DEFECT. The CONCERN was `hLIL` on part (a) of `thm-sharp-width`, and D1 resolves it.
- Stout's predictable-bound form is confirmed against Stout (1970)
  (`ledger/audits/stout-source.md`).

**`thm-sharp-width` is promoted at version 2.** The audits read version 1. Version 2 differs from
version 1 only in moving the binder `hLIL` onto part (b), which is the change the proved-gate audit
recommended. Version 2 implies version 1 verbatim (see D1). This follows the precedent of
`ledger/approval/PROVED-PROMOTION.md`, where version 3 of six statements was promoted on audits of
version 2, because version 3 differs from version 2 only in deleting one binder.

**Still held for the author.** P6, the AI paragraph of the paper (`limit-shapes.tex:303`).

## D3 (2026-10-01). The pin: the paper is reconciled with the frozen statements

**The author's ruling.** D3 is approved. The pinned text `paper/limit-shapes.tex` is reconciled with
the frozen statements: where the paper and the frozen blocks differ, the compiling Lean is the
authority, so the paper was edited to state what the frozen statements state. This closes P6, the AI
paragraph, whose final form is in the re-pinned text.

**What changed.** Only the paper and its pin changed. `paper/limit-shapes.tex` was edited (notation,
the norm hypothesis, the discussion of Theorem~1.3 parts~(i) and~(iv), and the AI paragraph).
`ledger/manifest.yaml` records the new `source_pin.sha256`
`d39e7f24d52e7a095508daefd075c7e9651289be97cfe5eadd67d8008aaa8328` and the shifted `source:` line
ranges. The frozen bytes, their hashes, their versions and their states are unchanged: no `state:`,
`version:` or `frozen_sha256:` line moves. CERTIFICATE, CORRESPONDENCE and ASSUMPTIONS are
regenerated.

**Evidence.** `check_manifest`, `check_coverage`, `paper_anchors`, `check_exponents`,
`check_constants`, `check_clauses`, `check_hazards` and `check_progress` pass on the re-pinned tree;
`tools/verify.py` passes all 15 gates after regeneration.

**Recorded** by the active worker on the author's instruction to continue the critical path
(2026-10-01). The frozen surface was not re-opened.

## D4 (2026-10-01). One version only: the earlier Euclidean version is removed

**The author's ruling.** The repository is a single-version product based solely on the final paper
`paper/limit-shapes.tex`. The earlier pinned paper and the seven nodes frozen from it are removed:
`ball-shape`, `fluctuation-bounds`, `hausdorff-bound`, `potential-geometry`, `radial-test`,
`coarse-bounds` and the ball shape theorem, together with `paper/cerw-flat.tex`, `paper/cerw.tex`,
`paper/sections/` and `paper/proof-audit-source.md`.

**What changed.**
- Five nodes are deleted outright (`ball-shape`, `fluctuation-bounds`, `hausdorff-bound`,
  `potential-geometry`, `radial-test`) with their frozen files and manifest entries; none is used by a
  remaining statement.  The ball shape theorem is folded into the final-paper node `thm-shape`: its
  proof is now derived directly from the kernel facts in `Support/Main/LimitShape.lean`.
- Two nodes are kept because final-paper statements depend on them, and re-sourced to the final paper
  as the Euclidean case of its norm lemmas: `local-time-potential` (`limit-shapes.tex:385-401`,
  `lem:local`) and `coarse-bounds` (`limit-shapes.tex:547-554`, `prop:coarse`).  Their frozen bytes,
  hashes, versions and states are unchanged; only the `source:` line and the docstring move.
- `ledger/manifest.yaml` drops the five entries and cites only `limit-shapes.tex`; the header no longer
  mentions a second version.  CORRESPONDENCE, PROOF, README and `formalization.yaml` carry no
  version-history commentary.  `CERWAudit/LimitShape` is re-pointed from the ball shape theorem to
  `CERW.StatementAudit.LimitShape.limit_shape`.

**Evidence.** `lake env lean` accepts `Support/Main/LimitShape.lean`, `CERW/Frozen/LimitShape.lean`,
`CERW/Frozen/LocalTimePotential.lean`, `CERW/Frozen/CoarseBounds.lean`, `Support/Lower/BulkProfile.lean`,
`Support/Lower/SharpWidth.lean` and `CERW/Frozen.lean`; `lake build CERWAudit` succeeds; the comparator
prints `Your solution is okay!` with the nanoda kernel enabled.

**Recorded** by the active worker on the author's instruction (2026-10-01).  The remaining frozen
statements were not re-opened.
