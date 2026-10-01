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
