# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively solicited
collaborative project, but issues and pull requests are welcome.

The shared analytic library comes from the separate
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability) library, which
`lakefile.lean` requires as a `git` dependency pinned to an exact commit; Lake materializes it
under `.lake/packages/Lattice-Probability` (or `lattice-probability`). It is read-only for
this project: extensions belong under `CERW/`, and contributors must not edit the dependency's
sources.

## Building locally

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build           # the dependencies and the project
lake build CERWAudit # the Mathlib-only comparator surface
```

The production build is required to emit no Lean or linter warnings. The sole exception is
`CERWAudit/LimitShape/Challenge.lean`, which contains one documented statement-level `sorry`,
checked against its completed solution by `leanprover/comparator`.

A few practical notes for working with a development of this size:

- **Never run `lake clean`.**  It wipes the `mathlib` and `Lattice-Probability` oleans and
  forces a multi-hour rebuild from source. To force a project-only rebuild, remove the project
  build artifacts under `.lake/build/lib/lean/CERW` (and the corresponding
  `.lake/build/ir/CERW`) and re-run `lake build`. - **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so `touch` does nothing;
  delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the module. - **The main results** are in `CERW/Frozen/`. The axiom report is
  `lake build CERW.Meta.AxiomsAudit`, built only as an explicit target. - **The comparator surface** under `CERWAudit/` is deliberately not a default target. Run
  `bash CERWAudit/check_standalone.sh --vocabulary` after editing a challenge or its
  `SolutionBasic.lean`; the two vocabulary blocks must stay byte-identical.

## Elaboration policy for new files

These rules come from measured elaboration passes over this and the sibling developments.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with `nlinarith`. When
  a nonlinear fact is needed, hoist it into a small `private` lemma over abstract real variables
  so that `Real.rpow` and `Real.exp` terms never enter a numeric tactic. - Prefer the explicit `mul_le_mul_of_nonneg_*` / `add_le_add_*` lemmas to `gcongr` on goals
  over `ℝ`. - Use `positivity` for sign goals only. - Before `ring` or `field_simp` on an expression built with `set`, run `clear_value` on the
  bound names. - Never raise `maxHeartbeats`. - Keep Lean files under 1500 lines. 