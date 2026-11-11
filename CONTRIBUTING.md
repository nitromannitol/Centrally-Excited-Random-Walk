# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

The shared analytic library comes from the separate
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability) library, which
`lakefile.lean` requires as a `git` dependency pinned to an exact commit; Lake materializes it
under `.lake/packages/`. It is read-only for this project: extensions belong under `CERW/`, and
contributors must not edit the dependency's sources.

## Building locally

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned in `lean-toolchain`.

```bash
lake exe cache get    # prebuilt mathlib
lake build            # the dependencies and the library
lake build CERWAudit  # the mathlib-only comparator surface
```

The library must build with **no warnings** and no linter suggestions. The only intentional
`sorry`s are the seven statement-level ones in the four
`CERWAudit/<Pair>/Challenge.lean` files, each checked against its solution by
[leanprover/comparator](https://github.com/leanprover/comparator).

## The main results and the axiom audit

The introduction's theorems are stated in `CERW/MainTheorems.lean`
(`CERW.MainTheorems.limit_shape`, `fluctuation_rates`, `sharp_radii`, `sharp_radii_lil`,
`sharp_bulk`, `sharp_width` and `norm_shape`). The registered statements of the paper are in
`CERW/LimitShapes/Frozen/`.

```bash
lake env lean tools/AllAxioms.lean    # the axioms of every declaration of the library
python3 tools/verify_current.py       # the paper: manifest, coverage, axioms, documentation
```

The second command needs the Python environment described under Building in the
[`README.md`](README.md).

`CERW/Meta/AxiomsAudit.lean` prints the axiom reports of the registered statements. It is built
only as an explicit target (`lake build CERW.Meta.AxiomsAudit`) and is not imported by the root
module, because a `#print axioms` command runs again whenever its module is rebuilt.
`tools/AllAxioms.lean` fails on any declaration of the library that depends on an axiom other
than `propext`, `Classical.choice` and `Quot.sound` (a `sorry` appears there as `sorryAx`), and
on a library file that the root module does not import.

## Conventions for Lean files

- No `sorry`, `admit`, `native_decide`, new `axiom` or `set_option maxHeartbeats` in the library.
- Keep new Lean files under 1500 lines.
- Statements stay faithful to the paper and are referred to by LaTeX label, never by line number.
- New declarations go under `CERW/`. The dependencies under `.lake/packages/` are read-only.
- Avoid `lake clean`: it removes the prebuilt mathlib and Lattice-Probability builds and forces
  the dependencies to be rebuilt from source. To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/CERW` (and the corresponding
  `.lake/build/ir/CERW`) and run `lake build` again.
- Lake invalidates by content hash, not by modification time, so `touch` has no effect. To
  rebuild a single module, delete its `.olean` under `.lake/build/lib/lean/` and run
  `lake build`.

### Elaboration policy for new files

These rules come from measured elaboration passes over this and the sibling developments.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with `nlinarith`. When a
  nonlinear fact is needed, hoist it into a small `private` lemma over abstract real variables,
  so that `Real.rpow` and `Real.exp` terms never enter a numeric tactic.
- Prefer the explicit `mul_le_mul_of_nonneg_*` and `add_le_add_*` lemmas to `gcongr` on goals
  over `ℝ`.
- Use `positivity` for sign goals only.
- Before `ring` or `field_simp` on an expression built with `set`, run `clear_value` on the
  bound names.
- Never raise `maxHeartbeats`.

## Comparators

`CERWAudit/` holds one pair per group of main theorems, `CERWAudit/<Pair>/Challenge.lean` and
`Solution.lean`, with a `comparator.json` that permits exactly `propext`, `Classical.choice` and
`Quot.sound`. A challenge imports only mathlib. Do not add a declaration to a challenge that the
statement does not need, and do not change a challenge without checking it against the paper's
statement.

```bash
bash CERWAudit/check_standalone.sh --vocabulary
```

This checks that each challenge elaborates on mathlib alone and that the vocabulary blocks of a
challenge and of its `SolutionBasic.lean` stay byte-identical; run it after editing either file.
[`CERWAudit/README.md`](CERWAudit/README.md) gives the commands that run the comparator itself. A
missing pair, a missing tool or a failed kernel check is a failure.

## Continuous integration

- **CI** (`.github/workflows/build.yml`) builds the library and the comparator surface, rejects
  any warning or linter suggestion in the library, and runs the manifest, axiom, kernel-replay
  and statement-type checks.
- **Comparator audit** (`.github/workflows/comparator.yml`) runs the official comparator on every
  pair under `CERWAudit/`, with the Lean kernel and the independent nanoda kernel.
