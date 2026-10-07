# CERWAudit Comparator Surface

This directory contains a Mathlib-only comparator challenge for the limit shape theorem
(`thm:shape`, `paper/limit-shapes.tex:106-119`), the headline result of the formalization of
*Kozma's centrally excited walk converges to a Euclidean ball* (Ahmed Bou-Rabee and Yuval Peres).

| Directory | Checked theorem |
| --- | --- |
| `LimitShape/` | `CERW.StatementAudit.LimitShape.limit_shape` |

`LimitShape/Challenge.lean` imports only `Mathlib`, rebuilds from scratch every definition
needed to read the theorem — the lattice `Site d = Fin d → ℤ` and the Euclidean norm
`euclidNorm`, the one-step kernel (`unit`, `unitSteps`, `firstStep`, `srwStep`, `stepProb`),
the Prop-valued CERW law `IsCERW`, the departure local time `localTime`, and the departure
range `A_n = departureRange` — states the theorem, and ends with one `sorry`, the proof being
checked.

## What Is Checked

The theorem states that for `d ≥ 2` and `0 < ε < 1/d`, almost surely, with
`r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}`:

- **Shape.** For every `0 < η < 1` and all sufficiently large `n`, the departure range
  `A_n` contains `{x : |x| < (1-η) r_n}` and is contained in `{x : |x| < (1+η) r_n}`.
- **Local times.** `sup_x |ℓ_n(x) - 2 d ε (r_n - |x|)_+| ≤ η r_n` eventually.
- **Recurrence.** Every site of `ℤ^d` is visited infinitely often.

The model is the centrally excited random walk of the paper: on its first departure from a
nonzero site `x` it steps `x ± e_i` with probability `1/(2d) ∓ (ε/2) x_i/|x|`, and takes a
simple random walk step on every departure from the origin and every later departure.  The
law is fixed by the cylinder-factorization predicate `IsCERW`; the sample space, the measure
and the realization are arbitrary.

The library's certified statement is `CERW.Frozen.limit_shape`
(`CERW/Frozen/LimitShape.lean`), which is proved from the kernel asymptotics of the paper via
`CERW.Support.Main.ball_shape_of_kernelFacts`.  The challenge states the same theorem over the
copied vocabulary.

## Definition Provenance

The challenge definitions are statement-level copies of the repository definitions needed to
state the theorem surface.

| Challenge declaration | Repository source |
| --- | --- |
| `Site`, `unit`, `euclidNorm` | `LatticeProb/Site.lean`, `LatticeProb/Walk/Ball.lean` (the `lattice-probability` dependency) |
| `unitSteps`, `firstStep`, `srwStep`, `stepProb` | `CERW/Model/Kernel.lean` |
| `IsCERW` | `CERW/Model/Law.lean` |
| `localTime`, `departureRange` | `CERW/Model/Occupation.lean` |

## Reproducing The Checks

The comparator configuration permits only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and enables the nanoda replay.  The challenge elaborates standalone against this repository's
Mathlib toolchain:

```bash
bash CERWAudit/check_standalone.sh CERWAudit/LimitShape/Challenge.lean
bash CERWAudit/check_standalone.sh --vocabulary   # Challenge vs SolutionBasic
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'` warning.  The solution
builds with `lake build CERWAudit`.  Then, with `leanprover/comparator`, `lean4export` (at
the toolchain's tag) and `landrun` built at the pins below, from the repository root:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator CERWAudit/LimitShape/comparator.json
```

expecting `Your solution is okay!`.

**Status.**  The challenge elaborates on Mathlib alone with one intentional `sorry`; the
solution builds and proves the byte-identical statement from `CERW.Frozen.limit_shape` through
`CERWAudit/Support/LimitShapeBridge.lean`; `leanprover/comparator` at commit
`575674928e239f5bc452aab72d1dd7b0f1326494`, with nanoda at `6ae1f0cd962f081f6c423454c5da729d841236a7`
and landrun at `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, printed `Your solution is okay!`
with the nanoda kernel enabled.
