# Ruling: the lattice kernel asymptotics are proved, and the hypothesis is removed

**The author's ruling.** Lattice-Probability now proves the asymptotics of the lattice Green function
and potential kernel:

```lean
theorem LatticeProb.External.potentialKernelAsymptotics_holds (d : ℕ) :
    LatticeProb.External.PotentialKernelAsymptotics d
```

It is in `LatticeProb/External/PotentialKernelAsymptoticsProved.lean`, at commit `4bdbaa4`, with no
`sorry` and no `axiom`. This repository is to consume it:
- update the Lattice-Probability pin;
- drop the hypothesis `hK : CERW.External.LatticePotentialKernel d` from the Euclidean anchors, so
  that they become unconditional;
- retire the External;
- re-freeze the anchors, recording the ruling and bumping the node versions.

## What changed

- **The pin.** `lakefile.lean` and `lake-manifest.json` pin Lattice-Probability at
  `4bdbaa4b05ca02163aacea948cfc385be6bb61b6`, where they had `b617769`. The Mathlib pin
  (`81a5d257`) and the toolchain are unchanged, and Lattice-Probability pins the same Mathlib.
- **The proposition is the same.** The body of `LatticeProb.External.PotentialKernelAsymptotics d`
  is, clause for clause, the body of the retired `CERW.External.LatticePotentialKernel d`:
  - the planar partial-sum limit with the `(2/π) log |x| + κ + O(|x|^{-2})` expansion;
  - for `d ≥ 3`, the Green-function expansion `2/((d − 2) ω_d) |x|^{2−d} + O(|x|^{-d})`.

  The kernel bridge (`CERW/Support/LocalTime/KernelAsymptotics.lean`, formerly
  `KernelExternal.lean`) consumes the library's proposition unchanged, and
  `exists_kernelFacts (hd : 2 ≤ d)` now takes no hypothesis.
- **The frozen statements.** In each of six frozen statements the single binder
  `(hK : CERW.External.LatticePotentialKernel d)` is deleted, and nothing else changes. They are
  re-registered as version 3, SEALED:
  - `thm-shape`, `thm-fluctuations` and `eq-hausdorff`;
  - `lem-local`, `lem-radial` and `prop-coarse`.
- **`lem-geometry`** never carried the hypothesis. Its frozen bytes are unchanged, and it stays at
  version 2.
- **The External node `ext-lattice-kernel` is retired.** `CERW/External/LatticePotentialKernel.lean`
  and the aggregator `CERW/External.lean` are removed, and the manifest has no FROZEN node.
  `ASSUMPTIONS.md` says that nothing is assumed.

## Evidence

- `lake build` completes (8,912 jobs) with no error and no warning.
- `#print axioms` for the seven anchors, and for
  `LatticeProb.External.potentialKernelAsymptotics_holds`, gives
  `[propext, Classical.choice, Quot.sound]`.
- `python3 tools/verify.py` passes; see the commit.

## Consequence

**The only assumption of the Euclidean development is discharged.** Every registered theorem is
unconditional.
