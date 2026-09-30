# Ruling: the seven Euclidean statements are promoted from SEALED to PROVED

**The author's ruling.** The promotion from SEALED to PROVED is authorized for the seven existing
statements once the final `check_axioms` passes, and it is to be recorded.

## The condition

The final `check_axioms` passed at commit `1e956c5`, the commit that removed the kernel hypothesis:
- `python3 tools/verify.py` exits 0, with all 15 gates passing;
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of the seven theorems.

## What is promoted

| node | Lean | version |
|---|---|---|
| `lem-geometry` | `CERW.Frozen.potential_geometry` | 2 |
| `thm-shape` | `CERW.Frozen.ball_shape` | 3 |
| `thm-fluctuations` | `CERW.Frozen.fluctuation_bounds` | 3 |
| `eq-hausdorff` | `CERW.Frozen.hausdorff_bound` | 3 |
| `lem-local` | `CERW.Frozen.local_time_potential` | 3 |
| `lem-radial` | `CERW.Frozen.radial_test` | 3 |
| `prop-coarse` | `CERW.Frozen.coarse_bounds` | 3 |

The `state:` field is the only thing that changes. The frozen bytes, their hashes and the versions
stay as they are.

## The audits behind it

- `ledger/audits/postseal-audit.md`: PASS on all five points.
- `ledger/audits/fable-audit-1.md` and `ledger/audits/fable-audit-2.md`: both PASS, with no
  defect.

**These audits read the version 2 statements.** Version 3 of the six statements that carried the
kernel hypothesis differs from version 2 only in deleting the binder
`(hK : CERW.External.LatticePotentialKernel d)`. The proofs apply the same Support theorems, now to
the kernel facts obtained from `LatticeProb.External.potentialKernelAsymptotics_holds`. The
library's proposition has the same body as the retired External; see
`ledger/approval/KERNEL-ASYMPTOTICS.md`.
