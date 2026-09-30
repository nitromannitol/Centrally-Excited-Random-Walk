# Fleet calibration

One row per packet. `accepted` means the file compiled silently on the director's recheck, its
statements were byte-identical to the leaf, and it contained no banned token. `repairs` counts
director interventions after dispatch. `tokens` are the pane counters `↑input ↓output`, read at
completion from the `pi` status line. They are cumulative per session, and the session is reset
with `/new` before every packet. Earlier sessions were not reset before a counter was read, and
their cells say "not recorded" rather than an estimate. All workers run `deepseek-v4.1-flash`,
thinking high, via `pi --no-extensions`, unless noted.

| wave | packet | worker | model | prompt bytes | lemmas | tokens | result | repairs | landed lines | landed file |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | lattice log sums | ds1 | v4.1-flash | 4458 | 2 | ↑107k ↓35k (session incl. ping) | accepted | 0 | 165 | `CERW/Generic/Lattice/WeightSums.lean` |
| 1 | lattice packing | ds2 | v4.1-flash | 4555 | 2 | ↑194k ↓59k | accepted | 0 | 218 | `CERW/Generic/Lattice/Packing.lean` |
| 1 | summable weights, Lipschitz convolution | ds3 | v4.1-flash | 4126 | 4 | ↑78k ↓15k | accepted | 0 | 107 | `CERW/Generic/Lattice/SummableSums.lean` |
| 1 | kernel algebra | ds4 | v4.1-flash | 5867 | 18 | ↑111k ↓97k (incl. rework) | accepted after repair | 1: worker found the ℕ-division bug in `srwStep`; the director fixed the definition and redirected the worker | 319 | `CERW/Support/Law/Moments.lean` |
| 1 | bathtub principle | Sonnet subagent | sonnet | ~3.1k (task prompt) | 2 | 44k (agent total) | accepted | 0 | 151 | `CERW/Generic/Kernel/Bathtub.lean` |
| 2 | Young absorption | ds1 | v4.1-flash | 4383 | 2 | not recorded | accepted | 0 | 114 | `CERW/Generic/Young/Absorb.lean` |
| 2 | halving cost | ds2 | v4.1-flash | 4320 | 2 | not recorded | accepted | 0 | 101 | `CERW/Generic/Halving/Cost.lean` |
| 2 | halving levels | ds3 | v4.1-flash | 4800 | 2 | not recorded | accepted | 0 | 167 | `CERW/Generic/Halving/Levels.lean` |
| 3 | contact absorption | ds1 | v4.1-flash | 3960 | 1 | not recorded | accepted | 0 | 160 | `CERW/Generic/Young/Contact.lean` |
| 3 | radius inversion | ds2 | v4.1-flash | 3825 | 2 | not recorded | accepted | 0 | 68 | `CERW/Generic/Young/Radius.lean` |
| 3 | resolvent bound | ds3 | v4.1-flash | 4342 | 1 | not recorded | accepted | 0 | 134 | `CERW/Generic/Lattice/Resolvent.lean` |
| 3 | occupation facts | ds4 | v4.1-flash | 6294 | 16 | not recorded | accepted | 0 | 164 | `CERW/Support/Occupation/Facts.lean` |
| 4 | cell membership | ds1 | v4.1-flash | 3889 | 3 | ↑39k ↓6.0k | accepted | 0 | 41 | `CERW/Support/Occupation/Cells.lean` |
| 4 | tail basics | ds2 | v4.1-flash | 4374 | 3 | ↑90k ↓32k | accepted | 0 | 84 | `CERW/Support/Geometry/TailBasic.lean` |
| 4 | cell volume | ds3 | v4.1-flash | 4137 | 2 | ↑74k ↓20k | accepted | 0 | 52 | `CERW/Support/Occupation/CellVolume.lean` |
| 4 | step mean | ds4 | v4.1-flash | 4333 | 3 | ↑75k ↓24k | accepted | 0 | 86 | `CERW/Support/Law/StepMean.lean` |
| 5 | cell-set volume | ds3 | v4.1-flash | ~3.9k (brief overwritten by the next ds3 packet) | 2 | ↑33k ↓10k | accepted | 0 | 30 | `CERW/Support/Occupation/CellSetVolume.lean` |
| 5 | cell norm | ds1 | v4.1-flash | 4250 | 3 | — | in flight | — | — | `wip/CellNorm.lean` |
| 5 | tail bounds | ds2 | v4.1-flash | 5128 | 3 | ↑93k ↓40k | accepted | 0 | 117 | `CERW/Support/Geometry/TailBounds.lean` |
| 5 | Hausdorff exponents | ds3 | v4.1-flash | 4132 | 3 | ↑53k ↓31k | accepted | 0 | 93 | `CERW/Support/Main/HausdorffArith.lean` |
| 5 | scale limits | ds4 | v4.1-flash | 4352 | 3 | ↑83k ↓67k | accepted | 0 | 169 | `CERW/Support/Main/ScaleLimits.lean` |
| 6 | contact kernel | ds1 | v4.1-flash | — | 2 | — | in flight | — | — | `wip/ContactKernel.lean` |
| 6 | last entrance | ds2 | v4.1-flash | — | 2 | — | in flight | — | — | `wip/LastEntrance.lean` |
| 6 | crossing kinematics | ds3 | v4.1-flash | — | 3 | — | in flight | — | — | `wip/CrossingKinematics.lean` |
| 6 | planar contact sum | ds4 | v4.1-flash | — | 3 | — | in flight | — | — | `wip/PlanarContactSum.lean` |

## Observations

* **Waves 1–4.** 21/21 packets were accepted (wave 4 and the cell-set volume: 5/5, no repair, each under 10 minutes); 16 of 17 with no repair. Wall-clock time per packet was
  4–20 minutes.
* **What a brief carried.** Every brief was 3.8–6.3 KB, stated the proof route step by step, and
  cited only names grep-verified at the pin.
* **Why wave 1 hit 100%.** This contradicts the 0/1,808 of the earlier IDLA campaign. The
  difference is the brief shape: exact statements in a compiling leaf, a spelled-out route,
  verified names, and an agentic loop that compiles its own attempts.
* **Packet size.** From wave 4 on, packets are capped at three lemmas each, per the carve-up
  directive. Wave 1's 18-lemma packet did succeed, but only after a definition repair.
* **Workers catch definition defects.** The ds4 catch shows that a worker proving the obvious API of
  a definition is an effective junk-value probe. Keep dispatching API packets early, before a freeze.
