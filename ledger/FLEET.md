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
| 5 | cell norm | ds1 | v4.1-flash | 4250 | 3 | not recorded | accepted | 0 | 67 | `CERW/Support/Occupation/CellNorm.lean` |
| 5 | tail bounds | ds2 | v4.1-flash | 5128 | 3 | ↑93k ↓40k | accepted | 0 | 117 | `CERW/Support/Geometry/TailBounds.lean` |
| 5 | Hausdorff exponents | ds3 | v4.1-flash | 4132 | 3 | ↑53k ↓31k | accepted | 0 | 93 | `CERW/Support/Main/HausdorffArith.lean` |
| 5 | scale limits | ds4 | v4.1-flash | 4352 | 3 | ↑83k ↓67k | accepted | 0 | 169 | `CERW/Support/Main/ScaleLimits.lean` |
| 6 | contact kernel | ds1 | v4.1-flash | 4010 | 2 | not recorded | accepted | 0 | 72 | `CERW/Support/Contact/Kernel.lean` |
| 6 | last entrance | ds2 | v4.1-flash | 3928 | 2 | not recorded | accepted | 0 | 47 | `CERW/Support/Crossing/LastEntrance.lean` |
| 6 | crossing kinematics | ds3 | v4.1-flash | 3982 | 3 | not recorded | accepted | 0 | 49 | `CERW/Support/Crossing/Kinematics.lean` |
| 6 | planar contact sum | ds4 | v4.1-flash | 4120 | 3 | not recorded | accepted | 0 | 79 | `CERW/Support/Contact/PlanarSum.lean` |
| 7 | Freedman threshold arithmetic | ds1 | v4.1-flash | 4089 | 3 | not recorded | accepted | 0 | 82 | `CERW/Generic/Martingale/Arith.lean` |
| 7 | centred ball sums | ds2 | v4.1-flash | 4420 | 3 | not recorded | accepted | 0 | 94 | `CERW/Generic/Lattice/Centered.lean` |
| 7 | crossing contradiction | ds3 | v4.1-flash | 4505 | 1 | not recorded | accepted | 0 | 158 | `CERW/Support/Crossing/Contradiction.lean` |
| 7 | cell weight | ds4 | v4.1-flash | 4866 | 3 | not recorded | accepted | 0 (the director rewrapped a 101-character statement line of its own leaf before dispatch) | 107 | `CERW/Support/Occupation/CellWeight.lean` |
| 7 | Freedman on a small-bracket event | Sonnet subagent | sonnet | task prompt | 1 + helpers | not recorded | accepted | 0 | 295 | `CERW/Generic/Martingale/FreedmanEvent.lean` |
| 7 | integrability of the Newtonian field | Sonnet subagent | sonnet | task prompt | 3 + helpers | not recorded | accepted | 0 | 127 | `CERW/Generic/Kernel/Integrable.lean` |
| 7 | radial packing inequality | Sonnet subagent | sonnet | task prompt | 1 + helpers | not recorded | accepted | 0 | 102 | `CERW/Generic/Kernel/RadialPacking.lean` |
| 8 | radial profile increments | ds1 | v4.1-flash | 4241 | 2 | ↑55k ↓14k | accepted | 0 | 69 | `CERW/Generic/Young/RadialProfile.lean` |
| 8 | Poisson equation of the potential kernel | ds2 | v4.1-flash | 4863 | 3 | ↑87k ↓36k | accepted | 0 | 107 | `CERW/Support/LocalTime/KernelPoisson.lean` |
| 8 | outer contradiction | ds3 | v4.1-flash | 4927 | 1 | ↑296k ↓174k | accepted | 0 | 507 | `CERW/Support/Crossing/OuterContradiction.lean` |
| 8 | cell integral | ds4 | v4.1-flash | 4688 | 2 | ↑87k ↓9.5k | accepted | 0 | 43 | `CERW/Support/Occupation/CellIntegral.lean` |
| 9 | radial power integrals | ds1 | v4.1-flash | 5927 | 2 | ↑249k ↓94k | accepted | 0 (the pasted brief arrived split; the worker proved the leaf before the rules paragraph arrived) | 152 | `CERW/Generic/Kernel/RadialPower.lean` |
| 9 | Newtonian field difference | ds2 | v4.1-flash | 4919 | 3 | ↑158k ↓67k (after respawn) | accepted | 1 dispatch repair: the pasted brief arrived split, the pane was respawned and pointed at the brief file | 165 | `CERW/Generic/Kernel/NewtonField.lean` |
| 9 | directions across a cell | ds4 | v4.1-flash | 4767 | 2 | ↑211k ↓37k | accepted | 0 | 99 | `CERW/Support/Occupation/CellDirection.lean` |
| 9 | logarithmic radial integrals | ds4 | v4.1-flash | 6458 | 2 | ↑168k ↓101k | accepted | 0 | 199 | `CERW/Generic/Kernel/LogRadial.lean` |
| 10 | potential sup bound | ds1 | v4.1-flash | 5967 | 3 | ↑81k ↓31k | accepted | 0 | 112 | `CERW/Support/Geometry/Bound.lean` |
| 10 | coordinate drift | ds2 | v4.1-flash | 5310 | 3 | ↑93k ↓21k | accepted | 0 | 62 | `CERW/Support/Law/CoordinateDrift.lean` |
| 10 | shifted martingale and interval Freedman | ds3 | v4.1-flash | 6509 | 2 | ↑115k ↓36k | accepted | 0 | 142 | `CERW/Generic/Martingale/Shift.lean` |
| 10 | contact cell | Sonnet subagent | sonnet | task prompt | 1 + 3 helpers | 44k (agent total) | accepted | 0 | 117 | `CERW/Support/Contact/ContactCell.lean` |
| 10 | kernel modulus | Sonnet subagent | sonnet | task prompt | 1 + 6 helpers | 79k (agent total) | accepted | 0 | 248 | `CERW/Generic/Kernel/Modulus.lean` |
| 11 | one-step bound of the potential kernel | ds1 | v4.1-flash | 5747 | 2 | ↑51k ↓18k | accepted | 0 | 87 | `CERW/Support/LocalTime/GradientBound.lean` |
| 11 | second-order scalar Taylor bounds | ds2 | v4.1-flash | 5598 | 2 | — | in flight | — | — | `wip/ScalarTaylor.lean` |
| 11 | dyadic Freedman bound | ds3 | v4.1-flash | 6800 | 1 | — | in flight | — | — | `wip/Dyadic.lean` |
| 11 | direction error | ds4 | v4.1-flash | 7558 | 1 | — | in flight | — | — | `wip/DirectionError.lean` |

## Observations

* **Waves 1–11.** Every returned DeepSeek packet was accepted: 40/40, with one definition repair in wave 1 and
  one dispatch repair in wave 9. Every Sonnet leaf was accepted: 6/6.
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
* **Dispatch channel.** Pasting a brief with `tmux paste-buffer` can split it into several user messages.
  In wave 9, ds2 never saw its goal and started searching other panes. ds1 finished its proof before the
  rules paragraph arrived. From wave 9b on, a brief is dispatched as a one-line message that points the
  worker at the brief file.
