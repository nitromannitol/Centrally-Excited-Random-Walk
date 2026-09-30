# Frontier — the work breakdown

The single source of the carve-up, regenerated at every milestone. Every node of the dependency DAG
appears here in frontier order, and packets are dispatched only from rows marked `READY`.

**Owners.**
* `director`: statements, routes and the non-routine assemblies.
* `sonnet`: a fresh Sonnet subagent.
* `ds1`–`ds4`: the DeepSeek panes.

**Status values.**
* `LANDED`: in the trunk, sorry-free, clean axioms.
* `IN-FLIGHT`: dispatched.
* `READY`: its dependencies are landed.
* `BLOCKED`: waiting on the dependencies listed.
* `DRAFT`: a frozen anchor elaborated but not yet approved.

A packet is one bounded result in one owned file, with at most three lemmas. No two packets in flight
share a file, a definition or an API.

**NL twins.** Each step node's NL twin is `ledger/nl/<id>.tex`, written before dispatch. For landed
infrastructure the twin is the route in its brief, recorded in `ledger/FLEET.md`.

Updated 2026-09-30.

## Leaves (library and Mathlib)

| id | provides | status |
|---|---|---|
| lp-freedman | `LatticeProb.freedman_upper`, `LatticeProb.freedman` | available |
| lp-green | `srwGreenInf`, `summable_srwHeat`, `walkOp_srwGreenInf`, `srwHeat_pos`, `exists_srwGreenInf_gradient`, `exists_srwGreen_gradient` | available |
| lp-sums | `summable_one_add_euclidNorm_rpow`, `card_ballFinset_le`, `sum_box_radial_le`, `shellCard_le` | available |
| ml-traj | `Kernel.traj`, `trajMeasure`, `map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure` | available |
| ml-polar | `Measure.toSphere`, `measurePreserving_homeomorphUnitSphereProd`, `integral_fun_norm_addHaar`, `toSphereBallBound_mul_measure_unitBall_le_toSphere_ball` | available |
| ml-ibp | `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (verified at the pin) | available |
| ml-bc | `ae_eventually_notMem`, `measure_setOf_frequently_eq_zero` | available |
| ml-ineq | `Real.young_inequality_of_nonneg`, Hölder for integrals, `EuclideanSpace.volume_ball*` | available |

## External

| id | owner | file | status |
|---|---|---|---|
| ext-lattice-kernel | director | `CERW/External/LatticePotentialKernel.lean` | DRAFT (elaborated in `scratch/Anchors.lean`; audits running) |

## Model and probability toolkit

| id | owner | file | deps | statement | status |
|---|---|---|---|---|---|
| s-kernel-moments | ds4 | `CERW/Support/Law/Moments.lean` | vocabulary | q_x ≥ 0 for ε<1/d, Σq_x = 1, mean −εu_x; the same for SRW and `stepProb` | LANDED |
| s-law-exists | director | `CERW/Support/Law/Existence.lean` | s-kernel-moments, ml-traj | a CERW process exists for d ≥ 1, 0 ≤ ε < 1/d | LANDED |
| s-occupation | ds4 | `CERW/Support/Occupation/Facts.lean` | vocabulary | n ≤ M_n R_n, k_{0,n} = R_n, ℓ_{s,t} ≤ ℓ_t, \|X_j\| ≤ j, A_n ⊆ ball(H_n) | LANDED |
| s-cell-membership | ds1 | `wip/CellMembership.lean` → `CERW/Support/Occupation/Cells.lean` | s-occupation | v ∈ D_n ↔ cellCenter v ∈ A_n; x ∈ D_n ↔ x ∈ A_n; ℓ̃_n = 0 off D_n | READY → dispatch |
| s-cell-norm | ds* (next free) | `wip/CellNorm.lean` → `CERW/Support/Occupation/CellNorm.lean` | s-occupation | \|v − x\| ≤ √d/2 on C_x; D_n ⊆ B(0, H_n + √d) | READY (queued) |
| s-cell-volume | ds3 | `wip/CellVolume.lean` → `CERW/Support/Occupation/CellVolume.lean` | vocabulary | C_x measurable, \|C_x\| = 1 | READY → dispatch |
| s-cellset-volume | ds3 (after s-cell-volume) | `wip/CellSetVolume.lean` | s-cell-volume | D_n measurable, \|D_n\| = R_n | BLOCKED(s-cell-volume) |
| s-step-mean | ds4 | `wip/StepMean.lean` → `CERW/Support/Law/StepMean.lean` | s-kernel-moments | Σ_e p(e) f(y+e) = Pf(y) − ε·1{fresh} u·Df(y) | READY → dispatch |
| s-law-cond | director | `CERW/Support/Law/CondStep.lean` | s-kernel-moments | E[f(X_{n+1}) \| ℱ_n] = Σ_e stepProb·f(X_n+e) a.s., from the cylinder law | READY (director) |
| s-dynkin | director | `CERW/Support/Law/Dynkin.lean` | s-law-cond, s-step-mean | Dynkin martingale for f(X): increments and bracket bounds | BLOCKED(s-law-cond, s-step-mean) |
| s-freedman-event | sonnet | `CERW/Generic/Martingale/FreedmanEvent.lean` | lp-freedman | P(\|Z_n\| ≥ t, ⟨Z⟩_n ≤ v) ≤ 2exp(−t²/(2(v+Bt))) via stopping | READY (statement to be written) |
| s-dyadic | director | `CERW/Generic/Martingale/Dyadic.lean` | s-freedman-event | union over ≤ n^K martingales and dyadic brackets: \|Z\| ≤ C(√(⟨Z⟩L)+BL) w.p. ≥ 1−Cn^{−p} | BLOCKED(s-freedman-event) |

## Section 2 (lem:local, lem:geometry)

| id | owner | file | deps | statement | status |
|---|---|---|---|---|---|
| s-weight-sums | ds1, ds3 | `CERW/Generic/Lattice/{WeightSums,SummableSums}.lean` | lp-sums | Σ(1+\|z\|)^{−d} ≤ C log R; Σ(1+\|z\|)^{2−2d} ≤ C (d≥3); J moments | LANDED |
| s-packing-lattice | ds2 | `CERW/Generic/Lattice/Packing.lean` | lp-sums | Σ_{x∈E}(1+\|x−y\|)^{1−d} ≤ C_d\|E\|^{1/d} | LANDED |
| s-kernel-props | director | `CERW/Support/LocalTime/KernelB.lean` | ext-lattice-kernel, lp-green | b := −G (d≥3) or the planar limit; (P−I)b = δ₀; b(0)=0; b<0 (d≥3); growth O(L)/O(1) | BLOCKED(freeze of ext-lattice-kernel) |
| s-gradient | director + ds | `CERW/Support/LocalTime/Gradient.lean` | s-kernel-props | Db(x) = (2/ω_d)x/\|x\|^d + O(\|x\|^{−d}); \|b(x+e)−b(x)\| ≤ C(1+\|x\|)^{1−d} | BLOCKED(s-kernel-props) |
| s-dynkin-local | director | `CERW/Support/LocalTime/Dynkin.lean` | s-dynkin, s-kernel-props, s-gradient | eq:dynkin and eq:bracket | BLOCKED |
| s-interval-mart | director | `CERW/Support/LocalTime/IntervalMartingale.lean` | s-dyadic, s-dynkin-local, s-weight-sums | eq:interval-mart | BLOCKED |
| s-local-young | ds (algebra part LANDED) | `CERW/Support/LocalTime/IntervalBound.lean` | s-dynkin-local, s-interval-mart, s-packing-lattice, `Young.Absorb` | eq:M, eq:interval | BLOCKED |
| s-direction-error | sonnet | `CERW/Generic/Kernel/DirectionError.lean` | ml-polar, ml-ineq | ∫_{B(0,R)} dv/((1+\|v\|)\|v−y\|^{d−1}) ≤ C log(R+2) | READY (statement to be written) |
| s-potential-integrable | sonnet | `CERW/Generic/Kernel/Integrable.lean` | ml-polar, `Kernel.Bathtub` | ∫_{B(y,ρ)} \|v−y\|^{1−d} = σ_dρ; sup_y ∫_D \|v−y\|^{1−d} ≤ σ_d(\|D\|/ω_d)^{1/d} | READY (statement to be written) |
| s-kernel-replace | director | `CERW/Support/LocalTime/Replacement.lean` | s-gradient, s-weight-sums, s-potential-integrable | the lattice source sum vs U_{D_n}: error ≤ CL | BLOCKED |
| s-cell-shift | director | `CERW/Support/LocalTime/CellShift.lean` | s-kernel-replace | moving y in its cell costs O(L) | BLOCKED |
| **lem-local** | director | `CERW/Frozen/LocalTimePotential.lean` | the rows above | lem:local | DRAFT |
| s-localmart | director | `CERW/Support/LocalTime/Retained.lean` | s-dyadic, s-dynkin-local | eq:localmart | BLOCKED |
| s-pointwise | director | same | s-dynkin-local, s-kernel-replace | eq:pointwise | BLOCKED |
| s-cellmodulus | director | same | s-kernel-replace, s-cell-shift | eq:cellmodulus | BLOCKED |
| s-Fmass | ds2 | `wip/TailBasic.lean` → `CERW/Support/Geometry/TailBasic.lean`, then `TailBounds.lean` | vocabulary | F ≥ 0, integrable weight, F antitone on (0,∞); F ≤ \|D\|/(σ_ds^{d−1}); F = 0 beyond D; increments | TailBasic READY → dispatch; TailBounds BLOCKED(TailBasic) |
| s-gauss-flux | director (design) + sonnet | `CERW/Generic/Newton/Flux.lean` | ml-polar, ml-ibp | r^{d−1}∫_S θ·K(rθ−c)dσ = σ_d·1{\|c\|<r} | READY (statement to be written) |
| s-kernel-average | sonnet | `CERW/Generic/Newton/ShellAverage.lean` | s-gauss-flux | eq:kernel-average | BLOCKED |
| s-potential-bound | sonnet | `CERW/Support/Geometry/Bound.lean` | `Kernel.Bathtub` (LANDED), s-potential-integrable | eq:potential-bound | BLOCKED(s-potential-integrable) |
| s-kernel-modulus | sonnet | `CERW/Generic/Kernel/Modulus.lean` | ml-polar | eq:kernel-modulus | READY (statement to be written) |
| s-holder | sonnet | `CERW/Support/Geometry/Holder.lean` | s-kernel-modulus | eq:holder | BLOCKED |
| s-newton | director | `CERW/Support/Geometry/Spherical.lean` | s-kernel-average, s-potential-integrable | eq:newton | BLOCKED |
| s-ballpotential | director | `CERW/Support/Geometry/Ball.lean` | s-kernel-average | eq:ballpotential | BLOCKED |
| **lem-geometry** | director | `CERW/Frozen/PotentialGeometry.lean` | the rows above | lem:geometry | DRAFT |

## Section 3 (lem:radial, prop:coarse)

| id | owner | file | deps | statement | status |
|---|---|---|---|---|---|
| s-levelsets | director | `CERW/Support/Coarse/LevelSets.lean` | s-kernel-props | eq:levelsets | BLOCKED |
| s-radial-drift | director + ds | `CERW/Support/Coarse/RadialDrift.lean` | s-levelsets, s-gradient | eq:radial-drift | BLOCKED |
| s-radial-mart | director | `CERW/Support/Coarse/RadialMartingale.lean` | s-dyadic, s-dynkin, s-radial-drift, s-Fmass | eq:radialbracket, eq:radialmart | BLOCKED |
| s-radial-source | director | `CERW/Support/Coarse/RadialAssembly.lean` | s-dynkin, s-radial-drift, s-Fmass | eq:radial-source, eq:shell-count | BLOCKED |
| **lem-radial** | director | `CERW/Frozen/RadialTest.lean` | s-radial-source, s-radial-mart | lem:radial | DRAFT |
| s-halving | ds3, ds2 | `CERW/Generic/Halving/{Levels,Cost}.lean` | — | halving on the grid and its cost | LANDED |
| s-shell | director | `CERW/Support/Coarse/Shell.lean` | lem-geometry, lem-local, ml-polar | eq:shell via eq:cap-average | BLOCKED |
| s-vector | director | `CERW/Support/Coarse/Vector.lean` | s-dyadic, s-dynkin | eq:vector | BLOCKED |
| s-crossing | director (Young part LANDED) | `CERW/Support/Coarse/Crossing.lean` | s-vector, lem-local | eq:crossing | BLOCKED |
| s-sstar | director | `CERW/Support/Coarse/Mass.lean` | lem-local, s-occupation | eq:sstar-lower | BLOCKED |
| s-coarse-tail | director | `CERW/Support/Coarse/Tail.lean` | lem-radial, s-shell, s-halving, s-sstar, s-Fmass | eq:coarse-tail | BLOCKED |
| s-HvsR | director | `CERW/Support/Coarse/OuterRadius.lean` | s-coarse-tail, s-crossing, s-Fmass | eq:HvsR | BLOCKED |
| s-radial-packing | sonnet | `CERW/Generic/Kernel/RadialPacking.lean` | `Kernel.Bathtub` (LANDED), ml-polar | ∫_D\|v\| ≥ (d/(d+1))ω_d^{−1/d}\|D\|^{1+1/d} | READY (statement to be written) |
| s-mass | director | `CERW/Support/Coarse/Mass.lean` | lem-geometry, lem-local, s-radial-packing, s-HvsR, s-cellset-volume | eq:massidentity, eq:coarse-masserror | BLOCKED |
| **prop-coarse** | director | `CERW/Frozen/CoarseBounds.lean` | s-sstar, s-HvsR, s-mass, lem-local | prop:coarse | DRAFT |

## Sections 4–5 and the main theorems

| id | owner | file | deps | statement | status |
|---|---|---|---|---|---|
| s-global | director | `CERW/Support/Contact/Setup.lean` | prop-coarse, lem-local, s-cell-norm | eq:global | BLOCKED |
| s-contact-cell | director | `CERW/Support/Contact/ContactCell.lean` | s-cell-membership | eq:bm, eq:contactcell | BLOCKED(s-cell-membership) |
| s-contact-bound | director | `CERW/Support/Contact/ContactBound.lean` | s-contact-cell, lem-geometry, s-pointwise, s-localmart, s-cellmodulus | eq:contactbound, eq:packing | BLOCKED |
| s-var-high | director (resolvent + absorption LANDED) | `CERW/Support/Contact/VarianceHigh.lean` | s-contact-bound, s-weight-sums, `Lattice.Resolvent`, `Young.Contact` | eq:kernelmoments … eq:masshigh | BLOCKED |
| s-var-planar | director | `CERW/Support/Contact/VariancePlanar.lean` | s-contact-bound, s-global, s-weight-sums | eq:massplanar, eq:envelopeplanar | BLOCKED |
| s-shellW | director | `CERW/Support/Contact/Radius.lean` | s-var-high, s-var-planar | eq:shellW | BLOCKED |
| s-quadratic | director | `CERW/Support/Contact/Quadratic.lean` | s-dynkin, s-dyadic, prop-coarse | eq:quadratic, eq:quadraticerror | BLOCKED |
| s-inradius | director (inversion LANDED) | `CERW/Support/Contact/Radius.lean` | s-quadratic, s-var-high, s-var-planar, `Young.Radius` | eq:inradius | BLOCKED |
| s-volume-profile | director | `CERW/Support/Contact/Profile.lean` | s-inradius, s-global, lem-geometry | eq:volume, inner eq:sandwich, eq:profile-rate | BLOCKED |
| s-tailend | director | `CERW/Support/Outer/TailEnd.lean` | lem-radial, s-shellW, s-halving, s-inradius, s-Fmass | eq:tailend | BLOCKED |
| s-outer | director | `CERW/Support/Outer/Crossing.lean` | s-tailend, s-crossing, s-inradius | eq:outer-contradiction | BLOCKED |
| s-assembly | director | `CERW/Support/Main/Event.lean` | s-volume-profile, s-outer, ml-bc | the event at each n; Borel–Cantelli | BLOCKED |
| **thm-fluctuations** | director | `CERW/Frozen/FluctuationBounds.lean` | s-assembly | thm:fluctuations | DRAFT |
| **thm-shape** | director | `CERW/Frozen/BallShape.lean` | thm-fluctuations, ml-bc | thm:shape | DRAFT |
| **eq-hausdorff** | director | `CERW/Frozen/HausdorffBound.lean` | thm-fluctuations | eq:hausdorff | DRAFT |

## Pre-freeze gate (per anchor; nothing is frozen without the author's approval)

| anchor | nl/<id>.tex | REVIEWED reading | consumption prototype | binder audit | non-vacuity | refute-first audit | 3 DeepSeek readings |
|---|---|---|---|---|---|---|---|
| ext-lattice-kernel | to write | to write | used by the anchors' prototypes | Opus audit running | truth check in audit (Lawler–Limic) | running | running |
| thm-shape | to write | to write | done (from thm-fluctuations) | running | `exists_isCERW` | running | running |
| thm-fluctuations | to write | to write | done (the `Good` clause extracted) | running | `exists_isCERW` | running | running |
| eq-hausdorff | to write | to write | to do | running | `exists_isCERW` | running | running |
| lem-local | to write | to write | done (instantiated) | running | `exists_isCERW` | running | running |
| lem-geometry | to write | to write | done (instantiated) | running | a ball D | running | running |
| lem-radial | to write | to write | done (instantiated) | running | `exists_isCERW` | running | running |
| prop-coarse | to write | to write | done (instantiated) | running | `exists_isCERW` | running | running |
