# Frontier — the work breakdown

The single source of the carve-up. It is **generated**, not hand-edited: the node table and
dependencies are fixed by the director, and each status is derived from the checkout at
generation time. Regenerated 2026-09-30 00:04.

* `LANDED`: every target file is in the trunk and sorry-free.
* `IN-FLIGHT`: the `wip/` leaf exists; the worker comes from the newest brief naming it.
* `READY`: all dependencies landed (for anchors, sealed).
* `BLOCKED(…)`: the dependencies still unmet.
* Anchor statuses come from `ledger/manifest.yaml`; `DRAFT` means not yet registered, since the
  freeze awaits the author's approval.

**Owners.** `director`: statements, routes and assemblies. `sonnet`: a fresh Sonnet subagent.
`ds1`–`ds4`: the DeepSeek panes.

**Packets.** One packet is one bounded result in one owned file, with at most three lemmas. From
wave 4 on, each packet's NL twin `ledger/nl/<id>.tex` is written before dispatch. Four twins were
written only after landing: s-freedman-event, s-potential-integrable, s-radial-packing and
s-law-cond. Twins for the wave 1–3 packets are not yet written.

**Leaves.** Available from LatticeProb @ b617769 and Mathlib @ 81a5d257; see PLAN §3.1.

| id | owner | files (under `CERW/`) | deps | statement | status |
|---|---|---|---|---|---|
| ext-lattice-kernel | director | `External/LatticePotentialKernel.lean` | — | eq:kernel-asymptotics (cited input) | DRAFT |
| **Model and probability toolkit** | | | | | |
| s-kernel-moments | ds4 | `Support/Law/Moments.lean` | — | q_x ≥ 0, Σ q_x = 1, mean −εu_x; same for SRW and stepProb | LANDED |
| s-law-exists | director | `Support/Law/Existence.lean` | s-kernel-moments | a CERW process exists (Ionescu–Tulcea) | LANDED |
| s-law-cond | director | `Support/Law/CondStep.lean` | s-law-exists | E[f(X_{n+1}) \| ℱ_n] = Σ_e p_n(e) f(X_n+e) a.s.; natural filtration | LANDED |
| s-step-mean | ds4 | `Support/Law/StepMean.lean` | s-kernel-moments | Σ_e p(e) f(y+e) = Pf(y) − ε·1{fresh} u·Df(y) | LANDED |
| s-dynkin | director | `Support/Law/Dynkin.lean` | s-law-cond, s-step-mean | Dynkin martingale of f(X): martingale, increments, conditional variances | LANDED |
| s-mart-shift | ds3 | `Generic/Martingale/Shift.lean` | s-freedman-event | M_{s+k} − M_s is a martingale for ℱ_{s+k}; Freedman for interval increments | LANDED |
| s-coordinate-drift | ds2 | `Support/Law/CoordinateDrift.lean` | s-dynkin, s-step-mean | P x_k = x_k; D x_k = e_k; next-step mean of x_k is x_k − ε·1{fresh}(u_x)_k | LANDED |
| s-freedman-event | sonnet | `Generic/Martingale/FreedmanEvent.lean` | — | P(\|M_n\| ≥ t, V_n ≤ v) ≤ 2exp(−t²/(2(v+bt/3))) for predictable V dominating the bracket | LANDED |
| s-freedman-arith | ds1 | `Generic/Martingale/Arith.lean` | — | threshold t = c(√(vL)+BL) gives exponent ≥ KL; union-count arithmetic | LANDED |
| s-dyadic | ds3 | `Generic/Martingale/Dyadic.lean` | s-freedman-arith, s-mart-shift | union over ≤ n^K martingales and dyadic brackets: \|Z\| ≤ C(√(VL)+BL) w.p. ≥ 1−Cn^{−p} | LANDED |
| s-occupation | ds4 | `Support/Occupation/Facts.lean` | — | n ≤ M_nR_n, k_{0,n} = R_n, ℓ_{s,t} ≤ ℓ_t, \|X_j\| ≤ j, A_n ⊆ ball(H_n) | LANDED |
| s-cell-membership | ds1 | `Support/Occupation/Cells.lean` | s-occupation | v ∈ D_n ↔ cellCenter v ∈ A_n; ℓ̃_n = 0 off D_n | LANDED |
| s-cell-norm | ds1 | `Support/Occupation/CellNorm.lean` | s-occupation | \|v − x\| ≤ √d/2 on C_x; D_n ⊆ B(0, H_n + √d) | LANDED |
| s-cell-volume | ds3 | `Support/Occupation/CellVolume.lean`, `Support/Occupation/CellSetVolume.lean` | — | \|C_x\| = 1; \|D_n\| = R_n | LANDED |
| s-cell-weight | ds4 | `Support/Occupation/CellWeight.lean` | s-cell-norm, s-cell-volume | ∫_{C_x}\|v\|^{1−d} ≍ \|x\|^{1−d} for \|x\| ≥ √d | LANDED |
| s-cell-integral | ds4 | `Support/Occupation/CellIntegral.lean` | s-cell-membership, s-cell-volume | ∫_S ℓ̃_n = n for measurable S ⊇ D_n | LANDED |
| **Section 2 (lem:local, lem:geometry)** | | | | | |
| s-weight-sums | ds1/ds3 | `Generic/Lattice/WeightSums.lean`, `Generic/Lattice/SummableSums.lean` | — | Σ(1+\|z\|)^{−d} ≤ C log R; Σ(1+\|z\|)^{2−2d} ≤ C (d≥3); J moments; Lipschitz convolution | LANDED |
| s-centered-sums | ds2 | `Generic/Lattice/Centered.lean` | s-weight-sums, s-packing-lattice | the ball sums centred at y over any finite set | LANDED |
| s-packing-lattice | ds2 | `Generic/Lattice/Packing.lean` | — | Σ_{x∈E}(1+\|x−y\|)^{1−d} ≤ C_d\|E\|^{1/d} | LANDED |
| s-kernel-poisson | ds2 | `Support/LocalTime/KernelPoisson.lean` | — | (P−I)b = δ₀ (planar partial-sum limit; b = −G for d ≥ 3); P^M(0,x) → 0 | LANDED |
| s-kernel-props | director | `Support/LocalTime/KernelB.lean` | ext-lattice-kernel, s-kernel-poisson | b defined from the External; b(0)=0; b<0 (d≥3); growth O(L)/O(1) | BLOCKED(ext-lattice-kernel) |
| s-gradient-bound | ds1 | `Support/LocalTime/GradientBound.lean` | — | \|G(x+e)−G(x)\| ≤ C(1+\|x\|)^{1−d} (d≥3); the same for limits of G_M(0)−G_M(x) | LANDED |
| s-scalar-taylor | ds2 | `Generic/Kernel/ScalarTaylor.lean` | — | \|log(1+t)−t\| ≤ 2t²; \|(1+t)^α−1−αt\| ≤ \|α\|\|α−1\|2^{\|α−2\|}t² for \|t\| ≤ 1/2 | LANDED |
| s-gradient | ds3 | `Support/LocalTime/GradientAsymp.lean` | s-scalar-taylor | Db = (2/ω_d)x/\|x\|^d + O(\|x\|^{−d}); \|b(x+e)−b(x)\| ≤ C(1+\|x\|)^{1−d} | IN-FLIGHT (ds3, 23:59) |
| s-dynkin-local | director | `Support/LocalTime/Dynkin.lean` | s-dynkin, s-kernel-props, s-gradient | eq:dynkin, eq:bracket | BLOCKED(s-kernel-props, s-gradient) |
| s-interval-mart | director | `Support/LocalTime/IntervalMartingale.lean` | s-dyadic, s-dynkin-local, s-centered-sums, s-mart-shift | eq:interval-mart | BLOCKED(s-dynkin-local) |
| s-local-young | director | `Support/LocalTime/IntervalBound.lean` | s-dynkin-local, s-interval-mart, s-packing-lattice | eq:M, eq:interval (Young part landed in Generic/Young/Absorb) | BLOCKED(s-dynkin-local, s-interval-mart) |
| s-radial-power | ds1 | `Generic/Kernel/RadialPower.lean` | — | ∫_{B(0,ρ)}\|v\|^{−s} = σ_dρ^{d−s}/(d−s) (s<d); ∫_{\|v\|≥ρ}\|v\|^{−s} = σ_dρ^{d−s}/(s−d) (s>d) | LANDED |
| s-newton-field | ds2 | `Generic/Kernel/NewtonField.lean` | — | K(v)=v/\|v\|^d: \|K(v)\| = \|v\|^{1−d}; \|K(a)−K(b)\| ≤ C_d\|a−b\|/\|b\|^d when 2\|a−b\| ≤ \|b\| | LANDED |
| s-cell-direction | ds4 | `Support/Occupation/CellDirection.lean` | s-cell-norm | \|u_a−u_b\| ≤ 2\|a−b\|/\|a\|; \|u_x−u_v\| ≤ 2(1+√d)/(1+\|v\|) on C_x | LANDED |
| s-log-radial | ds4 | `Generic/Kernel/LogRadial.lean` | — | ∫_{B(0,R)}(1+\|v\|)^{−d} ≤ σ_d log(1+R); ∫_{ρ≤\|v\|<R}\|v\|^{−d} = σ_d log(R/ρ) | LANDED |
| s-direction-error | ds4 | `Generic/Kernel/DirectionError.lean` | s-radial-power, s-log-radial | ∫_{B(0,R)} dv/((1+\|v\|)\|v−y\|^{d−1}) ≤ C log(R+2) | LANDED |
| s-potential-integrable | sonnet | `Generic/Kernel/Integrable.lean` | — | ∫_{B(y,ρ)}\|v−y\|^{1−d} = σ_dρ; ∫_D\|v−y\|^{1−d} ≤ σ_d(\|D\|/ω_d)^{1/d} | LANDED |
| s-kernel-replace | director | `Support/LocalTime/Replacement.lean` | s-gradient, s-centered-sums, s-potential-integrable, s-cell-direction | lattice source sum vs U_{D_n}: error ≤ CL | BLOCKED(s-gradient) |
| s-cell-modulus | ds1 | `Support/Geometry/CellModulus.lean` | s-potential-bound, s-newton-field, s-log-radial | \|U_D(y) − U_D(z)\| ≤ Cε log(R+2) for \|y−z\| ≤ √d (eq:cellmodulus) | LANDED |
| s-cell-shift | director | `Support/LocalTime/CellShift.lean` | s-kernel-replace, s-cell-modulus | moving y in its cell costs O(L) | BLOCKED(s-kernel-replace) |
| s-retained | director | `Support/LocalTime/Retained.lean` | s-dyadic, s-dynkin-local, s-kernel-replace, s-cell-shift | eq:localmart, eq:pointwise, eq:cellmodulus | BLOCKED(s-dynkin-local, s-kernel-replace, s-cell-shift) |
| **lem-local** | director | `Frozen/LocalTimePotential.lean` | s-local-young, s-kernel-replace, s-direction-error, s-cell-shift, s-interval-mart | lem:local | DRAFT |
| s-Fmass | ds2 | `Support/Geometry/TailBasic.lean`, `Support/Geometry/TailBounds.lean` | — | F ≥ 0, antitone on (0,∞); F ≤ \|D\|/(σ_ds^{d−1}); F = 0 beyond D; increments | LANDED |
| s-polar | sonnet | `Generic/Newton/Polar.lean` | — | ∫ f = ∫_0^∞ r^{d−1}∫_S f(rθ)dσ dr for integrable f | LANDED |
| s-gauss-flux | sonnet | `Generic/Newton/Gauss.lean` | s-polar | ∫ Dφ(v)[K(v−c)] dv = −σ_d φ(c) for φ ∈ C¹_c | IN-FLIGHT (director/sonnet) |
| s-flux | ds2 | `Generic/Newton/Flux.lean` | — | swap identity; flux continuous off r = \|c\|; flux → σ_d | IN-FLIGHT (ds2, 23:57) |
| s-ball-symmetry | ds1 | `Generic/Newton/BallSymmetry.lean` | — | U_{B(0,b)} is invariant under linear isometries, hence radial | IN-FLIGHT (ds1, 00:01) |
| s-kernel-average | director | `Generic/Newton/ShellAverage.lean` | s-gauss-flux, s-flux, s-polar | eq:kernel-average | BLOCKED(s-gauss-flux, s-flux) |
| s-potential-bound | ds1 | `Support/Geometry/Bound.lean` | s-potential-integrable | eq:potential-bound | LANDED |
| s-kernel-modulus | sonnet | `Generic/Kernel/Modulus.lean` | s-radial-power, s-newton-field | eq:kernel-modulus | LANDED |
| s-holder | sonnet | `Support/Geometry/Holder.lean` | s-kernel-modulus, s-potential-bound | eq:holder | LANDED |
| s-newton | director | `Support/Geometry/Spherical.lean` | s-kernel-average, s-potential-integrable | eq:newton | BLOCKED(s-kernel-average) |
| s-ballpotential | director | `Support/Geometry/Ball.lean` | s-newton, s-ball-symmetry | eq:ballpotential | BLOCKED(s-newton, s-ball-symmetry) |
| **lem-geometry** | director | `Frozen/PotentialGeometry.lean` | s-potential-bound, s-holder, s-newton, s-ballpotential | lem:geometry | DRAFT |
| **Section 3 (lem:radial, prop:coarse)** | | | | | |
| s-radial-profile | ds1 | `Generic/Young/RadialProfile.lean` | — | increments of log r and r^{−k}: two-sided mean-value bounds | LANDED |
| s-levelsets | director | `Support/Coarse/LevelSets.lean` | s-kernel-props, s-radial-profile | eq:levelsets | BLOCKED(s-kernel-props) |
| s-radial-drift | director | `Support/Coarse/RadialDrift.lean` | s-levelsets, s-gradient | eq:radial-drift | BLOCKED(s-levelsets, s-gradient) |
| s-radial-mart | director | `Support/Coarse/RadialMartingale.lean` | s-dyadic, s-dynkin, s-radial-drift, s-Fmass, s-cell-weight | eq:radialbracket, eq:radialmart | BLOCKED(s-radial-drift) |
| s-radial-source | director | `Support/Coarse/RadialAssembly.lean` | s-dynkin, s-radial-drift, s-Fmass, s-cell-weight | eq:radial-source, eq:shell-count | BLOCKED(s-radial-drift) |
| **lem-radial** | director | `Frozen/RadialTest.lean` | s-radial-source, s-radial-mart | lem:radial | DRAFT |
| s-halving | ds2/ds3 | `Generic/Halving/Levels.lean`, `Generic/Halving/Cost.lean` | — | halving on the grid and its cost | LANDED |
| s-shell | director | `Support/Coarse/Shell.lean` | lem-geometry, lem-local | eq:shell via eq:cap-average | BLOCKED(lem-geometry, lem-local) |
| **Model and probability toolkit** | | | | | |
| s-clamp | ds4 | `Generic/Martingale/Clamp.lean` | — | a martingale with a.s. bounded increments equals a.s. one with surely bounded increments | IN-FLIGHT (ds4, 23:59) |
| **Section 3 (lem:radial, prop:coarse)** | | | | | |
| s-vector | director | `Support/Coarse/Vector.lean` | s-dyadic, s-dynkin, s-coordinate-drift, s-mart-shift, s-clamp | eq:vector | BLOCKED(s-clamp) |
| s-last-entrance | ds2 | `Support/Crossing/LastEntrance.lean` | s-kernel-moments | last entrance; v·e ≤ 1 for unit steps | LANDED |
| s-crossing-kinematics | ds3 | `Support/Crossing/Kinematics.lean` | s-occupation | Σ ℓ_{s,t} = t−s; t−s ≤ m·M_{s,t}; v·u_x > b/r | LANDED |
| s-crossing-contradiction | ds3 | `Support/Crossing/Contradiction.lean` | — | C(s^γL^{2γ}+sL⁴) < s² eventually for s ≥ cN | LANDED |
| s-crossing | director | `Support/Coarse/Crossing.lean` | s-vector, lem-local, s-last-entrance, s-crossing-kinematics | eq:crossing (Young part landed) | BLOCKED(s-vector, lem-local) |
| s-sstar | director | `Support/Coarse/Mass.lean` | lem-local, s-occupation | eq:sstar-lower | BLOCKED(lem-local) |
| s-coarse-tail | director | `Support/Coarse/Tail.lean` | lem-radial, s-shell, s-halving, s-sstar, s-Fmass | eq:coarse-tail | BLOCKED(lem-radial, s-shell, s-sstar) |
| s-HvsR | director | `Support/Coarse/OuterRadius.lean` | s-coarse-tail, s-crossing, s-crossing-contradiction, s-cell-weight | eq:HvsR | BLOCKED(s-coarse-tail, s-crossing) |
| s-radial-packing | sonnet | `Generic/Kernel/RadialPacking.lean` | — | ∫_D\|v\| ≥ (d/(d+1))ω_d^{−1/d}\|D\|^{1+1/d} | LANDED |
| s-mass | director | `Support/Coarse/MassIdentity.lean` | lem-geometry, lem-local, s-radial-packing, s-HvsR, s-cell-integral | eq:massidentity, eq:coarse-masserror | BLOCKED(lem-geometry, lem-local, s-HvsR) |
| **prop-coarse** | director | `Frozen/CoarseBounds.lean` | s-sstar, s-HvsR, s-mass, lem-local | prop:coarse | DRAFT |
| **Sections 4–5 and the main theorems** | | | | | |
| s-contact-kernel | ds1 | `Support/Contact/Kernel.lean` | — | u_v·(v−y)\|v−y\|^{−d} ≥ 2^{1−d}\|v\|^{1−d} for \|y\| ≤ \|v\| | LANDED |
| s-planar-contact-sum | ds4 | `Support/Contact/PlanarSum.lean` | s-packing-lattice, s-occupation | Σ_{\|w\|≤R}(b−\|z+w\|)_+(1+\|w\|)^{−2} ≤ C(R+1) | LANDED |
| s-global | director | `Support/Contact/Setup.lean` | prop-coarse, lem-local, s-cell-norm | eq:global | BLOCKED(prop-coarse, lem-local) |
| s-contact-cell | sonnet | `Support/Contact/ContactCell.lean` | s-cell-membership | eq:bm, eq:contactcell | LANDED |
| s-contact-bound | director | `Support/Contact/ContactBound.lean` | s-contact-cell, lem-geometry, s-retained, s-contact-kernel | eq:contactbound, eq:packing | BLOCKED(lem-geometry, s-retained) |
| s-var-high | director | `Support/Contact/VarianceHigh.lean` | s-contact-bound, s-weight-sums | eq:kernelmoments … eq:masshigh (resolvent, absorption landed) | BLOCKED(s-contact-bound) |
| s-var-planar | director | `Support/Contact/VariancePlanar.lean` | s-contact-bound, s-global, s-planar-contact-sum | eq:massplanar, eq:envelopeplanar | BLOCKED(s-contact-bound, s-global) |
| s-shellW | director | `Support/Contact/ShellW.lean` | s-var-high, s-var-planar | eq:shellW | BLOCKED(s-var-high, s-var-planar) |
| s-quadratic | director | `Support/Contact/Quadratic.lean` | s-dynkin, s-dyadic, prop-coarse | eq:quadratic, eq:quadraticerror | BLOCKED(prop-coarse) |
| s-inradius | director | `Support/Contact/Radius.lean` | s-quadratic, s-var-high, s-var-planar | eq:inradius (inversion landed) | BLOCKED(s-quadratic, s-var-high, s-var-planar) |
| s-volume-profile | director | `Support/Contact/Profile.lean` | s-inradius, s-global, lem-geometry | eq:volume, inner eq:sandwich, eq:profile-rate | BLOCKED(s-inradius, s-global, lem-geometry) |
| s-outer-contradiction | ds3 | `Support/Crossing/OuterContradiction.lean` | — | C((C₁NL)^γL^γ + C₁NLλL) < (AWL−1)² eventually | LANDED |
| s-tailend | director | `Support/Outer/TailEnd.lean` | lem-radial, s-shellW, s-halving, s-inradius, s-Fmass | eq:tailend | BLOCKED(lem-radial, s-shellW, s-inradius) |
| s-outer | director | `Support/Outer/Crossing.lean` | s-tailend, s-crossing, s-inradius, s-outer-contradiction | eq:outer-contradiction | BLOCKED(s-tailend, s-crossing, s-inradius) |
| s-scale-limits | ds4 | `Support/Main/ScaleLimits.lean` | — | log(n+2)^a/n^c → 0; Q → 0; Q^{1/d}L → 0 | LANDED |
| s-hausdorff-arith | ds3 | `Support/Main/HausdorffArith.lean` | — | Hausdorff and planar exponent identities | LANDED |
| s-assembly | director | `Support/Main/Event.lean` | s-volume-profile, s-outer | the event at each n; Borel–Cantelli | BLOCKED(s-volume-profile, s-outer) |
| **thm-fluctuations** | director | `Frozen/FluctuationBounds.lean` | s-assembly | thm:fluctuations | DRAFT |
| **thm-shape** | director | `Frozen/BallShape.lean` | thm-fluctuations, s-scale-limits | thm:shape | DRAFT |
| **eq-hausdorff** | director | `Frozen/HausdorffBound.lean` | thm-fluctuations, s-hausdorff-arith, s-contact-cell | eq:hausdorff | DRAFT |

**Counts:** BLOCKED 32, DRAFT 7, IN-FLIGHT 5, LANDED 46.

## Pre-freeze gate

Complete for all 7 anchors and the External. The evidence is in `ledger/nl/`,
`ledger/readings.yaml`, `ledger/audits/` and `ledger/approval/PHASE-B.md`. The freeze is **held
pending the author's delivered approval**. The single open item is the planar remark in
`eq-hausdorff`: (A) one-sided, as drafted, or (B) two-sided, which is recommended.
