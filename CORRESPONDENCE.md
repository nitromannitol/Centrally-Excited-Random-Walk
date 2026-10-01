# Correspondence between the paper and the formalization

`paper/limit-shapes.tex` is the pinned source of the revised paper, *Limit
shapes of centrally excited random walks*. A registered theorem has one
declaration in its own file under `CERW/Frozen/`, with a paper line anchor and
label. The seven statements of the first version of the paper
(`paper/cerw-flat.tex`, the mechanical flattening of `paper/cerw.tex` and its
three section files) keep their frozen text and cite that file by line; their
node ids name the Lean theorem (`ball-shape`, `fluctuation-bounds`, …). The
paper writes the drift as `κ`; Lean, and this file, write `ε`.

The bytes strictly between `FROZEN-STATEMENT-BEGIN` and
`FROZEN-STATEMENT-END`, with one leading newline dropped and the trailing
newline retained, are hashed by `python3 -m leanform_tools.freeze` and checked
by `python3 -m leanform_tools.check_manifest`. Definitions shared by statements
live in `CERW/Model/`.

## Transcription conventions

**Lattice and continuum.**
- Lattice sites are `LatticeProb.Site d`, with the Euclidean norm
  `euclidNorm`. The continuum is `EuclideanSpace ℝ (Fin d)`, and `toSpace`
  embeds the lattice in it, so that `Ψ(x)` for a site `x` is `Ψ (toSpace x)`.
  `coordVec i` is the basis vector `e_i` of `ℝ^d`, `LatticeProb.unit i` is
  that of `ℤ^d`, and `unitSteps d` is the set of the `2d` unit steps. The
  direction `u_v = v/|v|`, with `u_0 = 0`, is `unitDir`.
- The cell `C_x = x + [-1/2, 1/2)^d` is `cell x`, and is half-open. The
  site whose cell contains `v` is `cellCenter v`.

**The walk.**
- The Euclidean walk is any process `X` on any probability space `(Ω, μ)`
  with `CERW.IsCERW μ ε X`: each `X n` is measurable, `X_0 = 0` almost
  surely, and the law of every initial segment factorizes through
  `CERW.stepProb`. The first departure from a site `x ≠ 0` uses the kernel
  `q_x`, with probability `1/(2d) ∓ (ε/2) x_i/|x|` at `x ± e_i`; every other
  departure is a simple random walk step.
- The walk with norm `Ψ`, and more generally with a drift field `ξ`, is
  `CERW.IsDriftCERW μ ε ξ X`, which factorizes through `CERW.driftStepProb`.
  At a first departure from `x ≠ 0` the probability of `x ± e_i` is
  `1/(2d) ∓ (ε/2) ξ_i(x)`. The test for a first departure is
  `x n ≠ 0 ∧ x n ∉ (Finset.range n).image x`. With `ξ(x) = u_x` the walk is
  the Euclidean one: `IsCERW μ ε X` is `IsDriftCERW μ ε u X`
  (`CERW.Support.Drift.isCERW_iff_isDriftCERW`).
- The subgradients are a function `ξ : Site d → EuclideanSpace ℝ (Fin d)`
  with `IsSubgradient Ψ (toSpace x) (ξ x)` for `x ≠ 0` and `ξ 0 = 0`, as in the
  paper's notation. The ellipticity condition
  `ε max_i Ψ(e_i) < 1/d` is `∀ i, ε * Ψ (coordVec i) < 1 / d`.
- The standing assumption `d ≥ 2` is `hd : 2 ≤ d`, or `hd : d = 2` for the planar
  statements, and `0 < ε < 1/d` is `hε : 0 < ε` and `hεd : ε < 1 / d`, or the
  quantifier `∀ ε, 0 < ε → ε < 1 / d → …` when a constant follows `ε`.
- Realizations exist: `CERW.Support.Law.exists_isCERW`,
  `CERW.Support.Drift.exists_isDriftCERW` and
  `CERW.Support.Main.exists_norm_realization`.

**Norms.**
- `CERW.IsNorm Ψ` says that `Ψ` is subadditive, absolutely homogeneous, and
  zero only at the origin. `CERW.IsSubgradient Ψ x ξ` is
  `∀ y, Ψ x + ⟪ξ, y - x⟫ ≤ Ψ y`.
- `|B_Ψ|` is `CERW.normBallVolume Ψ = (volume {y | Ψ y < 1}).toReal`, finite
  and positive because the ball is bounded and open. `Λ_Ψ` and `c_Ψ` are
  `CERW.normMax Ψ` and `CERW.normMin Ψ`, the `sSup` and `sInf` of `Ψ` on the
  Euclidean unit sphere, which are attained.
- `r_n` is `((d + 1) * n / (2 * d * ε * ωd)) ^ (1 / (d + 1))`, with
  `ωd = (volume (ball 0 1)).toReal`, and for a norm the same with
  `CERW.normBallVolume Ψ` in place of `ωd`. The first version writes
  `N = n ^ (1 / (d + 1))` and `a = ((d + 1) / (2 * d * ε * ωd)) ^ (1 / (d + 1))`.
  Every cast to `ℝ` is at a leaf.

**Occupation.**
- `A_n` is `CERW.departureRange`, the set `{X_0, …, X_{n-1}}`, and `ℓ_n` is
  `CERW.localTime`; the paper's set of sites visited by time `n` is `A_{n+1}`,
  and the first version's `V_n` is `CERW.visitedRange`. `M_n` is
  `CERW.maxLocalTime`, and `H_n = max_{j ≤ n} |X_j|` is `CERW.maxRadius`.
- `D_n` is `CERW.cellSet`, the union of the unit cells of `A_n`, and `ℓ̃_n` is
  `CERW.cellLocalTime`. `M_sh(r)` is `CERW.shellMax`. `M_{s,t}` and `k_{s,t}`
  are `CERW.intervalMax` and `CERW.freshCount`, with `I_j = 1{X_j ∉ A_j}`.

**Potentials.**
- `ω_d` is `CERW.unitBallVolume d`. `U_D` of `eq:potential-intro` is
  `CERW.potential`, and `F` is `CERW.tail`, with `σ_d = d ω_d`.
  `U_D^+` is `CERW.positivePotential`.
- `U_D` of `eq:potential-norm` is `CERW.normPotential d ε Ψ D y`, which is
  `2 * ε / unitBallVolume d * ∫ v in D, ⟪gradient Ψ v, v - y⟫ / ‖v - y‖ ^ d`.
  `∇Ψ` is Mathlib's `gradient Ψ`, which is `0` where `Ψ` is not differentiable.
  A norm is Lipschitz, so that set is Lebesgue-null and is seen only under
  integrals, all of which are integrable on bounded measurable sets. At the
  single point `v = y` the integrand reads `0`. For the Euclidean norm
  `gradient ‖·‖ v = u_v` at every `v`, so `normPotential` is `potential`.
- `F_τ` is `CERW.moreauEnvelope Ψ τ`, the real `⨅ z, Ψ z + ‖x - z‖ ^ 2 / (2 * τ)`,
  and `∇F_τ` is `gradient (moreauEnvelope Ψ τ)`.
- The distributional Laplacian `μ` of `lem:cell` is given by
  `CERW.IsDistribLaplacian Ψ m`: `∫ φ dm = ∫ Ψ * Laplacian.laplacian φ` for
  every smooth compactly supported `φ`, where `Laplacian.laplacian` is Mathlib's
  `Σ_i ∂_i²`. `lem:cell` is stated for every locally finite measure `m` with
  this property; such a measure exists (`CERW.Support.Norm.exists_isDistribLaplacian`).

**Radii.**
- `R_in(n)` is `CERW.innerRadius`, the `sInf` of `‖·‖` over the complement of
  `D_n`, and `inf_{y ∉ D_n} Ψ(y)` is `CERW.normInnerRadius Ψ`. `D_n` is
  bounded, so the set is nonempty and bounded below, and the `sInf` is the
  infimum. `R_out(n)` is `CERW.maxRadius`, and `max_{j ≤ n} Ψ(X_j)` is
  `CERW.normMaxRadius Ψ`. `R_mom(n)` is `CERW.momentRadius`.

**Martingales.**
- `⟨S, T⟩_n` is `CERW.predBracket μ ℱ S T n`, the sum over `t < n` of the
  conditional expectations `μ[ΔS_t ΔT_t | ℱ t]`. It is defined up to a null set,
  so statements use it under `∀ᵐ` or inside an outer-measure bound. `Martingale`
  is Mathlib's, for a `Filtration ℕ m0`.
- `𝒬_n = 2ε Σ_{x ∈ A_n} |x| - n + |X_n|²` is `CERW.quadraticMart`. The Dynkin
  martingale `𝓜^f` and its bracket are `CERW.dynkinMart p f X t` and
  `CERW.dynkinBracket p f g X t`, written from the step law `p`, such as
  `CERW.stepProb d ε` or `CERW.driftStepProb d ε ξ`, as sums over the unit
  steps; no conditional expectation is involved.
- The kernel `g` of Section 3 is `CERW.latticeKernel d`: for `d = 2` the
  `limUnder` of the partial sums `Σ_{j<M} [P^j(0,0) - P^j(0,x)]`, and for
  `d ≥ 3` the function `-LatticeProb.srwGreenInf d`, where
  `G(x) = Σ_{j≥0} P^j(0,x)` includes the term `j = 0`, so `G(0) ≥ 1`.

**Probability and limits.**
- "With probability at least `1 - Cn^{-p}`" is an upper bound
  `μ {ω | ¬ …} ≤ ENNReal.ofReal (C n^{-p})` on the outer measure of the
  exceptional event. A lower bound on a probability is `MeasurableSet E` together
  with `ENNReal.ofReal (n^{-p}) ≤ μ E`.
- A supremum tending to zero is `∀ η > 0, ∀ᶠ n, ∀ x, … ≤ η r_n`. "Almost surely,
  for all sufficiently large `n`" is `∀ᵐ ω ∂μ, ∀ᶠ n in atTop, …`.
- "`limsup a_n/s_n ≥ L`" is `∀ δ > 0, ∃ᶠ n, (L - δ) s_n ≤ a_n`, and
  "`limsup = L`" adds `∀ᶠ n, a_n ≤ (L + δ) s_n`, for each sign.
- A limit in distribution is `TendstoInDistribution S atTop id (fun _ => μ)
  (gaussianReal 0 v)`, with the variance `v` an `NNReal`, written
  `v.toNNReal` for a positive real `v`; `gaussianReal 0 0` is the point mass at
  `0`. A joint limit is in `EuclideanSpace ℝ (Fin k)`, with
  `multivariateGaussian 0 M` for a covariance matrix `M`.
- Volumes and the Hausdorff distance are in `ℝ≥0∞`. Balls are open, `(t)_+` is
  `max t 0`, and `log` is `Real.log`. The paper's `\nf{a}{b}` is the real
  quotient `a / b`.

**Constants.**
- Constants follow the parameters they may depend on and precede the
  probability space, and for the norm walk they precede `ξ` as well. The
  constants `C_d` of the first version's `lem:local` and `lem:geometry` precede
  `ε`; `C(d)` of `lem:cell` precedes `Ψ` and `ξ`; `C(d, Ψ)` of `lem:geometry`
  precedes `ε` and `D`; and `ρ₀` of `lem:radial` precedes `ε`. `PROOF.md`,
  section 4, lists the readings of the individual statements.
- The universe of `Ω` is `u`, and the cited results are carried as
  `CERW.External.MartingaleCLT.{u}` and `CERW.External.StoutLIL.{u}`.

## Registered statements

<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->

| id | Lean | paper | state |
|---|---|---|---|
| `potential-geometry` | `CERW.Frozen.potential_geometry` | first version of the paper, the lemma on the geometry of the potential, paper/cerw-flat.tex lines 497 to 514 | PROVED |
| `ball-shape` | `CERW.Frozen.ball_shape` | first version of the paper, the ball shape theorem, paper/cerw-flat.tex lines 135 to 160 | PROVED |
| `fluctuation-bounds` | `CERW.Frozen.fluctuation_bounds` | first version of the paper, the fluctuation bounds, paper/cerw-flat.tex lines 186 to 213 | PROVED |
| `hausdorff-bound` | `CERW.Frozen.hausdorff_bound` | first version of the paper, the Hausdorff estimate and the planar remark, paper/cerw-flat.tex lines 217 to 223 | PROVED |
| `local-time-potential` | `CERW.Frozen.local_time_potential` | first version of the paper, the lemma on local times and the potential, paper/cerw-flat.tex lines 397 to 414 | PROVED |
| `radial-test` | `CERW.Frozen.radial_test` | first version of the paper, the radial test lemma, paper/cerw-flat.tex lines 581 to 601 | PROVED |
| `coarse-bounds` | `CERW.Frozen.coarse_bounds` | first version of the paper, the coarse bounds, paper/cerw-flat.tex lines 547 to 561 | PROVED |
| `ext-martingale-clt` | `CERW.External.MartingaleCLT` | Hall and Heyde (1980), Corollary 3.1, cited at limit-shapes.tex lines 1399 and 1519 | FROZEN |
| `ext-stout-lil` | `CERW.External.StoutLIL` | Stout (1970), the martingale law of the iterated logarithm, cited at limit-shapes.tex lines 1410, 1519 and 1644 | FROZEN |
| `thm-shape` | `CERW.Frozen.limit_shape` | `limit-shapes.tex:103-116`, `thm:shape` | PROVED |
| `thm-fluctuations` | `CERW.Frozen.fluctuation_rates` | `limit-shapes.tex:130-152`, `thm:fluctuations` | PROVED |
| `thm-sharp-radii` | `CERW.Frozen.sharp_radii` | `limit-shapes.tex:159-164`, `thm:sharp` | PROVED |
| `thm-sharp-radii-lil` | `CERW.Frozen.sharp_radii_lil` | `limit-shapes.tex:165-170`, `thm:sharp` | PROVED |
| `thm-sharp-bulk` | `CERW.Frozen.sharp_bulk` | `limit-shapes.tex:171-175`, `thm:sharp` | PROVED |
| `thm-sharp-width` | `CERW.Frozen.sharp_width` | `limit-shapes.tex:176-187`, `thm:sharp` | PROVED |
| `thm-norm-shape` | `CERW.Frozen.norm_shape` | `limit-shapes.tex:330-343`, `thm:norm-shape` | PROVED |
| `lem-ballpotential` | `CERW.Frozen.norm_ball_potential` | `limit-shapes.tex:361-366`, `lem:ballpotential` | PROVED |
| `lem-local` | `CERW.Frozen.norm_local_time_potential` | `limit-shapes.tex:385-401`, `lem:local` | PROVED |
| `lem-freedman` | `CERW.Frozen.freedman_bound` | `limit-shapes.tex:437-442`, `lem:freedman` | PROVED |
| `lem-cell` | `CERW.Frozen.cell_gradient` | `limit-shapes.tex:455-460`, `lem:cell` | PROVED |
| `lem-geometry` | `CERW.Frozen.norm_potential_geometry` | `limit-shapes.tex:510-528`, `lem:geometry` | PROVED |
| `prop-coarse` | `CERW.Frozen.norm_coarse_bounds` | `limit-shapes.tex:547-554`, `prop:coarse` | PROVED |
| `lem-radial` | `CERW.Frozen.norm_radial_test` | `limit-shapes.tex:567-576`, `lem:radial` | PROVED |
| `lem-crossing` | `CERW.Frozen.drift_crossing` | `limit-shapes.tex:662-667`, `lem:crossing` | PROVED |
| `prop-norm-shape` | `CERW.Frozen.norm_shape_rates` | `limit-shapes.tex:746-762`, `prop:norm-shape` | PROVED |
| `lem-layer` | `CERW.Frozen.layer_potential` | `limit-shapes.tex:780-785`, `lem:layer` | PROVED |
| `lem-cap` | `CERW.Frozen.moreau_cap` | `limit-shapes.tex:810-815`, `lem:cap` | PROVED |
| `lem-contact` | `CERW.Frozen.contact_potential` | `limit-shapes.tex:892-897`, `lem:contact` | PROVED |
| `lem-outer-crossing` | `CERW.Frozen.outer_crossing` | `limit-shapes.tex:989-994`, `lem:outer-crossing` | PROVED |
| `prop-inner` | `CERW.Frozen.inner_radius` | `limit-shapes.tex:1060-1076`, `prop:inner` | PROVED |
| `prop-stronger-outer` | `CERW.Frozen.outer_radius` | `limit-shapes.tex:1172-1177`, `prop:stronger-outer` | PROVED |
| `lem-near-far` | `CERW.Frozen.near_far` | `limit-shapes.tex:1203-1208`, `lem:near-far` | PROVED |
| `thm-moment-fluctuations` | `CERW.Frozen.moment_fluctuations` | `limit-shapes.tex:1353-1374`, `thm:moment-fluctuations` | PROVED |
| `lem-fixed-site-centering` | `CERW.Frozen.fixed_site_centering` | `limit-shapes.tex:1430-1436`, `lem:fixed-site-centering` | PROVED |
| `thm-site-fluctuations` | `CERW.Frozen.site_fluctuations` | `limit-shapes.tex:1460-1485`, `thm:site-fluctuations` | PROVED |
| `lem-exp-deviation` | `CERW.Frozen.exp_deviation` | `limit-shapes.tex:1537-1551`, `lem:exp-deviation` | PROVED |
| `prop-bulk-profile` | `CERW.Frozen.bulk_profile` | `limit-shapes.tex:1655-1662`, `prop:bulk-profile` | PROVED |
| `lem-separated-brackets` | `CERW.Frozen.separated_brackets` | `limit-shapes.tex:1689-1696`, `lem:separated-brackets` | PROVED |
| `prop-log-lower` | `CERW.Frozen.log_lower_bounds` | `limit-shapes.tex:1759-1773`, `prop:log-lower` | PROVED |

<!-- FROZEN-SURFACE-END -->

The four rows `thm-sharp-radii`, `thm-sharp-radii-lil`, `thm-sharp-bulk` and
`thm-sharp-width` are the four parts (i), (ii), (iii) and (iv) of
Theorem 1.3; the last contains both (a) and (b). Every labelled
theorem-like environment of the pinned paper is claimed by a row.

## Cited results

Two results that the revised paper cites for its limit laws are assumed, and
each is carried as an explicit hypothesis by every theorem whose proof uses it
(`ASSUMPTIONS.md` gives the verbatim Lean propositions).

| node | cited result | Lean form | cited at | carried by |
|---|---|---|---|---|
| `ext-martingale-clt` | Hall and Heyde (1980), Corollary 3.1, the martingale central limit theorem | `CERW.External.MartingaleCLT`: for one square-integrable martingale `S` with `S_0 = 0`, deterministic normalizers `s_n > 0` and `v : ℝ≥0`, if the conditional Lindeberg sums `Σ_{i<n} E[((ΔS_{i+1})/s_n)² 1{\|ΔS_{i+1}\|/s_n > δ} \| ℱ_i]` tend to `0` in measure for every `δ > 0` and `⟨S⟩_n/s_n²` tends to `v` in measure, then `S_n/s_n` tends in distribution to `gaussianReal 0 v` | `limit-shapes.tex:1401, 1521` | `moment_fluctuations`, `site_fluctuations`, as `hCLT` |
| `ext-stout-lil` | Stout (1970), the martingale law of the iterated logarithm | `CERW.External.StoutLIL`: for one square-integrable martingale `S` with `S_0 = 0` and a predictable bound `B_{n+1}` (`ℱ_n`-measurable) on `\|ΔS_{n+1}\|` almost surely, if `⟨S⟩_n → ∞` and `B_n √(log log (⟨S⟩_n ∨ e^e))/√⟨S⟩_n → 0` almost surely, then almost surely, for every `δ > 0`, eventually `S_n ≤ (1 + δ) √(2⟨S⟩_n log log ⟨S⟩_n)`, and frequently `S_n ≥ (1 - δ) √(2⟨S⟩_n log log ⟨S⟩_n)` | `limit-shapes.tex:1412, 1521, 1647` | `sharp_radii_lil`, `moment_fluctuations`, `site_fluctuations`, as `hLIL`; `sharp_width`, as the premise of part (b) only |

The paper uses them at the following places:
- line 1401, Theorem 8.1: the central limit theorem for the quadratic martingale `𝒬`;
- line 1412, Theorem 8.1: the law of the iterated logarithm for `𝒬` and `-𝒬`, and through it
  Theorem 1.3 (ii), which `sharp_radii_lil` states with `hLIL`;
- line 1521, Theorem 8.3: both results for the martingales `𝓜^y`, in the central limit theorem, the
  joint limits and the law of the iterated logarithm;
- line 1647, Theorem 1.3 (iv)(b): the law of the iterated logarithm for the first coordinate of the
  compensated position, which `sharp_width` states as the premise of part (b); part (a) does not
  use it and is unconditional.

Both propositions are the special cases the paper uses, with `S_0 = 0` at every `ω` and the conclusion in
the junk-free form described above; `PROOF.md`, section 4, states the forms point by point. The
source check is `ledger/audits/external-sources.md`. It compares the propositions with restatements of
the cited theorems in the literature and records both as implied, with a remark. The propositions carry the
universe of `Ω` as a parameter.

The result that the first-version statements once carried as a hypothesis is proved in
Lattice-Probability:

| nodes | cited result | where it is proved |
|---|---|---|
| `ball-shape`, `fluctuation-bounds`, `hausdorff-bound`, `local-time-potential`, `radial-test`, `coarse-bounds`, and, in the revised surface, `lem-local`, `lem-radial`, `lem-contact`, `prop-inner`, `thm-site-fluctuations` | The asymptotics of the kernel `b` with `(P − I) b = 1_{0}`. For `d = 2`, `b` is the potential kernel, the limit of the partial sums `Σ_{j<M} [P^j(0,0) − P^j(0,x)]`, with `b(x) = (2/π) log \|x\| + κ + O(\|x\|^{-2})` (Lawler–Limic, Theorem 4.4.4). For `d ≥ 3`, `b = −G` with `G(x) = 2/((d−2)ω_d) \|x\|^{2−d} + O(\|x\|^{-d})` (Lawler–Limic, Theorem 4.3.1). `local-time-potential` and `lem-local` use it to build the local-time potential, `radial-test` and `lem-radial` the radial test, `lem-contact` and `prop-inner` the contact argument, and `thm-site-fluctuations` the lattice kernel `g` of Section 3; the other statements inherit it from these. | `LatticeProb.External.potentialKernelAsymptotics_holds`, which proves the proposition `LatticeProb.External.PotentialKernelAsymptotics d` in every dimension. Earlier versions of six first-version statements carried the same proposition as the hypothesis `CERW.External.LatticePotentialKernel d`; by the author's ruling (`ledger/approval/KERNEL-ASYMPTOTICS.md`) it was removed, and the statements are otherwise unchanged. |

Each proof that uses the asymptotics obtains the kernel facts from them
(`CERW.Support.LocalTime.exists_kernelFacts`, in
`CERW/Support/LocalTime/KernelAsymptotics.lean`) and applies the Support theorem
for that statement. `potential-geometry` and `lem-geometry` do not use them.

The gradient estimate for the kernel, `eq:gradient`, is proved rather than cited;
the paper cites it with the asymptotics as Lawler–Limic's Corollaries 4.3.3 and 4.4.5
(`cerw-flat.tex:351` in the first version). `CERW/Support/LocalTime/KernelBridge.lean`
derives the gradient asymptotics and the one-step gradient bound from the two
asymptotics, together with the level sets of `b` and its logarithmic
growth.

Freedman's inequality, cited for the martingale bounds, is proved in
Lattice-Probability (`LatticeProb.Prob.Freedman`). The forms the paper uses,
on the event of a small bracket and at every dyadic value of the bracket, are
derived in `CERW/Generic/Martingale/FreedmanEvent.lean` and
`CERW/Generic/Martingale/Dyadic.lean`. The Paley–Zygmund inequality, used for
`lem:exp-deviation`, and the Cramér–Wold device, used for
`thm:site-fluctuations`, are in Lattice-Probability (`LatticeProb.Prob.PaleyZygmund`
and `LatticeProb.Prob.CramerWold`).

The mean-value identity behind Newton's spherical averages (`eq:newton`) is
proved from Gauss's flux theorem for the field `w |w|^{-d}`, via polar
coordinates and a swap identity (`CERW/Generic/Newton/`,
`CERW/Support/Geometry/Newton.lean`).

Rademacher's theorem, which makes a norm differentiable almost everywhere, is
Mathlib's, and is applied in `CERW/Generic/Norm/Gradient.lean`. The existence of the
distributional Laplacian of a norm as a locally finite measure is proved in
`CERW/Support/Norm/LocalTime.lean`, from the Riesz–Markov–Kakutani theorem.

The planar remark after `eq:hausdorff` in the first version is stated in its
two-sided reading: the inner radius is at least `aN − C n^{1/6} √L`, and some
unvisited site lies within `aN + C n^{1/6} √L`. The one-sided reading is also
proved, as `CERW.Support.Main.hausdorff_bound_one_sided_of_kernelFacts`, but it is not
registered.
