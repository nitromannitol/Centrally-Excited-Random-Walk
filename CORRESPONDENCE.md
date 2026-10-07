# Correspondence between the paper and the formalization

`paper/limit-shapes.tex` is the pinned source of *Kozma's centrally excited walk converges to a Euclidean ball* (Ahmed Bou-Rabee and Yuval Peres). Each registered theorem has one declaration under `CERW/Frozen/`, with a paper label and source location. The paper writes the drift as `κ`; Lean writes it as `ε`.

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
  `CERW.normBallVolume Ψ` in place of `ωd`.
  Every cast to `ℝ` is at a leaf.

**Occupation.**
- `A_n` is `CERW.departureRange`, the set `{X_0, …, X_{n-1}}`, and `ℓ_n` is
  `CERW.localTime`; the paper's set of sites visited by time `n` is `A_{n+1}`,
  and the set of sites visited by time `n` is `CERW.visitedRange`. `M_n` is
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
  constants `C_d` of `lem:local` and `lem:geometry` precede
  `ε`; `C(d)` of `lem:cell` precedes `Ψ` and `ξ`; `C(d, Ψ)` of `lem:geometry`
  precedes `ε` and `D`; and `ρ₀` of `lem:radial` precedes `ε`. `PROOF.md`,
  section 4, lists the readings of the individual statements.
- The universe of `Ω` is `u`. No theorem carries a cited result as a hypothesis: the martingale
  central limit theorem `CERW.Generic.Martingale.CLT.MartingaleCLT.{u}` and the lower half of
  Stout's law `CERW.Generic.Martingale.Lil.StoutLower.{u}` are proved.

## Registered statements

<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->

| id | Lean | paper | state |
|---|---|---|---|
| `thm-shape` | `CERW.Frozen.limit_shape` | `limit-shapes.tex:106-119`, `thm:shape` | PROVED |
| `thm-fluctuations` | `CERW.Frozen.fluctuation_rates` | `limit-shapes.tex:130-152`, `thm:fluctuations` | PROVED |
| `thm-sharp-radii` | `CERW.Frozen.sharp_radii` | `limit-shapes.tex:159-164`, `thm:sharp` | PROVED |
| `thm-sharp-radii-lil` | `CERW.Frozen.sharp_radii_lil` | `limit-shapes.tex:165-170`, `thm:sharp` | PROVED |
| `thm-sharp-bulk` | `CERW.Frozen.sharp_bulk` | `limit-shapes.tex:171-175`, `thm:sharp` | PROVED |
| `thm-sharp-width` | `CERW.Frozen.sharp_width` | `limit-shapes.tex:176-189`, `thm:sharp` | PROVED |
| `thm-norm-shape` | `CERW.Frozen.norm_shape` | `limit-shapes.tex:341-354`, `thm:norm-shape` | PROVED |
| `lem-ballpotential` | `CERW.Frozen.norm_ball_potential` | `limit-shapes.tex:372-377`, `lem:ballpotential` | PROVED |
| `lem-local` | `CERW.Frozen.norm_local_time_potential` | `limit-shapes.tex:396-412`, `lem:local` | PROVED |
| `lem-freedman` | `CERW.Frozen.freedman_bound` | `limit-shapes.tex:448-453`, `lem:freedman` | PROVED |
| `lem-cell` | `CERW.Frozen.cell_gradient` | `limit-shapes.tex:466-471`, `lem:cell` | PROVED |
| `prop-coarse` | `CERW.Frozen.norm_coarse_bounds` | `limit-shapes.tex:541-548`, `prop:coarse` | PROVED |
| `lem-crossing` | `CERW.Frozen.drift_crossing` | `limit-shapes.tex:562-567`, `lem:crossing` | PROVED |
| `prop-norm-shape` | `CERW.Frozen.norm_shape_rates` | `limit-shapes.tex:701-717`, `prop:norm-shape` | PROVED |
| `lem-layer` | `CERW.Frozen.layer_potential` | `limit-shapes.tex:522-527`, `lem:layer` | PROVED |
| `lem-contact` | `CERW.Frozen.contact_potential` | `limit-shapes.tex:774-779`, `lem:contact` | PROVED |
| `lem-outer-crossing` | `CERW.Frozen.outer_crossing` | `limit-shapes.tex:578-583`, `lem:outer-crossing` | PROVED |
| `prop-inner` | `CERW.Frozen.inner_radius` | `limit-shapes.tex:903-919`, `prop:inner` | PROVED |
| `prop-stronger-outer` | `CERW.Frozen.outer_radius` | `limit-shapes.tex:1015-1020`, `prop:stronger-outer` | PROVED |
| `lem-near-far` | `CERW.Frozen.near_far` | `limit-shapes.tex:1046-1051`, `lem:near-far` | PROVED |
| `thm-moment-fluctuations` | `CERW.Frozen.moment_fluctuations` | `limit-shapes.tex:1196-1217`, `thm:moment-fluctuations` | PROVED |
| `lem-fixed-site-centering` | `CERW.Frozen.fixed_site_centering` | `limit-shapes.tex:1261-1267`, `lem:fixed-site-centering` | PROVED |
| `thm-site-fluctuations` | `CERW.Frozen.site_fluctuations` | `limit-shapes.tex:1291-1316`, `thm:site-fluctuations` | PROVED |
| `lem-exp-deviation` | `CERW.Frozen.exp_deviation` | `limit-shapes.tex:1366-1380`, `lem:exp-deviation` | PROVED |
| `prop-bulk-profile` | `CERW.Frozen.bulk_profile` | `limit-shapes.tex:1498-1505`, `prop:bulk-profile` | PROVED |
| `lem-separated-brackets` | `CERW.Frozen.separated_brackets` | `limit-shapes.tex:1532-1539`, `lem:separated-brackets` | PROVED |
| `prop-log-lower` | `CERW.Frozen.log_lower_bounds` | `limit-shapes.tex:1602-1616`, `prop:log-lower` | PROVED |

<!-- FROZEN-SURFACE-END -->

The four statements `thm-sharp-radii`, `thm-sharp-radii-lil`, `thm-sharp-bulk`
and `thm-sharp-width` correspond to parts (i), (ii), (iii) and (iv) of Theorem 1.3.
The last includes all three clauses (a), (b) and (c).

`lem:crossing` supplies the vector event and the crossing estimate on that event.
`lem:outer-crossing` supplies the simultaneous radial finite-family event and the
deterministic implication for each vector satisfying its displayed hypotheses.
`lem:contact` supplies the nearest projection, the seven estimates of Section 5.1,
and the contact bound almost surely on that event. `lem:exp-deviation` assumes
adaptation, integrability, the martingale identity, and almost-sure start and
increment bounds through the stated finite horizon. Constants precede the
probability space and the quantities on which they cannot depend.

The proofs are in `CERW/Support/RevisedPaper.lean`,
`CERW/Support/RevisedPaperCarrier.lean`, `CERW/Support/RevisedPaperContact.lean`,
`CERW/Support/RevisedPaperWidth.lean` and `CERW/Support/Lower/ExpDeviationAE.lean`.

## Additional mathematical results

The table above carries the labelled statements of the pinned paper. The paper also makes assertions that no label carries: the
scope of Newton's theorem, displays inside proofs, and consequences stated in the introduction. The modules named below prove them for the
actual objects of the paper. They are ordinary support: none is a registered node, none is a frozen statement, and the registered
statements above are unchanged by them. The table and the dedicated-support list below describe the
source assertions covered by these modules; limitations stated for one row concern that row's
named exports.

| lines of the pinned paper | assertion | declarations (module.name) | covered | not covered |
|---|---|---|---|---|
| l.760-763, `eq:radial-convolution` | Newton's theorem for a nonnegative integrable radial function: its Newton-field convolution equals the mass of the open ball of radius norm(y) times y/norm(y)^d, for almost every y. | `RadialNewtonAE.ae_integral_weight_smul_newtonField_eq_univ` | The vector identity, for almost every y, for a nonnegative radial profile chi that is Borel measurable and integrable on the spatial ball norm, in every dimension d >= 2; no bound, monotonicity or moment on chi. | The carrier is a Borel profile chi. A radial spatial function that is only integrable is reached through the next row. The `w != 0` guard is the null-singleton convention. |
| l.764-768, `eq:newton-convolution` | For a bounded measurable D and every real point y, the convolution of the radial function with the potential U_D is the integral against the ball mass m(norm(v - y)), with coefficient 2 eps / omega_d. | `RadialNewtonConvolution.exists_borel_profile`<br>`RadialNewtonConvolution.ballMass_congr`<br>`RadialNewtonConvolution.normPotential_convolution_eq`<br>`RadialNewtonConvolution.normPotential_convolution_eq_radial`<br>`RadialNewtonConvolution.convolution_normPotential_eq_radial` | Every point y, any real eps, every norm, every pointwise radial nonnegative integrable function f on the Euclidean space; the Borel profile of f and the open-ball masses are produced and transported. | These named exports are norm-only; arbitrary compact convex origin-interior gauges are supplied separately by `GaugeRadialNewtonConvolution`. |
| l.769-772, `eq:contact-convolution` | At a contact point y0 (Psi(y0) = b, {Psi < b} inside D) the convolution with U_E, E = D minus {Psi < b}, is at most (the integral of f) times H, H = U_D(y0). | `RadialNewtonConvolution.contact_convolution_le`<br>`RadialNewtonConvolution.contact_convolution_le_radial` | For every nonnegative integrable radial f, eps >= 0, any real b, bounded measurable D; integrability of the convolution and U_E(y0) = U_D(y0) are outputs. | Deterministic and abstract in D; the walk's own set D_n is in the next row. |
| l.634-651 and 768-771: the visited-cell set D_n, inner threshold b, contact point | The contact comparison for the actual cell set D_n of the sites visited before time n, with b the infimum of Psi outside D_n, an attained contact point that is a limit of unvisited points, and the unvisited-cell geometry. | `RadialNewtonSourceContact.isGLB_normInnerRadius`<br>`RadialNewtonSourceContact.exists_contact_point`<br>`RadialNewtonSourceContact.exists_unvisited_cell_of_contact_point`<br>`RadialNewtonSourceContact.ae_contact_convexity`<br>`RadialNewtonSourceContact.contact_convolution_le_cellSet`<br>`RadialNewtonSourceContact.source_contact_convolution` | Every path and every n (including n = 0), every norm, d >= 1 for the geometry and d >= 2 for the convolution; one contact witness before all admissible f. | The full excess-integral estimate of l.634-656 and the downstream rates are separate producers and are not reproved here. No claim that H > 0: for the l-infinity norm a legal path can give H = 0. |
| l.774-779, `lem:contact`, convolution form | The contact convolution bound on the event of the seven estimates, with the constants of the contact height. | `RadialNewtonSourceContact.contact_convolution_prob` | A law-level consequence of the registered `Frozen.contact_potential`: common constants chosen before the walk, for each admissible f. | This export gives a probability estimate for each admissible f. The registered contact theorem supplies the contact bound on the seven-estimate event. |
| l.1167-1179, planar all-real-point displays and Borel-Cantelli with p > 1 | In the plane, almost surely and eventually: the real-point excess-potential bound, the two-region local-time estimates, the absorbed inner-radius error; also on the seven-estimate event and at the legal carrier. | `PlanarRealProfileAE.planar_real_displays_ae`<br>`PlanarRealProfileAE.planar_real_displays_ae_on_E7`<br>`PlanarRealProfileAE.planar_real_profile_ae_on_carrier`<br>`PlanarRealProfileAE.exists_realization_planar_real_ae`<br>`PlanarRealProfile.planar_real_profile_prob`<br>`PlanarRealProfile.planar_displays_on_E7`<br>`PlanarRealProfile.planar_newton_gradient_at_real_point` | d = 2, 0 < eps < 1/2, an arbitrary realization of the walk (`IsCERW`); one constant before the probability space, the walk, the sample point and the time; E7 and legality are separate almost-sure conclusions. | Original-`F_n` finite-prefix measurability is supplied separately by `CERW.Support.Outer.PlanarRealFiltration.measurableSet_planarRealDisplays_filtration_of_isCERW` and `CERW.Support.Outer.PlanarRealFiltration.measurableSet_E7_filtration_of_isCERW`; this planar row does not assert a general gauge profile. |
| Sections 6-7 displays: `eq:potential-convolution`, `eq:envelopehigh`, `eq:global`, layer-cake identity, planar envelope, harmonicity | The displays of the inner- and outer-radius sections in their full form, at every point. | `SourceDisplays.potential_convolution`<br>`SourceDisplays.envelope_high_full`<br>`SourceDisplays.layer_cake_eq`<br>`SourceDisplays.global_approximation_scale`<br>`SourceDisplays.planar_envelope_all_points`<br>`SourceDisplays.planar_localtime_all_sites`<br>`SourceDisplays.harmonicOnNhd_planar_potential`<br>`SourceDisplays.harmonicAt_planar_newton_field` | The displays for the actual objects (U_D, U_D^+, the weight (1 + norm(z))^(2-2d), the cells of the range, the local time and the bracket); deterministic statements take only clauses of the good event. | `HarmonicAt U_E` as a consequence of the full planar profile is not an exported claim. |
| l.121, 154, 194, 198: consequences stated after the theorems on fluctuations and sharpness | Fixed-site limits, the volume and count rates, recurrence, the log-scale alternative, the width window n^(1/6 +- eta), the dyadic sharp bulk, the correct order of the local times. | `SourceIntroductionConsequences.source_site_and_volume_limits`<br>`SourceIntroductionConsequences.fluctuation_count_rates`<br>`SourceProbabilityConsequences.log_lower_and_fluctuation_ae`<br>`SourceProbabilityConsequences.width_upper_ae`<br>`SourceProbabilityConsequences.width_upper_ae_every_eta`<br>`SourceProbabilityConsequences.bulk_upper_sqrt_ball`<br>`SourceProbabilityConsequences.sharp_bulk_dyadic_ae`<br>`SourceProbabilityConsequences.planar_width_fluctuation_bound`<br>`SourceProbabilityConsequences.planar_not_improvable`<br>`SourceProbabilityConsequences.planar_exponent_not_lowerable`<br>`SourceProbabilityConsequences.local_times_correct_order`<br>`SourceProbabilityFiniteTime.planar_width_fluctuation_bound_all` | Each with the quantifiers, constants and scales of the source, by applying the registered estimates; the width bound is stated for every n >= 2. | These consume the registered theorems at their registered readings; they are not new registered statements. |
| l.356 and Theorem 2.1 remarks: norm = gauge of its unit ball; strict inclusion rates; volume limit; the explicit quadratic process | A norm is the Minkowski functional of its closed unit ball; sharp Laplacian growth; volume limit; inner-radius bound; the identity norm(X_n)^2 = n - 2 eps sum Psi + Q_n with Q a martingale; the inclusion form of the rates. | `NormGaugeConsequences.norm_shape_rates_inclusions`<br>`NormGaugeConsequences.gauge_shape_rates_inclusions`<br>`NormGaugeConsequences.norm_volume_limit`<br>`NormGaugeConsequences.norm_inner_radius_upper_bound`<br>`NormGaugeConsequences.exists_unique_isDistribLaplacian_norm_sharp`<br>`NormGaugeConsequences.norm_measure_ball_le_sharp`<br>`NormGaugeConsequences.sq_euclidNorm_eq_norm`<br>`NormGaugeConsequences.quadraticMartingale_ae_eq_driftDynkin`<br>`NormGaugeConsequences.martingale_driftDynkin_sq`<br>`QuadraticProcessMartingale.martingale_quadraticMartingale`<br>`QuadraticProcessMartingale.quadratic_identity_and_martingale`<br>`QuadraticProcessMartingale.quadraticMartingale_isCERW` | The norm instances of the gauge results, with the exact Laplacian coefficient; the explicit process is a martingale for the natural filtration (by transfer of the Dynkin martingale along the almost-sure equality). | Arbitrary asymmetric-gauge radial/contact identities are supplied separately by `GaugeRadialNewtonConvolution` and `GaugeSourceContactConsequences.gauge_source_contact`. |
| l.1366-1380, `lem:exp-deviation`, almost-sure and finite-filtration forms | Exponential deviations for martingales with an almost-sure start and almost-sure increment bound, and for a finite filtration indexed by Fin (n + 1). | `ExpDeviationAE.exp_deviation_ae_upTo`<br>`ExpDeviationAE.exp_deviation_ae`<br>`FiniteHorizonExpDeviation.martingale_extendProcess`<br>`FiniteHorizonExpDeviation.martingale_restrict`<br>`FiniteHorizonExpDeviation.exp_deviation_finite` | The two sure hypotheses weakened to almost sure, the same constants and conclusions; the finite-filtration reading agrees with the N-indexed reading (extension and restriction proved). | `Frozen.exp_deviation` is the finite-horizon almost-sure form; the form with pointwise bounds is proved in `CERW/Support/Lower/ExpDeviation.lean`. |

Covered by dedicated support outside the registry (not paper nodes, not frozen statements):
* The finite-prefix (`F_n`) measurability of the whole real-profile event is supplied by
  `CERW/Support/Outer/PlanarRealProfileFiltration.lean`.
* The unrestricted asymmetric-gauge radial Newton and contact inputs are supplied by
  `CERW/Support/Norm/GaugeRadialNewtonConvolution.lean` and
  `CERW/Support/Norm/GaugeSourceContactConsequences.lean`.
* The in-probability width gap is supplied by
  `CERW.Support.RevisedPaper.sharp_width_extended` and
  `CERW.Support.Lower.PlanarGap.gap_limsup_le_smallBall`. The window consequences are supplied by
  `SourceProbabilityConsequences.width_upper_ae`, `width_upper_ae_every_eta` and
  `SourceProbabilityFiniteTime.planar_width_fluctuation_bound_all`.

The unused whole-future carrier is not an original-`F_n`-consumed source obligation and is not
claimed here. None of the modules above is a registered statement; the registered statements are
unchanged by them.

The registry gates check labelled environments only; the table above is maintained by hand and is not checked by a gate.

## Martingale limit theorems and kernel estimates

The martingale central limit theorem is proved as
`CERW.Generic.Martingale.CLT.martingaleCLT_proved`.
Stout's law of the iterated logarithm is proved as
`CERW.Generic.Martingale.Lil.stout_upper` and
`CERW.Generic.Martingale.LilAssembly.stout_lower`.
These proofs are supplied to the assembly lemmas, so the paper's registered
theorems carry no cited-result hypothesis.

The lattice potential-kernel and Green-function asymptotics are proved in
Lattice-Probability by `LatticeProb.External.potentialKernelAsymptotics_holds`.
`CERW/Support/LocalTime/KernelAsymptotics.lean` supplies the kernel facts used
in this development. `CERW/Support/LocalTime/KernelBridge.lean` derives the
gradient asymptotics and the one-step gradient bound.

Freedman's inequality is proved in Lattice-Probability. The forms used for
small brackets and dyadic bracket values are proved in
`CERW/Generic/Martingale/FreedmanEvent.lean`.
