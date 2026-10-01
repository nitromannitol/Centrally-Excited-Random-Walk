# Independent audit: `CERW/Support/Outer/OuterRadius.lean`

Scope: `CERW.Support.Outer.outer_radius_of` (Proposition 7.1) and `fluctuation_rates_of` (Theorem 1.2),
5923 lines, 203 private declarations and 2 public theorems. Read-only. Probe files lived in the session
scratchpad and were compiled with `lake env lean`; no `lake build`, `lake update`, `lake clean` or `git`.

## Verdicts

1. Statements and composition: PASS
2. No smuggled hypothesis and no vacuity: PASS
3. Soundness of the riskiest steps against the paper: PASS
4. Theorem 1.2 clauses and exponents: PASS

No DEFECT found. Two non-blocking notes are listed at the end.

## 1. Conclusions are exactly the frozen Props; frozen terms compose; axioms (PASS)

* `#check @CERW.Support.Outer.outer_radius_of` gives `inner_radius → near_far → outer_crossing → outer_radius`.
  `#check @CERW.Support.Outer.fluctuation_rates_of` gives `inner_radius → outer_radius → near_far → fluctuation_rates`.
  Probe `example`s with `inner_radius.{0}` and so on elaborate with these exact conclusions.
  `near_far_holds : near_far` and `@outer_crossing_holds : outer_crossing` check at the Prop types.
* Text comparison of the `FROZEN-STATEMENT` blocks of `CERW/Frozen/{OuterRadius,FluctuationRates,InnerRadius,NearFar,OuterCrossing}.lean`
  against the `def` bodies in `CERW/Support/Statements.lean`, after whitespace normalisation, shows identical statements.
  The only difference is the binder form `{d} (hd : 2 ≤ d) :` against `∀ {d} (_ : 2 ≤ d),`.
* The proof terms in `CERW/Frozen/OuterRadius.lean` and `FluctuationRates.lean` are exactly `_OUTER` and `_FLUCT` of `scratch/proofs.py`.
  `inner_radius_of (contact_potential_of …)` is built the same way as `_INNER`.
  `fluctuation_rates_of _INNER _OUTER near_far_holds` takes the `outer_radius_of` term as its middle argument.
  The oleans are newer than the sources (19:58:50 against 19:58:01 on 2026-09-30).
* `#print axioms` was run on all 37 `CERW.Frozen.*` theorems, which are all the declarations in `CERW/Frozen/*.lean`.
  Every one shows only `[propext, Classical.choice, Quot.sound]`.
  The same holds for `CERW.Support.Outer.outer_radius_of`, `fluctuation_rates_of`, `near_far_holds`, `Norm.outer_crossing_holds` and `Inner.inner_radius_of`.

## 2. No smuggled hypotheses, no vacuity (PASS)

* A grep of the file for `sorry|axiom|native_decide|opaque|implemented_by|unsafe|admit|set_option|maxHeartbeats|attribute [|notation|macro|elab|syntax|instance`
  finds none of them. The same grep over `CERW/Frozen/*.lean` and `CERW/Support/Outer/*.lean` finds only matches in prose.
* Only the two target theorems are public. The only Prop-valued hypotheses on the public theorems are `inner_radius`, `near_far`, `outer_crossing` and `outer_radius`.
  `outer_radius` is an input to Theorem 1.2 only, as in the paper. All are discharged in the frozen proofs by theorems that are axiom-clean.
* Every auxiliary Prop-valued input of a private lemma is discharged inside the file by a proved theorem.
  * `NewtonConv d` is proved by `newton_conv (hd : 3 ≤ d)`.
    Integrability, which Bochner integrals would otherwise swallow into `0`, is proved separately by `ev_integrable_chi_mul_potential` and `ev_integrable_chi_norm`.
  * `hcm` is `CERW.Support.Geometry.exists_potential_cell_modulus`.
  * `hnf` is the `near_far` hypothesis.
  * `PathFacts` comes from `exists_pathFacts_prob`, which uses `Main.exists_event_prob` and `LocalTime.exists_kernelFacts`.
    The conversion `pf_of_fluctEvent` only doubles `C₁`. It does not strengthen any clause.
  * `LinOK` comes from `exists_linOK_prob`, a union bound over `s ∈ ballFinset d n` and `k ≤ n` with a Freedman-type bound.
  * `InnerOK` is the conclusion of `hinner`.
  * `CrossOK` comes from `euclid_crossing`, applied to the real `outer_crossing` with `ξ = unitDir ∘ toSpace`, `α = 1/2` and `h = R/2`.
  * `MassOK` comes from `mass_of_inner`. This is a genuine derivation from the volume and radius clauses.
* The antecedents of the deterministic cores are all derived from the hypotheses, never assumed.
  * `w ≤ r/8` for `d ≥ 3` and `w ≤ r/log n` for `d = 2` come from the a priori bound
    `w ≤ K₁ log n (1 + Mc r q^{1/d})` together with `tk_small`, which is an eventual statement proved from the polynomial growth of `r_n`.
  * The `qrate ≤ 1` and `1 ≤ log n` conditions are also derived.
  * The `n₀` thresholds are existentially chosen before `n`.
  * The constant order in `outer_radius_of` is `C₀, C₁, Cf`, then `Cin`, then `Cl`, then `Ccr(C₀, max C₁ Cl)`, then `C, n₀`. There is no circularity.
  * Small `n < n₀` is handled by `1 ≤ ofReal (C n^{-p})` with `C ≥ (n₀+1)^p`.
* `IsCERW` is satisfiable. Existence is proved in `Support/Law/Existence.lean`. It requires `X 0 = 0` only almost surely, and that null set is inside the failure event.
* The inputs `near_far` and `outer_crossing` are not themselves vacuous.
  `near_far` has satisfiable hypotheses: an annular set, cap bounds, and `∫ ‖v−y‖^{2−d} ≤ λ b`, which for `d = 2` reads `|D| ≤ λ b`.
  `outer_crossing` is instantiated with real data.

## 3. Mathematical soundness against the paper (PASS)

Compared against `paper/limit-shapes.tex`, Section 7 (lines 1170–1339) and Theorem 1.2 (lines 130–152).

* **Planar maximum principle (d = 2), Theorem 1.2 (iii).**
  * `mp_re_kernel` shows `Re(u_v/(v−z)) = ⟨u_v, v−z⟩/|v−z|²`.
  * `mp_differentiableOn_field` shows the field `∫_E u_v/(v−z)` is complex differentiable on `B(0,b)`, using domination by `δ⁻²` and `E ⊆ {|v| ≥ b}`.
  * `exp(U_E)` is the modulus of the holomorphic `H = exp(c·field)`. It uses `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn` and continuity from the Hölder lemma.
  * `planar_max_principle` handles a maximum on the circle and an interior maximum, where the potential is constant on the disc and hence equal on the boundary. Both cases are closed.
  * It is applied correctly in `local_core_planar`. The circle bound uses `U_E ≤ U_E^+ ≤ Bd`, available for `|y| = b ≤ R + 2√d`.
    The lower bound uses `co_potential_nonneg_inside` (`⟨u_v, v−y⟩ ≥ 0` for `|v| ≥ b ≥ |y|`).
  * The three regions `|x| ≤ b`, `b < |x| ≤ R` and `|x| > R` are treated as in the paper.
    The cone difference is `≤ 2dε·|b−r|`, and `Cδ`, `Cbd` and the `Z = √r (log n)^{3/2}` bookkeeping close.
  * The step `(r lg)^{1/4} √w ≤ √Kw √r lg^{3/2}` is `co_planar_bd`.
  * The `d = 2` constants match: `2dε = 4ε`, `ω_2` and the exponent `‖v−y‖²` are all consistent with `Model.potential`.
* **Planar exterior (Steps 1 to 3 of Section 7.3).**
  * `pl_first` bounds `W_x ≤ K r` via the packing sum, the `log` sum, `4ε(r−|z|)_+ + Ci r σ`, and `σ lg ≤ θ`.
  * `pl_probe` uses an unvisited cell, the pointwise bound and the cell modulus.
  * `pl_second` and `cap_mass_of_probe` give `|E ∩ B((b+w)u, t)| ≤ K P t`. For `t > r/4` it uses `|E| ≤ Cm' r P` with `r ≤ 4t`.
  * `near_far` is applied with `λ = K₅ P` and `P = √(r lg)`. The hypotheses `1 ≤ w ≤ b`, `λ ≥ 1` and `|E| ≤ λ b` are all checked, as are the cap bounds for `t ≥ w`.
  * This yields `U_E^+ ≤ C((r lg)^{1/4} √w + √(r lg))`, which is eq. `planar-positive-bound`.
  * `co_planar_arith` then gives `w ≤ C√r lg^{5/2}` by AM-GM against `w/2`.
* **d ≥ 3, `(log n)^{d+1}` outer bound.**
  * `hx_path` follows Steps 1 to 4. `U_E^+(y) ≤ (2ε/ω)Θ` outside is proved through `positivePotential_le_of_outside`, with `Θ = lg + sup_y I(y)/r`.
  * `|U_E(y_t)| ≤ CpΘ` is proved through `hx_probe_arith`, using the envelope bound `W ≤ Cenv(L + U^+)`.
  * The cap bound is `|E ∩ B| ≤ K₃ Θ t^{d−1}`.
  * `near_far` gives `U_E^+ ≤ C((Θ w^{d−1})^{1/d} + Θ)`, hence `L ≤ Cenv(2 + Cnf K₃)(…)` via `hx_outer_bound` and `local_mass_of_cap`.
  * The Fubini and layer-cake bound `∫_E |v−y|^{2−d} ≤ c₁ w² + (d−1) λ^{(d−2)/(d−1)} m^{1/(d−1)}` is `gmb_lintegral_bound` with `gmb_choose_scale`.
  * `hx_theta_arith` gives `Θ ≤ Kθ(w²/r + lg)`.
  * `arith_high` closes with Young's inequality in the form `lg·a ≤ δ w + lg^{m+1}Θ/δ^m`, giving `w ≤ K lg^{d+1}` under `K lg^d w ≤ r`.
  * The `d ≥ 3` envelope lemma uses that `Σ (1+|y|)^{2−2d}` converges, which needs `d ≥ 3`, and the Newton convolution `χ * U_D ≤ ‖χ‖₁ U_D^+`.
  * `outer_core_high` assembles it as in the paper's final paragraph. `R ≤ b + w ≤ r + Cin lg + Ka lg^{d+1}`.
* **Crossing.** `euclid_crossing` instantiates `outer_crossing` with `q = u_{Y j₀}`.
  It checks `⟨q, ξ(Y j)⟩ ≥ 1/2` on the window `T − R/2 < ⟨q, Y j⟩`, the compensated-increment bound with `log(n+2) ≤ 2 log n`, and the ramp martingale bounds.
  It also uses `outerMax` monotonicity through `⟨q, z⟩ ≤ |z|`.
* **Borel–Cantelli with the same constant (Theorem 1.2).**
  * `key` is proved for an arbitrary `q > 0`. It takes the union of the three events (`PathFacts`, `InnerOK`, `outer_radius`) and handles `n < max n₀ 2` trivially.
  * The probability clause uses `key p` and the almost-sure clause uses `key 2`.
  * The final constant is `max Cp C2`. The monotonicity `hmono : Good C → Good C'` for `C ≤ C'` is proved separately, for all four sub-clauses and both dimension branches.
  * The probability clause and the almost-sure clause therefore share the single `C` required by the frozen Prop.
  * The summability step is `Main.ae_eventually_of_le_rpow`, which requires `1 < p` and uses `Real.summable_nat_rpow_inv`. It is applied with `p = 2`, as in the paper's `p > 1`.

## 4. Theorem 1.2 clauses (PASS)

The frozen `Good` is compared with the theorem at lines 130–152 and the definitions at lines 98–127.

* Radii. `d = 2`: `|R_in − r| ≤ C√(r log n)` and `R_out − r ≤ C√r (log n)^{5/2}`.
  `d ≥ 3`: `|R_in − r| ≤ C log n` and `R_out − r ≤ C (log n)^{d+1}`. These match, including the `rpow` exponents `5/2` and `d+1`.
  The inner-radius clause is derived from `InnerOK` via `r q = √(r log n)` or `log n` (`radius_mul_qrate`).
* Volume. `volume (((r n)⁻¹ • cellSet Y n) ∆ ball 0 1) ≤ ofReal (C q)` with `q = √(log n / r)` for `d = 2` and `log n / r` for `d ≥ 3`.
  This matches the paper, and it is the same expression as in `inner_radius`.
* Local times. `|ℓ_n(x) − 2dε (r − |x|)_+| ≤ C√r (log n)^{3/2}` for `d = 2` and `C√(r log n)` for `d ≥ 3`, for all `x ∈ ℤ^d`. These match.
  The exponents arise as `√r lg^{3/2}` through `Z` in the plane, and as `lg^{d+1} ≤ r^{1/2}` eventually in `d ≥ 3`.
* `radius d ε n` is the paper's `r_n`. `unitBallVolume d` is definitionally `(volume (ball 0 1)).toReal`. `maxRadius` includes time `n`, and `cellSet` is the union of cells of `departureRange` (`j < n`), as in the paper.

## Notes (non-blocking)

* **Route difference in the plane.** The a priori local-time bound feeding `W_x ≤ C r` in Step 1 is not the paper's
  `ℓ_n ≤ 2dε(b−|x|)_+ + Cw + C√r log n`.
  The proof uses the Proposition 6.1 profile bound `ℓ̃_n ≤ 2dε(r−|y|)_+ + Cin r q^{1/2}` through `co_local_le` and `pl_braSum_le_of_cone`,
  with `(4εa₂ + a₁) log n = o(r)` from `σ lg ≤ θ`.
  This is a valid alternative and avoids using `w`. It is a transcription difference rather than a defect.
* **Freshness of the build.** I did not rebuild. I relied on `.lake/build` oleans that postdate the sources by about one minute.
  I did not verify the olean traces. The gate on `build_ok.sh` (a build in a pristine copy) remains the coordinator's check.
  The probe confirms that the compiled `import CERW` environment has the axiom-clean `CERW.Frozen.outer_radius` and `fluctuation_rates`.
