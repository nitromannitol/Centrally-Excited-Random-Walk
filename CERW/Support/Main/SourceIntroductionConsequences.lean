import CERW.Support.Norm.NormGaugeConsequences
import CERW.Support.Norm.EuclideanCoarse
import CERW.Support.Main.KernelAnchors
import CERW.Support.LocalTime.KernelAsymptotics
import CERW.Support.Drift.Bridge
import CERW.Frozen.FluctuationRates

/-!
# Two consequences stated in the introduction: the volume rate and the fixed-site limits

Let `d ≥ 2`, `0 < ε < 1/d`, let `ω_d` be the volume of the Euclidean unit ball, let
`r_n = ((d+1) n/(2 d ε ω_d))^{1/(d+1)}`, and let `X` be the centrally excited random walk
(`IsCERW μ ε X`), with departure range `A_n` (the sites `X_0, …, X_{n-1}`), local time
`ℓ_n(x) = #{j < n : X_j = x}` and cell union `D_n = ⋃_{x ∈ A_n} (x + [-1/2, 1/2)^d)`.

**The volume rate** (line 154 of the source: "Since `|D_n| = |A_n|`, part (ii) also bounds
`| |A_n| / r_n^d - ω_d |` by the right side of part (ii)").
`fluctuation_count_rates` states the fluctuation bounds of Theorem 1.2 together with the count
bound, in the form of `Frozen.fluctuation_rates`: for every `p > 0` there is `C > 0`, chosen before
the law, the walk and `n`, such that for every `n ≥ 2`, with probability at least `1 - C n^{-p}`, the
bounds on the radii, on the volume of `r_n⁻¹ D_n ∆ B(0,1)` and on the local times hold together with

`| |A_n| / r_n^d - ω_d | ≤ C √(log n / r_n)` if `d = 2` and `≤ C log n / r_n` if `d ≥ 3`;

and, almost surely, all of these bounds hold for all large `n`. The proof applies
`Frozen.fluctuation_rates` and derives the count bound from its volume clause with the same
constant: `volume_cellSet` gives `|D_n| = |A_n|`, the scaling of Lebesgue measure gives
`|r_n⁻¹ D_n| = |A_n| / r_n^d` (`volume_smul_cellSet`), and the measure of a symmetric difference
bounds the difference of the measures (`abs_card_div_pow_sub_unitBallVolume_le`). No estimate on
the symmetric difference is a hypothesis.

**The fixed-site limits** (line 118: "Part (ii) gives `ℓ_n(x)/r_n → 2dε` at every fixed site `x`,
hence part (iii), …; part (i) gives `|A_n|/r_n^d → ω_d`").
`source_site_and_volume_limits` states that, almost surely, simultaneously, for every site `x`,
`ℓ_n(x) / r_n → 2dε`, that `|A_n| / r_n^d → ω_d`, and that every site is visited infinitely often.
The count limit is `NormGaugeConsequences.norm_volume_limit` at the Euclidean norm, through
`isCERW_iff_isDriftCERW`, `isNorm_euclidean`, `isSubgradient_unitDir` and
`normBallVolume_euclidean`; the fixed-site limit is the fixed-site clause of
`ball_shape_of_kernelFacts` (stated for `N_n = n^{1/(d+1)}` and the constant `a`, with
`r_n = a N_n`), divided by `a`; and the recurrence is derived from the fixed-site limit
(`frequently_eq_of_tendsto_localTime_div`), not copied from the registered theorem. Both the local
time `ℓ_n` and the range `A_n` count departures (times `0, …, n-1`), as in the source, so no
correction between departures and visits arises.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Main.SourceIntroductionConsequences

open CERW

variable {d : ℕ}

/-! ## The count of departed sites from the volume of the cell union -/

/-- **The volume of the scaled cell union is the scaled count.** For `ρ > 0`,
`|ρ⁻¹ D_n| = |A_n| / ρ^d`, because `|D_n| = |A_n|` (`volume_cellSet`) and Lebesgue measure scales by
the `d`-th power. -/
theorem volume_smul_cellSet (Y : ℕ → Site d) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (ρ⁻¹ • cellSet Y n) = ENNReal.ofReal (((departureRange Y n).card : ℝ) / ρ ^ d) := by
  have hpos : 0 < (ρ⁻¹) ^ d := pow_pos (inv_pos.2 hρ) d
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, CERW.Support.Occupation.volume_cellSet,
    abs_of_pos hpos, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hpos.le, inv_pow,
    inv_mul_eq_div]

/-- **The count of departed sites differs from the volume of the unit ball by at most the volume of
the symmetric difference.** If `|ρ⁻¹ D_n ∆ B(0,1)| ≤ b` with `ρ > 0` and `b ≥ 0`, then
`| |A_n| / ρ^d - ω_d | ≤ b`. -/
theorem abs_card_div_pow_sub_unitBallVolume_le (Y : ℕ → Site d) (n : ℕ) {ρ b : ℝ} (hρ : 0 < ρ)
    (hb : 0 ≤ b)
    (h : volume ((ρ⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ENNReal.ofReal b) :
    |((departureRange Y n).card : ℝ) / ρ ^ d -
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal| ≤ b := by
  have hvs := volume_smul_cellSet Y n hρ
  have hfs : volume (ρ⁻¹ • cellSet Y n) ≠ ⊤ := by rw [hvs]; exact ENNReal.ofReal_ne_top
  have hft : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hfd : volume ((ρ⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have h1 : volume (ρ⁻¹ • cellSet Y n) ≤
      volume ((ρ⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) +
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    tsub_le_iff_right.mp le_measure_symmDiff
  have h2 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      volume ((ρ⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) +
        volume (ρ⁻¹ • cellSet Y n) := by
    have h3 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) -
        volume (ρ⁻¹ • cellSet Y n) ≤
        volume ((Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∆ (ρ⁻¹ • cellSet Y n)) :=
      le_measure_symmDiff
    rw [symmDiff_comm] at h3
    exact tsub_le_iff_right.mp h3
  have hd' : (volume ((ρ⁻¹ • cellSet Y n) ∆
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal ≤ b :=
    ENNReal.toReal_le_of_le_ofReal hb h
  have hs' : (volume (ρ⁻¹ • cellSet Y n)).toReal = ((departureRange Y n).card : ℝ) / ρ ^ d := by
    rw [hvs, ENNReal.toReal_ofReal (by positivity)]
  have h1' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfd, hft⟩) h1
  have h2' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfd, hfs⟩) h2
  rw [ENNReal.toReal_add hfd hft] at h1'
  rw [ENNReal.toReal_add hfd hfs] at h2'
  rw [abs_le]
  constructor <;> linarith

/-- **The count bound from the volume clause.** For `n ≥ 2`, `ρ > 0` and `C ≥ 0`, the bound
`|ρ⁻¹ D_n ∆ B(0,1)| ≤ C √(log n / ρ)` (`d = 2`), `≤ C log n / ρ` (`d ≥ 3`) gives the same bound for
`| |A_n| / ρ^d - ω_d |`. -/
theorem abs_card_div_pow_sub_le_of_volume_clause (Y : ℕ → Site d) {n : ℕ} (hn : 2 ≤ n) {ρ C : ℝ}
    (hρ : 0 < ρ) (hC : 0 ≤ C)
    (h : volume ((ρ⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ENNReal.ofReal (C * if d = 2 then Real.sqrt (Real.log n / ρ) else Real.log n / ρ)) :
    |((departureRange Y n).card : ℝ) / ρ ^ d -
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal| ≤
      C * if d = 2 then Real.sqrt (Real.log n / ρ) else Real.log n / ρ := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  refine abs_card_div_pow_sub_unitBallVolume_le Y n hρ ?_ h
  refine mul_nonneg hC ?_
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact div_nonneg hlog hρ.le

/-- **The volume rate of the count of departed sites** (line 154). The fluctuation bounds of
Theorem 1.2 (radii, volume of `r_n⁻¹ D_n ∆ B(0,1)`, local times), together with
`| |A_n| / r_n^d - ω_d | ≤ C √(log n / r_n)` (`d = 2`) and `≤ C log n / r_n` (`d ≥ 3`), hold
simultaneously, for every `n ≥ 2`, with probability at least `1 - C n^{-p}`, and, almost surely, for
all large `n`; the constant `C` is chosen after `p` and before the law, the walk and `n`. -/
theorem fluctuation_count_rates (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      ((if d = 2 then
          |CERW.innerRadius Y n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
            CERW.maxRadius Y n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        else
          |CERW.innerRadius Y n - r n| ≤ C * Real.log n ∧
            CERW.maxRadius Y n - r n ≤ C * Real.log n ^ ((d : ℝ) + 1)) ∧
      volume (((r n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          ≤ ENNReal.ofReal
            (C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) ∧
      ∀ x : Site d,
        |(CERW.localTime Y n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (r n * Real.log n)) ∧
      |((CERW.departureRange Y n).card : ℝ) / r n ^ d - ωd| ≤
        C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good C (X · ω) n) := by
  dsimp only
  intro ε hε hεd p hp
  obtain ⟨C, hC, h1, h2⟩ := CERW.Frozen.fluctuation_rates.{u} hd ε hε hεd p hp
  have hω : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal :=
    CERW.unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hr : ∀ n : ℕ, 2 ≤ n →
      0 < ((d + 1) * (n : ℝ) / (2 * d * ε * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d))
        1)).toReal)) ^ ((1 : ℝ) / (d + 1)) := fun n hn =>
    Real.rpow_pos_of_pos (by
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      positivity) _
  refine ⟨C, hC, fun μ _ X hX n hn => ?_, fun μ _ X hX => ?_⟩
  · refine le_trans (measure_mono ?_) (h1 μ X hX n hn)
    intro ω hω' hgood
    apply hω'
    exact ⟨hgood, abs_card_div_pow_sub_le_of_volume_clause (X · ω) hn (hr n hn) hC.le hgood.2.1⟩
  · filter_upwards [h2 μ X hX] with ω hωa
    filter_upwards [hωa, eventually_ge_atTop 2] with n hgood hn
    exact ⟨hgood, abs_card_div_pow_sub_le_of_volume_clause (X · ω) hn (hr n hn) hC.le hgood.2.1⟩

/-! ## The fixed-site limits and the recurrence -/

/-- The radius `r_n = ((d+1) n/(2 d ε V))^{1/(d+1)}` tends to infinity. -/
theorem tendsto_radius_atTop (hd : 1 ≤ d) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) :
    Tendsto (fun n : ℕ => (((d : ℝ) + 1) * n / (2 * d * ε * V)) ^ ((1 : ℝ) / (d + 1))) atTop
      atTop := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * V) := by positivity
  have h1 : Tendsto (fun n : ℕ => (((d : ℝ) + 1) / (2 * d * ε * V)) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have h2 := (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / ((d : ℝ) + 1))).comp h1
  refine Tendsto.congr (fun n => ?_) h2
  simp only [Function.comp_apply]
  rw [mul_div_right_comm]

/-- **Recurrence from the fixed-site limit.** If `ℓ_n(x)/r_n → c > 0` with `r_n → ∞`, then the walk
is at `x` at infinitely many times, because a site visited only finitely often has a bounded local
time. -/
theorem frequently_eq_of_tendsto_localTime_div {X : ℕ → Site d} {r : ℕ → ℝ}
    (hr : Tendsto r atTop atTop) {x : Site d} {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun n : ℕ => (CERW.localTime X n x : ℝ) / r n) atTop (𝓝 c)) :
    ∃ᶠ j in atTop, X j = x := by
  by_contra hnot
  rw [Filter.not_frequently] at hnot
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hnot
  have hbound : ∀ n, CERW.localTime X n x ≤ J := by
    intro n
    have hsub : (Finset.range n).filter (fun j => X j = x) ⊆ Finset.range J := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_range]
      by_contra hjJ
      exact hJ j (not_lt.mp hjJ) hj.2
    calc CERW.localTime X n x = ((Finset.range n).filter fun j => X j = x).card := rfl
      _ ≤ (Finset.range J).card := Finset.card_le_card hsub
      _ = J := Finset.card_range J
  have hlim : Tendsto (fun n : ℕ => (J : ℝ) / r n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hr
  have hle : ∀ᶠ n : ℕ in atTop, (CERW.localTime X n x : ℝ) / r n ≤ (J : ℝ) / r n := by
    filter_upwards [hr.eventually_gt_atTop 0] with n hn
    exact div_le_div_of_nonneg_right (by exact_mod_cast hbound n) hn.le
  have := le_of_tendsto_of_tendsto h hlim hle
  linarith

/-- **The fixed-site limits, the volume limit and the recurrence** (line 118). Let `d ≥ 2`,
`0 < ε < 1/d` and let `X` be the centrally excited random walk. Almost surely, simultaneously:
at every site `x`, `ℓ_n(x)/r_n → 2dε`; `|A_n|/r_n^d → ω_d`; and every site is visited infinitely
often. -/
theorem source_site_and_volume_limits (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d) (hX : CERW.IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ x : Site d,
        Tendsto (fun n : ℕ => (CERW.localTime (X · ω) n x : ℝ) / r n) atTop (𝓝 (2 * d * ε))) ∧
      Tendsto (fun n : ℕ => ((CERW.departureRange (X · ω) n).card : ℝ) / r n ^ d) atTop
        (𝓝 ωd) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x) := by
  intro ωd r
  have hd1 : 1 ≤ d := by omega
  have hω : 0 < ωd := CERW.unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  -- the count of departed sites: the volume limit at the Euclidean norm
  have hell : ∀ i : Fin d, ε * (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (coordVec i) <
      1 / (d : ℝ) := by
    intro i
    have h1 : ‖coordVec (d := d) i‖ = 1 := by simp [coordVec]
    show ε * ‖coordVec (d := d) i‖ < 1 / (d : ℝ)
    rw [h1, mul_one]
    exact hεd
  have hvol := CERW.Support.Norm.NormGaugeConsequences.norm_volume_limit hd
    (CERW.Support.Norm.EuclideanCoarse.isNorm_euclidean (d := d))
    (ξ := fun z => unitDir (toSpace z))
    (fun x hx => CERW.Support.Norm.EuclideanCoarse.isSubgradient_unitDir
      (fun h => hx (CERW.Support.Norm.EuclideanCoarse.eq_zero_of_toSpace_eq_zero h)))
    CERW.Support.Norm.EuclideanCoarse.unitDir_toSpace_zero hε hell μ X
    ((CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX)
  dsimp only at hvol
  rw [CERW.Support.Norm.EuclideanCoarse.normBallVolume_euclidean] at hvol
  -- the fixed-site local times: the shape theorem for the scale `N_n = n^{1/(d+1)}`
  obtain ⟨_, _, hF⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  have key := CERW.Support.Main.ball_shape_of_kernelFacts hd hF hε hεd μ X hX
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * ωd) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hr : ∀ n : ℕ, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    show (((d : ℝ) + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) = _
    rw [show ((d : ℝ) + 1) * n / (2 * d * ε * ωd) =
      (((d : ℝ) + 1) / (2 * d * ε * ωd)) * n by ring]
    exact Real.mul_rpow hc.le (Nat.cast_nonneg n)
  have hrtop : Tendsto r atTop atTop := tendsto_radius_atTop hd1 hε hω
  filter_upwards [key, hvol] with ω hkey hcount
  obtain ⟨-, -, -, hsite, -⟩ := hkey
  have hsite' : ∀ x : Site d,
      Tendsto (fun n : ℕ => (CERW.localTime (X · ω) n x : ℝ) / r n) atTop (𝓝 (2 * d * ε)) := by
    intro x
    have h1 := (hsite x).div_const a
    rw [mul_div_cancel_right₀ _ ha.ne'] at h1
    refine Tendsto.congr (fun n => ?_) h1
    rw [hr n, div_div, mul_comm]
  have hpos : 0 < 2 * (d : ℝ) * ε := by positivity
  exact ⟨hsite', hcount, fun x => frequently_eq_of_tendsto_localTime_div hrtop hpos (hsite' x)⟩

end CERW.Support.Main.SourceIntroductionConsequences
