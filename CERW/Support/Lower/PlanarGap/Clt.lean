import CERW.Support.Lower.SharpWidth
import CERW.Generic.Martingale.CLT.Proved
import CERW.Frozen.FluctuationRates

/-!
# The first coordinate of the compensated planar position is asymptotically Gaussian

For the planar walk, `Y_n = (X_n)_1 + ε Σ_{x ∈ A_n} (u_x)_1` is a martingale with increments at most
`2` and predictable bracket between `n/2 - ε²|A_n|` and `n/2`. The proved fluctuation rates put the
departure range inside a lattice ball of radius `2 r_n`, so `|A_n| = O(r_n²) = o(n)` almost surely
and `⟨Y⟩_n / n → 1/2`. The proved martingale central limit theorem then gives
`Y_n / √n ⇒ N(0, 1/2)`; its Lindeberg condition holds because the increments are bounded.

The same file extracts, from the proved fluctuation rates, the planar radius bounds
(`planar_radii_rates`) that the width estimates of `PlanarGap.Width` use. No hypothesis about the
walk is added: every condition of the limit theorem is proved from `IsCERW`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower.PlanarGap

open CERW CERW.Support.Law CERW.Support.Lower

/-! ### The proved fluctuation rates in the plane -/

/-- The proved fluctuation rates in the plane, radii only: with probability at least
`1 - C n^{-p}` the inner radius is within `C √(r_n log n)` of `r_n` and the outer radius is at most
`r_n + C √r_n (log n)^{5/2}`; almost surely the same bounds hold for all large `n`. -/
theorem planar_radii_rates {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ)) {p : ℝ}
    (hp : 0 < p) :
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ (|innerRadius (fun j => X j ω) n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
              maxRadius (fun j => X j ω) n - r n ≤
                C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2))} ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsCERW μ ε X →
          ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
            |innerRadius (fun j => X j ω) n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
              maxRadius (fun j => X j ω) n - r n ≤
                C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)) := by
  intro r
  obtain ⟨C, hC, hprob, hae⟩ :=
    CERW.Frozen.fluctuation_rates.{u} (d := 2) le_rfl ε hε0 hεd p hp
  refine ⟨C, hC, ?_, ?_⟩
  · intro Ω _ μ _ X hX n hn
    refine le_trans (measure_mono ?_) (hprob μ X hX n hn)
    intro ω hω hgood
    have h1 := hgood.1
    rw [if_pos rfl] at h1
    exact hω h1
  · intro Ω _ μ _ X hX
    filter_upwards [hae μ X hX] with ω hω
    filter_upwards [hω] with n hgood
    have h1 := hgood.1
    rw [if_pos rfl] at h1
    exact h1

/-! ### Real-analysis lemmas on the scale `r_n` -/

/-- A constant times a fixed power of `log n` is eventually below a positive constant times any
positive power of `n`. -/
theorem eventually_mul_log_rpow_le (A b : ℝ) {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, A * Real.log n ^ b ≤ c * (n : ℝ) ^ s := by
  have hc' : 0 < c / (|A| + 1) := by positivity
  have h := (isLittleO_log_rpow_rpow_atTop b hs).def hc'
  have h2 : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ) ^ b‖ ≤ c / (|A| + 1) * ‖(n : ℝ) ^ s‖ :=
    tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog b),
    Real.norm_of_nonneg (Real.rpow_nonneg hn0 s)] at hn
  have hA : |A| / (|A| + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc A * Real.log n ^ b ≤ |A| * Real.log n ^ b :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (Real.rpow_nonneg hlog b)
    _ ≤ |A| * (c / (|A| + 1) * (n : ℝ) ^ s) := mul_le_mul_of_nonneg_left hn (abs_nonneg A)
    _ = (|A| / (|A| + 1)) * (c * (n : ℝ) ^ s) := by ring
    _ ≤ 1 * (c * (n : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_right hA (mul_nonneg hc.le (Real.rpow_nonneg hn0 s))
    _ = c * (n : ℝ) ^ s := one_mul _

/-- The square root of `n` is the cube of `n ^ (1/6)`. -/
theorem sqrt_natCast_eq_rpow_sixth_cube (n : ℕ) :
    Real.sqrt (n : ℝ) = ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-- `n ^ (1/6)` tends to infinity. -/
theorem tendsto_natCast_rpow_sixth :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp tendsto_natCast_atTop_atTop

/-- The outer-radius excess `C √r (log n)^{5/2}` is eventually at most `η r`, for `r = K q²` and
`q = n^{1/6}`. -/
theorem eventually_sqrt_mul_log_le {K : ℝ} (hK : 0 < K) (C : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, C * Real.sqrt (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) *
        Real.log n ^ ((5 : ℝ) / 2) ≤ η * (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) := by
  filter_upwards [eventually_mul_log_rpow_le (C * Real.sqrt K) ((5 : ℝ) / 2)
    (by norm_num : (0 : ℝ) < 1 / 6) (mul_pos hη hK)] with n hn
  have hq : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsq : Real.sqrt (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) =
      Real.sqrt K * (n : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_mul hK.le, Real.sqrt_sq hq]
  rw [hsq]
  calc C * (Real.sqrt K * (n : ℝ) ^ ((1 : ℝ) / 6)) * Real.log n ^ ((5 : ℝ) / 2)
      = (C * Real.sqrt K * Real.log n ^ ((5 : ℝ) / 2)) * (n : ℝ) ^ ((1 : ℝ) / 6) := by ring
    _ ≤ (η * K * (n : ℝ) ^ ((1 : ℝ) / 6)) * (n : ℝ) ^ ((1 : ℝ) / 6) :=
        mul_le_mul_of_nonneg_right hn hq
    _ = η * (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) := by ring

/-! ### The departure range is a vanishing fraction of the time -/

/-- The departure range has at most `(2 H_n + 1)²` sites, `H_n` the outer radius. -/
theorem card_departureRange_le (x : ℕ → Site 2) (n : ℕ) :
    ((departureRange x n).card : ℝ) ≤ (2 * maxRadius x n + 1) ^ 2 := by
  have hR : 0 ≤ maxRadius x n :=
    (LatticeProb.euclidNorm_nonneg (x 0)).trans (euclidNorm_le_maxRadius x (Nat.zero_le n))
  have h1 := Finset.card_le_card (CERW.Support.Occupation.departureRange_subset_ballFinset x n)
  exact (Nat.cast_le.mpr h1).trans (LatticeProb.card_ballFinset_le 2 hR)

/-- The inverse powers `(n^{1/6})^{-m}`, `m ≠ 0`, tend to zero. -/
theorem tendsto_inv_rpow_sixth_pow {m : ℕ} (hm : m ≠ 0) :
    Tendsto (fun n : ℕ => (((n : ℝ) ^ ((1 : ℝ) / 6)) ^ m)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop hm).comp tendsto_natCast_rpow_sixth)

/-- The ratio `ε² (4 r + 1)² / n` tends to zero for `r = K (n^{1/6})²`. -/
theorem tendsto_card_ratio_bound (K ε : ℝ) :
    Tendsto (fun n : ℕ => ε ^ 2 * (4 * (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) + 1) ^ 2 / n)
      atTop (𝓝 0) := by
  have hsum := (((tendsto_inv_rpow_sixth_pow two_ne_zero).const_mul (16 * K ^ 2)).add
    ((tendsto_inv_rpow_sixth_pow (by norm_num : (4 : ℕ) ≠ 0)).const_mul (8 * K))).add
    (tendsto_inv_rpow_sixth_pow (by norm_num : (6 : ℕ) ≠ 0))
  have hlim := hsum.const_mul (ε ^ 2)
  have h0 : ε ^ 2 * (16 * K ^ 2 * 0 + 8 * K * 0 + 0) = 0 := by ring
  rw [h0] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hq0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hn6 : ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  generalize (n : ℝ) ^ ((1 : ℝ) / 6) = q at hn6 hq0 ⊢
  rw [← hn6]
  field_simp
  ring

/-! ### The central limit theorem -/

/-- A predictable bracket is almost everywhere strongly measurable: it is a finite sum of
conditional expectations. -/
private theorem aestronglyMeasurable_predBracket {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (n : ℕ) :
    AEStronglyMeasurable (predBracket μ ℱ S S n) μ := by
  have h := Finset.stronglyMeasurable_sum (Finset.range n)
    (f := fun t => μ[fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω) | ℱ t])
    fun t _ => stronglyMeasurable_condExp.mono (ℱ.le t)
  exact (h.aestronglyMeasurable).congr (Filter.Eventually.of_forall fun ω => by
    simp [predBracket])

/-- A sequence of functions that is eventually identically zero tends to zero in measure. -/
private theorem tendstoInMeasure_zero_of_eventually_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} (h : ∀ᶠ n in atTop, f n = fun _ => 0) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with n hn
  symm
  have hempty : {x | ε ≤ edist (f n x) ((fun _ => (0 : ℝ)) x)} = ∅ := by
    ext x
    simp [hn, not_le.mpr hε]
  rw [hempty, measure_empty]

/-- **The coordinate martingale is asymptotically Gaussian.** In the plane, for `0 < ε < 1/2`, the
first coordinate `(X_n)_1 + ε Σ_{x ∈ A_n} (u_x)_1` of the compensated position, divided by `√n`,
converges in distribution to `N(0, 1/2)`. -/
theorem coordinate_clt {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) :
    TendstoInDistribution
      (fun n ω => (((X n ω 0 : ℤ) : ℝ) + ε * ∑ x ∈ departureRange (fun j => X j ω) n,
        (unitDir (toSpace x)) 0) / Real.sqrt n)
      atTop id (fun _ => μ) (gaussianReal 0 (1 / 2)) := by
  have hCLT : CERW.Generic.Martingale.CLT.MartingaleCLT.{u} :=
    CERW.Generic.Martingale.CLT.martingaleCLT_proved.{u}
  obtain ⟨Y, hY, hY0, hYinc, hYL2, hYform, hYbr⟩ := exists_coord_martingale hε0 hεd hX
  set ℱ := pathFiltration hX.measurable with hℱ
  set s : ℕ → ℝ := fun n => max (Real.sqrt n) 1 with hs
  have hs_pos : ∀ n, 0 < s n := fun n => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hs_top : Tendsto s atTop atTop :=
    tendsto_atTop_mono (fun n => le_max_left _ _)
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hs_sq : ∀ n : ℕ, 1 ≤ n → s n ^ 2 = n := by
    intro n hn
    have h1 : 1 ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hn
    show (max (Real.sqrt n) 1) ^ 2 = n
    rw [max_eq_left h1, Real.sq_sqrt (Nat.cast_nonneg n)]
  -- the conditional Lindeberg sums vanish: the increments are bounded by `2`
  have hlind : ∀ δ : ℝ, 0 < δ → TendstoInMeasure μ
      (fun n => ∑ i ∈ Finset.range n,
        μ[fun ω => ((Y (i + 1) ω - Y i ω) / s n) ^ 2 *
          (if δ < |Y (i + 1) ω - Y i ω| / s n then 1 else 0) | ℱ i])
      atTop (fun _ => 0) := by
    intro δ hδ
    refine tendstoInMeasure_zero_of_eventually_eq ?_
    filter_upwards [hs_top.eventually_gt_atTop (2 / δ)] with n hn
    have hzero : ∀ i, (fun ω => ((Y (i + 1) ω - Y i ω) / s n) ^ 2 *
          (if δ < |Y (i + 1) ω - Y i ω| / s n then 1 else 0)) = 0 := by
      intro i
      funext ω
      have h1 : |Y (i + 1) ω - Y i ω| / s n ≤ δ := by
        rw [div_le_iff₀ (hs_pos n)]
        have h2 := (div_lt_iff₀ hδ).1 hn
        nlinarith [hYinc i ω]
      simp [not_lt.mpr h1]
    funext ω
    simp only [hzero, condExp_zero, Finset.sum_apply, Pi.zero_apply, Finset.sum_const_zero]
  -- the bracket divided by `n` tends to `1/2` almost surely
  have hbr : TendstoInMeasure μ (fun n ω => predBracket μ ℱ Y Y n ω / s n ^ 2) atTop
      (fun _ => (((1 / 2 : ℝ≥0)) : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · simpa only [div_eq_mul_inv] using
        (aestronglyMeasurable_predBracket μ ℱ Y n).mul_const ((s n ^ 2)⁻¹)
    · obtain ⟨C, hC, -, hae⟩ := planar_radii_rates hε0 hεd (p := 1) one_pos
      have hK : 0 < (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) := by positivity
      have hev := eventually_sqrt_mul_log_le hK C one_pos
      filter_upwards [hYbr, hae μ X hX] with ω hbrω hgoodω
      have hv : (((1 / 2 : ℝ≥0)) : ℝ) = 1 / 2 := by norm_num
      rw [hv]
      have hbound : ∀ᶠ n : ℕ in atTop, |predBracket μ ℱ Y Y n ω / s n ^ 2 - 1 / 2| ≤
          ε ^ 2 * (4 * ((3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) *
            ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) + 1) ^ 2 / n := by
        filter_upwards [hgoodω, hev, eventually_ge_atTop 1] with n hgood hn hn1
        have hr : ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
            (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
            ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) =
            (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 :=
          planar_radius_eq hε0 n
        rw [hr] at hgood
        set r := (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 with hrdef
        have hM : maxRadius (fun j => X j ω) n ≤ 2 * r := by linarith [hgood.2, hn]
        have hM0 : 0 ≤ maxRadius (fun j => X j ω) n :=
          (LatticeProb.euclidNorm_nonneg (X 0 ω)).trans
            (euclidNorm_le_maxRadius (fun j => X j ω) (Nat.zero_le n))
        have hcard := card_departureRange_le (fun j => X j ω) n
        have hcard2 : ((departureRange (fun j => X j ω) n).card : ℝ) ≤ (4 * r + 1) ^ 2 := by
          refine hcard.trans ?_
          have h1 : 2 * maxRadius (fun j => X j ω) n + 1 ≤ 4 * r + 1 := by linarith
          have h2 : 0 ≤ 2 * maxRadius (fun j => X j ω) n + 1 := by linarith
          exact pow_le_pow_left₀ h2 h1 2
        obtain ⟨hup, hlow⟩ := hbrω n
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        rw [hs_sq n hn1, abs_le]
        have hdiv : ∀ t : ℝ, t / n = t * (1 / n) := fun t => by ring
        constructor
        · have h3 : predBracket μ ℱ Y Y n ω / n ≥
              ((n : ℝ) / 2 - ε ^ 2 * ((departureRange (fun j => X j ω) n).card : ℝ)) / n :=
            div_le_div_of_nonneg_right hlow hn0.le
          have h4 : ε ^ 2 * ((departureRange (fun j => X j ω) n).card : ℝ) / n ≤
              ε ^ 2 * (4 * r + 1) ^ 2 / n := by
            refine div_le_div_of_nonneg_right ?_ hn0.le
            exact mul_le_mul_of_nonneg_left hcard2 (sq_nonneg ε)
          have h5 : ((n : ℝ) / 2 - ε ^ 2 * ((departureRange (fun j => X j ω) n).card : ℝ)) / n =
              1 / 2 - ε ^ 2 * ((departureRange (fun j => X j ω) n).card : ℝ) / n := by
            field_simp
          linarith
        · have h3 : predBracket μ ℱ Y Y n ω / n ≤ ((n : ℝ) / 2) / n :=
            div_le_div_of_nonneg_right hup hn0.le
          have h5 : ((n : ℝ) / 2) / n = 1 / 2 := by field_simp
          have h6 : 0 ≤ ε ^ 2 * (4 * r + 1) ^ 2 / n := by positivity
          linarith
      have hg := tendsto_card_ratio_bound ((3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3)) ε
      have hz : Tendsto (fun n : ℕ => predBracket μ ℱ Y Y n ω / s n ^ 2 - 1 / 2) atTop (𝓝 0) :=
        squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hbound) hg
      have h2 : Tendsto (fun n : ℕ => predBracket μ ℱ Y Y n ω / s n ^ 2) atTop
          (𝓝 (0 + 1 / 2)) := (hz.add_const (1 / 2)).congr (fun n => by ring)
      rwa [zero_add] at h2
  have hX2 := hCLT μ ℱ Y hY hYL2 hY0 s hs_pos (1 / 2) hlind hbr
  refine hX2.congr (fun n => ?_) Filter.EventuallyEq.rfl
  filter_upwards [hYform] with ω hω
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hs, hY0 ω]
  · have h1 : 1 ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hn
    show Y n ω / s n = _
    rw [hω n, hs]
    simp only [max_eq_left h1]

end CERW.Support.Lower.PlanarGap
