import CERW.Support.Statements
import CERW.Support.Contact.Quadratic
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import CERW.Support.Occupation.FreshSum
import CERW.Support.Occupation.Facts
import CERW.Generic.Kernel.RadialPacking
import CERW.Support.Main.ScaleLimits
import CERW.Support.Limit.MomentCommon

/-!
# The limit laws for the sum of the distances from the origin

`CERW.Support.Limit.moment_fluctuations_of` proves Theorem 8.1 of the paper (the central limit
theorem and the law of the iterated logarithm for `Σ_{x ∈ A_n} |x|` and for the moment radius),
from the limit shape and fluctuation theorems and the cited martingale limit theorems.

The proof follows the paper. The Dynkin martingale `𝒬` of `|x|²` equals
`2ε Σ_{x ∈ A_n} |x| - n + |X_n|²`. Its bracket is
`(4/d) Σ_{t<n} |X_t|² - 4ε² Σ_{first departures} |X_t|²`, which is asymptotic to `r_n^{d+3}` times
an explicit constant by comparing the local times with the limit profile and a lattice sum with its
integral. The cited central limit theorem and law of the iterated logarithm apply to `𝒬`, and the
sum and the moment radius follow by a perturbation argument and a delta-method argument.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Limit

open CERW.Support.Statements

open LatticeProb CERW CERW.Support.Occupation CERW.Support.Law CERW.Support.Contact

/-- The profile is nonnegative. -/
private theorem tentSq_nonneg (r t : ℝ) : 0 ≤ tentSq r t :=
  mul_nonneg (le_max_right _ _) (sq_nonneg t)

/-- The bracket of a martingale is almost everywhere strongly measurable. -/
private theorem aestronglyMeasurable_predBracket {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (n : ℕ) :
    AEStronglyMeasurable (predBracket μ ℱ M M n) μ := by
  unfold predBracket
  refine Finset.aestronglyMeasurable_sum _ fun t _ => ?_
  exact ((stronglyMeasurable_condExp (m := ℱ t)).mono (ℱ.le t)).aestronglyMeasurable

/-- The conditional Lindeberg sum tends to zero in measure when the increment bounds are
predictable and eventually negligible against the normalization. -/
private theorem tendstoInMeasure_lindeberg {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ)
    (hL2 : ∀ n, MemLp (M n) 2 μ)
    (B : ℕ → Ω → ℝ) (hBm : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)))
    (hBb : ∀ᵐ ω ∂μ, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω)
    (hBbd : ∀ n, ∃ C, ∀ᵐ ω ∂μ, |B n ω| ≤ C)
    {s : ℕ → ℝ} (hs : ∀ n, 0 < s n)
    (hBmax : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i < n, B (i + 1) ω ≤ δ * s n)
    (δ : ℝ) (hδ : 0 < δ) :
    TendstoInMeasure μ
      (fun n => ∑ i ∈ Finset.range n,
        μ[fun ω => ((M (i + 1) ω - M i ω) / s n) ^ 2 *
          (if δ < |M (i + 1) ω - M i ω| / s n then 1 else 0) | ℱ i])
      atTop (fun _ => 0) := by
  set g : ℕ → ℕ → Ω → ℝ := fun n i ω => ((M (i + 1) ω - M i ω) / s n) ^ 2 *
    (if δ < |M (i + 1) ω - M i ω| / s n then 1 else 0) with hg
  set Φ : ℕ → ℝ → ℝ := fun n x => (x / s n) ^ 2 * (if δ * s n < x then 1 else 0) with hΦ
  have hΦm : ∀ n, Measurable (Φ n) := fun n => by
    simp only [hΦ]
    exact (measurable_id.div_const _).pow_const 2 |>.mul
      (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
  have hΦnn : ∀ n x, 0 ≤ Φ n x := fun n x => by
    simp only [hΦ]
    split_ifs
    · positivity
    · simp
  -- pointwise bound of the truncated square by the predictable quantity
  have hgk : ∀ n i, ∀ᵐ ω ∂μ, g n i ω ≤ Φ n (B (i + 1) ω) := by
    intro n i
    filter_upwards [hBb] with ω hω
    have hb := hω i
    by_cases hc : δ < |M (i + 1) ω - M i ω| / s n
    · have hc' : δ * s n < B (i + 1) ω := by
        have := (lt_div_iff₀ (hs n)).1 hc
        linarith
      have habs : (M (i + 1) ω - M i ω) ^ 2 ≤ B (i + 1) ω ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      simp only [hg, hΦ]
      rw [if_pos hc, if_pos hc', mul_one, mul_one, div_pow, div_pow]
      exact div_le_div_of_nonneg_right habs (sq_nonneg _)
    · have h0 : g n i ω = 0 := by
        simp only [hg]
        rw [if_neg hc, mul_zero]
      rw [h0]
      exact hΦnn n _
  have hψm : ∀ n, Measurable (fun x : ℝ => if δ < |x| / s n then (1 : ℝ) else 0) := fun n =>
    Measurable.ite (measurableSet_lt measurable_const (measurable_id.abs.div_const _))
      measurable_const measurable_const
  have hgint : ∀ n i, Integrable (g n i) μ := by
    intro n i
    have hΔ : MemLp (fun ω => M (i + 1) ω - M i ω) 2 μ := (hL2 (i + 1)).sub (hL2 i)
    have hsq : Integrable (fun ω => ((M (i + 1) ω - M i ω) / s n) ^ 2) μ := by
      simp_rw [div_pow]
      exact hΔ.integrable_sq.div_const _
    refine hsq.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun ω => ((M (i + 1) ω - M i ω) / s n) ^ 2) μ :=
        hsq.aestronglyMeasurable
      have h2 : AEStronglyMeasurable
          (fun ω => if δ < |M (i + 1) ω - M i ω| / s n then (1 : ℝ) else 0) μ :=
        ((hψm n).comp_aemeasurable hΔ.aemeasurable).aestronglyMeasurable
      exact h1.mul h2
    · refine Filter.Eventually.of_forall fun ω => ?_
      simp only [hg]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      have : |if δ < |M (i + 1) ω - M i ω| / s n then (1 : ℝ) else 0| ≤ 1 := by
        split_ifs <;> simp
      calc ((M (i + 1) ω - M i ω) / s n) ^ 2 *
            |if δ < |M (i + 1) ω - M i ω| / s n then (1 : ℝ) else 0|
          ≤ ((M (i + 1) ω - M i ω) / s n) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = ((M (i + 1) ω - M i ω) / s n) ^ 2 := mul_one _
  have hkmeas : ∀ n i, StronglyMeasurable[ℱ i] (fun ω => Φ n (B (i + 1) ω)) := fun n i =>
    ((hΦm n).comp (hBm i).measurable).stronglyMeasurable
  have hkint : ∀ n i, Integrable (fun ω => Φ n (B (i + 1) ω)) μ := by
    intro n i
    obtain ⟨C, hC⟩ := hBbd (i + 1)
    refine Integrable.of_bound ((hkmeas n i).mono (ℱ.le i)).aestronglyMeasurable ((C / s n) ^ 2) ?_
    filter_upwards [hC] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hΦnn n _)]
    have h1 : Φ n (B (i + 1) ω) ≤ (B (i + 1) ω / s n) ^ 2 := by
      simp only [hΦ]
      split_ifs
      · rw [mul_one]
      · rw [mul_zero]
        exact sq_nonneg _
    refine h1.trans ?_
    rw [← sq_abs, abs_div, abs_of_pos (hs n)]
    exact pow_le_pow_left₀ (div_nonneg (abs_nonneg _) (hs n).le)
      (div_le_div_of_nonneg_right hω (hs n).le) 2
  have hcond : ∀ n i, μ[g n i | ℱ i] ≤ᵐ[μ] fun ω => Φ n (B (i + 1) ω) := by
    intro n i
    have h1 := condExp_mono (m := ℱ i) (hgint n i) (hkint n i) (hgk n i)
    have h2 := condExp_of_stronglyMeasurable (ℱ.le i) (hkmeas n i) (hkint n i)
    rw [h2] at h1
    exact h1
  have hg0 : ∀ n i ω, 0 ≤ g n i ω := fun n i ω => by
    simp only [hg]
    split_ifs
    · positivity
    · simp
  have hnn : ∀ n i, 0 ≤ᵐ[μ] μ[g n i | ℱ i] := fun n i =>
    condExp_nonneg (Filter.Eventually.of_forall (hg0 n i))
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
  · exact Finset.aestronglyMeasurable_sum _ fun i _ =>
      ((stronglyMeasurable_condExp (m := ℱ i)).mono (ℱ.le i)).aestronglyMeasurable
  · have hall : ∀ᵐ ω ∂μ, ∀ n i, 0 ≤ μ[g n i | ℱ i] ω ∧
        μ[g n i | ℱ i] ω ≤ Φ n (B (i + 1) ω) :=
      ae_all_iff.2 fun n => ae_all_iff.2 fun i => by
        filter_upwards [hnn n i, hcond n i] with ω h1 h2 using ⟨h1, h2⟩
    filter_upwards [hall, hBmax] with ω hω hBω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hBω δ hδ] with n hn
    simp only [Finset.sum_apply]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    have hi' := Finset.mem_range.1 hi
    have h1 := (hω n i).2
    have h2 := (hω n i).1
    have h3 : Φ n (B (i + 1) ω) = 0 := by
      simp only [hΦ]
      rw [if_neg (not_lt.2 (hn i hi')), mul_zero]
    linarith


/-- The central limit theorem for a martingale with predictable increment bounds that are
eventually negligible against the normalization, and whose bracket over `s_n²` tends to `V`
almost surely. -/
private theorem clt_normalized (hCLT : MartingaleCLT.{u}) {Ω : Type u}
    [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ μ) (hL2 : ∀ n, MemLp (M n) 2 μ)
    (hM0 : ∀ ω, M 0 ω = 0) (B : ℕ → Ω → ℝ) (hBm : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)))
    (hBb : ∀ᵐ ω ∂μ, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω)
    (hBbd : ∀ n, ∃ C, ∀ᵐ ω ∂μ, |B n ω| ≤ C) {s : ℕ → ℝ} (hs : ∀ n, 0 < s n) {V : ℝ}
    (hV : 0 ≤ V)
    (hBmax : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i < n, B (i + 1) ω ≤ δ * s n)
    (hbr : ∀ᵐ ω ∂μ,
      Tendsto (fun n => predBracket μ ℱ M M n ω / s n ^ 2) atTop (𝓝 V)) :
    TendstoInDistribution (fun n ω => M n ω / s n) atTop id (fun _ => μ)
      (gaussianReal 0 V.toNNReal) := by
  have hbrm : TendstoInMeasure μ (fun n => fun ω => predBracket μ ℱ M M n ω / s n ^ 2) atTop
      (fun _ => ((V.toNNReal : ℝ≥0) : ℝ)) := by
    rw [Real.coe_toNNReal V hV]
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) hbr
    simpa only [div_eq_mul_inv] using
      (aestronglyMeasurable_predBracket μ ℱ M n).mul_const ((s n ^ 2)⁻¹)
  exact hCLT μ ℱ M hM hL2 hM0 s hs V.toNNReal
    (fun δ hδ => tendstoInMeasure_lindeberg μ ℱ M hL2 B hBm hBb hBbd hs hBmax δ hδ) hbrm

/-- For `d ≥ 2`, `r_n / s_n → 0`. -/
private theorem tendsto_scale_div {d : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :
    Tendsto (fun n => r n / norming d r n) atTop (𝓝 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_
    (tendsto_scale_sq_div hd ha hr)
  · exact div_nonneg (by rw [hr n]; positivity) (norming_pos ha hr n).le
  · filter_upwards [(tendsto_scale_atTop ha hr).eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_right (by nlinarith) (norming_pos ha hr n).le

/-- A function of the departure range at time `n` is measurable. -/
private theorem measurable_departureRange_fun {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (n : ℕ) (G : Finset (Site d) → ℝ) :
    Measurable (fun ω => G (departureRange (fun j => X j ω) n)) := by
  have h : (fun ω => G (departureRange (fun j => X j ω) n)) =
      fun ω => (fun p : (i : Finset.Iic n) → Site d =>
        G ((Finset.range n).image (extendPath p))) (pastPath X n ω) := by
    funext ω
    congr 1
    unfold departureRange
    refine Finset.image_congr fun j hj => ?_
    exact (extendPath_pastPath X (Nat.le_of_lt (Finset.mem_range.1 hj)) ω).symm
  rw [h]
  exact (measurable_of_countable (fun p : (i : Finset.Iic n) → Site d =>
    G ((Finset.range n).image (extendPath p)))).comp (measurable_pastPath hX n)

/-- The central limit theorem and the law of the iterated logarithm for the Dynkin martingale of
`|x|²`, normalized by `r_n^{(d+3)/2}`. -/
private theorem dynkin_sq_laws {d : ℕ} (hd : 2 ≤ d) (hCLT : MartingaleCLT.{u})
    (hLIL : StoutLIL.{u}) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d)
    (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hloc : ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ y : Site d,
      |(localTime (fun j => X j ω) n y : ℝ) - 2 * d * ε * max (r n - euclidNorm y) 0|
        ≤ η * r n)
    (hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n) :
    TendstoInDistribution
      (fun n ω => dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n) atTop id
      (fun _ => μ) (gaussianReal 0 (bracketLimit d ε).toNNReal) ∧
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
      (∀ᶠ n : ℕ in atTop,
        σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n
          ≤ (Real.sqrt (bracketLimit d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop,
        (Real.sqrt (bracketLimit d ε) - δ) * Real.sqrt (2 * Real.log (Real.log n))
          ≤ σ * dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n) := by
  have hd1 : 1 ≤ d := by omega
  have hε0 : 0 ≤ ε := hε.le
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hVpos : 0 < bracketLimit d ε := by
    unfold bracketLimit
    positivity
  set ℱ := pathFiltration hX.measurable with hℱ
  set Q : ℕ → Ω → ℝ := dynkin ε (fun z : Site d => euclidNorm z ^ 2) X with hQ
  have hmart : Martingale Q ℱ μ := martingale_dynkin hd1 hε0 hεd hX _
  have hL2 : ∀ n, MemLp (Q n) 2 μ := memLp_dynkin_sq hd1 hε0 hεd hX
  have hQ0 : ∀ ω, Q 0 ω = 0 := fun ω => dynkin_zero ε _ X ω
  set B : ℕ → Ω → ℝ := fun n ω => 4 * euclidNorm (X (n - 1) ω) + 2 with hB
  have hB0 : ∀ n ω, 0 ≤ B n ω := fun n ω => by
    have := euclidNorm_nonneg (X (n - 1) ω)
    simp only [hB]
    linarith
  have hBm : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)) := fun n =>
    stronglyMeasurable_comp_pastPath hX.measurable n
      (fun p : (i : Finset.Iic n) → Site d =>
        4 * euclidNorm (p ⟨n, Finset.mem_Iic.2 le_rfl⟩) + 2)
  have hBb : ∀ᵐ ω ∂μ, ∀ n, |Q (n + 1) ω - Q n ω| ≤ B (n + 1) ω :=
    ae_abs_dynkin_sq_succ_sub_le hd1 hε0 hεd hX
  have hBbd : ∀ n, ∃ C, ∀ᵐ ω ∂μ, |B n ω| ≤ C := by
    intro n
    refine ⟨4 * n + 2, ?_⟩
    filter_upwards [ae_euclidNorm_le hd1 hε0 hεd hX] with ω hω'
    have h1 : euclidNorm (X (n - 1) ω) ≤ n := (hω' (n - 1)).trans (by exact_mod_cast Nat.sub_le n 1)
    have h2 := euclidNorm_nonneg (X (n - 1) ω)
    rw [abs_of_nonneg (hB0 n ω)]
    simp only [hB]
    linarith
  have hs := norming_pos ha hr
  have hs' := tendsto_norming_atTop ha hr
  have hrtend := tendsto_scale_atTop ha hr
  have hbr : ∀ᵐ ω ∂μ, Tendsto (fun n => predBracket μ ℱ Q Q n ω / norming d r n ^ 2) atTop
      (𝓝 (bracketLimit d ε)) := by
    filter_upwards [ae_predBracket_dynkin_sq hd1 hε0 hεd hX, hloc, hmax] with ω hbrω hlocω hmaxω
    have := tendsto_bracket_quotient hd1 hε hrtend (fun j => X j ω) hlocω hmaxω
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [hbrω n, norming_sq ha hr hn]
  have hBmax : ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i < n,
      B (i + 1) ω ≤ δ * norming d r n := by
    filter_upwards [hmax] with ω hmaxω δ hδ
    filter_upwards [hmaxω, (tendsto_scale_div hd ha hr).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 10)), hrtend.eventually_ge_atTop 1]
      with n h1 h2 h3 i hi
    have hsn := hs n
    have hX1 : euclidNorm (X i ω) ≤ maxRadius (fun j => X j ω) n :=
      euclidNorm_le_maxRadius (fun j => X j ω) hi.le
    have h4 : r n < δ / 10 * norming d r n := (div_lt_iff₀ hsn).1 h2
    show 4 * euclidNorm (X (i + 1 - 1) ω) + 2 ≤ δ * norming d r n
    rw [Nat.add_sub_cancel]
    linarith
  have hBs : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω ^ 2 / norming d r n) atTop (𝓝 0) := by
    filter_upwards [hmax] with ω hmaxω
    have hlim : Tendsto (fun n => 100 * (r n ^ 2 / norming d r n)) atTop (𝓝 0) := by
      simpa using (tendsto_scale_sq_div hd ha hr).const_mul 100
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_ hlim
    · exact div_nonneg (sq_nonneg _) (hs n).le
    · filter_upwards [hmaxω, hrtend.eventually_ge_atTop 1] with n h1 h2
      have hX1 : euclidNorm (X (n - 1) ω) ≤ maxRadius (fun j => X j ω) n :=
        euclidNorm_le_maxRadius (fun j => X j ω) (Nat.sub_le n 1)
      have hBn : B n ω ≤ 10 * r n := by
        simp only [hB]
        linarith
      have hsn := hs n
      calc B n ω ^ 2 / norming d r n ≤ (10 * r n) ^ 2 / norming d r n :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ (hB0 n ω) hBn 2) hsn.le
        _ = 100 * (r n ^ 2 / norming d r n) := by ring
  refine ⟨clt_normalized hCLT μ ℱ Q hmart hL2 hQ0 B hBm hBb hBbd hs hVpos.le hBmax hbr, ?_⟩
  have hκ : 0 < ((d : ℝ) + 3) / ((d : ℝ) + 1) := by positivity
  have hlog := tendsto_log_norming_sq ha hr
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      (∀ᶠ n : ℕ in atTop, σ * Q n ω / norming d r n
        ≤ (Real.sqrt (bracketLimit d ε) + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
      (∃ᶠ n : ℕ in atTop, (Real.sqrt (bracketLimit d ε) - δ) *
        Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * Q n ω / norming d r n) := by
    intro σ hσ
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    set M : ℕ → Ω → ℝ := fun n ω => σ * Q n ω with hM
    have hMmart : Martingale M ℱ μ := hmart.smul σ
    have hML2 : ∀ n, MemLp (M n) 2 μ := fun n => (hL2 n).const_mul σ
    have hM0 : ∀ ω, M 0 ω = 0 := fun ω => by simp [hM, hQ0]
    have hMBb : ∀ᵐ ω ∂μ, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω := by
      filter_upwards [hBb] with ω h n
      have : M (n + 1) ω - M n ω = σ * (Q (n + 1) ω - Q n ω) := by simp only [hM]; ring
      rw [this, abs_mul, hσabs, one_mul]
      exact h n
    have hbrM : ∀ n, predBracket μ ℱ M M n = predBracket μ ℱ Q Q n := by
      intro n
      unfold predBracket
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 1
      funext ω
      have h1 : (M (t + 1) ω - M t ω) * (M (t + 1) ω - M t ω)
          = (σ * σ) * ((Q (t + 1) ω - Q t ω) * (Q (t + 1) ω - Q t ω)) := by
        simp only [hM]
        ring
      rw [h1, hσ2, one_mul]
    have hMbr : ∀ᵐ ω ∂μ, Tendsto (fun n => predBracket μ ℱ M M n ω / norming d r n ^ 2)
        atTop (𝓝 (bracketLimit d ε)) := by
      filter_upwards [hbr] with ω h
      simpa only [hbrM] using h
    exact lil_normalized hLIL μ ℱ M hMmart hML2 hM0 B hB0 hBm hMBb hs hs' hVpos hκ hMbr hBs hlog
  filter_upwards [key 1 (Or.inl rfl), key (-1) (Or.inr rfl)] with ω h1 h2 δ hδ σ hσ
  rcases hσ with rfl | rfl
  · exact h1 δ hδ
  · exact h2 δ hδ

/-- Convergence in distribution to a variable with the same law. -/
private theorem tendstoInDistribution_of_map_eq {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace Ω''] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {ν : Measure Ω''} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {W : Ω'' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => μ) μ') (hW : AEMeasurable W ν)
    (hmap : μ'.map Z = ν.map W) : TendstoInDistribution X atTop W (fun _ => μ) ν := by
  refine ⟨h.forall_aemeasurable, hW, ?_⟩
  have e : (⟨ν.map W, Measure.isProbabilityMeasure_map hW⟩ : ProbabilityMeasure ℝ) =
      ⟨μ'.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩ :=
    Subtype.ext hmap.symm
  rw [e]
  exact h.tendsto

/-- Dividing a centered Gaussian by a constant `c` divides its variance by `c²`. -/
private theorem gaussianReal_map_div_toNNReal {V c : ℝ} (hV : 0 ≤ V) :
    (gaussianReal 0 V.toNNReal).map (· / c) = gaussianReal 0 (V / c ^ 2).toNNReal := by
  rw [gaussianReal_map_div_const, zero_div]
  congr 1
  apply NNReal.eq
  have : 0 ≤ V / c ^ 2 := div_nonneg hV (sq_nonneg c)
  rw [NNReal.coe_div, Real.coe_toNNReal _ this, Real.coe_toNNReal _ hV]
  rfl

/-- Multiplying a centered Gaussian by a constant `c` multiplies its variance by `c²`. -/
private theorem gaussianReal_map_mul_toNNReal {V : ℝ} (c : ℝ) (hV : 0 ≤ V) :
    (gaussianReal 0 V.toNNReal).map (c * ·) = gaussianReal 0 (c ^ 2 * V).toNNReal := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  have : 0 ≤ c ^ 2 * V := mul_nonneg (sq_nonneg c) hV
  rw [NNReal.coe_mul, Real.coe_toNNReal _ this, Real.coe_toNNReal _ hV]
  rfl

/-- The central limit theorem for the sum of the distances from the origin. -/
private theorem sum_clt {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n)
    (hQ1 : TendstoInDistribution
      (fun n ω => dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n) atTop id
      (fun _ => μ) (gaussianReal 0 (bracketLimit d ε).toNNReal)) :
    TendstoInDistribution
      (fun n ω => (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
        r n ^ (((d : ℝ) + 3) / 2)) atTop id (fun _ => μ)
      (gaussianReal 0 (sumVariance d ε).toNNReal) := by
  have hd1 : 1 ≤ d := by omega
  have hVpos := bracketLimit_pos hd1 hε
  have hT := hQ1.continuous_comp (g := fun x : ℝ => x / (2 * ε)) (by fun_prop)
  have hT' : TendstoInDistribution
      (fun n ω => (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n)
        / (2 * ε)) atTop id (fun _ => μ) (gaussianReal 0 (sumVariance d ε).toNNReal) := by
    refine tendstoInDistribution_of_map_eq hT measurable_id.aemeasurable ?_
    rw [sumVariance_eq d hε]
    simp only [Function.comp_def, id, Measure.map_id]
    exact gaussianReal_map_div_toNNReal hVpos.le
  have hX0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  have hSmeas : ∀ n, Measurable (fun ω => (∑ x ∈ departureRange (fun j => X j ω) n,
      euclidNorm x - n / (2 * ε)) / r n ^ (((d : ℝ) + 3) / 2)) := fun n =>
    measurable_departureRange_fun hX.measurable n
      (fun A => (∑ x ∈ A, euclidNorm x - n / (2 * ε)) / r n ^ (((d : ℝ) + 3) / 2))
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hT' ?_
    (fun n => (hSmeas n).aemeasurable)
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
  · exact (((hSmeas n).aemeasurable).sub ((hT'.forall_aemeasurable n))).aestronglyMeasurable
  · filter_upwards [hX0, hmax] with ω h0 hm
    have hlim : Tendsto (fun n => 2 / ε * (r n ^ 2 / norming d r n)) atTop (𝓝 0) := by
      simpa using (tendsto_scale_sq_div hd ha hr).const_mul (2 / ε)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hm, eventually_ne_atTop 0] with n hn hn0
    have hs := norming_pos ha hr n
    have hDeq : r n ^ (((d : ℝ) + 3) / 2) = norming d r n := by
      simp only [norming, if_neg hn0]
    have hXn : euclidNorm (X n ω) ≤ 2 * r n :=
      (euclidNorm_le_maxRadius (fun j => X j ω) le_rfl).trans hn
    have hXn0 := euclidNorm_nonneg (X n ω)
    simp only [Pi.sub_apply]
    rw [sum_sub_eq_dynkin hd1 hε X ω h0 n, hDeq, Real.norm_eq_abs]
    have h1 : (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n
          - euclidNorm (X n ω) ^ 2 / norming d r n) / (2 * ε)
        - dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω / norming d r n / (2 * ε)
        = -(euclidNorm (X n ω) ^ 2 / norming d r n / (2 * ε)) := by ring
    rw [h1, abs_neg, abs_of_nonneg (by positivity)]
    have h2 : euclidNorm (X n ω) ^ 2 ≤ (2 * r n) ^ 2 := pow_le_pow_left₀ hXn0 hXn 2
    calc euclidNorm (X n ω) ^ 2 / norming d r n / (2 * ε)
        ≤ (2 * r n) ^ 2 / norming d r n / (2 * ε) := by gcongr
      _ = 2 / ε * (r n ^ 2 / norming d r n) := by
          field_simp

/-- The central limit theorem for the moment radius. -/
private theorem radius_clt {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → Site d)
    (hX : IsCERW μ ε X) {a : ℝ} (ha : 0 < a) {r : ℕ → ℝ}
    (hr : ∀ n, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
    (hrpow : ∀ n, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d))
    (hS : TendstoInDistribution
      (fun n ω => (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
        r n ^ (((d : ℝ) + 3) / 2)) atTop id (fun _ => μ)
      (gaussianReal 0 (sumVariance d ε).toNNReal))
    (hA : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      radiusFactor d (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n)) atTop
      (𝓝 (1 / (d * unitBallVolume d)))) :
    TendstoInDistribution
      (fun n ω => (momentRadius (fun j => X j ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2)) atTop id
      (fun _ => μ) (gaussianReal 0 (radiusVariance d ε).toNNReal) := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω := unitBallVolume_pos d
  have hAmeas : ∀ n, Measurable (fun ω => radiusFactor d
      (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n)) := fun n =>
    measurable_departureRange_fun hX.measurable n
      (fun A => radiusFactor d (∑ x ∈ A, euclidNorm x) (r n))
  have hRmeas : ∀ n, Measurable (fun ω =>
      (momentRadius (fun j => X j ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2)) := fun n =>
    measurable_departureRange_fun hX.measurable n
      (fun A => ((((d : ℝ) + 1) / (d * unitBallVolume d) * ∑ x ∈ A, euclidNorm x) ^
        ((1 : ℝ) / (d + 1)) - r n) / r n ^ ((3 - (d : ℝ)) / 2))
  have hAm : TendstoInMeasure μ (fun n ω => radiusFactor d
      (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n)) atTop
      (fun _ => 1 / (d * unitBallVolume d)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hAmeas n).aestronglyMeasurable) hA
  have hSl := hS.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) hAm (fun n => (hAmeas n).aemeasurable)
  have hv : 0 ≤ sumVariance d ε := by
    unfold sumVariance
    positivity
  have hT : TendstoInDistribution (fun n ω => radiusFactor d
        (∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (r n) *
      ((∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x - n / (2 * ε)) /
        r n ^ (((d : ℝ) + 3) / 2))) atTop id (fun _ => μ)
      (gaussianReal 0 (radiusVariance d ε).toNNReal) := by
    refine tendstoInDistribution_of_map_eq hSl measurable_id.aemeasurable ?_
    have h1 := gaussianReal_map_mul_toNNReal (1 / ((d : ℝ) * unitBallVolume d)) hv
    rw [radiusVariance_eq hd1 hε]
    simp only [Measure.map_id]
    convert h1 using 2
    · funext x
      simp [mul_comm]
    · congr 1
      field_simp
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hT ?_
    (fun n => (hRmeas n).aemeasurable)
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
  · exact ((hRmeas n).aemeasurable.sub (hT.forall_aemeasurable n)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Pi.sub_apply]
    rw [momentRadius_eq_factor_mul hd1 hε ha hr hrpow (fun j => X j ω) n hn, sub_self]
    rfl

/-- Theorem 8.1 of the paper: the central limit theorem and the law of the iterated logarithm for
the sum of the distances from the origin over the range and for the moment radius. -/
theorem moment_fluctuations_of (hshape : limit_shape.{u})
    (hfluct : fluctuation_rates.{u}) : moment_fluctuations.{u} := by
  intro d hd hCLT hLIL ωd ε hε hεd r v₁ v₂ Ω _ μ _ X hX S R
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hω : 0 < ωd := unitBallVolume_pos d
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * ωd) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hr : ∀ n : ℕ, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    show (((d : ℝ) + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) = _
    rw [show ((d : ℝ) + 1) * n / (2 * d * ε * ωd) =
      (((d : ℝ) + 1) / (2 * d * ε * ωd)) * n by ring]
    exact Real.mul_rpow hc.le (Nat.cast_nonneg n)
  have hrdef : ∀ n : ℕ, r n =
      ((d + 1) * n / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)) := fun n => rfl
  have hrpow : ∀ n : ℕ, r n ^ (d + 1) = (d + 1) * n / (2 * d * ε * unitBallVolume d) :=
    fun n => by
    rw [hrdef n, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : ((1 : ℝ) / (d + 1)) * ((d + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  have hsh := hshape hd hε hεd μ X hX
  have hloc : ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ y : Site d,
      |(localTime (fun j => X j ω) n y : ℝ) - 2 * d * ε * max (r n - euclidNorm y) 0|
        ≤ η * r n := by
    filter_upwards [hsh] with ω h using h.2.1
  have hmax : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, maxRadius (fun j => X j ω) n ≤ 2 * r n := by
    obtain ⟨C, hC, -, hae⟩ := hfluct hd ε hε hεd 1 one_pos
    filter_upwards [hae μ X hX] with ω hω
    filter_upwards [hω, eventually_excess_le hd ha hr hC] with n hn hle
    have hex : maxRadius (fun j => X j ω) n - r n ≤ (if d = 2 then
        C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        else C * Real.log n ^ ((d : ℝ) + 1)) := by
      have h1 := hn.1
      by_cases h2 : d = 2
      · rw [if_pos h2] at h1 ⊢
        exact h1.2
      · rw [if_neg h2] at h1 ⊢
        exact h1.2
    linarith
  obtain ⟨hQ1, hQ2⟩ := dynkin_sq_laws hd hCLT hLIL hε hεd μ X hX ha hr hloc hmax
  have hSclt := sum_clt hd hε μ X hX ha hr hmax hQ1
  have hSlil := sum_lil hd hε μ X hX ha hr hmax hQ2
  have hAx := ae_tendsto_radiusFactor hd hε μ X hX ha hr hrdef hrpow hmax hQ2
  have hRclt := radius_clt hd hε μ X hX ha hr hrpow hSclt hAx
  have hRlil := radius_lil hd hε μ X ha hr hrpow hSlil hAx
  refine ⟨hSclt, hRclt, ?_⟩
  filter_upwards [hSlil, hRlil] with ω h1 h2 δ hδ σ hσ
  exact ⟨(h1 δ hδ σ hσ).1, (h1 δ hδ σ hσ).2, (h2 δ hδ σ hσ).1, (h2 δ hδ σ hσ).2⟩

end CERW.Support.Limit
