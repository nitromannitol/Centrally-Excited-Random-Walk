import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic

/-!
# Conditional Hoeffding bounds for bounded martingale differences

This supplies the conditional sub-Gaussian input to the Azuma estimate in the proof of
Proposition 9.4 (`prop:log-lower`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace CERW.LimitShapes.LogLower

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded, conditionally centred variable satisfies conditional Hoeffding. -/
theorem hasCondSubgaussianMGF_of_bounded
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X : Ω → ℝ}
    (hX : Measurable[mΩ] X) {b : ℝ} (_hb : 0 ≤ b)
    (hbound : ∀ ω, |X ω| ≤ b) (hmean : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - -b‖₊ / 2) ^ 2) μ := by
  letI : MeasurableSpace Ω := mΩ
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-b) b :=
    Eventually.of_forall fun ω => abs_le.mp (hbound ω)
  have hint : Integrable X μ := Integrable.of_mem_Icc (-b) b hX.aemeasurable hIcc
  have hmean' : μ[X | m] =ᵐ[μ.trim hm] 0 :=
    ((stronglyMeasurable_condExp).ae_eq_trim_iff hm stronglyMeasurable_zero).2 hmean
  have hkernel : ∀ᵐ ω ∂(μ.trim hm), ∀ᵐ y ∂(condExpKernel μ m ω),
      X y ∈ Set.Icc (-b) b := by
    apply Measure.ae_ae_of_ae_comp
    simpa only [condExpKernel_comp_trim hm] using hIcc
  have hcent := condExp_ae_eq_trim_integral_condExpKernel hm hint
  change Kernel.HasSubgaussianMGF X _ (condExpKernel μ m) (μ.trim hm)
  constructor
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hX.aemeasurable hIcc
  · filter_upwards [hkernel, hcent, hmean'] with ω hω hc hz
    have hzero : ∫ y, X y ∂condExpKernel μ m ω = 0 := hc.symm.trans hz
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hX.aemeasurable hω hzero).mgf_le

/-- Azuma's lower tail for a martingale with surely bounded increments. -/
theorem martingale_lower_tail
    {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hzero : ∀ ω, M 0 ω = 0) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ j ω, |M (j + 1) ω - M j ω| ≤ b)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    μ.real {ω | M n ω ≤ -t} ≤ Real.exp (-(t ^ 2 / (2 * n * b ^ 2))) := by
  let Y : ℕ → Ω → ℝ := fun j ω => M j ω - M (j + 1) ω
  let G : Filtration ℕ mΩ :=
    ⟨fun j => ℱ (j + 1), fun i j hij => ℱ.mono (by omega), fun j => ℱ.le (j + 1)⟩
  let c : ℝ≥0 := (‖b - -b‖₊ / 2) ^ 2
  have hYbound (j : ℕ) (ω : Ω) : |Y j ω| ≤ b := by
    simpa only [Y, abs_sub_comm] using hbound j ω
  have hYmeas (j : ℕ) : Measurable (Y j) :=
    (((hM.stronglyMeasurable j).mono (ℱ.le j)).sub
      ((hM.stronglyMeasurable (j + 1)).mono (ℱ.le (j + 1)))).measurable
  have hcent (j : ℕ) : μ[Y j | ℱ j] =ᵐ[μ] 0 := by
    have hs := condExp_sub (hM.integrable j) (hM.integrable (j + 1)) (ℱ j)
    have hn := hM.condExp_ae_eq (Nat.le_succ j)
    have hnow := condExp_of_stronglyMeasurable (ℱ.le j)
      (hM.stronglyMeasurable j) (hM.integrable j)
    filter_upwards [hs, hn] with ω hs hn
    change μ[M j - M (j + 1) | ℱ j] ω = 0
    rw [hs, Pi.sub_apply, hnow, hn, sub_self]
  have hcond (j : ℕ) : HasCondSubgaussianMGF (ℱ j) (ℱ.le j) (Y j) c μ :=
    hasCondSubgaussianMGF_of_bounded (ℱ.le j) (hYmeas j) hb (hYbound j) (hcent j)
  have hYzero : ∫ ω, Y 0 ω ∂μ = 0 := by
    rw [← integral_condExp (ℱ.le 0) (f := Y 0)]
    exact (integral_congr_ae (hcent 0)).trans (integral_zero _ _)
  have hinit : HasSubgaussianMGF (Y 0) c μ :=
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hYmeas 0).aemeasurable
      (Eventually.of_forall fun ω => abs_le.mp (hYbound 0 ω)) hYzero
  have hadapt : StronglyAdapted G Y := by
    intro j
    exact ((hM.stronglyMeasurable j).mono (ℱ.mono (Nat.le_succ j))).sub
      (hM.stronglyMeasurable (j + 1))
  have htail := measure_sum_ge_le_of_hasCondSubgaussianMGF
    (cY := fun _ => c) hadapt hinit n (fun i _ => hcond (i + 1)) ht
  have hsum (ω : Ω) : ∑ j ∈ Finset.range n, Y j ω = -M n ω := by
    calc
      _ = -∑ j ∈ Finset.range n, (M (j + 1) ω - M j ω) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by dsimp [Y]; ring
      _ = -M n ω := by
        rw [Finset.sum_range_sub (fun j => M j ω), hzero]
        ring
  have hc : (c : ℝ) = b ^ 2 := by
    simp only [c, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith : 0 ≤ b - -b)]
    congr 1
    ring
  simpa only [hsum, le_neg, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, hc, mul_assoc, neg_div] using htail

end CERW.LimitShapes.LogLower
