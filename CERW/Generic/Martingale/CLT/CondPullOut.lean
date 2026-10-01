import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Pull-out of a complex weight and bounded convergence in measure

Two measure-theoretic ingredients of the martingale central limit theorem.

* A bounded complex-valued weight, measurable for a sub-sigma-algebra `m`, can be pulled out of the
  conditional expectation of a real integrable function: the integral of `W * f` equals the integral
  of `W * E[f | m]`.
* A uniformly bounded sequence of nonnegative functions that tends to `0` in measure on a
  probability space has integrals tending to `0`.
-/

namespace CERW.Generic.Martingale.CLT

open MeasureTheory Filter
open scoped Topology

section PullOut

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} {f : Ω → ℝ} {W : Ω → ℂ} {K : ℝ}

/-- The integral of a bounded `m`-measurable complex weight times a real integrable function
equals the integral of the weight times the conditional expectation of the function given `m`. -/
theorem integral_mul_ofReal_eq_integral_mul_condExp (hm : m ≤ m0) (hf : Integrable f μ)
    (hW : StronglyMeasurable[m] W) (hK : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ K) :
    ∫ ω, W ω * (f ω : ℂ) ∂μ = ∫ ω, W ω * (μ[f | m] ω : ℂ) ∂μ := by
  let B : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip
  have hB : ∀ (w : ℂ) (x : ℝ), B w x = w * (x : ℂ) := by
    intro w x
    simp [B, mul_comm]
  have h1 := condExp_stronglyMeasurable_bilin_of_bound (m := m) (mΩ := m0) (μ := μ)
    B hm hW hf K hK
  calc ∫ ω, W ω * (f ω : ℂ) ∂μ = ∫ ω, B (W ω) (f ω) ∂μ := by simp_rw [hB]
    _ = ∫ ω, (μ[fun ω => B (W ω) (f ω) | m]) ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, B (W ω) (μ[f | m] ω) ∂μ := integral_congr_ae h1
    _ = ∫ ω, W ω * (μ[f | m] ω : ℂ) ∂μ := by simp_rw [hB]

end PullOut

section BoundedConvergence

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : ℕ → Ω → ℝ} {C : ℝ}

/-- A uniformly bounded sequence of nonnegative functions that tends to `0` in measure has
integrals tending to `0`. -/
theorem tendsto_integral_of_tendstoInMeasure_of_bounded
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hb : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ f n ω ∧ f n ω ≤ C)
    (h : TendstoInMeasure μ f atTop (fun _ => 0)) :
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at h
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  have hev : ∀ᶠ n in atTop, (|C| + 1) * μ.real {ω | ε / 2 ≤ ‖f n ω - 0‖} < ε / 2 := by
    have := (h (ε / 2) hδ).const_mul (|C| + 1)
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [hev] with n hn
  set S : Set Ω := {ω | ε / 2 ≤ ‖f n ω - 0‖} with hS
  have hSm : NullMeasurableSet S μ :=
    aestronglyMeasurable_const.nullMeasurableSet_le (((hf n).sub aestronglyMeasurable_const).norm)
  have hpt : ∀ᵐ ω ∂μ, f n ω ≤ ε / 2 + |C| * S.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hb n] with ω hω
    by_cases hωS : ω ∈ S
    · rw [Set.indicator_of_mem hωS]
      linarith [hω.2, le_abs_self C]
    · rw [Set.indicator_of_notMem hωS]
      have : ‖f n ω - 0‖ < ε / 2 := not_le.mp hωS
      rw [sub_zero, Real.norm_of_nonneg hω.1] at this
      simp only [mul_zero, add_zero]
      exact this.le
  have hind : Integrable (S.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator₀ hSm
  have hint : Integrable (fun ω => ε / 2 + |C| * S.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const _).add (hind.const_mul _)
  have hle : ∫ ω, f n ω ∂μ ≤ ∫ ω, (ε / 2 + |C| * S.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
    integral_mono_of_nonneg ((hb n).mono fun ω hω => hω.1) hint hpt
  have heq : ∫ ω, (ε / 2 + |C| * S.indicator (fun _ => (1 : ℝ)) ω) ∂μ
      = ε / 2 + |C| * μ.real S := by
    rw [integral_add (integrable_const _) (hind.const_mul _), integral_const_mul,
      integral_indicator₀ hSm, setIntegral_const]
    simp
  have hnn : 0 ≤ ∫ ω, f n ω ∂μ := integral_nonneg_of_ae ((hb n).mono fun ω hω => hω.1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hμS : 0 ≤ μ.real S := measureReal_nonneg
  have hC : |C| * μ.real S ≤ (|C| + 1) * μ.real S := by
    nlinarith
  linarith

end BoundedConvergence

end CERW.Generic.Martingale.CLT
