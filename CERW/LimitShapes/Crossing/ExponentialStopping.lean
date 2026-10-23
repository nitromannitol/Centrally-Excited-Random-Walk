import CERW.LimitShapes.Crossing.ExponentialOccupation
import Mathlib.Probability.Martingale.OptionalSampling

/-!
# Expectation of the stopped exponential distance

The internal stopping argument for `eq:distance-crossing` uses the actual drift
compensator and the bounded optional sampling theorem.
-/

namespace CERW.LimitShapes.Crossing.ExponentialStopping

open MeasureTheory Filter LatticeProb CERW CERW.Support.Law CERW.Support.Drift

/-- Stopping at a finite natural time evaluates the process at that time. -/
private theorem stoppedValue_coe {Ω E : Type*} (u : ℕ → Ω → E) (τ : Ω → ℕ) :
    MeasureTheory.stoppedValue u (fun ω => (τ ω : WithTop ℕ)) =
      (fun ω => u (τ ω) ω) := by
  funext ω
  change u ((τ ω : WithTop ℕ).untopA) ω = u (τ ω) ω
  rfl

/-- Every site function evaluated at a bounded stopping time is integrable. -/
theorem integrable_stopped_site_function {d : ℕ} (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 ≤ ε) {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x i, ε * |ξ x i| ≤ 1 / (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X)
    (f : Site d → ℝ) {τ : Ω → ℕ} (hτ : IsStoppingTime (pathFiltration hX.measurable)
      (fun ω => (τ ω : WithTop ℕ)))
    {N : ℕ} (hb : ∀ ω, τ ω ≤ N) : Integrable (fun ω => f (X (τ ω) ω)) μ := by
  have ht : IsStoppingTime (pathFiltration hX.measurable)
      (fun ω => (τ ω : WithTop ℕ)) := by
    exact hτ
  have hi (n : ℕ) : Integrable (fun ω => f (X n ω)) μ :=
    integrable_path_next_drift hd hε hξ hX n (fun p _ => f (p ⟨n, by simp⟩))
  have hh := MeasureTheory.integrable_stoppedValue ℕ ht hi
    (N := N) (fun ω => WithTop.coe_le_coe.mpr (hb ω))
  simpa only [stoppedValue_coe] using hh

/-- The bounded stopping argument for the exponential distance, conditional on the
actual far-site drift and occupation bounds. -/
theorem integral_exp_stopped_le {d : ℕ} (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 ≤ ε) {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x i, ε * |ξ x i| ≤ 1 / (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X)
    (N L : ℕ) (δ : Site d → ℝ) (hδ : ∀ x, 0 ≤ δ x) (hδ0 : δ 0 = 0)
    (θ R κ : ℝ) (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) (hR : 1 ≤ R)
    (hθR : θ * R ≤ 1 / 2) (hκ : 0 < κ)
    (hL : (L + 1 : ℝ) * (θ + 1 / (2 * R)) ≤ κ)
    (hlip : ∀ x e, e ∈ unitSteps d → δ (x + e) ≤ δ x + 1)
    (τ : Ω → ℕ) (hτ : IsStoppingTime (pathFiltration hX.measurable)
      (fun ω => (τ ω : WithTop ℕ)))
    (hb : ∀ ω, τ ω ≤ N)
    (hcount : ∀ᵐ ω ∂μ, ∀ x, R ≤ δ x → localTime (X · ω) (τ ω) x ≤ L + 1)
    (hfar : ∀ j < N, ∀ᵐ ω ∂μ, j < τ ω → R ≤ δ (X j ω) →
      (∑ e ∈ unitSteps d, driftStepProb d ε ξ (X · ω) j e *
        (Real.exp (θ * δ (X j ω + e)) - Real.exp (θ * δ (X j ω)))) ≤
      θ * Real.exp (θ * δ (X j ω)) * (θ + 1 / (2 * δ (X j ω)) -
        if X j ω ∉ departureRange (X · ω) j then κ else 0)) :
    ∫ ω, Real.exp (θ * δ (X (τ ω) ω)) ∂μ ≤ 1 + Real.exp 1 * N := by
  classical
  let f : Site d → ℝ := fun x => Real.exp (θ * δ x)
  let M := driftDynkin ε ξ f X
  have hM := martingale_driftDynkin hd hε hξ hX f
  have ht : IsStoppingTime (pathFiltration hX.measurable)
      (fun ω => (τ ω : WithTop ℕ)) := by
    exact hτ
  have hbt : ∀ ω, (τ ω : WithTop ℕ) ≤ N := fun ω => WithTop.coe_le_coe.mpr (hb ω)
  have heq := hM.stoppedValue_ae_eq_condExp_of_le_const (n := N) ht hbt
  have hiM : Integrable (fun ω => M (τ ω) ω) μ := by
    simpa only [stoppedValue_coe] using
      MeasureTheory.integrable_stoppedValue ℕ ht hM.integrable hbt
  have hintM : (∫ ω, M (τ ω) ω ∂μ) = 0 := by
    calc
      _ = ∫ ω, μ[M N | ht.measurableSpace] ω ∂μ := by
        apply integral_congr_ae
        simpa only [stoppedValue_coe, M] using heq
      _ = ∫ ω, M N ω ∂μ := integral_condExp (ht.measurableSpace_le_of_le hbt)
      _ = ∫ ω, μ[M N | pathFiltration hX.measurable 0] ω ∂μ :=
        (integral_condExp ((pathFiltration hX.measurable).le 0)).symm
      _ = 0 := by
        rw [integral_congr_ae (hM.condExp_ae_eq (Nat.zero_le N))]
        simp only [driftDynkin_zero, integral_zero]
  have hstart : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  have hfall : ∀ᵐ ω ∂μ, ∀ j, j < N → j < τ ω → R ≤ δ (X j ω) →
      (∑ e ∈ unitSteps d, driftStepProb d ε ξ (X · ω) j e *
        (f (X j ω + e) - f (X j ω))) ≤
      θ * f (X j ω) * (θ + 1 / (2 * δ (X j ω)) -
        if X j ω ∉ departureRange (X · ω) j then κ else 0) := by
    exact ae_all_iff.mpr fun j => ae_all_iff.mpr (hfar j)
  have hbound : ∀ᵐ ω ∂μ, f (X (τ ω) ω) ≤ M (τ ω) ω + (1 + Real.exp 1 * N) := by
    filter_upwards [hstart, hcount, hfall] with ω hs hc hf
    have hg := ExponentialOccupation.sum_exponential_drift_le hd ε hε ξ hξ
      (X · ω) (τ ω) δ hδ θ R κ hθ hθhalf hR hθR hκ L hL hlip hc
      (fun j hj => hf j (lt_of_lt_of_le hj (hb ω)) hj)
    have hsum : (∑ j ∈ Finset.range (τ ω),
        (driftNextMean ε ξ f (X · ω) j - f (X j ω))) ≤ Real.exp 1 * N := by
      have hn : (τ ω : ℝ) ≤ N := by exact_mod_cast hb ω
      simpa only [← stepMean_driftStepProb hd, stepMean, f] using
        hg.trans (mul_le_mul_of_nonneg_left hn (Real.exp_pos 1).le)
    have hm : M (τ ω) ω = f (X (τ ω) ω) - 1 -
        ∑ j ∈ Finset.range (τ ω),
          (driftNextMean ε ξ f (X · ω) j - f (X j ω)) := by
      simp only [M, driftDynkin, hs, f, hδ0, mul_zero, Real.exp_zero]
    linarith
  have hi := integrable_stopped_site_function hd hε hξ hX f hτ hb
  calc
    _ ≤ ∫ ω, M (τ ω) ω + (1 + Real.exp 1 * N) ∂μ :=
      integral_mono_ae hi (hiM.add (integrable_const _)) hbound
    _ = 1 + Real.exp 1 * N := by rw [integral_add hiM (integrable_const _), hintM]; simp

end CERW.LimitShapes.Crossing.ExponentialStopping
