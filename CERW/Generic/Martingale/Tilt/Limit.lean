import CERW.Generic.Martingale.Tilt.LimitStatements
import CERW.Generic.Martingale.Tilt.SharpLowerTail

/-!
# The passage to an unbounded horizon

`TiltTailOn` at each horizon `n` with `W = {v (1 - ρ) ≤ varSum n}`. Then `n → ∞`: `μ(Wᶜ) → 0`,
and the gated sums settle at their limit `L`.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

/-- The total conditional variance is measurable. -/
theorem measurable_varSum {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (n : ℕ) : Measurable (varSum μ ℱ Y n) := by
  unfold varSum
  refine Finset.measurable_sum _ fun t _ => ?_
  exact ((stronglyMeasurable_condExp (μ := μ) (m := ℱ t)).mono (ℱ.le t)).measurable

/-- Measures of sets that eventually agree with a limit set almost everywhere converge. -/
theorem tendsto_toReal_measure_of_ae_iff {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsFiniteMeasure μ] {S : ℕ → Set Ω} {T : Set Ω} (hT : MeasurableSet T)
    (hS : ∀ n, MeasurableSet (S n)) (h : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∈ S n ↔ ω ∈ T) :
    Tendsto (fun n => (μ (S n)).toReal) atTop (𝓝 (μ T).toReal) :=
  (ENNReal.tendsto_toReal (measure_ne_top μ T)).comp
    (tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hT hS h)

/-- The sharp lower tail at an unbounded horizon, from its steps. -/
theorem sharpLowerTailLimit_of (hT : TiltTailOn.{u}) (hA : TailArith) :
    SharpLowerTailLimit.{u} := by
  intro η hη
  obtain ⟨ρ₀, ε₀, A₀, θ, hρ₀, _, hε₀, _, hall⟩ := hA η hη
  refine ⟨ρ₀, ε₀, A₀, hρ₀, hε₀, ?_⟩
  intro Ω m0 μ _ ℱ Y b L hLm hInc v a ρ hv ha hρ hρle hVle hVev hLev hA0 hab
  obtain ⟨hs, hl, hls, hslb, hsa, hE₁, hE₂, hF⟩ :=
    hall v a ρ b hv ha hρ hρle (hInc 0).nonneg hA0 hab
  have hWm : ∀ n, MeasurableSet {ω | v * (1 - ρ) ≤ varSum μ ℱ Y n ω} := fun n =>
    measurableSet_le measurable_const (measurable_varSum μ ℱ Y n)
  have key : ∀ n, Real.exp (-(((a + θ * a) / (v * (1 - ρ))) ^ 2 * v * (1 + ρ) / 2
      + ((a + θ * a) / (v * (1 - ρ))) * (θ * a)
      + 2 * ((a + θ * a) / (v * (1 - ρ))) ^ 3 * b * v)) *
      (1 / 2 - Real.exp (3 * ((a + θ * a) / (v * (1 - ρ))) ^ 2 * v) *
        Real.sqrt (μ {ω | v * (1 - ρ) ≤ varSum μ ℱ Y n ω}ᶜ).toReal) ≤
      (μ {ω | a ≤ ∑ t ∈ Finset.range n, Y t ω}).toReal := by
    intro n
    have h := hT μ ℱ Y b n (hInc n) (v := v) (ρ := ρ) (s := (a + θ * a) / (v * (1 - ρ)))
      (w := θ * a) (l₁ := θ * a / v) (l₂ := θ * a / v)
      (W := {ω | v * (1 - ρ) ≤ varSum μ ℱ Y n ω}) (hWm n) hs hl hl hls hslb (hVle n)
      (Filter.Eventually.of_forall fun ω hω => hω)
    rw [hsa] at h
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)) h
    linarith
  have hW0 : Tendsto (fun n => (μ {ω | v * (1 - ρ) ≤ varSum μ ℱ Y n ω}ᶜ).toReal) atTop
      (𝓝 0) := by
    have h := tendsto_toReal_measure_of_ae_iff μ (T := (∅ : Set Ω)) MeasurableSet.empty
      (fun n => (hWm n).compl) (by
        filter_upwards [hVev] with ω hω
        filter_upwards [hω] with n hn
        exact iff_of_false (fun h => h hn) (Set.notMem_empty ω))
    simpa using h
  have hP : Tendsto (fun n => (μ {ω | a ≤ ∑ t ∈ Finset.range n, Y t ω}).toReal) atTop
      (𝓝 (μ {ω | a ≤ L ω}).toReal) := by
    refine tendsto_toReal_measure_of_ae_iff μ (measurableSet_le measurable_const hLm)
      (fun n => measurableSet_le measurable_const
        (Finset.measurable_sum _ fun t ht => (hInc n).measurable (Finset.mem_range.mp ht))) ?_
    filter_upwards [hLev] with ω hω
    filter_upwards [hω] with n hn
    simp only [hn]
  have hR := (((hW0.sqrt).const_mul
    (Real.exp (3 * ((a + θ * a) / (v * (1 - ρ))) ^ 2 * v))).const_sub (1 / 2)).const_mul
    (Real.exp (-(((a + θ * a) / (v * (1 - ρ))) ^ 2 * v * (1 + ρ) / 2
      + ((a + θ * a) / (v * (1 - ρ))) * (θ * a)
      + 2 * ((a + θ * a) / (v * (1 - ρ))) ^ 3 * b * v)))
  have hlim := le_of_tendsto_of_tendsto hR hP (Filter.Eventually.of_forall key)
  refine hF.trans ?_
  simpa using hlim

end CERW.Generic.Martingale.Tilt
