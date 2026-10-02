import Mathlib.Probability.Martingale.BorelCantelli
import Mathlib.Probability.Process.Stopping

/-!
# Lévy's Borel–Cantelli lemma along stopping times

For stopping times `τ 0 ≤ τ 1 ≤ …` the σ-algebras of events before them form a filtration, and
Lévy's generalized Borel–Cantelli lemma applies to events `A k` that lie before `τ k`.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory Filter Topology

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The filtration of the σ-algebras of events before the nondecreasing stopping times `τ k`. -/
def stoppedFiltration (ℱ : Filtration ℕ m0) (τ : ℕ → Ω → WithTop ℕ)
    (hτ : ∀ k, IsStoppingTime ℱ (τ k)) (hmono : ∀ k ω, τ k ω ≤ τ (k + 1) ω) :
    Filtration ℕ m0 where
  seq k := (hτ k).measurableSpace
  mono' := by
    refine monotone_nat_of_le_succ fun k => ?_
    exact IsStoppingTime.measurableSpace_mono (hτ k) (hτ (k + 1)) fun ω => hmono k ω
  le' k := (hτ k).measurableSpace_le

/-- Lévy's generalized Borel–Cantelli lemma along stopping times: events `A k` before `τ k`
occur infinitely often exactly where the conditional probabilities of `A (k + 1)` given the events
before `τ k` have an infinite sum. -/
theorem ae_mem_limsup_iff_stopped {μ : Measure Ω} [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    (τ : ℕ → Ω → WithTop ℕ) (hτ : ∀ k, IsStoppingTime ℱ (τ k))
    (hmono : ∀ k ω, τ k ω ≤ τ (k + 1) ω) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet[(hτ k).measurableSpace] (A k)) :
    ∀ᵐ ω ∂μ, ω ∈ limsup A atTop ↔
      Tendsto (fun n => ∑ k ∈ Finset.range n,
        (μ[(A (k + 1)).indicator (1 : Ω → ℝ) | (hτ k).measurableSpace]) ω) atTop atTop :=
  ae_mem_limsup_atTop_iff (ℱ := stoppedFiltration ℱ τ hτ hmono) μ hA

/-- If the conditional probabilities of `A (k + 1)` given the events before `τ k` are almost
surely at least a deterministic sequence with divergent sum, then `A k` occurs infinitely often
almost surely. -/
theorem ae_mem_limsup_of_condProb_ge {μ : Measure Ω} [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    (τ : ℕ → Ω → WithTop ℕ) (hτ : ∀ k, IsStoppingTime ℱ (τ k))
    (hmono : ∀ k ω, τ k ω ≤ τ (k + 1) ω) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet[(hτ k).measurableSpace] (A k)) {q : ℕ → ℝ}
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, q k) atTop atTop)
    (hge : ∀ k, ∀ᵐ ω ∂μ,
      q k ≤ (μ[(A (k + 1)).indicator (1 : Ω → ℝ) | (hτ k).measurableSpace]) ω) :
    ∀ᵐ ω ∂μ, ω ∈ limsup A atTop := by
  filter_upwards [ae_mem_limsup_iff_stopped (μ := μ) ℱ τ hτ hmono hA, ae_all_iff.2 hge]
    with ω h1 h2
  refine h1.2 (tendsto_atTop_mono (fun n => ?_) hdiv)
  exact Finset.sum_le_sum fun k _ => h2 k

end CERW.Generic.Martingale.LilLower
