import CERW.Generic.Martingale.LilAssembly.Core

/-!
# The block events are measurable at their passage times

The event `{a ≤ M(τ_k) - M(τ_{k-1})}` is measurable in the σ-algebra of `τ_k`: the stopped value at
`τ_k` is, and so is the one at `τ_{k-1} ≤ τ_k`.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology CERW.Generic.Martingale.LilLower

/-- The block event `k` is measurable at the passage time over `θ^k`. -/
theorem measurableSet_blockEvent {Ω : Type*} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℕ m0}
    {M V : ℕ → Ω → ℝ} {θ : ℝ} (δ : ℝ) (hM : StronglyAdapted ℱ M) (hθ : 1 ≤ θ)
    (hτ : ∀ k, IsStoppingTime ℱ (firstPassage V (θ ^ k))) (k : ℕ) :
    MeasurableSet[(hτ k).measurableSpace] (blockEvent M V θ δ k) := by
  rcases k with _ | j
  · simp [blockEvent]
  · have hle : (hτ j).measurableSpace ≤ (hτ (j + 1)).measurableSpace :=
      (hτ j).measurableSpace_mono (hτ (j + 1)) fun ω =>
        firstPassage_mono (pow_le_pow_right₀ hθ (Nat.le_succ j))
    have hprog := hM.isStronglyProgressive_of_discrete
    have hf : Measurable[(hτ (j + 1)).measurableSpace]
        (stoppedValue M (firstPassage V (θ ^ (j + 1)))) :=
      measurable_stoppedValue hprog (hτ (j + 1))
    have hg : Measurable[(hτ (j + 1)).measurableSpace]
        (stoppedValue M (firstPassage V (θ ^ j))) :=
      (measurable_stoppedValue hprog (hτ j)).mono hle le_rfl
    have h := measurableSet_le (mδ := (hτ (j + 1)).measurableSpace)
      (measurable_const (a := (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale (θ ^ (j + 1))))
      (hf.sub hg)
    simpa [blockEvent] using h

end CERW.Generic.Martingale.LilAssembly
