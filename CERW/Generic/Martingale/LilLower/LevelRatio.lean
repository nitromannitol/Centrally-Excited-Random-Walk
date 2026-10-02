import CERW.Model.Bracket
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The ratio that controls the gate

For a martingale `S` and a predictable bound `B` on its increments, the ratio
`K_i = B_{i+1} √(log log (P_{i+1} ∨ e^e)) / √P_{i+1}`, with `P` the predictable bracket, is
measurable at time `i`, and tends to `0` along a path where the hypothesis of the law of the
iterated logarithm holds.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory Filter Topology

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The ratio `B_{i+1} √(log log (P_{i+1} ∨ e^e)) / √P_{i+1}` at time `i`. -/
noncomputable def levelRatio (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ) (i : ℕ)
    (ω : Ω) : ℝ :=
  B (i + 1) ω * Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ S S (i + 1) ω)
    (Real.exp (Real.exp 1))))) / Real.sqrt (CERW.predBracket μ ℱ S S (i + 1) ω)

/-- The predictable bracket at time `i + 1` is measurable at time `i`. -/
theorem stronglyMeasurable_predBracket_succ (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (S : ℕ → Ω → ℝ) (i : ℕ) :
    StronglyMeasurable[ℱ i] (CERW.predBracket μ ℱ S S (i + 1)) := by
  unfold CERW.predBracket
  refine Finset.stronglyMeasurable_sum _ fun t ht => ?_
  exact stronglyMeasurable_condExp.mono (ℱ.mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)))

/-- The ratio at time `i` is measurable at time `i` when `B (i + 1)` is. -/
theorem stronglyMeasurable_levelRatio (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ)
    (hB : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) (i : ℕ) :
    StronglyMeasurable[ℱ i] (levelRatio μ ℱ S B i) := by
  have hP : Measurable[ℱ i] (CERW.predBracket μ ℱ S S (i + 1)) :=
    (stronglyMeasurable_predBracket_succ μ ℱ S i).measurable
  have hBi : Measurable[ℱ i] (B (i + 1)) := (hB i).measurable
  refine Measurable.stronglyMeasurable ?_
  unfold levelRatio
  refine Measurable.div (hBi.mul ?_) ?_
  · exact (Real.measurable_log.comp (Real.measurable_log.comp
      (hP.max measurable_const))).sqrt
  · exact hP.sqrt

/-- The ratio tends to `0` along a path where the hypothesis of the law of the iterated
logarithm holds: it is that hypothesis at the shifted index. -/
theorem tendsto_levelRatio_zero (μ : Measure Ω) (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ)
    {ω : Ω}
    (h : Tendsto (fun n => B n ω * Real.sqrt (Real.log (Real.log (max
        (CERW.predBracket μ ℱ S S n ω) (Real.exp (Real.exp 1))))) /
          Real.sqrt (CERW.predBracket μ ℱ S S n ω)) atTop (𝓝 0)) :
    Tendsto (fun i => levelRatio μ ℱ S B i ω) atTop (𝓝 0) := by
  exact (Filter.tendsto_add_atTop_iff_nat 1).2 h

end CERW.Generic.Martingale.LilLower
