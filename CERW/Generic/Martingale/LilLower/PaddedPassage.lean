import CERW.Generic.Martingale.LilLower.BracketTimes
import CERW.Generic.Martingale.LilLower.PaddedBracket

/-!
# The passage times of the padded bracket are stopping times

The padded bracket `paddedBracket c G (k + 1)` is measurable at time `k` when each `c j` and
`G j` is measurable at time `j`, so its first passage over a level is a stopping time of the
filtration that joins `ℱ` with an independent filtration, on the product space.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory

variable {Ω : Type*} {Ξ : Type*} {m0 : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ}

/-- The padded bracket at time `k + 1` is measurable at time `k`. -/
theorem stronglyMeasurable_paddedBracket_succ {ℱ : Filtration ℕ m0} {c G : ℕ → Ω → ℝ}
    (hc : ∀ j, StronglyMeasurable[ℱ j] (c j)) (hG : ∀ j, StronglyMeasurable[ℱ j] (G j))
    (k : ℕ) : StronglyMeasurable[ℱ k] (paddedBracket c G (k + 1)) := by
  have hmeas : ∀ j ∈ Finset.range (k + 1), StronglyMeasurable[ℱ k]
      (fun ω => G j ω * c j ω + (1 - G j ω)) := by
    intro j hj
    have hjk : ℱ j ≤ ℱ k := ℱ.mono (Nat.le_of_lt_succ (Finset.mem_range.1 hj))
    have hcj : StronglyMeasurable[ℱ k] (c j) := (hc j).mono hjk
    have hGj : StronglyMeasurable[ℱ k] (G j) := (hG j).mono hjk
    exact (hGj.mul hcj).add (stronglyMeasurable_const.sub hGj)
  exact Finset.stronglyMeasurable_fun_sum (Finset.range (k + 1)) hmeas

/-- The first passage of the padded bracket over a level is a stopping time on the product, for
the joined filtration. -/
theorem isStoppingTime_paddedPassage {ℱ : Filtration ℕ m0} {𝒦 : ℕ → MeasurableSpace Ξ}
    (h𝒦 : Monotone 𝒦) (h𝒦le : ∀ n, 𝒦 n ≤ mΞ) {c G : ℕ → Ω → ℝ}
    (hc : ∀ j, StronglyMeasurable[ℱ j] (c j)) (hG : ∀ j, StronglyMeasurable[ℱ j] (G j))
    (x : ℝ) :
    IsStoppingTime (liftFiltration ℱ 𝒦 h𝒦 h𝒦le)
      (firstPassage (fun n (z : Ω × Ξ) => paddedBracket c G n z.1) x) := by
  refine isStoppingTime_firstPassage (ℱ := liftFiltration ℱ 𝒦 h𝒦 h𝒦le) (fun k => ?_) x
  exact stronglyMeasurable_comp_fst_joinSigma (𝒦 k)
    (stronglyMeasurable_paddedBracket_succ hc hG k)

end CERW.Generic.Martingale.LilLower
