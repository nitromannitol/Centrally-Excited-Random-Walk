import CERW.Frozen.DriftCrossing

/-!
# Guard for the crossing lemma

`lem:crossing` is deterministic. A guard exhibits one concrete instance of every one of its
hypotheses: the zero drift field and the constant path at the origin in the plane, with the
constant `C = 1` and `n = 2`. The martingale `Z` of the statement is then identically zero, so the
event inequality holds, and the conclusion is the trivial bound `0 ≤ √(⋯)`.
-/

namespace CERW.Support.Guards

open MeasureTheory LatticeProb CERW

/-- On the zero drift field and the constant path at the origin in the plane, with `ε = 1/4`,
`n = 2` and `C = 1`, the conclusion of `lem:crossing` holds for every unit vector and every
interval. -/
theorem drift_crossing_applies :
    let x : ℕ → Site 2 := fun _ => 0
    ∀ u : EuclideanSpace ℝ (Fin 2), ‖u‖ = 1 → ∀ s t : ℕ, s < t → t ≤ 2 →
      inner ℝ u (CERW.toSpace (x t) - CERW.toSpace (x s))
        ≤ 1 * Real.sqrt ((t - s : ℝ) * Real.log 2) := by
  intro x u hu s t hst ht
  refine CERW.Frozen.drift_crossing (d := 2) (ε := 1 / 4) (by norm_num)
    (fun _ : Site 2 => 0) x 2 1 ?_ u hu s t hst ht ?_
  · intro s t hst ht
    have hZ : ∀ r : ℕ, (fun r => CERW.toSpace (x r) + (1 / 4 : ℝ) •
        ∑ j ∈ Finset.range r,
          if x j ∉ CERW.departureRange x j then (fun _ : Site 2 => 0) (x j) else 0)
        r = (0 : EuclideanSpace ℝ (Fin 2)) := by
      intro r
      have h0 : CERW.toSpace (0 : Site 2) = 0 := by ext i; simp
      simp [x, h0]
    rw [hZ t, hZ s, sub_self, norm_zero]
    positivity
  · intro j hj hjt hnot
    simp

end CERW.Support.Guards
