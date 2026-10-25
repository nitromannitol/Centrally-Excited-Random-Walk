module

public import CERW.LimitShapes.Crossing.Probability
public import CERW.LimitShapes.Exit.UpperProbabilityAux

@[expose] public section

/-!
# The radius consequence of distance crossing

The distance estimate in `eq:distance-crossing` gives the radius hypothesis used in
Proposition `prop:coarse`, with a polynomial horizon.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory

/-- Norm equivalence turns distance crossing into the radius estimate for the lower bound. -/
theorem radius_bound_of_distance_crossing {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {X : ℕ → Site d} {n N : ℕ} {C R : ℝ} (hC : 0 ≤ C) (hn : n ≤ N)
    (hlog : Real.log N ≤ (d + 3 : ℝ) * Real.log R)
    (hc : CERW.LimitShapes.DistanceCrossingBound Ψ C X N) :
    ∀ a : ℝ, 0 ≤ a → maxRadius X n ≤ a / normMin Ψ +
      (C * (d + 3 : ℝ)) *
        (1 + (CERW.LimitShapes.exteriorLocalTime Ψ X n a : ℝ)) * Real.log R := by
  obtain ⟨hm, hmin⟩ := Generic.Norm.normMin_pos_mul_le hΨ hd
  intro a ha
  have hzero : Ψ (0 : EuclideanSpace ℝ (Fin d)) = 0 :=
    (Generic.Norm.map_zero_nonneg_neg hΨ).1
  have hne : ({v : EuclideanSpace ℝ (Fin d) | Ψ v ≤ a}).Nonempty :=
    ⟨0, by simpa only [Set.mem_setOf_eq, hzero] using ha⟩
  unfold maxRadius
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hdist : ‖toSpace (X j)‖ - a / normMin Ψ ≤
      Metric.infDist (toSpace (X j)) {v | Ψ v ≤ a} := by
    apply (Metric.le_infDist hne).mpr
    intro v hv
    have hvnorm : ‖v‖ ≤ a / normMin Ψ :=
      (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using (hmin v).trans hv)
    rw [dist_eq_norm]
    linarith [norm_le_norm_sub_add (toSpace (X j)) v]
  have hh := hc n hn a ha j hjn
  have hscale := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ C * (1 +
      (CERW.LimitShapes.exteriorLocalTime Ψ X n a : ℝ)) by positivity)
  rw [norm_toSpace] at hdist
  have he : C * (1 + (CERW.LimitShapes.exteriorLocalTime Ψ X n a : ℝ)) *
      ((d + 3 : ℝ) * Real.log R) =
      (C * (d + 3 : ℝ)) *
        (1 + (CERW.LimitShapes.exteriorLocalTime Ψ X n a : ℝ)) * Real.log R := by ring
  rw [he] at hscale
  linarith only [hdist, hh, hscale]

end CERW.LimitShapes.Exit
