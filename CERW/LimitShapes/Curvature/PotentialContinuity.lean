import CERW.Support.Geometry.Holder

/-! # Continuity of the signed potential

The Hölder estimate gives global continuity of the actual integral in `sec:global-profile`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The actual potential of a bounded measurable set is continuous in dimension at least two. -/
theorem continuous_potential {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hEb : Bornology.IsBounded E) : Continuous (CERW.potential d ε E) := by
  obtain ⟨C, hC, hholder⟩ := CERW.Support.Geometry.exists_potential_holder hd
  exact CERW.Support.Geometry.continuous_of_holder_half (by positivity)
    (hholder ε hε E hE hEb.measure_lt_top.ne)

end CERW.LimitShapes.Curvature
