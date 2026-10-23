import CERW.Support.Outer.Radius.InnerGeometry
import CERW.LimitShapes.Curvature.Mass

/-!
# Geometry of the actual annular remainder

The contact point and the potential decomposition used in `eq:mass`.
-/

namespace CERW.LimitShapes.Curvature

open CERW LatticeProb MeasureTheory
open CERW.Support.Outer.Radius

/-- The cell set has a true contact point in the closure of its complement. -/
theorem exists_annular_contact {d : ℕ} (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) :
    ∃ y : EuclideanSpace ℝ (Fin d), ‖y‖ = innerRadius X n ∧
      y ∈ closure (cellSet X n)ᶜ := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : (cellSet X n)ᶜ.Nonempty := by
    by_contra h
    have heq : cellSet X n = Set.univ := by
      simpa only [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] using h
    have hb := Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball hd X n)
    rw [heq] at hb
    exact NormedSpace.unbounded_univ ℝ _ hb
  obtain ⟨y, hy, hnorm⟩ := CERW.Support.Contact.exists_mem_closure_norm_eq_sInf hne
  exact ⟨y, hnorm, hy⟩

/-- Outside the inner ball the full potential equals the annular potential. -/
theorem potential_eq_annular {d : ℕ} (hd : 2 ≤ d) (ε : ℝ)
    (X : ℕ → Site d) (n : ℕ) (hb : 0 < innerRadius X n)
    (y : EuclideanSpace ℝ (Fin d)) (hy : innerRadius X n ≤ ‖y‖) :
    potential d ε (cellSet X n) y =
      potential d ε (cellSet X n \ Metric.ball 0 (innerRadius X n)) y := by
  rw [potential_split hd ε (CERW.Support.Occupation.measurableSet_cellSet X n)
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ d) X n))
    hb (ball_innerRadius_subset (by omega) X n) y,
    max_eq_right (sub_nonpos.mpr hy), mul_zero, zero_add]

/-- The actual annulus is measurable and lies between its stated radii. -/
theorem annular_measurable_band {d : ℕ} (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) :
    let E := cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius X n)
    MeasurableSet E ∧ ∀ v ∈ E,
      innerRadius X n ≤ ‖v‖ ∧ ‖v‖ ≤ maxRadius X n + 2 * Real.sqrt d := by
  refine ⟨(CERW.Support.Occupation.measurableSet_cellSet X n).diff measurableSet_ball, ?_⟩
  intro v hv
  have h := sdiff_subset_annulus hd X n hv
  exact ⟨h.1, by linarith [h.2]⟩

end CERW.LimitShapes.Curvature
