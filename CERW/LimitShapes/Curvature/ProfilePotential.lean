import CERW.LimitShapes.Curvature.EventData
import CERW.LimitShapes.Curvature.PotentialMaximum
import CERW.LimitShapes.Curvature.Width
import CERW.Support.Outer.Radius.PotentialConvolution

/-!
# Global bounds for the annular potential

The maximum principle and the width estimate give the potential bound in
`sec:global-profile`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- Replacing the signed kernel by its positive part increases the potential. -/
theorem potential_le_positivePotential {d : ℕ} (hd : 1 ≤ d) {ε R : ℝ}
    (hε : 0 ≤ ε) {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, ‖v‖ ≤ R) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε E y ≤ positivePotential d ε E y := by
  exact CERW.Support.Outer.Radius.ev_potential_le_positivePotential hd hε hE
    (band_measure_ne_top hband) y

/-- The width estimate converts annular upper and lower bounds into a global bound. -/
theorem exists_global_potential_bound {d : ℕ} (hd : 2 ≤ d)
    (A B D : ℝ) (hA : 0 < A) (hB : 0 < B) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε b R delta L : ℝ), 0 < ε → 0 < b → b ≤ R →
      1 ≤ delta → 1 ≤ L → R - b ≤ A * delta * L ^ d →
      ∀ E : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet E →
      (∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R) →
      (∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ →
        -D * delta ≤ potential d ε E y) →
      (∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ R →
        positivePotential d ε E y ≤
          B * ((delta * (R - b) ^ (d - 1)) ^ ((1 : ℝ) / d) + delta)) →
      ∀ y : EuclideanSpace ℝ (Fin d),
        |potential d ε E y| ≤ C * delta * L ^ (d - 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_profile_error_le_of_width hd A B hA hB
  refine ⟨C + D, by linarith, ?_⟩
  intro ε b R delta L hε hb hbR hdelta hL hw E hE hband hlower hupper
  have hd0 : 0 ≤ delta := by linarith
  have hLp : 1 ≤ L ^ (d - 1) := one_le_pow₀ hL
  have hlow : D * delta ≤ (C + D) * delta * L ^ (d - 1) := by
    calc
      D * delta ≤ (C + D) * delta := by nlinarith
      _ ≤ (C + D) * delta * L ^ (d - 1) :=
        le_mul_of_one_le_right (by positivity) hLp
  have hhigh := hbound (R - b) delta L (sub_nonneg.mpr hbR) hdelta hL hw
  apply abs_potential_le_of_annulus hd hε hb hbR (by positivity) hE hband
  intro y hyb hyR
  apply abs_le.mpr
  constructor
  · have := hlower y hyb
    linarith
  · calc
      potential d ε E y ≤ positivePotential d ε E y :=
        potential_le_positivePotential (by omega) hε.le hE (fun v hv => (hband v hv).2) y
      _ ≤ B * ((delta * (R - b) ^ (d - 1)) ^ ((1 : ℝ) / d) + delta) :=
        hupper y hyb hyR
      _ ≤ C * delta * L ^ (d - 1) := hhigh
      _ ≤ (C + D) * delta * L ^ (d - 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + D) hd0) (by positivity)

end CERW.LimitShapes.Curvature
