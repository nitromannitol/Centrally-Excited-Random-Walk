module

public import CERW.LimitShapes.Curvature.Mass
public import CERW.Support.Outer.Radius.ProbeGeometry

@[expose] public section

/-!
# Integrated outer cap mass

The negative cap kernel and positive curvature bound give `eq:outer-cap-mass`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The explicit integrated outer cap estimate in `eq:outer-cap-mass`. -/
theorem cap_measure_le_of_curvature {d : ℕ} (hd : 2 ≤ d)
    {ε b A t delta F₀ : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hbA : b ≤ A) (ht : 0 < t) (htA : t ≤ A / 2)
    (hdelta : 0 ≤ delta) (hF : 0 ≤ F₀)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ A)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (hpotential : -delta ≤ CERW.potential d ε E ((A + 4 * t) • u))
    (hcurvature : curvatureIntegral E ((A + 4 * t) • u) ≤ F₀) :
    volume.real (E ∩ Metric.ball (A • u) t) ≤
      (5 : ℝ) ^ d * (CERW.unitBallVolume d / (2 * ε) * delta + F₀ / 2) *
        t ^ (d - 1) := by
  have hω := unitBallVolume_pos d
  have hA : 0 < A := hb.trans_le hbA
  have hsum : b + (A - b) = A := by ring
  have hEb : Bornology.IsBounded E :=
    (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (r := A)).subset (by
      intro v hv
      simpa only [Metric.mem_closedBall, dist_zero_right] using (hband v hv).2)
  have hsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + (A - b)} := by
    intro v hv
    simpa only [hsum, Set.mem_setOf_eq] using hband v hv
  have htb : 2 * t ≤ b + (A - b) := by rw [hsum]; linarith
  have hy : A ≤ ‖(A + 4 * t) • u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hu, mul_one]
    linarith
  have hhi : CERW.positivePotential d ε E
      ((A + 4 * t) • u) ≤ ε / unitBallVolume d * F₀ :=
    (positivePotential_le_curvatureIntegral hd hε.le hb hbA hE hband _ hy).trans
      (mul_le_mul_of_nonneg_left hcurvature (by positivity))
  have hcap := CERW.Support.Outer.Radius.cap_mass_of_probe hd hε hE hEb hsub hb ht
    htb hu (by simpa only [hsum] using hpotential) (by simpa only [hsum] using hhi)
  have hcoeff : unitBallVolume d / (2 * ε) * (5 : ℝ) ^ d *
      (delta + ε / unitBallVolume d * F₀) =
      (5 : ℝ) ^ d * (unitBallVolume d / (2 * ε) * delta + F₀ / 2) := by
    field_simp [hε.ne', hω.ne']
  have _ := hdelta
  have _ := hF
  simpa only [hsum, ← measureReal_def, hcoeff] using hcap

end CERW.LimitShapes.Curvature
