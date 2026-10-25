module

public import CERW.LimitShapes.Curvature.Mass

@[expose] public section

/-!
# Curvature at a distant point

The outer endpoint estimate used in `eq:curvature-improved` follows from the
separation of the evaluation point from the radial band.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- Outside twice the outer radius, the curvature is bounded by mass and separation. -/
theorem curvatureIntegral_le_far_point {d : ℕ} (hd : 3 ≤ d)
    {b R : ℝ} (hb : 0 < b) (hbR : b ≤ R)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R)
    (y : EuclideanSpace ℝ (Fin d)) (hy : 2 * R ≤ ‖y‖) :
    curvatureIntegral E y ≤ volume.real E * (R ^ ((2 : ℝ) - d) / b) := by
  have hR : 0 < R := hb.trans_le hbR
  have hfin := band_measure_ne_top (fun v hv => (hband v hv).2)
  have hi := integrableOn_curvature (by omega : 2 ≤ d) hb hE hband y
  have hle := integral_mono_ae hi
    (integrableOn_const (C := R ^ ((2 : ℝ) - d) / b) hfin) (by
      apply ae_restrict_of_forall_mem hE
      intro v hv
      have hsep : R ≤ ‖v - y‖ := by
        have := norm_sub_norm_le y v
        rw [norm_sub_rev y v] at this
        linarith [(hband v hv).2]
      have hp := Real.rpow_le_rpow_of_nonpos hR hsep
        (show (2 : ℝ) - d ≤ 0 by
          have : (3 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      exact (div_le_div_of_nonneg_right hp (norm_nonneg v)).trans
        (div_le_div_of_nonneg_left (by positivity) hb (hband v hv).1))
  simpa only [curvatureIntegral, integral_const, smul_eq_mul, Measure.real,
    Measure.restrict_apply_univ] using hle

end CERW.LimitShapes.Curvature
