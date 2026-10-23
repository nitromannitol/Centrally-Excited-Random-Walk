import CERW.LimitShapes.Curvature.Mass

/-! # Comparing the Newtonian integral with curvature (`eq:positive-bound`) -/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- Bounded radial support converts the curvature integral into a Newtonian bound. -/
theorem integral_rpow_le_radius_mul_curvature {d : ℕ} (hd : 2 ≤ d)
    {b R : ℝ} (hb : 0 < b) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∫ v in E, ‖v - y‖ ^ ((2 : ℝ) - d) ≤ R * curvatureIntegral E y := by
  have hi := integrableOn_curvature hd hb hE hband y
  have hm : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
      (volume.restrict E) := by fun_prop
  have hw : ∀ᵐ v ∂volume.restrict E, ‖‖v‖‖ ≤ R := by
    apply ae_restrict_of_forall_mem hE
    intro v hv
    simpa only [norm_norm] using (hband v hv).2
  have hip := hi.mul_bdd hm hw
  have heq : (fun v => (‖v - y‖ ^ ((2 : ℝ) - d) / ‖v‖) * ‖v‖) =ᵐ[volume.restrict E]
      (fun v => ‖v - y‖ ^ ((2 : ℝ) - d)) := by
    apply ae_restrict_of_forall_mem hE
    intro v hv
    exact div_mul_cancel₀ _ (ne_of_gt (hb.trans_le (hband v hv).1))
  have hin := hip.congr heq
  rw [curvatureIntegral, ← integral_const_mul]
  apply integral_mono_ae hin (hi.const_mul R)
  apply ae_restrict_of_forall_mem hE
  intro v hv
  have hv0 := hb.trans_le (hband v hv).1
  have hp := Real.rpow_nonneg (norm_nonneg (v - y)) ((2 : ℝ) - d)
  calc
    _ = (‖v - y‖ ^ ((2 : ℝ) - d) / ‖v‖) * ‖v‖ :=
      (div_mul_cancel₀ _ (ne_of_gt hv0)).symm
    _ ≤ (‖v - y‖ ^ ((2 : ℝ) - d) / ‖v‖) * R :=
      mul_le_mul_of_nonneg_left (hband v hv).2 (div_nonneg hp hv0.le)
    _ = _ := mul_comm _ _

end CERW.LimitShapes.Curvature
