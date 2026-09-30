import CERW.Generic.Kernel.NewtonField
import CERW.Generic.Kernel.DirectionError
import CERW.Support.Occupation.CellDirection
import CERW.Support.Occupation.CellVolume

/-!
# Replacing the lattice direction by the continuous direction

The third replacement in the proof of `eq:approx`: `|u_x - u_v| ≤ 2(1 + √d)/(1 + |v|)` on `C_x`, so
replacing `u_x` by `u_v` inside the cell integrals costs at most
`C ∫_{B(0,R')} dv/((1 + |v|) |v - y|^{d-1}) = O(log(R' + 2))` (`eq:direction-error`), provided the
cells lie in `B(0, R')` and `|y| ≤ 2R'`.
-/

namespace CERW.Support.LocalTime

open MeasureTheory LatticeProb CERW CERW.Generic.Kernel CERW.Support.Occupation

variable {d : ℕ}

/-- The direction replacement: for a finite set of sites whose cells lie in `B(0, R')` with
`R' ≥ 1`, and `|y| ≤ 2R'`, `Σ_{x ∈ E} |∫_{C_x} (u_x - u_v) · K(v - y) dv| ≤ C log(R' + 2)`. -/
theorem exists_sum_abs_setIntegral_unitDir_sub_le (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Finset (Site d)) (y : EuclideanSpace ℝ (Fin d)) (R' : ℝ), 1 ≤ R' →
      ‖y‖ ≤ 2 * R' → (∀ x ∈ E, cell x ⊆ Metric.ball 0 R') →
        ∑ x ∈ E, |∫ v in cell x, inner ℝ (unitDir (toSpace x) - unitDir v) (newtonField (v - y))|
          ≤ C * Real.log (R' + 2) := by
  obtain ⟨C₁, hC₁nonneg, hC₁⟩ := exists_direction_error (d := d) hd
  refine ⟨2 * (1 + Real.sqrt d) * C₁, ?_, ?_⟩
  · have hd0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg d
    nlinarith [hC₁nonneg, hd0]
  · intro E y R' hR hy hcell
    let g : EuclideanSpace ℝ (Fin d) → ℝ :=
      fun v => (1 + ‖v‖)⁻¹ * ‖v - y‖ ^ (1 - (d : ℝ))
    let c : ℝ := 2 * (1 + Real.sqrt d)
    have hc_nonneg : 0 ≤ c := by
      have hd0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg d
      simp only [c]
      nlinarith [hd0]
    have hg_int_ball : IntegrableOn g (Metric.ball 0 R') := (hC₁ R' hR y hy).1
    have hg_val : ∫ v in Metric.ball 0 R', g v ≤ C₁ * Real.log (R' + 2) :=
      (hC₁ R' hR y hy).2
    have hg_nonneg : ∀ v, 0 ≤ g v := fun v =>
      mul_nonneg (inv_nonneg.mpr (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
    have hterm : ∀ x ∈ E, |∫ v in cell x, inner ℝ (unitDir (toSpace x) - unitDir v)
        (newtonField (v - y))| ≤ c * ∫ v in cell x, g v := by
      intro x hx
      have hsubx : cell x ⊆ Metric.ball 0 R' := hcell x hx
      have hgint : IntegrableOn g (cell x) := hg_int_ball.mono_set hsubx
      have hbound : ∀ᵐ v ∂(volume.restrict (cell x)),
          ‖inner ℝ (unitDir (toSpace x) - unitDir v) (newtonField (v - y))‖ ≤ c * g v := by
        filter_upwards [self_mem_ae_restrict (measurableSet_cell x)] with v hv
        have hu := norm_unitDir_sub_le_of_mem_cell (d := d) (by omega : 1 ≤ d) hv
        have hk : ‖newtonField (v - y)‖ = ‖v - y‖ ^ (1 - (d : ℝ)) := norm_newtonField hd _
        have hxnonneg : 0 ≤ ‖v - y‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
        have hstep1 : ‖inner ℝ (unitDir (toSpace x) - unitDir v) (newtonField (v - y))‖
            ≤ ‖unitDir (toSpace x) - unitDir v‖ * ‖newtonField (v - y)‖ := by
          rw [Real.norm_eq_abs]
          exact abs_real_inner_le_norm _ _
        have hstep2 : ‖unitDir (toSpace x) - unitDir v‖ * ‖newtonField (v - y)‖
            ≤ (2 * (1 + Real.sqrt d) / (1 + ‖v‖)) * ‖v - y‖ ^ (1 - (d : ℝ)) := by
          rw [hk]
          exact mul_le_mul_of_nonneg_right hu hxnonneg
        calc ‖inner ℝ (unitDir (toSpace x) - unitDir v) (newtonField (v - y))‖
            ≤ (2 * (1 + Real.sqrt d) / (1 + ‖v‖)) * ‖v - y‖ ^ (1 - (d : ℝ)) :=
              le_trans hstep1 hstep2
          _ = c * g v := by
              simp only [c, g, div_eq_mul_inv]
              ring
      rw [← Real.norm_eq_abs]
      refine le_trans (norm_integral_le_of_norm_le (hgint.const_mul c) hbound) ?_
      rw [integral_const_mul]
    let U : Set (EuclideanSpace ℝ (Fin d)) := ⋃ x ∈ E, cell x
    have hU_sub : U ⊆ Metric.ball 0 R' := by
      intro v hv
      simp only [U, Set.mem_iUnion] at hv
      obtain ⟨x, hx, hvx⟩ := hv
      exact hcell x hx hvx
    have hUbij : ∫ v in U, g v = ∑ x ∈ E, ∫ v in cell x, g v := by
      simp only [U]
      exact integral_biUnion_finset E (fun x _ => measurableSet_cell x)
        (fun x _ y _ hxy => cell_disjoint hxy)
        (fun x hx => hg_int_ball.mono_set (hcell x hx))
    have hU_le : ∫ v in U, g v ≤ C₁ * Real.log (R' + 2) := by
      calc ∫ v in U, g v ≤ ∫ v in Metric.ball 0 R', g v :=
            setIntegral_mono_set hg_int_ball
              (Filter.Eventually.of_forall hg_nonneg)
              (Filter.Eventually.of_forall (fun v hv => hU_sub hv))
        _ ≤ C₁ * Real.log (R' + 2) := hg_val
    calc ∑ x ∈ E, |∫ v in cell x, inner ℝ (unitDir (toSpace x) - unitDir v)
            (newtonField (v - y))|
        ≤ ∑ x ∈ E, c * ∫ v in cell x, g v := Finset.sum_le_sum hterm
      _ = c * ∑ x ∈ E, ∫ v in cell x, g v :=
            (Finset.mul_sum E (fun x => ∫ v in cell x, g v) c).symm
      _ = c * ∫ v in U, g v := by rw [hUbij]
      _ ≤ c * (C₁ * Real.log (R' + 2)) := mul_le_mul_of_nonneg_left hU_le hc_nonneg
      _ = (2 * (1 + Real.sqrt d) * C₁) * Real.log (R' + 2) := by
            simp only [c]
            ring

end CERW.Support.LocalTime
