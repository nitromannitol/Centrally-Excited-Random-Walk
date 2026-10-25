module

public import CERW.Model.Potential
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-!
# Regularity and bounds for the potential kernel

The kernel in `eq:potential-intro` is smooth in its evaluation point away from its pole.
Positive separation gives bounds suitable for integration on bounded measurable sets.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The integrand of the actual potential in `eq:potential-intro`. -/
noncomputable def potentialKernel {d : ℕ}
    (v y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d

/-- For fixed evaluation point, the potential kernel is measurable in its pole. -/
theorem measurable_potentialKernel {d : ℕ} (y : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun v => potentialKernel v y) := by
  unfold potentialKernel unitDir
  fun_prop

/-- The potential kernel is smooth in the evaluation point away from its pole. -/
theorem contDiffAt_potentialKernel {d : ℕ} {v y : EuclideanSpace ℝ (Fin d)}
    (hvy : v ≠ y) : ContDiffAt ℝ ⊤ (potentialKernel v) y := by
  have hs : ContDiffAt ℝ ⊤ (fun z : EuclideanSpace ℝ (Fin d) => v - z) y :=
    contDiffAt_const.sub contDiffAt_id
  exact (contDiffAt_const.inner ℝ hs).div ((hs.norm ℝ (sub_ne_zero.mpr hvy)).pow d)
    (pow_ne_zero d (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvy)))

/-- The first spatial derivative of the potential kernel, in quotient form. -/
theorem fderiv_potentialKernel_apply {d : ℕ} {v y : EuclideanSpace ℝ (Fin d)}
    (hvy : v ≠ y) (h : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (potentialKernel v) y h =
      (-inner ℝ (unitDir v) h * ‖v - y‖ ^ d +
        inner ℝ (unitDir v) (v - y) *
          ((d : ℝ) * ‖v - y‖ ^ (d - 1) * inner ℝ (v - y) h / ‖v - y‖)) /
        (‖v - y‖ ^ d) ^ 2 := by
  have hn : ‖v - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvy)
  have hs := (hasFDerivAt_const (𝕜 := ℝ) v y).sub (hasFDerivAt_id y)
  have hnorm := hs.norm_sq.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at hnorm
  have hnum := (hasFDerivAt_const (𝕜 := ℝ) (unitDir v) y).inner ℝ hs
  have hi := (hasDerivAt_inv (pow_ne_zero d hn)).comp_hasFDerivAt y (hnorm.pow d)
  have hk := hnum.mul hi
  have heq := congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => L h) hk.fderiv
  change fderiv ℝ (potentialKernel v) y h = _ at heq
  rw [heq]
  simp [ContinuousLinearMap.comp_apply, inner_sub_left, inner_sub_right]
  field_simp
  ring

/-- The potential kernel is jointly smooth when the pole and its direction are nonsingular. -/
theorem contDiffAt_joint_potentialKernel {d : ℕ}
    {v y : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) (hvy : v ≠ y) :
    ContDiffAt ℝ ⊤
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        potentialKernel p.2 p.1) (y, v) := by
  have hdir : ContDiffAt ℝ ⊤
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => unitDir p.2)
      (y, v) :=
    ((contDiffAt_snd.norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul contDiffAt_snd
  have hs : ContDiffAt ℝ ⊤
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.2 - p.1)
      (y, v) := contDiffAt_snd.sub contDiffAt_fst
  exact (hdir.inner ℝ hs).div ((hs.norm ℝ (sub_ne_zero.mpr hvy)).pow d)
    (pow_ne_zero d (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvy)))

/-- Separation from the pole bounds the potential kernel on a bounded spatial domain. -/
theorem norm_potentialKernel_le {d : ℕ} {v y : EuclideanSpace ℝ (Fin d)}
    {δ R : ℝ} (hδ : 0 < δ) (hsep : δ ≤ ‖v - y‖) (hv : ‖v‖ ≤ R) :
    ‖potentialKernel v y‖ ≤ (R + ‖y‖) / δ ^ d := by
  have hnum : ‖inner ℝ (unitDir v) (v - y)‖ ≤ R + ‖y‖ := by
    calc
      ‖inner ℝ (unitDir v) (v - y)‖ ≤ ‖unitDir v‖ * ‖v - y‖ :=
        norm_inner_le_norm _ _
      _ ≤ 1 * ‖v - y‖ := mul_le_mul_of_nonneg_right (norm_unitDir_le v) (norm_nonneg _)
      _ ≤ R + ‖y‖ := by simpa only [one_mul] using
        (norm_sub_le v y).trans (by gcongr)
  rw [potentialKernel, norm_div, norm_pow, norm_norm]
  exact div_le_div₀ (by linarith [norm_nonneg v, norm_nonneg y]) hnum (pow_pos hδ d)
    (pow_le_pow_left₀ hδ.le hsep d)

/-- Every point outside the closure has a ball uniformly separated from all poles in the set. -/
theorem exists_potential_separation {d : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ closure E) :
    ∃ δ > 0, ∀ v ∈ E, ∀ y ∈ Metric.ball x δ, δ ≤ ‖v - y‖ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x hx
  refine ⟨r / 2, by linarith, ?_⟩
  intro v hv y hy
  have hvx : r ≤ ‖v - x‖ := by
    by_contra! h
    exact hball (by simpa only [Metric.mem_ball, dist_eq_norm] using h) (subset_closure hv)
  have hyx : ‖y - x‖ < r / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have htri := norm_sub_le_norm_sub_add_norm_sub v y x
  linarith

end CERW.LimitShapes.Curvature
