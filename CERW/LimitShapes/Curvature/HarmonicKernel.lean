import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Harmonicity of the Newton kernel

The radial power in `eq:curvature-improved` has zero Laplacian away from its pole.
-/

namespace CERW.LimitShapes.Curvature

open InnerProductSpace Laplacian Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The derivative of a power of the squared distance away from its pole. -/
lemma hasFDerivAt_sqDist_rpow (p : ℝ) (v y : V) (hy : y ≠ v) :
    HasFDerivAt (fun z => (‖z - v‖ ^ 2) ^ p)
      ((p * (‖y - v‖ ^ 2) ^ (p - 1)) • (2 • innerSL ℝ (y - v))) y := by
  have hq := ((hasFDerivAt_id y).sub_const v).norm_sq
  exact (Real.hasDerivAt_rpow_const (Or.inl (pow_ne_zero 2
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))))).comp_hasFDerivAt y hq

/-- The Hessian of a power of squared distance on a diagonal. -/
lemma fderiv_fderiv_sqDist_rpow_apply (p : ℝ) (v y w : V) (hy : y ≠ v) :
    fderiv ℝ (fderiv ℝ (fun z => (‖z - v‖ ^ 2) ^ p)) y w w =
      4 * p * (p - 1) * (‖y - v‖ ^ 2) ^ (p - 2) *
        (inner ℝ (y - v) w) ^ 2 +
      2 * p * (‖y - v‖ ^ 2) ^ (p - 1) * ‖w‖ ^ 2 := by
  have hq0 : ‖y - v‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))
  have he : fderiv ℝ (fun z => (‖z - v‖ ^ 2) ^ p) =ᶠ[𝓝 y]
      fun z => (p * (‖z - v‖ ^ 2) ^ (p - 1)) • (2 • innerSL ℝ (z - v)) := by
    filter_upwards [eventually_ne_nhds hy] with z hz
    exact (hasFDerivAt_sqDist_rpow p v z hz).fderiv
  have hc := ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hq0)).comp_hasFDerivAt y
    (((hasFDerivAt_id y).sub_const v).norm_sq)).const_mul p
  have hl := ((innerSL ℝ (E := V)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).sub_const v)).const_smul (2 : ℕ)
  have hh := hc.smul hl
  change HasFDerivAt (fun z : V => (p * (‖z - v‖ ^ 2) ^ (p - 1)) •
    ((2 : ℕ) • innerSL ℝ (z - v))) _ y at hh
  rw [he.fderiv_eq, hh.fderiv]
  simp only [two_smul, Function.comp_def, id, Pi.add_apply, innerSL_apply_apply,
    add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [show p - 1 - 1 = p - 2 by ring]
  ring_nf
  simp only [innerSL, LinearMap.mkContinuous₂_apply, innerₛₗ_apply_apply,
    real_inner_self_eq_norm_sq]
  ring

/-- Powers of squared distance have the radial Laplacian formula. -/
lemma laplacian_sqDist_rpow {d : ℕ} (p : ℝ)
    (v y : EuclideanSpace ℝ (Fin d)) (hy : y ≠ v) :
    laplacian (fun z => (‖z - v‖ ^ 2) ^ p) y =
      2 * p * (2 * (p - 1) + d) * (‖y - v‖ ^ 2) ^ (p - 1) := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ e]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_sqDist_rpow_apply p v y _ hy]
  have he : ∀ i, ‖e i‖ = 1 := e.norm_eq_one
  simp_rw [he, one_pow, mul_one]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, e.sum_sq_inner_left]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hq : 0 < ‖y - v‖ ^ 2 := sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))
  have hp : (‖y - v‖ ^ 2) ^ (p - 2) * ‖y - v‖ ^ 2 =
      (‖y - v‖ ^ 2) ^ (p - 1) := by
    conv_lhs => arg 2; rw [← Real.rpow_one (‖y - v‖ ^ 2)]
    rw [← Real.rpow_add hq]
    congr 1
    ring
  calc
    _ = 4 * p * (p - 1) *
        ((‖y - v‖ ^ 2) ^ (p - 2) * ‖y - v‖ ^ 2) +
        d * (2 * p * (‖y - v‖ ^ 2) ^ (p - 1)) := by ring
    _ = _ := by rw [hp]; ring

/-- The scalar curvature kernel is harmonic away from its pole. -/
theorem harmonicAt_curvatureKernel {d : ℕ}
    (v y : EuclideanSpace ℝ (Fin d)) (hy : y ≠ v) :
    HarmonicAt (fun z => ‖v - z‖ ^ ((2 : ℝ) - d) / ‖v‖) y := by
  let p : ℝ := ((2 : ℝ) - d) / 2
  have he : (fun z => ‖v - z‖ ^ ((2 : ℝ) - d)) =
      (fun z => (‖z - v‖ ^ 2) ^ p) := by
    funext z
    rw [norm_sub_rev, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    dsimp [p]
    ring
  have hh : HarmonicAt (fun z => (‖z - v‖ ^ 2) ^ p) y := by
    constructor
    · exact (((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ).rpow_const_of_ne
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))))
    · filter_upwards [eventually_ne_nhds hy] with z hz
      rw [laplacian_sqDist_rpow p v z hz]
      have hp : 2 * (p - 1) + d = 0 := by dsimp [p]; ring
      simp only [hp, mul_zero, zero_mul, Pi.zero_apply]
  have hh' := hh.const_smul (c := ‖v‖⁻¹)
  change HarmonicAt (fun z => ‖v‖⁻¹ * (‖z - v‖ ^ 2) ^ p) y at hh'
  simp_rw [← congrFun he] at hh'
  simpa only [div_eq_mul_inv, mul_comm] using hh'

end CERW.LimitShapes.Curvature
