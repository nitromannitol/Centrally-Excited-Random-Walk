module

public import CERW.LimitShapes.Curvature.PotentialKernel
public import CERW.LimitShapes.Curvature.HarmonicKernel

@[expose] public section

/-!
# Laplacian of the signed potential kernel

The linear factor in `eq:potential-intro` cancels the radial Laplacian off the pole.
-/

namespace CERW.LimitShapes.Curvature

open CERW InnerProductSpace Laplacian Filter Topology

/-- The diagonal Hessian of an affine factor times a smooth scalar function. -/
lemma fderiv_fderiv_inner_mul {d : ℕ} (a v y w : EuclideanSpace ℝ (Fin d))
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiffAt ℝ 2 g y) :
    fderiv ℝ (fderiv ℝ (fun z => inner ℝ a (v - z) * g z)) y w w =
      inner ℝ a (v - y) * fderiv ℝ (fderiv ℝ g) y w w -
        2 * inner ℝ a w * fderiv ℝ g y w := by
  let A := -innerSL ℝ a
  have hl (z : EuclideanSpace ℝ (Fin d)) :
      HasFDerivAt (fun z => inner ℝ a (v - z)) A z := by
    convert (innerSL ℝ a).hasFDerivAt.comp z
      ((hasFDerivAt_const v z).sub (hasFDerivAt_id z)) using 1 <;>
      ext u <;> simp [A]
  have hdg := hg.differentiableAt (by norm_num)
  have hdg' := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : fderiv ℝ (fun z => inner ℝ a (v - z) * g z) =ᶠ[𝓝 y]
      fun z => inner ℝ a (v - z) • fderiv ℝ g z + g z • A := by
    filter_upwards [hg.eventually (by norm_num)] with z hz
    rw [fderiv_fun_mul (hl z).differentiableAt
      (hz.differentiableAt (by norm_num)), (hl z).fderiv]
  have hh := ((hl y).smul hdg'.hasFDerivAt).add
    (hdg.hasFDerivAt.smul_const A)
  change HasFDerivAt
    (fun z => inner ℝ a (v - z) • fderiv ℝ g z + g z • A) _ y at hh
  rw [he.fderiv_eq, hh.fderiv]
  simp [A, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-- The affine radial product has an explicit Laplacian away from its pole. -/
lemma laplacian_inner_mul_sqDist_rpow {d : ℕ} (p : ℝ)
    (a v y : EuclideanSpace ℝ (Fin d)) (hy : y ≠ v) :
    laplacian (fun z => inner ℝ a (v - z) * (‖z - v‖ ^ 2) ^ p) y =
      2 * p * (2 * p + d) * inner ℝ a (v - y) *
        (‖y - v‖ ^ 2) ^ (p - 1) := by
  have hg : ContDiffAt ℝ 2 (fun z => (‖z - v‖ ^ 2) ^ p) y :=
    ((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ).rpow_const_of_ne
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy)))
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ e]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_inner_mul a v y _ hg]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hr := laplacian_sqDist_rpow p v y hy
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ e] at hr
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hr
  rw [hr]
  simp_rw [(hasFDerivAt_sqDist_rpow p v y hy).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  have hs : (∑ i, 2 * inner ℝ a (e i) *
      (p * (‖y - v‖ ^ 2) ^ (p - 1) * (2 * inner ℝ (y - v) (e i)))) =
      4 * p * (‖y - v‖ ^ 2) ^ (p - 1) * inner ℝ a (y - v) := by
    calc
      _ = 4 * p * (‖y - v‖ ^ 2) ^ (p - 1) *
          ∑ i, inner ℝ a (e i) * inner ℝ (e i) (y - v) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm (e i) (y - v)]
        ring
      _ = _ := by rw [e.sum_inner_mul_inner]
  rw [hs]
  have hn : inner ℝ a (y - v) = -inner ℝ a (v - y) := by
    rw [← inner_neg_right, neg_sub]
  rw [hn]
  ring

/-- The signed potential kernel in `eq:potential-intro` is harmonic away from its pole. -/
theorem harmonicAt_potentialKernel {d : ℕ}
    (v y : EuclideanSpace ℝ (Fin d)) (hy : y ≠ v) :
    HarmonicAt (potentialKernel v) y := by
  let p : ℝ := -(d : ℝ) / 2
  have he : potentialKernel v =
      (fun z => inner ℝ (unitDir v) (v - z) * (‖z - v‖ ^ 2) ^ p) := by
    funext z
    rw [potentialKernel, norm_sub_rev, div_eq_mul_inv]
    congr 1
    rw [← Real.rpow_natCast (‖z - v‖) 2, ← Real.rpow_mul (norm_nonneg _)]
    simp only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * p = -(d : ℝ) by dsimp [p]; ring]
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  rw [he]
  constructor
  · exact (contDiffAt_const.inner ℝ (contDiffAt_const.sub contDiffAt_id)).mul
      (((contDiffAt_id.sub contDiffAt_const).norm_sq ℝ).rpow_const_of_ne
        (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))))
  · filter_upwards [eventually_ne_nhds hy] with z hz
    rw [laplacian_inner_mul_sqDist_rpow p (unitDir v) v z hz]
    have hp : 2 * p + d = 0 := by dsimp [p]; ring
    simp only [hp, mul_zero, zero_mul, Pi.zero_apply]

end CERW.LimitShapes.Curvature
