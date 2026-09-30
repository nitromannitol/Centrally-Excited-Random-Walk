import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Increments of the radial profile

The radial profile of the lattice potential kernel is `(2/π) log r` in the plane and
`-(2/((d-2) ω_d)) r^{2-d}` for `d ≥ 3`. Over `[s, r]` it increases by an amount comparable to
`(r - s)` times its derivative at an endpoint. In the plane,
`(r-s)/r ≤ log r - log s ≤ (r-s)/s`. For `k > 0`,
`(r-s) r^{-k-1} ≤ (s^{-k} - r^{-k})/k ≤ (r-s) s^{-k-1}`. These give the level-set property
`eq:levelsets` of the radial test.
-/

namespace CERW.Generic.Young

/-- For `0 < s ≤ r`: `(r - s)/r ≤ log r - log s ≤ (r - s)/s`. -/
theorem log_sub_log_mem_Icc {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    (r - s) / r ≤ Real.log r - Real.log s ∧ Real.log r - Real.log s ≤ (r - s) / s := by
  have hr : 0 < r := lt_of_lt_of_le hs hsr
  have hrne : r ≠ 0 := hr.ne'
  have hsne : s ≠ 0 := hs.ne'
  have ht : 0 < r / s := div_pos hr hs
  rw [← Real.log_div hrne hsne]
  constructor
  · calc (r - s) / r = 1 - (r / s)⁻¹ := by rw [inv_div]; field_simp
      _ ≤ Real.log (r / s) := Real.one_sub_inv_le_log_of_pos ht
  · calc Real.log (r / s) ≤ r / s - 1 := Real.log_le_sub_one_of_pos ht
      _ = (r - s) / s := by field_simp

/-- For `k > 0` and `0 < s ≤ r`:
`(r - s) r^{-k-1} ≤ (s^{-k} - r^{-k})/k ≤ (r - s) s^{-k-1}`. -/
theorem rpow_neg_sub_mem_Icc {k s r : ℝ} (hk : 0 < k) (hs : 0 < s) (hsr : s ≤ r) :
    (r - s) * r ^ (-k - 1) ≤ (s ^ (-k) - r ^ (-k)) / k ∧
      (s ^ (-k) - r ^ (-k)) / k ≤ (r - s) * s ^ (-k - 1) := by
  rcases eq_or_lt_of_le hsr with rfl | hlt
  · simp
  have hz : -k - 1 ≤ 0 := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-k)) (Set.Icc s r) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hs.trans_le hx.1)))
  have hderiv : ∀ x ∈ Set.Ioo s r,
      HasDerivAt (fun t : ℝ => t ^ (-k)) (-k * x ^ (-k - 1)) x := by
    intro x hx
    have hxpos : 0 < x := hs.trans hx.1
    exact Real.hasDerivAt_rpow_const (x := x) (p := -k) (Or.inl (ne_of_gt hxpos))
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (f := fun t : ℝ => t ^ (-k))
    (f' := fun t : ℝ => -k * t ^ (-k - 1)) hlt hcont hderiv
  have hcs : s < c := hc.1
  have hcr : c < r := hc.2
  have hcpos : 0 < c := hs.trans hcs
  have hrs : 0 ≤ r - s := sub_nonneg.mpr hsr
  have hne : r - s ≠ 0 := (sub_pos.mpr hlt).ne'
  have hmul : r ^ (-k) - s ^ (-k) = -k * c ^ (-k - 1) * (r - s) :=
    (div_eq_iff hne).mp hc'.symm
  have hmid : (s ^ (-k) - r ^ (-k)) / k = (r - s) * c ^ (-k - 1) := by
    have h2 : s ^ (-k) - r ^ (-k) = -(r ^ (-k) - s ^ (-k)) := by ring
    rw [h2, hmul]
    field_simp
  have hlow : r ^ (-k - 1) ≤ c ^ (-k - 1) :=
    Real.rpow_le_rpow_of_nonpos hcpos hcr.le hz
  have hhigh : c ^ (-k - 1) ≤ s ^ (-k - 1) :=
    Real.rpow_le_rpow_of_nonpos hs hcs.le hz
  constructor
  · rw [hmid]
    exact mul_le_mul_of_nonneg_left hlow hrs
  · rw [hmid]
    exact mul_le_mul_of_nonneg_left hhigh hrs

end CERW.Generic.Young
