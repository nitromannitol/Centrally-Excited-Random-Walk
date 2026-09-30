import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exponent arithmetic for the Hausdorff bound

With `N = n^{1/(d+1)}`, the normalized outer excess `Q^{1/d} L` of `eq:sandwich` is
`n^{-1/12} L^{5/4}` in the plane, where `Q = (L/N)^{1/2}`. For `d ≥ 3`, where
`Q = (L/N)^{d/(2d-1)}`, it is `n^{-1/((d+1)(2d-1))} L^{2d/(2d-1)}` (`eq:hausdorff`). The planar
inner deficit `N Q` is `n^{1/6} √L` (the remark after `eq:hausdorff`).
-/

namespace CERW.Support.Main

/-- In the plane, `Q^{1/2} L = n^{-1/12} L^{5/4}` with `N = n^{1/3}` and `Q = (L/N)^{1/2}`. -/
theorem planar_excess_rate {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    ((L / n ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2) * L
      = n ^ (-(1 : ℝ) / 12) * L ^ ((5 : ℝ) / 4) := by
  have hn3 : 0 < n ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hn _
  have hbase : 0 < L / n ^ ((1 : ℝ) / 3) := div_pos hL hn3
  have hLL : L ^ ((1 : ℝ) / 4) * L = L ^ ((5 : ℝ) / 4) := by
    nth_rewrite 2 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    norm_num
  rw [← Real.rpow_mul (le_of_lt hbase) ((1 : ℝ) / 2) ((1 : ℝ) / 2)]
  rw [Real.div_rpow (le_of_lt hL) (le_of_lt hn3)]
  rw [← Real.rpow_mul (le_of_lt hn) ((1 : ℝ) / 3) (((1 : ℝ) / 2) * ((1 : ℝ) / 2))]
  have e1 : ((1 : ℝ) / 2) * ((1 : ℝ) / 2) = (1 : ℝ) / 4 := by norm_num
  have e2 : ((1 : ℝ) / 3) * (((1 : ℝ) / 2) * ((1 : ℝ) / 2)) = (1 : ℝ) / 12 := by norm_num
  rw [e2, e1]
  have hnneg : n ^ (-(1 : ℝ) / 12) = (n ^ ((1 : ℝ) / 12))⁻¹ := by
    rw [show (-(1 : ℝ) / 12) = -((1 : ℝ) / 12) by ring]
    exact Real.rpow_neg (le_of_lt hn) ((1 : ℝ) / 12)
  rw [hnneg]
  rw [div_eq_mul_inv, mul_comm (L ^ ((1 : ℝ) / 4)) (n ^ ((1 : ℝ) / 12))⁻¹, mul_assoc, hLL]

/-- For `d ≥ 1`, `Q^{1/d} L = n^{-1/((d+1)(2d-1))} L^{2d/(2d-1)}` with `N = n^{1/(d+1)}` and
`Q = (L/N)^{d/(2d-1)}`. -/
theorem excess_rate {d : ℕ} (hd : 1 ≤ d) {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    ((L / n ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1))) ^ ((1 : ℝ) / d) * L
      = n ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1))) * L ^ ((2 * d : ℝ) / (2 * d - 1)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdnz : (d : ℝ) ≠ 0 := by positivity
  have hden : 2 * (d : ℝ) - 1 ≠ 0 := by linarith
  have hnA : 0 < n ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hn _
  have hbase : 0 < L / n ^ ((1 : ℝ) / (d + 1)) := div_pos hL hnA
  have e1 : ((d : ℝ) / (2 * d - 1)) * ((1 : ℝ) / d) = (1 : ℝ) / (2 * d - 1) := by
    field_simp [hdnz, hden]
  have e2 : ((1 : ℝ) / (d + 1)) * (((d : ℝ) / (2 * d - 1)) * ((1 : ℝ) / d))
      = (1 : ℝ) / ((d + 1) * (2 * d - 1)) := by
    rw [e1]
    field_simp [hden]
  have hLL : L ^ ((1 : ℝ) / (2 * d - 1)) * L = L ^ ((2 * d : ℝ) / (2 * d - 1)) := by
    nth_rewrite 2 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    congr 1
    field_simp [hden]
    ring
  have hnneg : n ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
      = (n ^ ((1 : ℝ) / ((d + 1) * (2 * d - 1))))⁻¹ := by
    rw [show (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
        = -((1 : ℝ) / ((d + 1) * (2 * d - 1))) by ring]
    exact Real.rpow_neg (le_of_lt hn) _
  rw [← Real.rpow_mul (le_of_lt hbase) ((d : ℝ) / (2 * d - 1)) ((1 : ℝ) / d)]
  rw [Real.div_rpow (le_of_lt hL) (le_of_lt hnA)]
  rw [← Real.rpow_mul (le_of_lt hn) ((1 : ℝ) / (d + 1))
      (((d : ℝ) / (2 * d - 1)) * ((1 : ℝ) / d))]
  rw [e2, e1]
  rw [hnneg]
  rw [div_eq_mul_inv, mul_comm (L ^ ((1 : ℝ) / (2 * d - 1)))
      (n ^ ((1 : ℝ) / ((d + 1) * (2 * d - 1))))⁻¹, mul_assoc, hLL]

/-- In the plane, `N Q = n^{1/6} √L` with `N = n^{1/3}` and `Q = (L/N)^{1/2}`. -/
theorem planar_inner_rate {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    n ^ ((1 : ℝ) / 3) * (L / n ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2)
      = n ^ ((1 : ℝ) / 6) * Real.sqrt L := by
  have hn3 : 0 < n ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hn _
  have h16 : ((1 : ℝ) / 3) * ((1 : ℝ) / 2) = (1 : ℝ) / 6 := by norm_num
  have hninv : (n ^ ((1 : ℝ) / 6))⁻¹ = n ^ (-((1 : ℝ) / 6)) :=
    (Real.rpow_neg (le_of_lt hn) ((1 : ℝ) / 6)).symm
  have hexp : (1 : ℝ) / 3 + -((1 : ℝ) / 6) = (1 : ℝ) / 6 := by norm_num
  have hQ : (L / n ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2)
      = L ^ ((1 : ℝ) / 2) / n ^ ((1 : ℝ) / 6) := by
    rw [Real.div_rpow (le_of_lt hL) (le_of_lt hn3)]
    rw [← Real.rpow_mul (le_of_lt hn) ((1 : ℝ) / 3) ((1 : ℝ) / 2), h16]
  have hratio : n ^ ((1 : ℝ) / 3) / n ^ ((1 : ℝ) / 6) = n ^ ((1 : ℝ) / 6) := by
    rw [div_eq_mul_inv, hninv, ← Real.rpow_add hn, hexp]
  rw [hQ, Real.sqrt_eq_rpow]
  calc n ^ ((1 : ℝ) / 3) * (L ^ ((1 : ℝ) / 2) / n ^ ((1 : ℝ) / 6))
      = (n ^ ((1 : ℝ) / 3) / n ^ ((1 : ℝ) / 6)) * L ^ ((1 : ℝ) / 2) := by ring
    _ = n ^ ((1 : ℝ) / 6) * L ^ ((1 : ℝ) / 2) := by rw [hratio]

end CERW.Support.Main
