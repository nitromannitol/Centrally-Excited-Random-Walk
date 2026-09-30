import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Second-order bounds for `log(1 + t)` and `(1 + t)^α`

For `|t| ≤ 1/2`: `|log(1 + t) - t| ≤ 2t²` and `|(1 + t)^α - 1 - αt| ≤ |α| |α - 1| 2^{|α - 2|} t²`.
Applied with `1 + t = |x ± e_i|²/|x|²`, these give the leading term of the central difference of
`log |x|` and of `|x|^{2-d}` in `eq:gradient`.
-/

namespace CERW.Generic.Kernel

/-- For `|u| ≤ 1/2`, the base `1 + u` lies in `[1/2, 3/2]`, so `(1 + u)^(α - 2)` is bounded by
`2^|α - 2|`. -/
lemma rpow_two_sub_le (α : ℝ) {u : ℝ} (hu : |u| ≤ 1 / 2) :
    (1 + u) ^ (α - 2) ≤ 2 ^ |α - 2| := by
  have hu1 : (1 / 2 : ℝ) ≤ 1 + u := by linarith [abs_le.mp hu]
  have hu2 : 1 + u ≤ 3 / 2 := by linarith [abs_le.mp hu]
  have hpos : 0 < 1 + u := by linarith
  rcases le_or_gt (α - 2) 0 with h | h
  · have h1 : (1 + u) ^ (α - 2) ≤ (1 / 2 : ℝ) ^ (α - 2) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hu1 h
    have h2 : (1 / 2 : ℝ) ^ (α - 2) = 2 ^ |α - 2| := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (α - 2),
        abs_of_nonpos h]
    linarith [h1, h2.le]
  · have h1 : (1 + u) ^ (α - 2) ≤ (3 / 2 : ℝ) ^ (α - 2) :=
      Real.rpow_le_rpow hpos.le hu2 h.le
    have h2 : (3 / 2 : ℝ) ^ (α - 2) ≤ 2 ^ (α - 2) :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) h.le
    have h3 : |α - 2| = α - 2 := abs_of_nonneg h.le
    calc (1 + u) ^ (α - 2) ≤ (3 / 2 : ℝ) ^ (α - 2) := h1
      _ ≤ 2 ^ (α - 2) := h2
      _ = 2 ^ |α - 2| := by rw [h3]

/-- Derivative of `v ↦ (1 + v)^p` at `u`, when `1 + u ≠ 0`. -/
lemma hasDerivAt_one_add_rpow (p : ℝ) {u : ℝ} (h : 1 + u ≠ 0) :
    HasDerivAt (fun v : ℝ => (1 + v) ^ p) (p * (1 + u) ^ (p - 1)) u := by
  have houter : HasDerivAt (fun v : ℝ => v ^ p) (p * (1 + u) ^ (p - 1)) (1 + u) :=
    Real.hasDerivAt_rpow_const (x := 1 + u) (p := p) (Or.inl h)
  have hinner : HasDerivAt (fun v : ℝ => 1 + v) 1 u := (hasDerivAt_id u).const_add 1
  have hcomp : HasDerivAt ((fun v : ℝ => v ^ p) ∘ (fun v : ℝ => 1 + v))
      ((p * (1 + u) ^ (p - 1)) * 1) u := houter.comp u hinner
  convert hcomp using 1
  · ext v; rfl
  · rw [mul_one]

/-- For `|s| ≤ 1/2`, the increment `(1 + s)^(α - 1) - 1` is bounded by
`|α - 1| * 2^|α - 2| * |s|`. -/
lemma rpow_sub_one_le (α : ℝ) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |(1 + s) ^ (α - 1) - 1| ≤ |α - 1| * 2 ^ |α - 2| * |s| := by
  let f : ℝ → ℝ := fun u => (1 + u) ^ (α - 1)
  let f' : ℝ → ℝ := fun u => (α - 1) * (1 + u) ^ (α - 2)
  let S : Set ℝ := Set.Icc (-|s|) |s|
  have hS : Convex ℝ S := convex_Icc _ _
  have hmem : ∀ u ∈ S, |u| ≤ 1 / 2 := by
    intro u hu
    simp only [S, Set.mem_Icc] at hu
    linarith [abs_le.mpr hu, hs]
  have hderiv : ∀ u ∈ S, HasDerivWithinAt f (f' u) S u := by
    intro u hu
    have hne : 1 + u ≠ 0 := by linarith [abs_le.mp (hmem u hu)]
    have hd := hasDerivAt_one_add_rpow (α - 1) hne
    rw [show (α - 1) - 1 = α - 2 by ring] at hd
    exact hd.hasDerivWithinAt
  have hbound : ∀ u ∈ S, ‖f' u‖ ≤ |α - 1| * 2 ^ |α - 2| := by
    intro u hu
    have hA : (1 + u) ^ (α - 2) ≤ 2 ^ |α - 2| := rpow_two_sub_le α (hmem u hu)
    have hnn : 0 ≤ (1 + u) ^ (α - 2) :=
      Real.rpow_nonneg (by linarith [abs_le.mp (hmem u hu)]) _
    simp only [f', Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left hA (abs_nonneg _)
  have h0 : (0 : ℝ) ∈ S := by
    simp only [S, Set.mem_Icc]
    exact ⟨by linarith [abs_nonneg s], by linarith [abs_nonneg s]⟩
  have hsS : s ∈ S := by
    simp only [S, Set.mem_Icc]
    exact ⟨neg_abs_le s, le_abs_self s⟩
  have hmvt := hS.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound h0 hsS
  have hf0 : f 0 = 1 := by simp only [f, add_zero, Real.one_rpow]
  simpa only [f, f', hf0, sub_zero, Real.norm_eq_abs] using hmvt

/-- `|log(1 + t) - t| ≤ 2t²` for `|t| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h1 : |t| < 1 := by linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := -t) (by simpa using h1) 1
  rw [Finset.sum_range_one] at h
  have h' : |Real.log (1 + t) - t| ≤ t ^ 2 / (1 - |t|) := by
    convert h using 1
    · simp only [Nat.cast_zero, zero_add, div_one, pow_one, sub_neg_eq_add]
      rw [show -t + Real.log (1 + t) = Real.log (1 + t) - t by ring]
    · rw [abs_neg, show (1 + 1 : ℕ) = 2 by norm_num, sq_abs]
  have hpos : 0 < 1 - |t| := by linarith
  have hkey : t ^ 2 / (1 - |t|) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg (sq_nonneg t) (by linarith : (0 : ℝ) ≤ 1 - 2 * |t|)]
  linarith

/-- `|(1 + t)^α - 1 - αt| ≤ |α| |α - 1| 2^{|α - 2|} t²` for `|t| ≤ 1/2`. -/
theorem abs_one_add_rpow_sub_le (α : ℝ) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |(1 + t) ^ α - 1 - α * t| ≤ |α| * |α - 1| * 2 ^ |α - 2| * t ^ 2 := by
  let K : ℝ := |α| * |α - 1| * 2 ^ |α - 2|
  let g : ℝ → ℝ := fun u => (1 + u) ^ α - 1 - α * u
  let g' : ℝ → ℝ := fun u => α * ((1 + u) ^ (α - 1) - 1)
  let S : Set ℝ := Set.Icc (-|t|) |t|
  have hS : Convex ℝ S := convex_Icc _ _
  have hmem : ∀ u ∈ S, |u| ≤ 1 / 2 := by
    intro u hu
    simp only [S, Set.mem_Icc] at hu
    linarith [abs_le.mpr hu, ht]
  have hderiv : ∀ u ∈ S, HasDerivWithinAt g (g' u) S u := by
    intro u hu
    have hne : 1 + u ≠ 0 := by linarith [abs_le.mp (hmem u hu)]
    have hpow := hasDerivAt_one_add_rpow α hne
    have hlin : HasDerivAt (fun v : ℝ => α * v) α u := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul α
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 u := hasDerivAt_const u 1
    have hg := (hpow.sub hconst).sub hlin
    have hval : α * (1 + u) ^ (α - 1) - 0 - α = g' u := by
      simp only [g', sub_zero]
      ring
    rw [hval] at hg
    exact hg.hasDerivWithinAt
  have hbound : ∀ u ∈ S, ‖g' u‖ ≤ K * |t| := by
    intro u hu
    have hu' : |u| ≤ 1 / 2 := hmem u hu
    have hut : |u| ≤ |t| := by
      simp only [S, Set.mem_Icc] at hu
      exact abs_le.mpr hu
    have hB := rpow_sub_one_le α hu'
    simp only [g', Real.norm_eq_abs, abs_mul]
    calc |α| * |(1 + u) ^ (α - 1) - 1|
        ≤ |α| * (|α - 1| * 2 ^ |α - 2| * |u|) := by gcongr
      _ ≤ |α| * (|α - 1| * 2 ^ |α - 2| * |t|) := by gcongr
      _ = K * |t| := by simp only [K]; ring
  have h0 : (0 : ℝ) ∈ S := by
    simp only [S, Set.mem_Icc]
    exact ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
  have htS : t ∈ S := by
    simp only [S, Set.mem_Icc]
    exact ⟨neg_abs_le t, le_abs_self t⟩
  have hmvt := hS.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound h0 htS
  have hg0 : g 0 = 0 := by
    simp only [g, add_zero, mul_zero, Real.one_rpow]
    ring
  calc |(1 + t) ^ α - 1 - α * t| = ‖g t - g 0‖ := by
        simp only [g, hg0, Real.norm_eq_abs, sub_zero]
    _ ≤ K * |t| * |t - 0| := hmvt
    _ = K * t ^ 2 := by rw [sub_zero, mul_assoc, abs_mul_abs_self]; ring

end CERW.Generic.Kernel
