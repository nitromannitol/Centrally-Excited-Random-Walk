import CERW.Generic.Lattice.Packing

/-!
# Fractional planar packing

A shell estimate for the fractional weight used in the near-pole bound of `lem:contact`.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb

/-- The inverse square root sum is bounded by a telescoping square root sum. -/
private lemma sum_inv_sqrt_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (Real.sqrt (1 + (k : ℝ)))⁻¹ ≤
      2 * Real.sqrt (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have ha : 0 < Real.sqrt (1 + ((n + 1 : ℕ) : ℝ)) := by positivity
    have hb : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
    have hab : Real.sqrt (n + 1) ≤ Real.sqrt (1 + ((n + 1 : ℕ) : ℝ)) := by
      apply Real.sqrt_le_sqrt
      push_cast
      linarith
    have ha2 := Real.sq_sqrt (by positivity : 0 ≤ 1 + ((n + 1 : ℕ) : ℝ))
    have hb2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
    have hstep : (Real.sqrt (1 + ((n + 1 : ℕ) : ℝ)))⁻¹ ≤
        2 * (Real.sqrt (1 + ((n + 1 : ℕ) : ℝ)) - Real.sqrt (n + 1)) := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ ha).2
      have := sq_nonneg
        (Real.sqrt (1 + ((n + 1 : ℕ) : ℝ)) - Real.sqrt (n + 1))
      have hd : (1 : ℝ) + ((n + 1 : ℕ) : ℝ) - (n + 1) = 1 := by
        push_cast
        ring
      nlinarith only [ha2, hb2, this, hd]
    have heq : (1 : ℝ) + ((n + 1 : ℕ) : ℝ) = ↑(n + 1) + 1 := by push_cast; ring
    rw [← heq]
    linarith

/-- The planar fractional weight in a ball has square root growth. -/
theorem sum_planar_fractional_le (S : Finset (Site 2)) (y : Site 2)
    (R : ℝ) (hR : 0 ≤ R) (hS : ∀ x ∈ S, euclidNorm (x - y) ≤ R) :
    ∑ x ∈ S, ((1 + euclidNorm (x - y)) *
      Real.sqrt (1 + euclidNorm (x - y)))⁻¹ ≤ 17 * Real.sqrt (R + 1) := by
  classical
  let f : Site 2 → ℝ := fun z =>
    ((1 + (supNorm z : ℝ)) * Real.sqrt (1 + (supNorm z : ℝ)))⁻¹
  have hpoint (z : Site 2) :
      ((1 + euclidNorm z) * Real.sqrt (1 + euclidNorm z))⁻¹ ≤ f z := by
    have hn := euclidNorm_nonneg z
    dsimp [f]
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    exact mul_le_mul (by linarith [supNorm_le_euclidNorm z])
      (Real.sqrt_le_sqrt (by linarith [supNorm_le_euclidNorm z])) (by positivity)
      (by positivity)
  have hsub : S.image (fun x => x - y) ⊆ boxFinset (0 : Site 2) ⌊R⌋₊ := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [mem_boxFinset_zero_iff]
    exact Nat.le_floor ((supNorm_le_euclidNorm _).trans (hS x hx))
  have hsum : ∑ x ∈ S, f (x - y) ≤ ∑ z ∈ boxFinset (0 : Site 2) ⌊R⌋₊, f z := by
    rw [← Finset.sum_image (f := f)
      (fun a _ b _ h => sub_left_injective h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by dsimp [f]; positivity)
  have hbox := sum_box_radial_le (d := 2)
    (fun k => ((1 + (k : ℝ)) * Real.sqrt (1 + (k : ℝ)))⁻¹)
    (fun _ => by positivity) ⌊R⌋₊
  have hterm (k : ℕ) :
      2 * (2 : ℝ) * (2 * (k : ℝ) + 1) ^ (2 - 1) *
        ((1 + (k : ℝ)) * Real.sqrt (1 + (k : ℝ)))⁻¹ ≤
          8 * (Real.sqrt (1 + (k : ℝ)))⁻¹ := by
    have hk : 0 < 1 + (k : ℝ) := by positivity
    have hs : 0 < Real.sqrt (1 + (k : ℝ)) := by positivity
    norm_num only [Nat.reduceSub, pow_one]
    have heq : 8 * (Real.sqrt (1 + (k : ℝ)))⁻¹ =
        (8 * (1 + (k : ℝ))) /
          ((1 + (k : ℝ)) * Real.sqrt (1 + (k : ℝ))) := by
      field_simp
    rw [heq, ← div_eq_mul_inv]
    exact (div_le_div_iff_of_pos_right (mul_pos hk hs)).2 (by linarith)
  have hrad := Finset.sum_le_sum (s := Finset.Icc 1 ⌊R⌋₊) (fun k _ => hterm k)
  rw [← Finset.mul_sum] at hrad
  have hs := sum_inv_sqrt_le ⌊R⌋₊
  have hf : Real.sqrt (⌊R⌋₊ + 1) ≤ Real.sqrt (R + 1) :=
    Real.sqrt_le_sqrt (by have := Nat.floor_le hR; linarith)
  have hone : 1 ≤ Real.sqrt (R + 1) := by
    simpa using Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ R + 1)
  calc
    _ ≤ ∑ x ∈ S, f (x - y) := Finset.sum_le_sum fun x _ => hpoint (x - y)
    _ ≤ ∑ z ∈ boxFinset (0 : Site 2) ⌊R⌋₊, f z := hsum
    _ ≤ 17 * Real.sqrt (R + 1) := by
      dsimp [f] at *
      norm_num only [Nat.cast_zero, add_zero, Real.sqrt_one, mul_one, inv_one] at hbox
      nlinarith

end CERW.LimitShapes.Energy
