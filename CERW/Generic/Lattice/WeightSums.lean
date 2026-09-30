import LatticeProb.Walk.Ball
import LatticeProb.Walk.Shells

/-!
# Logarithmic lattice sums

The weight `(1 + |z|)^{-d}` summed over the lattice ball of radius `R` grows like `log R`.
This is the source of every logarithm in `lem:local` and in the planar contact estimates.
-/

namespace CERW.Generic.Lattice

open LatticeProb

variable {d : ℕ}

/-- For `k ≥ 1`, the `k`-th radial term of the lattice box sum is at most
`d 2^d / (k + 1)`. -/
lemma radial_term_le (hd : 1 ≤ d) {k : ℕ} (hk : 1 ≤ k) :
    2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-(d : ℝ))
      ≤ (d : ℝ) * (2 : ℝ) ^ d * (1 / ((k : ℝ) + 1)) := by
  have hbase : (0 : ℝ) < 1 + (k : ℝ) := by positivity
  have hstep : (2 * (k : ℝ) + 1) ^ (d - 1)
      ≤ (2 : ℝ) ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1) := by
    calc (2 * (k : ℝ) + 1) ^ (d - 1)
        ≤ (2 * (1 + (k : ℝ))) ^ (d - 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (2 : ℝ) ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1) := by rw [mul_pow]
  have hprod : (1 + (k : ℝ)) ^ (d - 1) * (1 + (k : ℝ)) ^ (-(d : ℝ))
      = 1 / (1 + (k : ℝ)) := by
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have h : (d - 1 : ℕ) + 1 = d := by omega
      have := congrArg (fun m : ℕ => (m : ℝ)) h
      push_cast at this
      linarith
    calc (1 + (k : ℝ)) ^ (d - 1) * (1 + (k : ℝ)) ^ (-(d : ℝ))
        = (1 + (k : ℝ)) ^ (((d - 1 : ℕ) : ℝ))
            * (1 + (k : ℝ)) ^ (-(d : ℝ)) := by rw [Real.rpow_natCast]
      _ = (1 + (k : ℝ)) ^ (((d - 1 : ℕ) : ℝ) + (-(d : ℝ))) := by
          rw [← Real.rpow_add hbase]
      _ = (1 + (k : ℝ)) ^ (-1 : ℝ) := by
          rw [hcast]
          ring_nf
      _ = 1 / (1 + (k : ℝ)) := by rw [Real.rpow_neg_one]; ring
  have h2d : 2 * (2 : ℝ) ^ (d - 1) = (2 : ℝ) ^ d := by
    calc 2 * (2 : ℝ) ^ (d - 1) = (2 : ℝ) ^ 1 * (2 : ℝ) ^ (d - 1) := by norm_num
      _ = (2 : ℝ) ^ (1 + (d - 1)) := by rw [← pow_add]
      _ = (2 : ℝ) ^ d := by congr 1; omega
  have h1 : 2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-(d : ℝ))
      ≤ 2 * (d : ℝ) * ((2 : ℝ) ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1))
          * (1 + (k : ℝ)) ^ (-(d : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstep (by positivity))
      (Real.rpow_nonneg (le_of_lt hbase) _)
  calc 2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-(d : ℝ))
      ≤ 2 * (d : ℝ) * ((2 : ℝ) ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1))
          * (1 + (k : ℝ)) ^ (-(d : ℝ)) := h1
    _ = 2 * (d : ℝ) * (2 : ℝ) ^ (d - 1)
          * ((1 + (k : ℝ)) ^ (d - 1) * (1 + (k : ℝ)) ^ (-(d : ℝ))) := by ring
    _ = 2 * (d : ℝ) * (2 : ℝ) ^ (d - 1) * (1 / (1 + (k : ℝ))) := by rw [hprod]
    _ = (d : ℝ) * (2 * (2 : ℝ) ^ (d - 1)) * (1 / (1 + (k : ℝ))) := by ring
    _ = (d : ℝ) * (2 : ℝ) ^ d * (1 / (1 + (k : ℝ))) := by rw [h2d]
    _ = (d : ℝ) * (2 : ℝ) ^ d * (1 / ((k : ℝ) + 1)) := by ring

/-- The radial weight sum over the box of radius `n` is at most
`1 + d 2^d log (n + 1)`. -/
lemma sum_box_rpow_neg_le (hd : 1 ≤ d) (n : ℕ) :
    ∑ y ∈ boxFinset (0 : Site d) n, (1 + (supNorm y : ℝ)) ^ (-(d : ℝ))
      ≤ 1 + (d : ℝ) * (2 : ℝ) ^ d * Real.log ((n : ℝ) + 1) := by
  have hfnn : ∀ k : ℕ, 0 ≤ (1 + (k : ℝ)) ^ (-(d : ℝ)) :=
    fun k => Real.rpow_nonneg (by positivity) _
  have hbox := sum_box_radial_le (d := d) (fun k => (1 + (k : ℝ)) ^ (-(d : ℝ))) hfnn n
  have hsum : ∑ k ∈ Finset.Icc 1 n,
        2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-(d : ℝ))
      ≤ (d : ℝ) * (2 : ℝ) ^ d * Real.log ((n : ℝ) + 1) := by
    calc ∑ k ∈ Finset.Icc 1 n,
          2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-(d : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 n,
            (d : ℝ) * (2 : ℝ) ^ d * (1 / ((k : ℝ) + 1)) :=
          Finset.sum_le_sum (fun k hk => radial_term_le hd (Finset.mem_Icc.mp hk).1)
      _ = (d : ℝ) * (2 : ℝ) ^ d * ∑ k ∈ Finset.Icc 1 n, (1 / ((k : ℝ) + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ (d : ℝ) * (2 : ℝ) ^ d * Real.log ((n : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_left (sum_inv_succ_le_log n) (by positivity)
  calc ∑ y ∈ boxFinset (0 : Site d) n, (1 + (supNorm y : ℝ)) ^ (-(d : ℝ))
      ≤ (1 + ((0 : ℕ) : ℝ)) ^ (-(d : ℝ))
          + ∑ k ∈ Finset.Icc 1 n,
            2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-(d : ℝ)) := hbox
    _ = 1 + ∑ k ∈ Finset.Icc 1 n,
            2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1)
              * (1 + (k : ℝ)) ^ (-(d : ℝ)) := by norm_num
    _ ≤ 1 + (d : ℝ) * (2 : ℝ) ^ d * Real.log ((n : ℝ) + 1) := by linarith

/-- The sum of `(1 + |z|)^{-d}` over the lattice ball of radius `R ≥ 1` is `O(log R)`. -/
theorem sum_ballFinset_rpow_neg_le_log (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (-(d : ℝ)) ≤ C * Real.log (R + 2) := by
  refine ⟨1 + (d : ℝ) * (2 : ℝ) ^ d, by positivity, fun R hR => ?_⟩
  have hsub : ballFinset d R ⊆ boxFinset (0 : Site d) ⌊R⌋₊ := by
    intro z hz
    rw [mem_ballFinset_iff] at hz
    rw [mem_boxFinset_zero_iff]
    exact Nat.le_floor (le_trans (supNorm_le_euclidNorm z) hz)
  have hstep1 : ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (-(d : ℝ))
      ≤ ∑ z ∈ boxFinset (0 : Site d) ⌊R⌋₊,
          (1 + (supNorm z : ℝ)) ^ (-(d : ℝ)) := by
    calc ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (-(d : ℝ))
        ≤ ∑ z ∈ ballFinset d R, (1 + (supNorm z : ℝ)) ^ (-(d : ℝ)) := by
          refine Finset.sum_le_sum (fun z _ => ?_)
          refine Real.rpow_le_rpow_of_nonpos (x := 1 + (supNorm z : ℝ))
            (y := 1 + euclidNorm z) (z := -(d : ℝ)) (by positivity) ?_
            (by have h : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d; linarith)
          linarith [supNorm_le_euclidNorm z]
      _ ≤ ∑ z ∈ boxFinset (0 : Site d) ⌊R⌋₊,
            (1 + (supNorm z : ℝ)) ^ (-(d : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => ?_)
          exact Real.rpow_nonneg (by positivity) _
  have hbox := sum_box_rpow_neg_le hd ⌊R⌋₊
  have hlog : Real.log ((⌊R⌋₊ : ℝ) + 1) ≤ Real.log (R + 2) := by
    refine Real.log_le_log (by positivity) ?_
    have hfloor : ((⌊R⌋₊ : ℕ) : ℝ) ≤ R := Nat.floor_le (by linarith)
    linarith
  have hlog1 : 1 ≤ Real.log (R + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_three
    linarith
  calc ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (-(d : ℝ))
      ≤ ∑ z ∈ boxFinset (0 : Site d) ⌊R⌋₊,
          (1 + (supNorm z : ℝ)) ^ (-(d : ℝ)) := hstep1
    _ ≤ 1 + (d : ℝ) * (2 : ℝ) ^ d * Real.log ((⌊R⌋₊ : ℝ) + 1) := hbox
    _ ≤ 1 + (d : ℝ) * (2 : ℝ) ^ d * Real.log (R + 2) := by
          have hc : (0 : ℝ) ≤ (d : ℝ) * (2 : ℝ) ^ d := by positivity
          have := mul_le_mul_of_nonneg_left hlog hc
          linarith
    _ ≤ (1 + (d : ℝ) * (2 : ℝ) ^ d) * Real.log (R + 2) := by
          nlinarith [hlog1]

/-- In dimension three the first moment `Σ |z| (1 + |z|)^{-4}` over the lattice ball of radius
`R ≥ 1` is `O(log R)`; this is the moment `J` of `eq:kernelmoments` for `d = 3`. -/
theorem sum_ballFinset_norm_mul_rpow_le_log_three :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ z ∈ ballFinset 3 R, euclidNorm z * (1 + euclidNorm z) ^ (-4 : ℝ)
        ≤ C * Real.log (R + 2) := by
  obtain ⟨C, hC, hbound⟩ := sum_ballFinset_rpow_neg_le_log (d := 3) (by norm_num)
  refine ⟨C, hC, fun R hR => ?_⟩
  calc ∑ z ∈ ballFinset 3 R, euclidNorm z * (1 + euclidNorm z) ^ (-4 : ℝ)
      ≤ ∑ z ∈ ballFinset 3 R, (1 + euclidNorm z) ^ (-(3 : ℝ)) := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        have hbase : (0 : ℝ) < 1 + euclidNorm z := by linarith [euclidNorm_nonneg z]
        have hle : euclidNorm z ≤ 1 + euclidNorm z := by linarith [euclidNorm_nonneg z]
        have hnn : (0 : ℝ) ≤ (1 + euclidNorm z) ^ (-4 : ℝ) :=
          Real.rpow_nonneg (le_of_lt hbase) _
        calc euclidNorm z * (1 + euclidNorm z) ^ (-4 : ℝ)
            ≤ (1 + euclidNorm z) * (1 + euclidNorm z) ^ (-4 : ℝ) :=
              mul_le_mul_of_nonneg_right hle hnn
          _ = (1 + euclidNorm z) ^ (-(3 : ℝ)) := by
              calc (1 + euclidNorm z) * (1 + euclidNorm z) ^ (-4 : ℝ)
                  = (1 + euclidNorm z) ^ (1 : ℝ) * (1 + euclidNorm z) ^ (-4 : ℝ) := by
                    rw [Real.rpow_one]
                _ = (1 + euclidNorm z) ^ ((1 : ℝ) + (-4 : ℝ)) := by
                    rw [← Real.rpow_add hbase]
                _ = (1 + euclidNorm z) ^ (-(3 : ℝ)) := by norm_num
    _ ≤ C * Real.log (R + 2) := hbound R hR

end CERW.Generic.Lattice
