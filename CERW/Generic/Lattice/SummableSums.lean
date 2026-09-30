import LatticeProb.Walk.Ball

/-!
# Summable lattice weights

In dimension `d ≥ 3` the bracket weight `(1 + |z|)^{2-2d}` has finite total mass, and in
dimension `d ≥ 4` so does its first moment (`eq:bracket`, `eq:kernelmoments`). A convolution
of a nonnegative weight against a one-Lipschitz profile is controlled by the mass and the
first moment of the weight, which is the step behind `eq:envelopehigh`.
-/

namespace CERW.Generic.Lattice

open LatticeProb

variable {d : ℕ}

/-- For `d ≥ 3` the sums of `(1 + |z|)^{2-2d}` over lattice balls are uniformly bounded. -/
theorem sum_ballFinset_rpow_two_sub_two_mul_le (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ,
      ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ)) ≤ C := by
  have hsummable : Summable fun z : Site d => (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ)) := by
    have h := summable_one_add_euclidNorm_rpow d (p := 2 * (d : ℝ) - 2) (by
      have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)
    refine h.congr fun z => ?_
    rw [show -(2 * (d : ℝ) - 2) = 2 - 2 * (d : ℝ) by ring]
  refine ⟨(∑' z : Site d, (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ))) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ ∑' z : Site d, (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ)) :=
      tsum_nonneg fun z =>
        Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
    linarith
  · intro R
    have hle := hsummable.sum_le_tsum (ballFinset d R) fun z _ =>
      Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
    linarith

/-- For `d ≥ 4` the sums of `|z| (1 + |z|)^{2-2d}` over lattice balls are uniformly bounded. -/
theorem sum_ballFinset_norm_mul_rpow_le (hd : 4 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ,
      ∑ z ∈ ballFinset d R, euclidNorm z * (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ)) ≤ C := by
  have hpoint : ∀ z : Site d, euclidNorm z * (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ))
      ≤ (1 + euclidNorm z) ^ (3 - 2 * (d : ℝ)) := by
    intro z
    have hbase : 0 < 1 + euclidNorm z := by linarith [euclidNorm_nonneg z]
    have hnorm : euclidNorm z ≤ 1 + euclidNorm z := by linarith [euclidNorm_nonneg z]
    have hnonneg : 0 ≤ (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ)) :=
      Real.rpow_nonneg (le_of_lt hbase) _
    calc euclidNorm z * (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ))
        ≤ (1 + euclidNorm z) * (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ)) :=
          mul_le_mul_of_nonneg_right hnorm hnonneg
      _ = (1 + euclidNorm z) ^ (3 - 2 * (d : ℝ)) := by
          rw [show (3 : ℝ) - 2 * (d : ℝ) = 1 + (2 - 2 * (d : ℝ)) by ring,
            Real.rpow_add hbase, Real.rpow_one]
  have hsummable : Summable fun z : Site d => (1 + euclidNorm z) ^ (3 - 2 * (d : ℝ)) := by
    have h := summable_one_add_euclidNorm_rpow d (p := 2 * (d : ℝ) - 3) (by
      have hd' : (4 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)
    refine h.congr fun z => ?_
    rw [show -(2 * (d : ℝ) - 3) = 3 - 2 * (d : ℝ) by ring]
  refine ⟨(∑' z : Site d, (1 + euclidNorm z) ^ (3 - 2 * (d : ℝ))) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ ∑' z : Site d, (1 + euclidNorm z) ^ (3 - 2 * (d : ℝ)) :=
      tsum_nonneg fun z =>
        Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
    linarith
  · intro R
    calc ∑ z ∈ ballFinset d R, euclidNorm z * (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ))
        ≤ ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (3 - 2 * (d : ℝ)) :=
          Finset.sum_le_sum fun z _ => hpoint z
      _ ≤ ∑' z : Site d, (1 + euclidNorm z) ^ (3 - 2 * (d : ℝ)) :=
          hsummable.sum_le_tsum (ballFinset d R) fun z _ =>
            Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
      _ ≤ (∑' z : Site d, (1 + euclidNorm z) ^ (3 - 2 * (d : ℝ))) + 1 := by linarith

/-- The Euclidean norm of a lattice site is invariant under negation. -/
theorem euclidNorm_neg (x : Site d) : euclidNorm (-x) = euclidNorm x := by
  unfold euclidNorm
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.neg_apply, Int.cast_neg, neg_sq]

/-- Convolution of a nonnegative weight against a one-Lipschitz profile: if
`s u - s v ≤ |u - v|` for all `u, v`, then `Σ_x k(x) s(y - x) ≤ (Σ_x k(x)) s(y) + Σ_x |x| k(x)`. -/
theorem sum_mul_le_of_lipschitz (S : Finset (Site d)) (k : Site d → ℝ) (hk : ∀ x, 0 ≤ k x)
    (s : Site d → ℝ) (hs : ∀ u v, s u - s v ≤ euclidNorm (u - v)) (y : Site d) :
    ∑ x ∈ S, k x * s (y - x) ≤ (∑ x ∈ S, k x) * s y + ∑ x ∈ S, euclidNorm x * k x := by
  have hterm : ∀ x : Site d,
      k x * s (y - x) ≤ k x * s y + euclidNorm x * k x := by
    intro x
    have hstep : s (y - x) - s y ≤ euclidNorm x := by
      have h := hs (y - x) y
      rwa [show (y - x) - y = -x by abel, euclidNorm_neg] at h
    have h1 : k x * s (y - x) ≤ k x * s y + k x * euclidNorm x := by
      have h := mul_le_mul_of_nonneg_left hstep (hk x)
      rw [mul_sub] at h
      linarith
    calc k x * s (y - x) ≤ k x * s y + k x * euclidNorm x := h1
      _ = k x * s y + euclidNorm x * k x := by rw [mul_comm (k x) (euclidNorm x)]
  calc ∑ x ∈ S, k x * s (y - x)
      ≤ ∑ x ∈ S, (k x * s y + euclidNorm x * k x) :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = (∑ x ∈ S, k x * s y) + ∑ x ∈ S, euclidNorm x * k x :=
        Finset.sum_add_distrib
    _ = (∑ x ∈ S, k x) * s y + ∑ x ∈ S, euclidNorm x * k x := by
        rw [Finset.sum_mul]

end CERW.Generic.Lattice
