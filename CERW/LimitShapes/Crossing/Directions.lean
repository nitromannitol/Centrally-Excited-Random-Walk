import CERW.Support.Norm.Section5Localization

/-!
# Projection directions for the distance crossing estimate

For each integer norm radius, the possible outward directions come from
lattice sites within the terminal horizon. Their union over relevant radii
has polynomial cardinality and is chosen independently of the walk.
-/

open LatticeProb

namespace CERW.LimitShapes.Crossing.Directions

open CERW CERW.Support.Norm.Section5Localization
open private norm_scaled_le from CERW.Support.Norm.ContactEvent

variable {d : ℕ}

/-- Outward projection directions for the norm ball of integer radius `m`,
indexed by lattice sites within Euclidean distance `N`. -/
noncomputable def normBallDirections (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (m N : ℕ) :
    Finset (EuclideanSpace ℝ (Fin d)) := by
  classical
  exact ((ballFinset d (N : ℝ)).filter (fun z => (m : ℝ) < Ψ (toSpace z))).image
    (fun z => (normMax Ψ / ‖toSpace z - canonicalProjection Ψ m (toSpace z)‖) •
      (toSpace z - canonicalProjection Ψ m (toSpace z)))

/-- The deterministic family of directions for all integer norm balls that
can be crossed before the terminal horizon. -/
noncomputable def crossingDirections (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (N : ℕ) :
    Finset (EuclideanSpace ℝ (Fin d)) := by
  classical
  exact (Finset.range (⌈normMax Ψ * N⌉₊ + 1)).biUnion (fun m => normBallDirections Ψ m N)

/-- Every selected projection direction has norm at most the norm's maximum
on the Euclidean unit sphere. -/
theorem norm_le_of_mem_crossingDirections {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΛ : 0 ≤ normMax Ψ) {N : ℕ} {q : EuclideanSpace ℝ (Fin d)}
    (hq : q ∈ crossingDirections Ψ N) : ‖q‖ ≤ normMax Ψ := by
  classical
  obtain ⟨m, _, hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hq
  exact norm_scaled_le hΛ _

/-- A single integer norm ball needs at most as many directions as lattice sites
within Euclidean distance `N`. -/
theorem card_normBallDirections_le (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (m N : ℕ) :
    ((normBallDirections Ψ m N).card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ d := by
  classical
  exact (Nat.cast_le.mpr (Finset.card_image_le.trans (Finset.card_filter_le _ _))).trans
    (LatticeProb.card_ballFinset_le d (Nat.cast_nonneg N))

/-- The total direction family grows at most as the horizon to the power `d+1`. -/
theorem card_crossingDirections_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΛ : 0 ≤ normMax Ψ) (N : ℕ) :
    ((crossingDirections Ψ N).card : ℝ) ≤
      (normMax Ψ + 2) * 3 ^ d * ((N : ℝ) + 1) ^ (d + 1) := by
  classical
  let R := ⌈normMax Ψ * N⌉₊
  have hcard : ((crossingDirections Ψ N).card : ℝ) ≤
      ∑ m ∈ Finset.range (R + 1), ((normBallDirections Ψ m N).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le :
      ((Finset.range (R + 1)).biUnion (fun m => normBallDirections Ψ m N)).card ≤
        ∑ m ∈ Finset.range (R + 1), (normBallDirections Ψ m N).card)
  have hR : ((R + 1 : ℕ) : ℝ) ≤ (normMax Ψ + 2) * ((N : ℝ) + 1) := by
    have h := Nat.ceil_lt_add_one (mul_nonneg hΛ (Nat.cast_nonneg N))
    change (R : ℝ) < normMax Ψ * N + 1 at h
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hpow : (2 * (N : ℝ) + 1) ^ d ≤ 3 ^ d * ((N : ℝ) + 1) ^ d := by
    calc _ ≤ (3 * ((N : ℝ) + 1)) ^ d :=
        pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) N]) d
      _ = _ := mul_pow _ _ d
  calc ((crossingDirections Ψ N).card : ℝ)
      ≤ ∑ m ∈ Finset.range (R + 1), ((normBallDirections Ψ m N).card : ℝ) := hcard
    _ ≤ ∑ _m ∈ Finset.range (R + 1), (2 * (N : ℝ) + 1) ^ d :=
      Finset.sum_le_sum fun m _ => card_normBallDirections_le Ψ m N
    _ = ((R + 1 : ℕ) : ℝ) * (2 * (N : ℝ) + 1) ^ d := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((normMax Ψ + 2) * ((N : ℝ) + 1)) * (3 ^ d * ((N : ℝ) + 1) ^ d) :=
      mul_le_mul hR hpow (by positivity) (by positivity)
    _ = (normMax Ψ + 2) * 3 ^ d * ((N : ℝ) + 1) ^ (d + 1) := by
      rw [pow_succ]
      ring

end CERW.LimitShapes.Crossing.Directions
