import CERW.Generic.Lattice.WeightSums
import CERW.Generic.Lattice.Packing
import CERW.Generic.Lattice.SummableSums

/-!
# Lattice weight sums centred at an arbitrary site

The ball sums of `CERW.Generic.Lattice` translated to an arbitrary centre `y` and restricted
to an arbitrary finite set of sites. For `(1 + |x - y|)^{-d}` the sum is `O(log R)` within
distance `R`. For `(1 + |x - y|)^{2-2d}` with `d ≥ 3` it is `O(1)`. These are the forms in which
`lem:local` and the contact variance use them.
-/

namespace CERW.Generic.Lattice

open LatticeProb

variable {d : ℕ}

/-- Within distance `R ≥ 1` of `y`, a finite set carries `O(log R)` of `(1 + |x - y|)^{-d}`. -/
theorem sum_finset_rpow_neg_le_log (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset (Site d)) (y : Site d) (R : ℝ), 1 ≤ R →
      (∀ x ∈ E, euclidNorm (x - y) ≤ R) →
        ∑ x ∈ E, (1 + euclidNorm (x - y)) ^ (-(d : ℝ)) ≤ C * Real.log (R + 2) := by
  obtain ⟨C, hCpos, hC⟩ := sum_ballFinset_rpow_neg_le_log (d := d) hd
  refine ⟨C, hCpos, ?_⟩
  intro E y R hR hE
  have hinj : Set.InjOn (fun x : Site d => x - y) ↑E :=
    fun a _ b _ hab => sub_left_injective hab
  have himage : ∑ x ∈ E, (1 + euclidNorm (x - y)) ^ (-(d : ℝ))
      = ∑ z ∈ E.image (fun x => x - y), (1 + euclidNorm z) ^ (-(d : ℝ)) :=
    (Finset.sum_image (f := fun z => (1 + euclidNorm z) ^ (-(d : ℝ))) hinj).symm
  rw [himage]
  have hsub : E.image (fun x => x - y) ⊆ ballFinset d R := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [mem_ballFinset_iff]
    exact hE x hx
  calc ∑ z ∈ E.image (fun x => x - y), (1 + euclidNorm z) ^ (-(d : ℝ))
      ≤ ∑ z ∈ ballFinset d R, (1 + euclidNorm z) ^ (-(d : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun z _ _ => Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _)
    _ ≤ C * Real.log (R + 2) := hC R hR

/-- For `d ≥ 3` every finite set carries `O(1)` of `(1 + |x - y|)^{2-2d}`. -/
theorem sum_finset_rpow_two_sub_two_mul_le (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset (Site d)) (y : Site d),
      ∑ x ∈ E, (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := sum_ballFinset_rpow_two_sub_two_mul_le (d := d) hd
  refine ⟨C, hCpos, ?_⟩
  intro E y
  have hinj : Set.InjOn (fun x : Site d => x - y) ↑E :=
    fun a _ b _ hab => sub_left_injective hab
  have himage : ∑ x ∈ E, (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))
      = ∑ z ∈ E.image (fun x => x - y), (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ)) :=
    (Finset.sum_image (f := fun z => (1 + euclidNorm z) ^ (2 - 2 * (d : ℝ))) hinj).symm
  rw [himage]
  have hsub : E.image (fun x => x - y) ⊆ ballFinset d (∑ x ∈ E, euclidNorm (x - y)) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [mem_ballFinset_iff]
    exact Finset.single_le_sum (fun x _ => euclidNorm_nonneg (x - y)) hx
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun z _ _ => Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _)).trans (hC _)

end CERW.Generic.Lattice
