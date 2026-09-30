import CERW.Support.Contact.PlanarSum
import CERW.Generic.Lattice.Centered
import CERW.Model.Occupation

/-!
# The planar bracket at the unvisited site

In the plane, if every departure site satisfies `ℓ_n(x) ≤ c₀ (b - |x|)_+ + A`, and all departure
sites lie within distance `R` of a site `z` with `|z| ≥ b`, then
`B_z = Σ_x ℓ_n(x) (1 + |x - z|)^{-2} ≤ C (c₀ (R + 1) + A log(R + 2))`. The profile part uses
`(b - |x|)_+ ≤ |x - z|`, and the constant part uses the logarithmic lattice sum. This is the bound
`B_z ≤ C (N + N^{3/4} L^{3/2} + √N L²)` of the planar contact variance.
-/

namespace CERW.Support.Contact

open LatticeProb Finset CERW

/-- The planar hole bracket: `B_z ≤ C (c₀ (R + 1) + A log(R + 2))` when every departure site has
`ℓ_n(x) ≤ c₀ (b - |x|)_+ + A` and lies within distance `R` of `z`, with `|z| ≥ b`. -/
theorem exists_planar_bracket_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site 2) (n : ℕ) (c₀ b A R : ℝ) (z : Site 2), 1 ≤ R → 0 ≤ c₀ →
      0 ≤ A → b ≤ euclidNorm z → (∀ x ∈ departureRange X n, euclidNorm (x - z) ≤ R) →
      (∀ x ∈ departureRange X n, (localTime X n x : ℝ) ≤ c₀ * max (b - euclidNorm x) 0 + A) →
        ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-2 : ℝ) ≤
          C * (c₀ * (R + 1) + A * Real.log (R + 2)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := sum_max_sub_mul_rpow_le_two
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := 2) (by norm_num)
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro X n c₀ b A R z hR hc₀ hA hbz hdist hlocal
  have hk : ∀ w : Site 2, 0 ≤ (1 + euclidNorm w) ^ (-2 : ℝ) :=
    fun w => Real.rpow_nonneg (by linarith [euclidNorm_nonneg w]) _
  have hterm : ∀ x ∈ departureRange X n,
      (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-2 : ℝ) ≤
        c₀ * (max (b - euclidNorm x) 0 * (1 + euclidNorm (x - z)) ^ (-2 : ℝ))
          + A * (1 + euclidNorm (x - z)) ^ (-2 : ℝ) := by
    intro x hx
    calc (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-2 : ℝ)
        ≤ (c₀ * max (b - euclidNorm x) 0 + A) * (1 + euclidNorm (x - z)) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (hlocal x hx) (hk (x - z))
      _ = c₀ * (max (b - euclidNorm x) 0 * (1 + euclidNorm (x - z)) ^ (-2 : ℝ))
            + A * (1 + euclidNorm (x - z)) ^ (-2 : ℝ) := by ring
  have hAlog : ∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-2 : ℝ)
      ≤ C₂ * Real.log (R + 2) := by
    exact hC₂ (departureRange X n) z R (by linarith) hdist
  have hprofile : ∑ x ∈ departureRange X n,
        max (b - euclidNorm x) 0 * (1 + euclidNorm (x - z)) ^ (-2 : ℝ) ≤ C₁ * (R + 1) := by
    have hinj : Set.InjOn (fun x : Site 2 => x - z) ↑(departureRange X n) :=
      fun a _ b _ hab => sub_left_injective hab
    have himage : ∑ x ∈ departureRange X n,
          max (b - euclidNorm x) 0 * (1 + euclidNorm (x - z)) ^ (-2 : ℝ)
        = ∑ w ∈ (departureRange X n).image (fun x => x - z),
            max (b - euclidNorm (z + w)) 0 * (1 + euclidNorm w) ^ (-2 : ℝ) := by
      let f : Site 2 → ℝ :=
        fun w => max (b - euclidNorm (z + w)) 0 * (1 + euclidNorm w) ^ (-2 : ℝ)
      have hcongr : ∑ x ∈ departureRange X n,
            max (b - euclidNorm x) 0 * (1 + euclidNorm (x - z)) ^ (-2 : ℝ)
          = ∑ x ∈ departureRange X n, f (x - z) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [f]
        rw [show z + (x - z) = x by abel]
      rw [hcongr, (Finset.sum_image (f := f) hinj).symm]
    rw [himage]
    have hsub : (departureRange X n).image (fun x => x - z) ⊆ ballFinset 2 R := by
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      rw [mem_ballFinset_iff]
      exact hdist x hx
    calc ∑ w ∈ (departureRange X n).image (fun x => x - z),
            max (b - euclidNorm (z + w)) 0 * (1 + euclidNorm w) ^ (-2 : ℝ)
        ≤ ∑ w ∈ ballFinset 2 R,
            max (b - euclidNorm (z + w)) 0 * (1 + euclidNorm w) ^ (-2 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun w _ _ => mul_nonneg (le_max_right _ _) (hk w))
      _ ≤ C₁ * (R + 1) := hC₁ z b R hbz (by linarith)
  calc ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-2 : ℝ)
      ≤ ∑ x ∈ departureRange X n,
          (c₀ * (max (b - euclidNorm x) 0 * (1 + euclidNorm (x - z)) ^ (-2 : ℝ))
            + A * (1 + euclidNorm (x - z)) ^ (-2 : ℝ)) := Finset.sum_le_sum hterm
    _ = c₀ * (∑ x ∈ departureRange X n,
            max (b - euclidNorm x) 0 * (1 + euclidNorm (x - z)) ^ (-2 : ℝ))
          + A * (∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-2 : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ c₀ * (C₁ * (R + 1)) + A * (C₂ * Real.log (R + 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hprofile hc₀)
          (mul_le_mul_of_nonneg_left hAlog hA)
    _ ≤ (C₁ + C₂) * (c₀ * (R + 1) + A * Real.log (R + 2)) := by
        have hL : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
        have hR1 : 0 ≤ R + 1 := by linarith
        have h1 : 0 ≤ C₁ * A * Real.log (R + 2) :=
          mul_nonneg (mul_nonneg hC₁pos.le hA) hL
        have h2 : 0 ≤ C₂ * c₀ * (R + 1) :=
          mul_nonneg (mul_nonneg hC₂pos.le hc₀) hR1
        nlinarith [h1, h2]

end CERW.Support.Contact
