import CERW.LimitShapes.Crossing.Directions
import CERW.LimitShapes.Crossing.Levels

/-!
# Distance crossings on the vector and ramp events

Projection estimates give distance crossings for all relevant integer balls.
Radial contraction then gives the estimate at every nonnegative real level,
using the same terminal logarithm for every prefix of the path.
-/

open LatticeProb

namespace CERW.LimitShapes.Crossing.Deterministic

open CERW CERW.Support.Norm.Section5Localization Directions

/-- The vector and finite-family ramp bounds imply the full simultaneous distance
crossing estimate for every legal path. -/
theorem distanceCrossingBound_of_estimates {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {C₁ : ℝ} (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d), X 0 = 0 → (∀ j, X (j + 1) - X j ∈ unitSteps d) →
      ∀ N : ℕ, 2 ≤ N →
      (∀ s t : ℕ, s < t → t ≤ N →
        ‖(toSpace (X t) + ε • ∑ j ∈ Finset.range t,
            if X j ∉ departureRange X j then ξ (X j) else 0) -
          (toSpace (X s) + ε • ∑ j ∈ Finset.range s,
            if X j ∉ departureRange X j then ξ (X j) else 0)‖ ≤
          C₁ * Real.sqrt (((t : ℝ) - s) * Real.log N)) →
      (∀ t : ℕ, t ≤ N → ∀ q ∈ crossingDirections Ψ N, ∀ k : ℕ, k ≤ N →
        |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) X t| ≤
          C₁ * (Real.sqrt (Real.log N * ∑ z ∈ (departureRange X t).filter
            (fun z => k * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
            (localTime X t z : ℝ)) + Real.log N)) →
      DistanceCrossingBound Ψ C X N := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, hC₀, hproj⟩ := Projection.distance_le_of_projection_estimates hd hΨ hε hell hC₁
  obtain ⟨C, hC, hlevels⟩ := Levels.distanceCrossingBound_of_integer_levels hd1 hΨ hC₀.le
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hξ0 X hX0 hstep N hN hvec hramp
  apply hlevels X hX0 hstep N hN
  intro m hm hmN t ht j hj
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hLm : (0 : ℝ) ≤ exteriorLocalTime Ψ X t m := Nat.cast_nonneg _
  apply hproj ξ hξ hξ0 N hN t ht X hX0 hstep m
    (exteriorLocalTime Ψ X t m) hm0 hLm (canonicalProjection Ψ m)
    (fun y => (canonicalProjection_spec hΨ hm0 y).1)
    (fun y _ hv => canonicalProjection_dist_le hΨ hm0 y hv)
    (fun y _ hv => (canonicalProjection_spec hΨ hm0 y).2 _ hv) _ _ _ j hj
  · intro z hz
    by_cases hzt : z ∈ departureRange X t
    · exact Nat.cast_le.mpr (Finset.le_sup (f := localTime X t)
        (Finset.mem_filter.mpr ⟨hzt, hz⟩))
    · rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hzt
      rw [hzt]
      simpa only [Nat.cast_zero] using hLm
  · intro s u hsu hu
    exact hvec s u hsu (hu.trans ht)
  · intro i hi hmi k hk
    have hinorm := CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hstep i
    have hiN : (i : ℝ) ≤ N := Nat.cast_le.mpr (hi.trans ht)
    have hmem : (normMax Ψ / ‖toSpace (X i) -
        canonicalProjection Ψ m (toSpace (X i))‖) •
        (toSpace (X i) - canonicalProjection Ψ m (toSpace (X i))) ∈
        crossingDirections Ψ N := by
      classical
      apply Finset.mem_biUnion.mpr
      refine ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hmN), ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨X i, Finset.mem_filter.mpr ⟨?_, hmi⟩, rfl⟩
      exact mem_ballFinset_iff.mpr (hinorm.trans hiN)
    exact hramp t ht _ hmem k (hk.trans ht)

end CERW.LimitShapes.Crossing.Deterministic
