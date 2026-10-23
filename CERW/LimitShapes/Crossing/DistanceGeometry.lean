import CERW.Support.Norm.Section5Localization

/-!
# Distance geometry for the exponential crossing argument

The Euclidean distance to a norm sublevel set agrees with the displacement from its
canonical projection. Its one-step upper bound and its pairing with a subgradient give
the deterministic geometry used in the paper's equation `eq:distance-crossing`.
-/

namespace CERW.LimitShapes.Crossing.DistanceGeometry

open CERW CERW.Support.Norm.Section5Localization
open CERW.Support.Norm.ProjectionGeometry

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Distance to the norm ball is the displacement from the canonical projection. -/
theorem inf_dist_eq_norm_sub_projection (hΨ : IsNorm Ψ) {a : ℝ} (ha : 0 ≤ a)
    (x : EuclideanSpace ℝ (Fin d)) :
    Metric.infDist x {v | Ψ v ≤ a} = ‖x - canonicalProjection Ψ a x‖ := by
  have hz := (canonicalProjection_spec hΨ ha x).1
  apply le_antisymm
  · simpa only [dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (x := x)
        (s := {v | Ψ v ≤ a}) (y := canonicalProjection Ψ a x) hz)
  · apply (Metric.le_infDist ⟨canonicalProjection Ψ a x, hz⟩).2
    intro v hv
    simpa only [dist_eq_norm] using canonicalProjection_dist_le hΨ ha x hv

/-- The one-step distance estimate in the paper's equation `eq:distance-crossing`. -/
theorem inf_dist_add_le (hΨ : IsNorm Ψ) {a : ℝ} (ha : 0 ≤ a)
    (x e : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ ≤ 1)
    (hδ : 1 ≤ Metric.infDist x {v | Ψ v ≤ a}) :
    Metric.infDist (x + e) {v | Ψ v ≤ a} ≤
      Metric.infDist x {v | Ψ v ≤ a} +
        inner ℝ ((Metric.infDist x {v | Ψ v ≤ a})⁻¹ •
          (x - canonicalProjection Ψ a x)) e +
        1 / (2 * Metric.infDist x {v | Ψ v ≤ a}) := by
  set z := canonicalProjection Ψ a x
  set δ := Metric.infDist x {v | Ψ v ≤ a}
  have hnorm : ‖x - z‖ = δ := (inf_dist_eq_norm_sub_projection hΨ ha x).symm
  have hpos : 0 < δ := lt_of_lt_of_le zero_lt_one hδ
  have hsquare := norm_add_sq_real (x - z) e
  rw [hnorm] at hsquare
  have he2 : ‖e‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg e]
  have hlinear : 2 * δ * ‖(x - z) + e‖ ≤
      2 * δ ^ 2 + 2 * inner ℝ (x - z) e + 1 := by
    nlinarith [sq_nonneg (‖(x - z) + e‖ - δ)]
  have hbound : ‖(x - z) + e‖ ≤
      δ + δ⁻¹ * inner ℝ (x - z) e + 1 / (2 * δ) := by
    calc ‖(x - z) + e‖ ≤
        (2 * δ ^ 2 + 2 * inner ℝ (x - z) e + 1) / (2 * δ) :=
          (le_div_iff₀ (by positivity)).2 (by nlinarith [hlinear])
      _ = δ + δ⁻¹ * inner ℝ (x - z) e + 1 / (2 * δ) := by
          field_simp
  calc Metric.infDist (x + e) {v | Ψ v ≤ a} ≤ dist (x + e) z :=
        Metric.infDist_le_dist_of_mem (canonicalProjection_spec hΨ ha x).1
    _ = ‖(x - z) + e‖ := by rw [dist_eq_norm]; congr 1; abel
    _ ≤ δ + inner ℝ (δ⁻¹ • (x - z)) e + 1 / (2 * δ) := by
        simpa only [real_inner_smul_left] using hbound

/-- Every subgradient has pairing at least the minimum norm in the outward distance
 direction, as used in the paper's equation `eq:distance-crossing`. -/
theorem norm_min_le_inner_direction (hd : 1 ≤ d) (hΨ : IsNorm Ψ)
    {a : ℝ} (ha : 0 ≤ a) (x : EuclideanSpace ℝ (Fin d)) (_hx : x ≠ 0)
    (ξ : EuclideanSpace ℝ (Fin d)) (hξ : IsSubgradient Ψ x ξ)
    (hδ : 1 ≤ Metric.infDist x {v | Ψ v ≤ a}) :
    normMin Ψ ≤ inner ℝ ξ ((Metric.infDist x {v | Ψ v ≤ a})⁻¹ •
      (x - canonicalProjection Ψ a x)) := by
  set z := canonicalProjection Ψ a x
  set δ := Metric.infDist x {v | Ψ v ≤ a}
  have hnorm : ‖x - z‖ = δ := (inf_dist_eq_norm_sub_projection hΨ ha x).symm
  have hpos : 0 < δ := lt_of_lt_of_le zero_lt_one hδ
  have hout : a < Ψ x := by
    by_contra h
    have hzero : δ ≤ dist x x := Metric.infDist_le_dist_of_mem (not_lt.mp h)
    rw [dist_self] at hzero
    linarith
  have hrad := normMin_mul_dist_le hΨ hd ha
    (fun v hv => canonicalProjection_dist_le hΨ ha x (v := v) hv) hout
  have hsub := sub_le_inner_of_subgradient (canonicalProjection_spec hΨ ha x).1 hξ
  rw [hnorm] at hrad
  rw [real_inner_smul_right]
  have hpair : normMin Ψ * δ ≤ inner ℝ ξ (x - z) := hrad.trans hsub
  calc normMin Ψ ≤ inner ℝ ξ (x - z) / δ := (le_div_iff₀ hpos).2 hpair
    _ = δ⁻¹ * inner ℝ ξ (x - z) := by rw [div_eq_mul_inv, mul_comm]

end CERW.LimitShapes.Crossing.DistanceGeometry
