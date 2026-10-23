import CERW.LimitShapes.Crossing.DistanceGeometry
import CERW.Support.Drift.Dynkin

/-!
# Exponential distance drift

The actual one-step kernel satisfies the exponential distance estimate in the paper's
equation `eq:distance-crossing`.
-/

namespace CERW.LimitShapes.Crossing.ExponentialDrift

open LatticeProb CERW CERW.Support.Drift CERW.Support.Law
open CERW.Support.Norm.ProjectionGeometry
open CERW.Support.Norm.Section5Localization
open CERW.LimitShapes.Crossing.DistanceGeometry

open private CERW.Support.Norm.toSpace_add from CERW.Support.Norm.OuterCrossing

/-- The exponential has a quadratic upper bound on the unit interval. -/
private lemma exp_le_quad {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have h := Real.exp_bound hu (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  have := (abs_le.mp h).2
  nlinarith [sq_nonneg u]

/-- The exponential distance drift estimate of equation `eq:distance-crossing` for the
actual one-step kernel, without assumptions on the path. -/
theorem sum_driftStepProb_exp_distance_le {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {a : ℝ} (ha : 0 ≤ a)
    {ε : ℝ} (hε : 0 ≤ ε) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (hsub : ∀ x, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (_hzero : ξ 0 = 0)
    (hξ : ∀ x i, ε * |ξ x i| ≤ 1 / (d : ℝ))
    (X : ℕ → Site d) (j : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hδ : 1 ≤ Metric.infDist (toSpace (X j)) {v | Ψ v ≤ a}) :
    let δ := fun z : Site d => Metric.infDist (toSpace z) {v | Ψ v ≤ a}
    ∑ e ∈ unitSteps d, driftStepProb d ε ξ X j e *
        (Real.exp (θ * δ (X j + e)) - Real.exp (θ * δ (X j))) ≤
      θ * Real.exp (θ * δ (X j)) * (θ + 1 / (2 * δ (X j)) -
        if X j ∉ departureRange X j then ε * normMin Ψ else 0) := by
  dsimp only
  let δ := fun z : Site d => Metric.infDist (toSpace z) {v | Ψ v ≤ a}
  let ν := (δ (X j))⁻¹ •
    (toSpace (X j) - canonicalProjection Ψ a (toSpace (X j)))
  let p := driftStepProb d ε ξ X j
  have hzeroΨ : Ψ 0 = 0 := by
    simpa only [zero_smul, abs_zero, zero_mul] using
      hΨ.smul 0 (0 : EuclideanSpace ℝ (Fin d))
  have hx : X j ≠ 0 := by
    intro hz
    have hz' : toSpace (X j) = 0 := by ext i; simp [hz, toSpace_apply]
    have hmem : toSpace (X j) ∈ {v | Ψ v ≤ a} := by
      rw [hz']; exact le_trans hzeroΨ.le ha
    have := Metric.infDist_le_dist_of_mem (x := toSpace (X j)) hmem
    rw [dist_self] at this
    linarith
  have hx' : toSpace (X j) ≠ 0 := by
    intro hz
    have hmem : toSpace (X j) ∈ {v | Ψ v ≤ a} := by
      rw [hz]; exact le_trans hzeroΨ.le ha
    have := Metric.infDist_le_dist_of_mem (x := toSpace (X j)) hmem
    rw [dist_self] at this
    linarith
  have hpair : normMin Ψ ≤ inner ℝ (ξ (X j)) ν :=
    norm_min_le_inner_direction hd hΨ ha _ hx' _ (hsub _ hx) hδ
  have hmean : ∑ e ∈ unitSteps d, p e * inner ℝ ν (toSpace e) =
      -(if X j ∉ departureRange X j then ε * inner ℝ (ξ (X j)) ν else 0) := by
    have hm : ∑ e ∈ unitSteps d, p e • toSpace e =
        if X j ∉ departureRange X j then -(ε • ξ (X j)) else 0 := by
      dsimp only [p]
      unfold driftStepProb
      by_cases hf : X j ∉ departureRange X j
      · have hf' := hf
        simp only [departureRange] at hf'
        have hc : X j ≠ 0 ∧ X j ∉ (Finset.range j).image X := ⟨hx, hf'⟩
        simp only [if_pos hc, if_pos hf]
        exact sum_driftFirstStep_smul ε (ξ (X j))
      · have hf' := hf
        simp only [departureRange, not_not] at hf'
        simp only [hf', hf, not_true_eq_false, and_false, ↓reduceIte]
        exact sum_srwStep_smul
    calc
      _ = inner ℝ ν (∑ e ∈ unitSteps d, p e • toSpace e) := by
        rw [inner_sum]
        apply Finset.sum_congr rfl
        intro e _
        exact (real_inner_smul_right _ _ _).symm
      _ = _ := by
        rw [hm]
        split_ifs <;> simp only [inner_neg_right, real_inner_smul_right,
          inner_zero_right, neg_zero, real_inner_comm ν]
  have hpoint (e : Site d) (he : e ∈ unitSteps d) :
      Real.exp (θ * δ (X j + e)) - Real.exp (θ * δ (X j)) ≤
        θ * Real.exp (θ * δ (X j)) *
          (inner ℝ ν (toSpace e) + 1 / (2 * δ (X j)) + θ) := by
    have heone : ‖toSpace e‖ = 1 := by
      rw [norm_toSpace, euclidNorm_of_mem_unitSteps he]
    have hg := inf_dist_add_le hΨ ha (toSpace (X j)) (toSpace e) heone.le hδ
    rw [← CERW.Support.Norm.toSpace_add] at hg
    have habs : |δ (X j + e) - δ (X j)| ≤ 1 := by
      have h := (Metric.lipschitz_infDist_pt {v | Ψ v ≤ a}).dist_le_mul
        (toSpace (X j + e)) (toSpace (X j))
      simpa only [δ, Real.dist_eq, CERW.Support.Norm.toSpace_add, dist_eq_norm, Real.norm_eq_abs,
        add_sub_cancel_left,
        heone, NNReal.coe_one, one_mul] using h
    have hu : |θ * (δ (X j + e) - δ (X j))| ≤ θ := by
      rw [abs_mul, abs_of_pos hθ]
      exact mul_le_of_le_one_right hθ.le habs
    have ht := exp_le_quad (hu.trans hθone)
    have hs : (θ * (δ (X j + e) - δ (X j))) ^ 2 ≤ θ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hu 2
    have hb : Real.exp (θ * (δ (X j + e) - δ (X j))) - 1 ≤
        θ * (inner ℝ ν (toSpace e) + 1 / (2 * δ (X j)) + θ) := by
      dsimp only [δ, ν] at *
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (θ * δ (X j))).le
    rw [mul_sub, ← Real.exp_add] at hm
    have heq : θ * δ (X j) + θ * (δ (X j + e) - δ (X j)) =
        θ * δ (X j + e) := by ring
    rw [heq, mul_one] at hm
    calc
      _ ≤ _ := hm
      _ = _ := by ring
  have hsum := Finset.sum_le_sum fun e he =>
    mul_le_mul_of_nonneg_left (hpoint e he) (driftStepProb_nonneg hε hξ X j e)
  have hnorm : ∑ e ∈ unitSteps d, p e = 1 := sum_driftStepProb hd ε ξ X j
  change ∑ e ∈ unitSteps d, p e * _ ≤ _
  calc
    _ ≤ ∑ e ∈ unitSteps d, p e * (θ * Real.exp (θ * δ (X j)) *
        (inner ℝ ν (toSpace e) + 1 / (2 * δ (X j)) + θ)) := hsum
    _ = θ * Real.exp (θ * δ (X j)) *
        ((∑ e ∈ unitSteps d, p e * inner ℝ ν (toSpace e)) +
          1 / (2 * δ (X j)) + θ) := by
      simp_rw [show ∀ e, p e * (θ * Real.exp (θ * δ (X j)) *
          (inner ℝ ν (toSpace e) + 1 / (2 * δ (X j)) + θ)) =
          θ * Real.exp (θ * δ (X j)) * (p e * inner ℝ ν (toSpace e) +
            p e * (1 / (2 * δ (X j))) + p e * θ) by intro e; ring]
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hnorm, one_mul]
    _ ≤ _ := by
      rw [hmean]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      split_ifs <;> nlinarith [mul_le_mul_of_nonneg_left hpair hε]

end CERW.LimitShapes.Crossing.ExponentialDrift
