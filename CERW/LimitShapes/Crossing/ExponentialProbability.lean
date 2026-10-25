module

public import CERW.LimitShapes.Crossing.ExponentialTail
public import CERW.LimitShapes.Crossing.Levels
public import CERW.LimitShapes.Crossing.DistanceGeometry
public import CERW.Generic.Martingale.Arith
public import CERW.Support.Occupation.Facts

@[expose] public section

/-!
# Simultaneous distance crossings from exponential tails

The fixed-level exponential tail and a finite union over levels and exterior local
times prove the simultaneous estimate in the paper's equation `eq:distance-crossing`.
Real levels follow by radial rounding.
-/

universe u

open MeasureTheory Filter LatticeProb CERW CERW.LimitShapes

namespace CERW.LimitShapes.Crossing.ExponentialProbability

/-- The simultaneous distance crossing estimate follows from fixed-level exponential tails,
with a constant uniform over subgradient fields and probability laws. -/
theorem distance_crossing_from_exponential {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ N : ℕ, 2 ≤ N →
        μ {ω | ¬ CERW.LimitShapes.DistanceCrossingBound Ψ C (X · ω) N} ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc, _⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc
    (CERW.Support.Norm.ProjectionGeometry.normMin_le_normMax hΨ hd1)
  obtain ⟨C₀, hC₀, htail⟩ :=
    ExponentialTail.exists_measure_distance_crossing_le hd hΨ hε hell p hp
  obtain ⟨Cd, hCd, hround⟩ :=
    Levels.distanceCrossingBound_of_integer_levels hd1 hΨ hC₀.le
  let Cf := 4 * C₀ * (normMax Ψ + 2)
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  refine ⟨Cd + Cf, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX N hN
  classical
  let A := Finset.range (⌈normMax Ψ * N⌉₊ + 1)
  let T := Finset.range (N + 1)
  let E := fun (m L : ℕ) => {ω | ∃ t ≤ N,
    exteriorLocalTime Ψ (X · ω) t m ≤ L ∧ ∃ j ≤ t,
      C₀ * (L + 1 : ℝ) * Real.log N ≤
        Metric.infDist (toSpace (X j ω)) {v | Ψ v ≤ (m : ℝ)}}
  let B : Set Ω := ⋃ m ∈ A, ⋃ L ∈ T, E m L
  have hE : ∀ m L, μ (E m L) ≤ ENNReal.ofReal (C₀ * (N : ℝ) ^ (-p - 2)) := by
    intro m L
    exact htail ξ hξ hξ0 μ X hX N hN L m (Nat.cast_nonneg m)
  have hB : μ B ≤ ENNReal.ofReal
      ((A.card : ℝ) * ((T.card : ℝ) * (C₀ * (N : ℝ) ^ (-p - 2)))) := by
    calc μ B ≤ ∑ m ∈ A, μ (⋃ L ∈ T, E m L) := measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ A, ∑ L ∈ T, μ (E m L) :=
        Finset.sum_le_sum fun _ _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ A, ∑ _L ∈ T, ENNReal.ofReal (C₀ * (N : ℝ) ^ (-p - 2)) :=
        Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun L _ => hE m L
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ A.card from Nat.cast_nonneg _),
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ T.card from Nat.cast_nonneg _)]
        simp only [ENNReal.ofReal_natCast]
  have hcard : (A.card : ℝ) ≤ (normMax Ψ + 2) * ((N : ℝ) + 1) := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ normMax Ψ * N by positivity)).le
    dsimp [A]
    rw [Finset.card_range, Nat.cast_add, Nat.cast_one]
    nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  have hprob : μ B ≤ ENNReal.ofReal (Cf * (N : ℝ) ^ (-p)) := by
    apply hB.trans
    apply ENNReal.ofReal_le_ofReal
    have hpow := CERW.Generic.Martingale.pow_mul_rpow_neg_le
      (by omega : 1 ≤ N) 2 p
    have hexp : -p - 2 = -(p + (2 : ℕ)) := by norm_num; ring
    have htcard : (T.card : ℝ) = (N : ℝ) + 1 := by
      dsimp [T]
      rw [Finset.card_range, Nat.cast_add, Nat.cast_one]
    rw [htcard, hexp]
    calc
      _ ≤ ((normMax Ψ + 2) * ((N : ℝ) + 1)) *
          (((N : ℝ) + 1) * (C₀ * (N : ℝ) ^ (-(p + (2 : ℕ))))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (C₀ * (normMax Ψ + 2)) *
          (((N : ℝ) + 1) ^ 2 * (N : ℝ) ^ (-(p + (2 : ℕ)))) := by ring
      _ ≤ (C₀ * (normMax Ψ + 2)) * (2 ^ 2 * (N : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = Cf * (N : ℝ) ^ (-p) := by dsimp [Cf]; ring
  have hcoord := CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
  have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by rw [ae_iff]; exact hX.start
  have hs := ae_all_iff.mpr
    (CERW.Support.Drift.ae_sub_mem_unitSteps_drift hd1 hε.le hcoord hX)
  have hsub : {ω | ¬ DistanceCrossingBound Ψ (Cd + Cf) (X · ω) N} ≤ᵐ[μ] B := by
    filter_upwards [h0, hs] with ω hstart hstep hbad
    by_contra hb
    have hgood : DistanceCrossingBound Ψ Cd (X · ω) N := by
      apply hround (X · ω) hstart hstep N hN
      intro m _ hm t ht j hj
      have hL : exteriorLocalTime Ψ (X · ω) t m ≤ N := by
        apply (Finset.sup_le fun z _ => ?_).trans ht
        exact (localTime_le_maxLocalTime (X · ω) t z).trans
          (CERW.Support.Occupation.maxLocalTime_le (X · ω) t)
      have hnot : ω ∉ E m (exteriorLocalTime Ψ (X · ω) t m) := by
        intro he
        apply hb
        change ω ∈ ⋃ m ∈ A, ⋃ L ∈ T, E m L
        apply Set.mem_iUnion_of_mem m
        apply Set.mem_iUnion_of_mem (show m ∈ A from Finset.mem_range.mpr (by omega))
        apply Set.mem_iUnion_of_mem (exteriorLocalTime Ψ (X · ω) t m)
        exact Set.mem_iUnion_of_mem (Finset.mem_range.mpr (by omega) :
          exteriorLocalTime Ψ (X · ω) t m ∈ T) he
      have hdist : Metric.infDist (toSpace (X j ω)) {v | Ψ v ≤ (m : ℝ)} <
          C₀ * (exteriorLocalTime Ψ (X · ω) t m + 1 : ℝ) * Real.log N := by
        exact lt_of_not_ge (fun hh => hnot ⟨t, ht, le_rfl, j, hj, hh⟩)
      rw [← DistanceGeometry.inf_dist_eq_norm_sub_projection hΨ (Nat.cast_nonneg m)]
      simpa only [add_comm] using hdist.le
    apply hbad
    intro t ht a ha j hj
    exact (hgood t ht a ha j hj).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : Cd ≤ Cd + Cf) (by positivity))
        (Real.log_natCast_nonneg N))
  exact (measure_mono_ae hsub).trans (hprob.trans
    (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith : Cf ≤ Cd + Cf) (by positivity))))

end CERW.LimitShapes.Crossing.ExponentialProbability
