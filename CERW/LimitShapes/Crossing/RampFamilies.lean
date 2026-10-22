import CERW.LimitShapes.Crossing.RampBound

/-!
# Simultaneous ramp estimates at all prefixes and grid levels

A finite union turns the horizon Freedman estimate into one event for every
prefix, grid level and direction in a deterministic finite family. The size
of that family remains explicit in the exceptional probability.
-/

universe u

open MeasureTheory ProbabilityTheory LatticeProb

namespace CERW.LimitShapes.Crossing.RampFamilies

open CERW

/-- A single polynomial exceptional bound for all prefixes and grid levels in a finite
deterministic family of directions whose norms are at most `Λ`. -/
theorem exists_prefix_ramp_family_bound {Λ : ℝ} (hΛ : 0 ≤ Λ) (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ}, 1 ≤ d →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)),
        0 ≤ ε → (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X →
      ∀ N : ℕ, 2 ≤ N → ∀ Q : Finset (EuclideanSpace ℝ (Fin d)),
        (∀ q ∈ Q, ‖q‖ ≤ Λ) →
        μ {ω | ¬ ∀ n : ℕ, n ≤ N → ∀ q ∈ Q, ∀ k : ℕ, k ≤ N →
          |dynkinMart (driftStepProb d ε ξ)
            (fun z => max (inner ℝ q (toSpace z) - k * Λ) 0) (X · ω) n| ≤
            C * (Real.sqrt (Real.log N * ∑ z ∈ (departureRange (X · ω) n).filter
              (fun z => k * Λ - Λ < inner ℝ q (toSpace z)), (localTime (X · ω) n z : ℝ)) +
              Real.log N)} ≤
          ENNReal.ofReal (C * (Q.card : ℝ) * ((N : ℝ) + 1) ^ 2 * (N : ℝ) ^ (-p)) := by
  obtain ⟨C, hC, hF⟩ := RampBound.exists_ramp_freedman_bound.{u} hΛ p hp
  refine ⟨C, hC, ?_⟩
  intro d hd Ω _ μ _ ε ξ hε hξ X hX N hN Q hQ
  classical
  let T := Finset.range (N + 1)
  let E : ℕ → EuclideanSpace ℝ (Fin d) → ℕ → Set Ω := fun n q k =>
    {ω | ¬ |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * Λ) 0) (X · ω) n| ≤
      C * (Real.sqrt (Real.log N * ∑ z ∈ (departureRange (X · ω) n).filter
        (fun z => k * Λ - Λ < inner ℝ q (toSpace z)), (localTime (X · ω) n z : ℝ)) +
          Real.log N)}
  have hsub : {ω | ¬ ∀ n : ℕ, n ≤ N → ∀ q ∈ Q, ∀ k : ℕ, k ≤ N →
      |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * Λ) 0) (X · ω) n| ≤
        C * (Real.sqrt (Real.log N * ∑ z ∈ (departureRange (X · ω) n).filter
          (fun z => k * Λ - Λ < inner ℝ q (toSpace z)), (localTime (X · ω) n z : ℝ)) +
            Real.log N)} ⊆ ⋃ n ∈ T, ⋃ q ∈ Q, ⋃ k ∈ T, E n q k := by
    intro ω hbad
    simp only [Set.mem_setOf_eq, not_forall] at hbad
    obtain ⟨n, hn, q, hq, k, hk, hbad⟩ := hbad
    simp only [Set.mem_iUnion]
    exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), q, hq, k,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hk), hbad⟩
  have htail : ∀ n ∈ T, ∀ q ∈ Q, ∀ k : ℕ,
      μ (E n q k) ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-p)) := by
    intro n hn q hq k
    exact hF hd μ ε ξ hε hξ X hX N hN n
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) q (hQ q hq) (k * Λ)
  refine (measure_mono hsub).trans ?_
  calc μ (⋃ n ∈ T, ⋃ q ∈ Q, ⋃ k ∈ T, E n q k)
      ≤ ∑ n ∈ T, μ (⋃ q ∈ Q, ⋃ k ∈ T, E n q k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ T, ∑ q ∈ Q, μ (⋃ k ∈ T, E n q k) :=
      Finset.sum_le_sum fun n _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ T, ∑ q ∈ Q, ∑ k ∈ T, μ (E n q k) :=
      Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ _n ∈ T, ∑ _q ∈ Q, ∑ _k ∈ T, ENNReal.ofReal (C * (N : ℝ) ^ (-p)) :=
      Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun q hq =>
        Finset.sum_le_sum fun k _ => htail n hn q hq k
    _ = ENNReal.ofReal ((T.card : ℝ) * ((Q.card : ℝ) *
        ((T.card : ℝ) * (C * (N : ℝ) ^ (-p))))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp only [ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (C * (Q.card : ℝ) * ((N : ℝ) + 1) ^ 2 * (N : ℝ) ^ (-p)) := by
      congr 1
      dsimp [T]
      rw [Finset.card_range]
      push_cast
      ring

end CERW.LimitShapes.Crossing.RampFamilies
