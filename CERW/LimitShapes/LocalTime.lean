import CERW.Frozen.NormLocalTime

/-!
# Approximation of local times by the potential

The approximation in `lem:local` is the third clause of the
earlier local-time lemma. The other two clauses are not part of this statement.
-/

universe u

open MeasureTheory
open LatticeProb (Site)

namespace CERW.LimitShapes

/-- The approximation estimate of Lemma 3.1, for a deterministic path. -/
def LocalApproximation {d : ℕ} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε C : ℝ)
    (X : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
    |CERW.cellLocalTime X n y - CERW.normPotential d ε Ψ (CERW.cellSet X n) y| ≤
      C * Real.log n + C *
        (if d = 2 then Real.sqrt (CERW.maxLocalTime X n) * Real.log n
          else Real.sqrt (CERW.maxLocalTime X n * Real.log n))

end CERW.LimitShapes

/-- The uniform local-time approximation with its polynomial exceptional probability. -/
theorem CERW.LimitShapes.local_time_potential_bound {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
            |CERW.cellLocalTime (X · ω) n y
                - CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y| ≤
              C * Real.log n + C *
                (if d = 2 then Real.sqrt (CERW.maxLocalTime (X · ω) n) * Real.log n
                  else Real.sqrt (CERW.maxLocalTime (X · ω) n * Real.log n))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
:= by
  intro Ψ hΨ ε hε hell p hp
  obtain ⟨C, hC, h⟩ := CERW.Frozen.norm_local_time_potential hd Ψ hΨ ε hε hell p hp
  refine ⟨C, hC, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_⟩
  refine le_trans ?_ (h ξ hξ hξ0 μ X hX n hn)
  apply measure_mono
  intro ω hbad hgood
  exact hbad hgood.2.2
