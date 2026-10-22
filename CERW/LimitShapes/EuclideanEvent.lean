import CERW.LimitShapes.Frozen.CommonEvent
import CERW.Support.Norm.EuclideanCoarse

/-!
# The common event for the Euclidean walk

The event at `sec:norm-event` specializes to the Euclidean norm and its radial
subgradient field. Its constants and time threshold are uniform over all
probability spaces and realizations of the Euclidean walk.
-/

universe u

open MeasureTheory

namespace CERW.LimitShapes.EuclideanEvent

open CERW.Support.Norm.EuclideanCoarse

/-- The Euclidean specialization of `sec:norm-event` has polynomial exceptional
probability, with all constants and the threshold chosen before the realization. -/
theorem exists_euclidean_event {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) (p : ℝ) (hp : 0 < p) :
    ∃ K : CERW.LimitShapes.EventConstants,
      0 < K.cCo ∧ 0 < K.CCo ∧ 0 < K.CLoc ∧ 0 < K.CQuad ∧
      0 < K.CSquare ∧ 0 < K.CMart ∧ 0 < K.CCross ∧
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure μ] (X : ℕ → Ω → LatticeProb.Site d),
          CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
          μ (CERW.LimitShapes.section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
              ε (fun x => CERW.unitDir (CERW.toSpace x)) K X n)ᶜ ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hell : ∀ i : Fin d, ε * ‖CERW.coordVec i‖ < 1 / (d : ℝ) := by
    intro i
    have hnorm : ‖CERW.coordVec i‖ = 1 := by simp [CERW.coordVec]
    rw [hnorm, mul_one]
    exact hεd
  have hξ : ∀ x : LatticeProb.Site d, x ≠ 0 →
      CERW.IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
        (CERW.toSpace x) (CERW.unitDir (CERW.toSpace x)) := by
    intro x hx
    exact isSubgradient_unitDir fun h => hx (eq_zero_of_toSpace_eq_zero h)
  obtain ⟨K, hcCo, hCCo, hCLoc, hCQuad, hCSquare, hCMart, hCCross,
    C, hC, n₀, hn₀, hprob⟩ :=
    CERW.LimitShapes.exists_common_event.{u} hd isNorm_euclidean hε hell p hp
  refine ⟨K, hcCo, hCCo, hCLoc, hCQuad, hCSquare, hCMart, hCCross,
    C, hC, n₀, hn₀, ?_⟩
  intro Ω _ μ _ X hX n hn
  exact hprob (fun x => CERW.unitDir (CERW.toSpace x)) hξ unitDir_toSpace_zero μ X
    ((CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX) n hn

end CERW.LimitShapes.EuclideanEvent
