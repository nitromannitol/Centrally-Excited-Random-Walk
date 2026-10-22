import CERW.LimitShapes.Event

/-!
# Exact predictable brackets of the Dynkin martingales

The pathwise conditional-variance formula agrees almost surely with the
predictable quadratic variation defined by conditional expectation.
-/

open MeasureTheory ProbabilityTheory Filter
open LatticeProb (Site)

namespace CERW.LimitShapes

open CERW CERW.Support.Law CERW.Support.Drift

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
  {X : ℕ → Ω → Site d}

/-- The exact conditional variance of an increment of a Dynkin martingale. -/
theorem condExp_sq_driftDynkin_eq (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) (hX : IsDriftCERW μ ε ξ X)
    (f : Site d → ℝ) (t : ℕ) :
    μ[fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) ^ 2 |
        pathFiltration hX.measurable t] =ᵐ[μ]
      fun ω => (∑ e ∈ unitSteps d,
          driftStepProb d ε ξ (X · ω) t e * (f (X t ω + e) - f (X t ω)) ^ 2) -
        stepMean (driftStepProb d ε ξ) f (X · ω) t ^ 2 := by
  let h : ((i : Finset.Iic t) → Site d) → Site d → ℝ :=
    fun p z => (f z - driftNextMean ε ξ f (extendPath p) t) ^ 2
  have hsq : (fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) ^ 2) =
      fun ω => h (pastPath X t ω) (X (t + 1) ω) := by
    funext ω
    rw [driftDynkin_succ_sub, driftNextMean_pastPath]
  have hint := integrable_path_next_drift hd hε hξ hX t h
  rw [hsq]
  filter_upwards [condExp_path_next_drift hd hε hξ hX t h hint] with ω hω
  rw [hω]
  simp only [h, ← driftNextMean_pastPath]
  have hvar := sum_mul_sub_mean_sq (unitSteps d)
    (fun e => driftStepProb d ε ξ (X · ω) t e)
    (fun e => f (X t ω + e)) (sum_driftStepProb hd ε ξ (X · ω) t) (f (X t ω))
  simp only [driftNextMean]
  rw [hvar]
  have hmean : stepMean (driftStepProb d ε ξ) f (X · ω) t =
      (∑ e ∈ unitSteps d, driftStepProb d ε ξ (X · ω) t e * f (X t ω + e)) - f (X t ω) := by
    unfold stepMean
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_driftStepProb hd ε ξ (X · ω) t, one_mul]
  rw [hmean]

/-- The predictable quadratic variation is the transition-kernel bracket, at every time
simultaneously almost surely. -/
theorem ae_predBracket_driftDynkin (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) (hX : IsDriftCERW μ ε ξ X)
    (f : Site d → ℝ) :
    ∀ᵐ ω ∂μ, ∀ n : ℕ,
      predBracket μ (pathFiltration hX.measurable)
        (driftDynkin ε ξ f X) (driftDynkin ε ξ f X) n ω =
      dynkinBracket (driftStepProb d ε ξ) f f (X · ω) n := by
  have hall := ae_all_iff.mpr (fun t : ℕ => condExp_sq_driftDynkin_eq hd hε hξ hX f t)
  filter_upwards [hall] with ω hω n
  rw [predBracket, Finset.sum_apply, dynkinBracket]
  simp only [← pow_two]
  exact Finset.sum_congr rfl fun t _ => hω t

end CERW.LimitShapes
