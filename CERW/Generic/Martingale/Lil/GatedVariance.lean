import CERW.Generic.Martingale.Lil.Statements

/-!
# A predictable gate does not increase the conditional variances

The increments of `predictableStop M W w` are those of `M` times a gate with values in `[0, 1]`,
so their conditional variances are at most those of `M`.
-/

universe u

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology CERW.Generic.Martingale

/-- A predictable gate does not increase the conditional variances of the increments. -/
theorem gated_variance : GatedVariance.{u} := by
  intro Ω m0 μ _ ℱ M W w _ hL2 hW k
  have hint : Integrable (fun ω => (M (k + 1) ω - M k ω) ^ 2) μ :=
    ((hL2 (k + 1)).sub (hL2 k)).integrable_sq
  have hg : AEStronglyMeasurable (bracketIndicator W w k) μ :=
    ((stronglyMeasurable_bracketIndicator (v := w) hW k).mono (ℱ.le k)).aestronglyMeasurable
  have heq : (fun ω => (predictableStop M W w (k + 1) ω - predictableStop M W w k ω) ^ 2)
      = fun ω => bracketIndicator W w k ω * (M (k + 1) ω - M k ω) ^ 2 := by
    funext ω
    rw [predictableStop_succ_sub, mul_pow, sq (bracketIndicator W w k ω),
      bracketIndicator_mul_self]
  have hint' : Integrable (fun ω =>
      (predictableStop M W w (k + 1) ω - predictableStop M W w k ω) ^ 2) μ := by
    rw [heq]
    refine Integrable.bdd_mul hint hg (c := 1) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (bracketIndicator_nonneg W w k ω)]
    exact bracketIndicator_le_one W w k ω
  refine condExp_mono hint' hint (Filter.Eventually.of_forall fun ω => ?_)
  have h := congrFun heq ω
  beta_reduce
  rw [h]
  have hnn : 0 ≤ (M (k + 1) ω - M k ω) ^ 2 := sq_nonneg _
  exact mul_le_of_le_one_left hnn (bracketIndicator_le_one W w k ω)

end CERW.Generic.Martingale.Lil
