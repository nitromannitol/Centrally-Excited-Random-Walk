import CERW.Generic.Martingale.Lil.Statements

/-!
# A regular version of the predictable bracket

The sum `V_k = Σ_{t<k} max(E[(S_{t+1} - S_t)² | ℱ_t], 0)` is surely nondecreasing, starts at
`0`, has `V_{k+1}` `ℱ_k`-measurable, dominates the conditional variances of the increments, and
equals the predictable bracket `CERW.predBracket` almost surely at all times.
-/

universe u

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology

/-- A version of the predictable bracket that is surely nondecreasing and predictable. -/
theorem reg_bracket : RegBracket.{u} := by
  intro Ω m0 μ _ ℱ S
  let c : ℕ → Ω → ℝ := fun t => μ[fun ω => (S (t + 1) ω - S t ω) ^ 2 | ℱ t]
  refine ⟨fun k ω => ∑ t ∈ Finset.range k, max (c t ω) 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    refine Finset.stronglyMeasurable_fun_sum _ fun t ht => ?_
    have htk : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    exact (((stronglyMeasurable_condExp (m := ℱ t)).mono (ℱ.mono htk)).measurable.max
      measurable_const).stronglyMeasurable
  · intro ω
    exact Finset.sum_range_zero _
  · intro k ω
    dsimp only
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (le_max_right _ _)
  · intro k
    refine Filter.Eventually.of_forall fun ω => ?_
    dsimp only
    rw [Finset.sum_range_succ, add_sub_cancel_left]
    exact le_max_left _ _
  · have hpb : ∀ t ω, CERW.predBracket μ ℱ S S (t + 1) ω - CERW.predBracket μ ℱ S S t ω
        = c t ω := by
      intro t ω
      simp only [CERW.predBracket, Finset.sum_range_succ, Finset.sum_apply, add_sub_cancel_left,
        c, sq]
    have h : ∀ t, ∀ᵐ ω ∂μ, max (c t ω) 0 = (CERW.predBracket μ ℱ S S (t + 1) ω
        - CERW.predBracket μ ℱ S S t ω) := by
      intro t
      have hnn : 0 ≤ᵐ[μ] c t :=
        condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      filter_upwards [hnn] with ω hω
      rw [hpb]
      exact max_eq_left hω
    filter_upwards [ae_all_iff.2 h] with ω hω k
    induction k with
    | zero => simp [CERW.predBracket]
    | succ k ih =>
        rw [Finset.sum_range_succ, ih, hω k]
        ring

end CERW.Generic.Martingale.Lil
