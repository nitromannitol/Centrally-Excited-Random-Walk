import CERW.Generic.Martingale.LilLower.CoinSpace
import CERW.Model.Bracket

/-!
# The hypotheses of the lower half of Stout's law are satisfiable

A witness for the hypotheses of `CERW.Generic.Martingale.Lil.StoutLower`: the walk whose steps are
independent fair signs, with the constant bound `1`. Its predictable bracket at time `n` is `n`,
so the bracket tends to infinity and the ratio `√(log log n) / √n` tends to zero.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower

/-- The quotient `√(log log (x ∨ e^e)) / √x` tends to zero as `x` tends to infinity. -/
private lemma tendsto_sqrt_loglog_div_sqrt :
    Tendsto (fun x : ℝ => Real.sqrt (Real.log (Real.log (max x (Real.exp (Real.exp 1))))) /
      Real.sqrt x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (Real.log x / x)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlog
    rwa [Real.sqrt_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun x => by positivity) ?_ hsqrt
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1))] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx : Real.exp 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hx
  have h1 : 1 ≤ Real.log x := by linarith [Real.add_one_le_exp 1]
  rw [max_eq_left hx, ← Real.sqrt_div (Real.log_nonneg h1)]
  refine Real.sqrt_le_sqrt ?_
  exact div_le_div_of_nonneg_right (Real.log_le_self (by linarith)) hx0.le

/-- A process whose increments are signs has predictable bracket at time `n` equal to `n`. -/
private lemma predBracket_walk {Ξ : Type*} {mΞ : MeasurableSpace Ξ} (ν : Measure Ξ)
    [IsProbabilityMeasure ν] (ℱ : Filtration ℕ mΞ) {S ε : ℕ → Ξ → ℝ}
    (hinc : ∀ n ξ, S (n + 1) ξ - S n ξ = ε (n + 1) ξ) (hsq : ∀ j ξ, ε j ξ ^ 2 = 1)
    (n : ℕ) (ξ : Ξ) : CERW.predBracket ν ℱ S S n ξ = n := by
  have hterm : ∀ t, (fun ξ => (S (t + 1) ξ - S t ξ) * (S (t + 1) ξ - S t ξ)) = fun _ => (1 : ℝ) :=
    fun t => funext fun ξ => by rw [hinc, ← sq, hsq]
  unfold CERW.predBracket
  rw [Finset.sum_apply]
  simp only [hterm, condExp_const (ℱ.le _)]
  simp

/-- There are a probability space, a filtration, a martingale `S` and a predictable bound `B`
satisfying every hypothesis of `CERW.Generic.Martingale.Lil.StoutLower`. -/
theorem stoutLower_hypotheses_satisfiable :
    ∃ (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ),
        Martingale S ℱ μ ∧ (∀ n, MemLp (S n) 2 μ) ∧ (∀ ω, S 0 ω = 0) ∧
        (∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) ∧
        (∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ B (n + 1) ω) ∧
        (∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω) atTop atTop) ∧
        (∀ᵐ ω ∂μ, Tendsto (fun n => B n ω *
          Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ S S n ω)
            (Real.exp (Real.exp 1))))) / Real.sqrt (CERW.predBracket μ ℱ S S n ω))
          atTop (𝓝 0)) := by
  obtain ⟨Ξ, mΞ, ν, hν, 𝒦, ε, hε⟩ := exists_signSequence
  have habs : ∀ j ξ, |ε j ξ| ≤ 1 := fun j ξ => (sq_le_one_iff_abs_le_one _).1 (hε.sq_eq_one j ξ).le
  have hmeas : ∀ j, StronglyMeasurable (ε (j + 1)) := fun j => (hε.measurable j).mono (hε.le _)
  have hmem : ∀ j, MemLp (ε (j + 1)) 2 ν := fun j =>
    MemLp.of_bound (hmeas j).aestronglyMeasurable 1
      (Eventually.of_forall fun ξ => by simpa using habs (j + 1) ξ)
  have hinc : ∀ (n : ℕ) (ξ : Ξ), (∑ j ∈ Finset.range (n + 1), ε (j + 1) ξ) -
      ∑ j ∈ Finset.range n, ε (j + 1) ξ = ε (n + 1) ξ := fun n ξ => by
    rw [Finset.sum_range_succ, add_sub_cancel_left]
  have hSmem : ∀ n, MemLp (fun ξ => ∑ j ∈ Finset.range n, ε (j + 1) ξ) 2 ν := fun n =>
    memLp_finsetSum _ fun j _ => hmem j
  refine ⟨Ξ, mΞ, ν, hν, ⟨𝒦, hε.mono, hε.le⟩, fun n ξ => ∑ j ∈ Finset.range n, ε (j + 1) ξ,
    fun _ _ => 1, ?_, hSmem, fun ξ => Finset.sum_range_zero _, fun _ => stronglyMeasurable_const,
    Eventually.of_forall fun ξ n => ?_, Eventually.of_forall fun ξ => ?_,
    Eventually.of_forall fun ξ => ?_⟩
  · refine martingale_of_condExp_sub_eq_zero_nat (fun n => ?_)
      (fun n => (hSmem n).integrable one_le_two) fun i => ?_
    · refine Finset.stronglyMeasurable_fun_sum (Finset.range n) fun j hj => ?_
      exact (hε.measurable j).mono (hε.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hj)))
    · have h : ((fun ξ => ∑ j ∈ Finset.range (i + 1), ε (j + 1) ξ) -
          fun ξ => ∑ j ∈ Finset.range i, ε (j + 1) ξ) = ε (i + 1) := funext (hinc i)
      change ν[(fun ξ => ∑ j ∈ Finset.range (i + 1), ε (j + 1) ξ) -
        (fun ξ => ∑ j ∈ Finset.range i, ε (j + 1) ξ) | 𝒦 i] =ᵐ[ν] 0
      rw [h]
      exact hε.condExp_eq_zero i
  · rw [hinc]
    exact habs _ _
  · exact tendsto_natCast_atTop_atTop.congr fun n =>
      (predBracket_walk ν _ (S := fun n ξ => ∑ j ∈ Finset.range n, ε (j + 1) ξ) hinc
        hε.sq_eq_one n ξ).symm
  · refine (tendsto_sqrt_loglog_div_sqrt.comp tendsto_natCast_atTop_atTop).congr fun n => ?_
    rw [predBracket_walk ν _ (S := fun n ξ => ∑ j ∈ Finset.range n, ε (j + 1) ξ) hinc
      hε.sq_eq_one n ξ, one_mul]
    rfl

end CERW.Generic.Martingale.LilAssembly
