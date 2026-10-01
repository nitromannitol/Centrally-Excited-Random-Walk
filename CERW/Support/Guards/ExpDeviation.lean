import CERW.Frozen.ExpDeviation
import Mathlib.Probability.Distributions.Uniform

/-!
# Guard for the exponential-deviation lemma

`lem:exp-deviation` is abstract. A guard exhibits a nontrivial instance of every one of its
hypotheses on a two-point probability space: the single coin flip revealed at time `1` by the
filtration `ℱ 0 = ⊥`, `ℱ t = ⊤` for `t ≥ 1`. The one-step martingale `coinMart` has increments
of size one and predictable bracket exactly `1` at time `1`, so with `c₀ = C₀ = 1`, `α = 0` and
`E = univ` all the hypotheses hold and the conclusions of the lemma apply.
-/

namespace CERW.Support.Guards

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The two-point probability space underlying the guard. -/
private abbrev Coin := Bool

/-- The uniform measure on the two-point space. -/
private noncomputable def coinMeasure : Measure Coin := (PMF.uniformOfFintype Coin).toMeasure

private instance : IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure
  infer_instance

/-- The filtration that reveals the single coin at time one. -/
private def coinFiltration : Filtration ℕ (⊤ : MeasurableSpace Coin) where
  seq t := if t = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · subst hi
      exact bot_le
    · have hj : j ≠ 0 := by omega
      simp [hi, hj]
  le' := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact bot_le
    · simp [hi]

/-- The one-step martingale of the guard. -/
private def coinMart : ℕ → Coin → ℝ :=
  fun t ω => if t = 0 then 0 else if ω then 1 else -1

private theorem coinFiltration_zero : coinFiltration 0 = ⊥ := by simp [coinFiltration]

private theorem coinFiltration_pos {t : ℕ} (ht : t ≠ 0) : coinFiltration t = ⊤ := by
  simp [coinFiltration, ht]

private theorem coinMart_zero : coinMart 0 = fun _ => (0 : ℝ) := by
  funext ω; simp [coinMart]

private theorem coinMart_pos {t : ℕ} (ht : t ≠ 0) :
    coinMart t = fun ω => if ω then 1 else -1 := by
  funext ω; simp [coinMart, ht]

private theorem coinMart_eq_one {t : ℕ} (ht : t ≠ 0) : coinMart t = coinMart 1 := by
  rw [coinMart_pos ht, coinMart_pos (by norm_num : (1 : ℕ) ≠ 0)]

private theorem coinMeasure_singleton (b : Coin) : coinMeasure {b} = 1 / 2 := by
  unfold coinMeasure
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), PMF.uniformOfFintype_apply]
  norm_num

private theorem integrable_coinMart : Integrable (coinMart 1) coinMeasure := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (by fun_prop : Measurable (coinMart 1)).aestronglyMeasurable
  · filter_upwards with ω
    cases ω <;> simp [coinMart]

private theorem integral_coinMart :
    ∫ ω, coinMart 1 ω ∂coinMeasure = 0 := by
  have h : ∀ b : Coin, coinMeasure.real {b} = 1 / 2 := by
    intro b
    rw [Measure.real, coinMeasure_singleton]
    norm_num
  rw [integral_fintype integrable_coinMart]
  simp only [h]
  rw [Fintype.sum_bool]
  norm_num [coinMart]

private theorem integral_coinMart_sq :
    ∫ ω, (coinMart 1 ω - coinMart 0 ω) ^ 2 ∂coinMeasure = 1 := by
  have hfun : (fun ω => (coinMart 1 ω - coinMart 0 ω) ^ 2) = fun _ => (1 : ℝ) := by
    funext ω
    cases ω <;> simp [coinMart]
  rw [hfun, integral_const, Measure.real, measure_univ]
  norm_num

private theorem coinMart_stronglyAdapted : StronglyAdapted coinFiltration coinMart := by
  intro t
  by_cases ht : t = 0
  · subst ht
    rw [coinFiltration_zero, coinMart_zero]
    exact stronglyMeasurable_const
  · rw [coinFiltration_pos ht]
    exact (Measurable.of_discrete (f := coinMart t)).stronglyMeasurable

private theorem coinMart_martingale : Martingale coinMart coinFiltration coinMeasure := by
  refine ⟨coinMart_stronglyAdapted, ?_⟩
  intro i j hij
  by_cases hi : i = 0
  · subst hi
    rw [coinFiltration_zero, condExp_bot]
    filter_upwards with ω
    by_cases hj : j = 0
    · subst hj; simp [coinMart]
    · have hjeq : coinMart j = coinMart 1 := coinMart_eq_one hj
      rw [hjeq, integral_coinMart]
      simp [coinMart]
  · have hj : j ≠ 0 := by omega
    rw [coinFiltration_pos hi]
    haveI : SigmaFinite (coinMeasure.trim (le_refl (⊤ : MeasurableSpace Coin))) := inferInstance
    rw [condExp_of_stronglyMeasurable (le_refl (⊤ : MeasurableSpace Coin))
      ((Measurable.of_discrete (f := coinMart j)).stronglyMeasurable)
      (by rw [coinMart_eq_one hj]; exact integrable_coinMart)]
    rw [coinMart_pos hj, coinMart_pos hi]

private theorem predBracket_coinMart :
    CERW.predBracket coinMeasure coinFiltration coinMart coinMart 1 = fun _ => 1 := by
  funext ω
  rw [CERW.predBracket, Finset.range_one, Finset.sum_singleton]
  rw [coinFiltration_zero, condExp_bot]
  have hfun : (fun ω' => (coinMart (0 + 1) ω' - coinMart 0 ω') *
        (coinMart (0 + 1) ω' - coinMart 0 ω'))
      = fun ω' => (coinMart 1 ω' - coinMart 0 ω') ^ 2 := by
    funext ω'; ring
  rw [hfun, integral_coinMart_sq]

/-- The hypotheses of `lem:exp-deviation` hold at `c₀ = C₀ = 1`, `m = n = 1`, `b = 1`,
`δ = 0`, `α = 0` and `E = univ` on the one-step coin martingale, whose predictable bracket
at time one is exactly `1`. -/
theorem exp_deviation_applies :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ β : ℝ, C ≤ β → β * 1 ≤ c →
        (∀ _i : Fin 1, Real.exp (-(C * β ^ 2)) / 4 - 0 ≤
              (coinMeasure {ω | c * β ≤ coinMart 1 ω}).toReal ∧
            Real.exp (-(C * β ^ 2)) / 4 - 0 ≤
              (coinMeasure {ω | coinMart 1 ω ≤ -(c * β)}).toReal) ∧
          ((∀ _i _j : Fin 1, _i ≠ _j → ∀ᵐ ω ∂coinMeasure, ω ∈ Set.univ →
                |CERW.predBracket coinMeasure coinFiltration coinMart coinMart 1 ω| ≤ 0) →
            β ^ 2 * 0 + β ^ 3 * 1 ≤ 1 →
            (coinMeasure {ω | ∀ _i : Fin 1, coinMart 1 ω < c * β}).toReal
              ≤ C * (((1 : ℕ) : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * 0 + β ^ 3 * 1
                + Real.exp (C * β ^ 2) * Real.sqrt 0)) := by
  obtain ⟨c, C, hc, hC, h⟩ := CERW.Frozen.exp_deviation.{0} 1 1 (by norm_num) le_rfl
  refine ⟨c, C, hc, hC, fun β hβ hβb => ?_⟩
  exact h (m0 := ⊤) coinMeasure coinFiltration 1 1 one_pos one_pos 1 0 0
    (by norm_num) le_rfl le_rfl (by norm_num)
    (fun _ => coinMart) (fun _ => coinMart_martingale) (fun _ _ => by simp [coinMart])
    (fun _ t ht ω => by
      have ht0 : t = 0 := by omega
      subst ht0
      cases ω <;> simp [coinMart])
    Set.univ MeasurableSet.univ (by rw [measure_univ]; norm_num)
    (fun _ => by
      filter_upwards with ω _
      rw [predBracket_coinMart]
      norm_num)
    β hβ hβb

end

end CERW.Support.Guards
