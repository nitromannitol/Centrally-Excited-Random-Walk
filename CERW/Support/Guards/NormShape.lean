import CERW.Frozen.LimitShape
import CERW.Frozen.NormShape
import CERW.Frozen.NormBallPotential
import CERW.Frozen.NormLocalTime
import CERW.Frozen.FreedmanBound
import CERW.Support.Main.NormGuards

/-!
# Guards for the limit shape of a norm

The hypotheses of `limit_shape`, `norm_shape`, `norm_ball_potential`, `norm_local_time_potential`
and `freedman_bound` can hold together at concrete parameters, so the statements are not
vacuous. The ball shape is at `d = 2` and `ε = 1/4`; the norm shape is at `d = 3`, `ε = 1/4` and
the Euclidean norm with the field `x/|x|`; the potential of a ball and the local time bounds are
at `d = 2`, `ε = 1/4`, the Euclidean norm and exponent `p = 1`; the martingale bound is at
`p = 1`. Each statement that quantifies over a realization of the walk, or over a martingale,
comes with a proof that such an object exists.
-/

namespace CERW.Support.Guards

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

/-- In dimension two with `ε = 1/4`, almost surely every realization of the walk fills a
Euclidean ball of radius `r_n`, has the local time profile of the cone `2dε(r_n - |x|)_+`, and
visits every site infinitely often. -/
theorem limit_shape_applies :
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 4 : ℝ) X →
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((2 + 1) * n / (2 * 2 * (1 / 4) * ωd)) ^ ((1 : ℝ) / (2 + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site 2 | euclidNorm x < (1 - η) * r n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site 2)) ⊆
          {x | euclidNorm x < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site 2,
        |(CERW.localTime (X · ω) n x : ℝ) - 2 * 2 * (1 / 4) * max (r n - euclidNorm x) 0|
          ≤ η * r n) ∧
      (∀ x : Site 2, ∃ᶠ j in atTop, X j ω = x) := by
  have hd : 2 ≤ 2 := le_rfl
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hεd : (1 / 4 : ℝ) < 1 / ((2 : ℕ) : ℝ) := by norm_num
  intro Ω _ μ _ X hX
  exact CERW.Frozen.limit_shape hd hε hεd μ X hX

/-- In dimension two with `ε = 1/4`, there is a probability space carrying a centrally excited
random walk. -/
theorem limit_shape_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 4 : ℝ) X :=
  CERW.Support.Law.exists_isCERW (by norm_num) (by norm_num) (by norm_num)

/-- In dimension three with `ε = 1/4`, for the Euclidean norm and the subgradients `x/|x|`,
almost surely the range of the walk is asymptotically the Euclidean ball of radius `r_n`, the
local times follow the cone `2dε(r_n - |x|)_+`, and every site is visited infinitely often. -/
theorem norm_shape_applies :
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site 3),
      CERW.IsDriftCERW μ (1 / 4 : ℝ) (fun x : Site 3 => CERW.unitDir (CERW.toSpace x)) X →
    let r : ℕ → ℝ := fun n =>
      ((3 + 1) * n / (2 * 3 * (1 / 4) *
        CERW.normBallVolume (fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖))) ^ ((1 : ℝ) / (3 + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site 3 | ‖CERW.toSpace x‖ < (1 - η) * r n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site 3)) ⊆
          {x | ‖CERW.toSpace x‖ < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site 3,
        |(CERW.localTime (X · ω) n x : ℝ) - 2 * 3 * (1 / 4) * max (r n - ‖CERW.toSpace x‖) 0|
          ≤ η * r n) ∧
      (∀ x : Site 3, ∃ᶠ j in atTop, X j ω = x) := by
  have hd : 2 ≤ 3 := by norm_num
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hεd : (1 / 4 : ℝ) < 1 / ((3 : ℕ) : ℝ) := by norm_num
  obtain ⟨hΨ, hξ, hξ0, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := 3) hεd
  intro Ω _ μ _ X hX
  exact CERW.Frozen.norm_shape hd hΨ hξ hξ0 hε hell μ X hX

/-- In dimension three with `ε = 1/4`, there is a probability space carrying the walk with the
Euclidean norm and the subgradients `x/|x|`. -/
theorem norm_shape_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 3),
      CERW.IsDriftCERW μ (1 / 4 : ℝ) (fun x : Site 3 => CERW.unitDir (CERW.toSpace x)) X := by
  have hεd : (1 / 4 : ℝ) < 1 / ((3 : ℕ) : ℝ) := by norm_num
  obtain ⟨hΨ, hξ, hξ0, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := 3) hεd
  exact CERW.Support.Main.exists_norm_realization (by norm_num) hΨ hξ hξ0 (by norm_num) hell

/-- In dimension three with `ε = 1/4`, the Euclidean norm admits a subgradient selection with
value zero at the origin together with a realization of the walk that uses it. -/
theorem norm_shape_selection_inhabited :
    ∃ ξ : Site 3 → EuclideanSpace ℝ (Fin 3),
      (∀ x : Site 3, x ≠ 0 → CERW.IsSubgradient (fun v => ‖v‖) (CERW.toSpace x) (ξ x)) ∧
      ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 3), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X := by
  have hεd : (1 / 4 : ℝ) < 1 / ((3 : ℕ) : ℝ) := by norm_num
  obtain ⟨hΨ, -, -, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := 3) hεd
  exact CERW.Support.Main.norm_hypotheses_inhabited (by norm_num) hΨ (by norm_num) hell

/-- The potential of the unit disc for the Euclidean norm with `ε = 1/4` is the cone
`(1 - |y|)_+`. -/
theorem norm_ball_potential_applies (y : EuclideanSpace ℝ (Fin 2)) :
    CERW.normPotential 2 (1 / 4 : ℝ) (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖)
      {v | ‖v‖ < 1} y = max (1 - ‖y‖) 0 := by
  obtain ⟨hΨ, -, -, -⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := 2)
    (ε := 1 / 4) (by norm_num)
  have hρ : (0 : ℝ) < 1 := one_pos
  have h := CERW.Frozen.norm_ball_potential (by norm_num) hΨ (1 / 4 : ℝ) hρ y
  rw [h]
  norm_num

/-- The potential of the unit disc for the Euclidean norm with `ε = 1/4` equals `1` at the
center. -/
theorem norm_ball_potential_center :
    CERW.normPotential 2 (1 / 4 : ℝ) (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖)
      {v | ‖v‖ < 1} 0 = 1 := by
  rw [norm_ball_potential_applies 0]
  norm_num

/-- In dimension two with `ε = 1/4`, for the Euclidean norm and exponent `p = 1`, there is a
constant `C > 0` such that, for every realization of the walk with any subgradient selection, the
largest local time, the interval local times and the approximation of the cell local time by the
potential hold with probability at least `1 - C n⁻¹`. -/
theorem norm_local_time_potential_applies :
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 → CERW.IsSubgradient (fun v => ‖v‖) (CERW.toSpace x) (ξ x)) →
        ξ 0 = 0 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ((CERW.maxLocalTime (X · ω) n : ℝ)
                    ≤ C * ((CERW.departureRange (X · ω) n).card : ℝ) ^ ((1 : ℝ) / 2)
                      + C * Real.log n ^ 2 ∧
                  (∀ s t : ℕ, s < t → t ≤ n →
                    (CERW.intervalMax (X · ω) s t : ℝ)
                      ≤ C * (CERW.freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / 2)
                        + C * Real.log n ^ 2) ∧
                  ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ ≤ 2 * n →
                    |CERW.cellLocalTime (X · ω) n y
                        - CERW.normPotential 2 (1 / 4 : ℝ) (fun v => ‖v‖)
                          (CERW.cellSet (X · ω) n) y|
                      ≤ C * Real.log n + C *
                        (if (2 : ℕ) = 2 then
                          Real.sqrt (CERW.maxLocalTime (X · ω) n) * Real.log n
                          else Real.sqrt (CERW.maxLocalTime (X · ω) n * Real.log n)))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-1 : ℝ)) := by
  have hd : 2 ≤ 2 := le_rfl
  have hεd : (1 / 4 : ℝ) < 1 / ((2 : ℕ) : ℝ) := by norm_num
  obtain ⟨hΨ, -, -, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := 2) hεd
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hp : (0 : ℝ) < 1 := one_pos
  exact CERW.Frozen.norm_local_time_potential hd _ hΨ (1 / 4 : ℝ) hε hell 1 hp

/-- In dimension two with `ε = 1/4`, the Euclidean norm admits a subgradient selection with value
zero at the origin together with a realization of the walk that uses it. -/
theorem norm_local_time_potential_inhabited :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → CERW.IsSubgradient (fun v => ‖v‖) (CERW.toSpace x) (ξ x)) ∧
      ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X := by
  have hεd : (1 / 4 : ℝ) < 1 / ((2 : ℕ) : ℝ) := by norm_num
  obtain ⟨hΨ, -, -, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := 2) hεd
  exact CERW.Support.Main.norm_hypotheses_inhabited (by norm_num) hΨ (by norm_num) hell

/-- With exponent `p = 1`, there is a constant `C > 0` such that every martingale with increments
of absolute value at most one satisfies `|Z_n - Z_0| ≤ C (√(⟨Z⟩_n log n) + log n)` with
probability at least `1 - C n⁻¹`. -/
theorem freedman_bound_applies :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
      ∀ {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ), Martingale Z ℱ μ →
        (∀ᵐ ω ∂μ, ∀ t, |Z (t + 1) ω - Z t ω| ≤ 1) →
        μ {ω | ¬ |Z n ω - Z 0 ω|
            ≤ C * (Real.sqrt (CERW.predBracket μ ℱ Z Z n ω * Real.log n) + Real.log n)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-1 : ℝ)) :=
  CERW.Frozen.freedman_bound 1 one_pos

end CERW.Support.Guards
