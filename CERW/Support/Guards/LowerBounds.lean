import CERW.Frozen.BulkProfile
import CERW.Frozen.LogLowerBounds
import CERW.Frozen.SeparatedBrackets
import CERW.Frozen.SharpBulk
import CERW.Support.Law.Existence

/-!
# Non-vacuity guards for the lower-bound statements

The statements `bulk_profile`, `sharp_bulk`, `separated_brackets` and `log_lower_bounds` quantify
over all centrally excited random walks with parameter `ε`. For each of them the guard states
the conclusion at concrete parameters, in the plane with `ε = 1/8` and in space with `ε = 1/12`
(both satisfy `0 < ε < 1/d`), and proves it by applying the frozen theorem. A second guard shows
that a centrally excited random walk with these parameters exists, so that the quantified family
is not empty.
-/

namespace CERW.Support.Guards

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

/-- There is a probability space carrying a centrally excited random walk in the plane with
parameter `ε = 1/8`. -/
private theorem exists_cerw_plane :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X :=
  CERW.Support.Law.exists_isCERW (by norm_num) (by norm_num) (by norm_num)

/-- There is a probability space carrying a centrally excited random walk in space with
parameter `ε = 1/12`. -/
private theorem exists_cerw_space :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X :=
  CERW.Support.Law.exists_isCERW (by norm_num) (by norm_num) (by norm_num)

/-! ### `prop:bulk-profile` -/

/-- In the plane with `ε = 1/8`, `θ = 1/2` and `p = 1`, the bulk profile bound holds with a
finite constant for every centrally excited random walk. -/
theorem bulk_profile_applies :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * (1 / 8) * ωd)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    ∃ C : ℝ, 0 < C ∧
      let Good : (ℕ → Site 2) → ℕ → Prop := fun Y n =>
        ∀ y : Site 2, euclidNorm y ≤ (1 / 2) * r n →
          |(CERW.localTime Y n y : ℝ) - 2 * ((2 : ℕ) : ℝ) * (1 / 8) * (r n - euclidNorm y)|
            ≤ C * (Real.sqrt (r n) * Real.log n)
      (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ)))) ∧
      (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X →
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good (X · ω) n) :=
  CERW.Frozen.bulk_profile (d := 2) (le_refl 2) (1 / 8) (by norm_num) (by norm_num) (1 / 2)
    (by norm_num) (by norm_num) 1 one_pos

/-- The centrally excited random walk in the plane with `ε = 1/8`, to which
`bulk_profile_applies` applies, exists. -/
theorem bulk_profile_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X :=
  exists_cerw_plane

/-- In space with `ε = 1/12`, `θ = 1/2` and `p = 1`, the bulk profile bound holds with a
finite constant for every centrally excited random walk. -/
theorem bulk_profile_applies_space :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal
    let r : ℕ → ℝ := fun n =>
      ((((3 : ℕ) : ℝ) + 1) * n / (2 * ((3 : ℕ) : ℝ) * (1 / 12) * ωd)) ^
        ((1 : ℝ) / (((3 : ℕ) : ℝ) + 1))
    ∃ C : ℝ, 0 < C ∧
      let Good : (ℕ → Site 3) → ℕ → Prop := fun Y n =>
        ∀ y : Site 3, euclidNorm y ≤ (1 / 2) * r n →
          |(CERW.localTime Y n y : ℝ) - 2 * ((3 : ℕ) : ℝ) * (1 / 12) * (r n - euclidNorm y)|
            ≤ C * Real.sqrt (r n * Real.log n)
      (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ)))) ∧
      (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X →
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good (X · ω) n) :=
  CERW.Frozen.bulk_profile (d := 3) (by norm_num) (1 / 12) (by norm_num) (by norm_num) (1 / 2)
    (by norm_num) (by norm_num) 1 one_pos

/-- The centrally excited random walk in space with `ε = 1/12`, to which
`bulk_profile_applies_space` applies, exists. -/
theorem bulk_profile_inhabited_space :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X :=
  exists_cerw_space

/-! ### `thm:sharp`, part (iii) -/

/-- In the plane with `ε = 1/8`, the maximum of the local-time deviations over the ball of
radius `r_n^{1/2}` is at least `c √r_n log n`, with probability at least `1 - n^{-c}`, for all
large `n` and every centrally excited random walk. -/
theorem sharp_bulk_applies :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * (1 / 8) * ωd)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∃ x : Site 2, euclidNorm x ≤ Real.sqrt (r n) ∧
            c * (Real.sqrt (r n) * Real.log n)
              ≤ |(CERW.localTime (X · ω) n x : ℝ) -
                2 * ((2 : ℕ) : ℝ) * (1 / 8) * (r n - euclidNorm x)|}
          ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) :=
  CERW.Frozen.sharp_bulk (d := 2) (le_refl 2) (1 / 8) (by norm_num) (by norm_num)

/-- The centrally excited random walk in the plane with `ε = 1/8`, to which
`sharp_bulk_applies` applies, exists. -/
theorem sharp_bulk_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X :=
  exists_cerw_plane

/-- In space with `ε = 1/12`, the maximum of the local-time deviations over the ball of
radius `r_n^{1/2}` is at least `c √(r_n log n)`, with probability at least `1 - n^{-c}`, for
all large `n` and every centrally excited random walk. -/
theorem sharp_bulk_applies_space :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal
    let r : ℕ → ℝ := fun n =>
      ((((3 : ℕ) : ℝ) + 1) * n / (2 * ((3 : ℕ) : ℝ) * (1 / 12) * ωd)) ^
        ((1 : ℝ) / (((3 : ℕ) : ℝ) + 1))
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∃ x : Site 3, euclidNorm x ≤ Real.sqrt (r n) ∧
            c * Real.sqrt (r n * Real.log n)
              ≤ |(CERW.localTime (X · ω) n x : ℝ) -
                2 * ((3 : ℕ) : ℝ) * (1 / 12) * (r n - euclidNorm x)|}
          ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) :=
  CERW.Frozen.sharp_bulk (d := 3) (by norm_num) (1 / 12) (by norm_num) (by norm_num)

/-- The centrally excited random walk in space with `ε = 1/12`, to which
`sharp_bulk_applies_space` applies, exists. -/
theorem sharp_bulk_inhabited_space :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X :=
  exists_cerw_space

/-! ### `lem:separated-brackets` -/

/-- In the plane with `ε = 1/8`, the normalized brackets of the martingales `S^1, …, S^m` of
the proof have diagonal in `[c₀, C₀]` and off-diagonal at most `C r_n^{-1/4}`, outside an event
of probability at most `C n^{-10}`, for all large `n` and every centrally excited random
walk. -/
theorem separated_brackets_applies :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * (1 / 8) * ωd)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    let e₁ : Site 2 := LatticeProb.unit ⟨0, by omega⟩
    let g : Site 2 → ℝ := CERW.latticeKernel 2
    let σ : ℕ → ℝ := fun n => Real.sqrt (r n * Real.log (r n))
    let k : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let m : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let y : ℕ → ℕ → Site 2 := fun n i => ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • e₁
    let f : ℕ → ℕ → Site 2 → ℝ := fun n i z =>
      g (z - (y n i + (k n : ℤ) • e₁)) - g (z - y n i)
    ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∀ i j : ℕ, 1 ≤ i → i ≤ m n → 1 ≤ j → j ≤ m n →
            let B : ℝ := CERW.dynkinBracket (CERW.stepProb 2 (1 / 8)) (f n i) (f n j) (X · ω) n /
              σ n ^ 2
            (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C * r n ^ (-(1 : ℝ) / 4))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(10 : ℝ))) :=
  CERW.Frozen.separated_brackets (d := 2) (le_refl 2) (1 / 8) (by norm_num) (by norm_num)

/-- The centrally excited random walk in the plane with `ε = 1/8`, to which
`separated_brackets_applies` applies, exists. -/
theorem separated_brackets_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X :=
  exists_cerw_plane

/-- In space with `ε = 1/12`, the normalized brackets of the martingales `S^1, …, S^m` of
the proof have diagonal in `[c₀, C₀]` and off-diagonal at most `C r_n^{-1/4}`, outside an event
of probability at most `C n^{-10}`, for all large `n` and every centrally excited random
walk. -/
theorem separated_brackets_applies_space :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal
    let r : ℕ → ℝ := fun n =>
      ((((3 : ℕ) : ℝ) + 1) * n / (2 * ((3 : ℕ) : ℝ) * (1 / 12) * ωd)) ^
        ((1 : ℝ) / (((3 : ℕ) : ℝ) + 1))
    let e₁ : Site 3 := LatticeProb.unit ⟨0, by omega⟩
    let g : Site 3 → ℝ := CERW.latticeKernel 3
    let σ : ℕ → ℝ := fun n => Real.sqrt (r n)
    let m : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let y : ℕ → ℕ → Site 3 := fun n i => ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • e₁
    let f : ℕ → ℕ → Site 3 → ℝ := fun n i z => g (z - y n i)
    ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∀ i j : ℕ, 1 ≤ i → i ≤ m n → 1 ≤ j → j ≤ m n →
            let B : ℝ := CERW.dynkinBracket (CERW.stepProb 3 (1 / 12)) (f n i) (f n j) (X · ω) n /
              σ n ^ 2
            (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C * r n ^ (-(1 : ℝ) / 4))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(10 : ℝ))) :=
  CERW.Frozen.separated_brackets (d := 3) (by norm_num) (1 / 12) (by norm_num) (by norm_num)

/-- The centrally excited random walk in space with `ε = 1/12`, to which
`separated_brackets_applies_space` applies, exists. -/
theorem separated_brackets_inhabited_space :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X :=
  exists_cerw_space

/-! ### `prop:log-lower` -/

/-- In the plane with `ε = 1/8`, the tail bounds and the almost-sure logarithmic lower bounds
for the radii hold for every centrally excited random walk. -/
theorem log_lower_bounds_applies :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * (1 / 8) * ωd)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    ∃ c C h₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X →
        (∀ n : ℕ, n₀ ≤ n → ∀ h : ℝ, h₀ ≤ h → h ≤ r n / 8 →
          μ {ω | r n - h ≤ CERW.innerRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ r n + h}
            ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (2 - 1) * Real.exp (-(C * h))))) ∧
          μ {ω | CERW.maxRadius (X · ω) n ≤ r n + h}
            ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (2 - 1) * Real.exp (-(C * h))))
              + Real.exp (-(c * r n ^ (((2 : ℕ) : ℝ) - 3) * h ^ 2)))) ∧
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          c * Real.log n < max (r n - CERW.innerRadius (X · ω) n)
            (CERW.maxRadius (X · ω) n - r n) ∧
          (3 ≤ 2 → c * Real.log n < CERW.maxRadius (X · ω) n - r n) :=
  CERW.Frozen.log_lower_bounds (d := 2) (le_refl 2) (1 / 8) (by norm_num) (by norm_num)

/-- The centrally excited random walk in the plane with `ε = 1/8`, to which
`log_lower_bounds_applies` applies, exists. -/
theorem log_lower_bounds_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 8) X :=
  exists_cerw_plane

/-- In space with `ε = 1/12`, the tail bounds and the almost-sure logarithmic lower bounds
for the radii, including the one for the outer radius alone, hold for every centrally excited
random walk. -/
theorem log_lower_bounds_applies_space :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal
    let r : ℕ → ℝ := fun n =>
      ((((3 : ℕ) : ℝ) + 1) * n / (2 * ((3 : ℕ) : ℝ) * (1 / 12) * ωd)) ^
        ((1 : ℝ) / (((3 : ℕ) : ℝ) + 1))
    ∃ c C h₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X →
        (∀ n : ℕ, n₀ ≤ n → ∀ h : ℝ, h₀ ≤ h → h ≤ r n / 8 →
          μ {ω | r n - h ≤ CERW.innerRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ r n + h}
            ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (3 - 1) * Real.exp (-(C * h))))) ∧
          μ {ω | CERW.maxRadius (X · ω) n ≤ r n + h}
            ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (3 - 1) * Real.exp (-(C * h))))
              + Real.exp (-(c * r n ^ (((3 : ℕ) : ℝ) - 3) * h ^ 2)))) ∧
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          c * Real.log n < max (r n - CERW.innerRadius (X · ω) n)
            (CERW.maxRadius (X · ω) n - r n) ∧
          (3 ≤ 3 → c * Real.log n < CERW.maxRadius (X · ω) n - r n) :=
  CERW.Frozen.log_lower_bounds (d := 3) (by norm_num) (1 / 12) (by norm_num) (by norm_num)

/-- The centrally excited random walk in space with `ε = 1/12`, to which
`log_lower_bounds_applies_space` applies, exists. -/
theorem log_lower_bounds_inhabited_space :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 3), CERW.IsCERW μ (1 / 12) X :=
  exists_cerw_space

end CERW.Support.Guards
