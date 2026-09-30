import CERW.Support.Main.EventProb
import CERW.Support.Main.GoodMono
import CERW.Support.Main.BorelCantelli
import CERW.Support.Main.ShapeAssembly

/-!
# The fluctuation and shape theorems from the kernel facts

`thm:fluctuations`: for each `p`, `exists_event_prob` bounds the failure probability of
`fluctEvent`, and the deterministic core `hcore` (the statement of `exists_good_of_event`)
shows that `fluctEvent` implies `fluctGood` for large `n`. One constant serves both, by
`fluctGood_mono`. With `p = 2`, `ae_eventually_of_le_rpow` gives the almost-sure conjunct.
`thm:shape` then follows from `ball_shape_of_ae_good`.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Main

open CERW CERW.Support.LocalTime

/-- `thm:fluctuations`, for any kernel `b` with the kernel facts, given the deterministic core
(`hcore`, the statement of `exists_good_of_event`). -/
theorem fluctuation_bounds_of_core {d : ℕ} (hd : 2 ≤ d)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h)
    (hcore : ∀ ε : ℝ, 0 < ε → ∀ C₀ C₁ : ℝ, 0 < C₀ → 0 < C₁ → ∀ bd r₀ : ℕ, 1 ≤ bd →
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type u} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        let L : ℝ := Real.log (n + 2)
        let Q : ℝ :=
          if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
        fluctEvent d ε b C₀ C₁ bd r₀ X ω n →
          fluctGood d ε C (fun j => X j ω) n ∧
          ∃ x : Site d, x ∉ CERW.departureRange (fun j => X j ω) n ∧
            euclidNorm x < a * N + C * N * Q) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    let L : ℕ → ℝ := fun n => Real.log (n + 2)
    let Q : ℕ → ℝ := fun n =>
      if d = 2 then (L n / N n) ^ ((1 : ℝ) / 2) else (L n / N n) ^ ((d : ℝ) / (2 * d - 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      {x : Site d | euclidNorm x < (a - C * Q n) * N n} ⊆ ↑(CERW.departureRange Y n) ∧
      (↑(CERW.departureRange Y n) : Set (Site d)) ⊆ ↑(CERW.visitedRange Y n) ∧
      (↑(CERW.visitedRange Y n) : Set (Site d)) ⊆
        {x | euclidNorm x < (a + C * Q n ^ ((1 : ℝ) / d) * L n) * N n} ∧
      volume (((N n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a)
          + ENNReal.ofReal |((CERW.departureRange Y n).card : ℝ) / N n ^ d - ωd * a ^ d|
        ≤ ENNReal.ofReal (C * Q n) ∧
      ∀ x : Site d,
        |(CERW.localTime Y n x : ℝ) / N n - 2 * d * ε * max (a - euclidNorm x / N n) 0|
          ≤ C * Q n ^ ((1 : ℝ) / d)
    (∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Good C (X · ω) n) := by
  intro ωd ε hε hεd a N L Q Good
  have hfirst : ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
    intro p hp
    let bd : ℕ := ⌈Real.sqrt d / 2⌉₊ + 6
    have hbd : 1 ≤ bd := by simp only [bd]; omega
    obtain ⟨r₀, hr₀⟩ := exists_event_prob (d := d) hd hK
    obtain ⟨C₀, C₁, hC₀, hC₁, hprob⟩ := hr₀ ε hε hεd p hp
    obtain ⟨C, hC, n₀, hcore'⟩ := hcore ε hε C₀ C₁ hC₀ hC₁ bd r₀ hbd
    refine ⟨max C C₁, max n₀ 2, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le hC (le_max_left C C₁)
    · omega
    · intro Ω _ μ _ X hX n hn
      have hnp : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hn₀ : n₀ ≤ n := (le_max_left n₀ 2).trans hn
      have hn₂ : 2 ≤ n := (le_max_right n₀ 2).trans hn
      calc μ {ω | ¬ Good (max C C₁) (X · ω) n}
          ≤ μ {ω | ¬ fluctEvent d ε b C₀ C₁ bd r₀ X ω n} := by
            refine measure_mono ?_
            intro ω hω
            simp only [Set.mem_setOf_eq] at hω ⊢
            intro hfe
            exact hω (fluctGood_mono (le_max_left C C₁) ((hcore' X ω n hn₀ hfe).1))
        _ ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (-p)) := hprob μ X hX n hn₂
        _ ≤ ENNReal.ofReal (max C C₁ * (n : ℝ) ^ (-p)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            exact mul_le_mul_of_nonneg_right (le_max_right C C₁) hnp
  refine ⟨hfirst, ?_⟩
  obtain ⟨C₂, n₂, hC₂, hn₂, hprob₂⟩ := hfirst 2 (by norm_num)
  refine ⟨C₂, hC₂, ?_⟩
  intro Ω _ μ _ X hX
  refine ae_eventually_of_le_rpow (p := 2) (C := C₂) (by norm_num) (n₀ := n₂) ?_
  intro n hn
  exact hprob₂ μ X hX n hn

/-- `thm:shape`, for any kernel `b` with the kernel facts, given the deterministic core. -/
theorem ball_shape_of_core {d : ℕ} (hd : 2 ≤ d)
    {b : Site d → ℝ} {h : ℝ → ℝ} (hK : KernelFacts d b h)
    (hcore : ∀ ε : ℝ, 0 < ε → ∀ C₀ C₁ : ℝ, 0 < C₀ → 0 < C₁ → ∀ bd r₀ : ℕ, 1 ≤ bd →
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type u} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        let L : ℝ := Real.log (n + 2)
        let Q : ℝ :=
          if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
        fluctEvent d ε b C₀ C₁ bd r₀ X ω n →
          fluctGood d ε C (fun j => X j ω) n ∧
          ∃ x : Site d, x ∉ CERW.departureRange (fun j => X j ω) n ∧
            euclidNorm x < a * N + C * N * Q)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < a → ∀ᶠ n in atTop,
        {x : Site d | euclidNorm x < (a - η) * N n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆ ↑(CERW.visitedRange (X · ω) n) ∧
        (↑(CERW.visitedRange (X · ω) n) : Set (Site d)) ⊆
          {x | euclidNorm x < (a + η) * N n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) / N n - 2 * d * ε * max (a - euclidNorm x / N n) 0|
          ≤ η) ∧
      Tendsto (fun n => ((CERW.visitedRange (X · ω) n).card : ℝ) / N n ^ d) atTop
        (𝓝 (ωd * a ^ d)) ∧
      (∀ x : Site d,
        Tendsto (fun n => (CERW.localTime (X · ω) n x : ℝ) / N n) atTop (𝓝 (2 * d * ε * a))) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x) := by
  have h1 := fluctuation_bounds_of_core (d := d) hd hK hcore
  obtain ⟨C, hC, hG⟩ := (h1 ε hε hεd).2
  exact ball_shape_of_ae_good hd hε hC.le μ X (hG μ X hX)

end CERW.Support.Main
