import CERW.Support.Main.ShapeInclusion
import CERW.Support.Main.ShapeCount

/-!
# The shape theorem from the almost-sure fluctuation event

`thm:shape`, given the almost-sure conjunct of `thm:fluctuations`. Suppose that for almost every
`ω` the event `fluctGood d ε C (X · ω) n` holds for all large `n`. Then almost surely the ball
inclusions, the uniform profile convergence, the count asymptotics, the fixed-site limits and the
recurrence of `thm:shape` all hold.
-/

universe u

namespace CERW.Support.Main

open Filter Topology MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- `thm:shape` from the almost-sure fluctuation event. -/
theorem ball_shape_of_ae_good (hd : 2 ≤ d) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → Site d)
    (hG : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, fluctGood d ε C (X · ω) n) :
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
  intro ωd a N
  filter_upwards [hG] with ω hω
  have hSP := sandwich_and_profile_of_good hd (Y := (X · ω)) hω
  have hCP := count_and_pointwise_of_good hd hε hC (Y := (X · ω)) hω
  dsimp only at hSP hCP
  obtain ⟨hinc, hprof⟩ := hSP
  obtain ⟨hcard, hpoint, hrec⟩ := hCP
  refine ⟨?_, hprof, hcard, hpoint, ?_⟩
  · intro η hη _
    exact hinc η hη
  · intro x
    exact hrec x

end CERW.Support.Main
