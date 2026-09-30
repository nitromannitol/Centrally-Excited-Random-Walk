import CERW.Support.Main.HausdorffAssembly

/-!
# The one-sided Hausdorff bound

`eq:hausdorff` with the one-sided planar remark (variant (A) of the freeze proposal). It is the
two-sided statement `hausdorff_bound_of_core` without the unvisited site: the exceptional set
of the one-sided statement is contained in the exceptional set of the two-sided one.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Main

open CERW CERW.Support.LocalTime

/-- `eq:hausdorff` with the one-sided planar remark, for any kernel `b` with the kernel facts,
given the deterministic core (`hcore`, the statement of `exists_good_of_event`). -/
theorem hausdorff_bound_one_sided_of_core {d : ℕ} (hd : 2 ≤ d)
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
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        let L : ℝ := Real.log (n + 2)
        μ {ω | ¬ (Metric.hausdorffEDist
                    ((fun x => N⁻¹ • CERW.toSpace x) '' ↑(CERW.visitedRange (X · ω) n))
                    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) a)
                  ≤ ENNReal.ofReal (C * (if d = 2 then (n : ℝ) ^ (-(1 : ℝ) / 12) * L ^ ((5 : ℝ) / 4)
                      else (n : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
                        * L ^ ((2 * d : ℝ) / (2 * d - 1)))) ∧
                  (d = 2 → {x : Site d | euclidNorm x < a * N - C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L} ⊆ ↑(CERW.departureRange (X · ω) n)))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro ωd ε hε hεd a p hp
  obtain ⟨C, n₀, hC, hn₀, hbound⟩ :=
    hausdorff_bound_of_core (d := d) hd hK hcore ε hε hεd p hp
  refine ⟨C, n₀, hC, hn₀, ?_⟩
  intro Ω _ μ _ X hX n hn
  dsimp only
  refine (measure_mono ?_).trans (hbound μ X hX n hn)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro htwo
  exact hω ⟨htwo.1, fun hd2 => (htwo.2 hd2).1⟩

end CERW.Support.Main
