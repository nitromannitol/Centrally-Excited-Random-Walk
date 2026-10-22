import CERW.LimitShapes.EuclideanSeparatedBrackets

/-!
# Separated brackets on the common event

The event defining Ωₙ at `lem:separated-brackets` is the event of `sec:norm-event`
at exponent ten. Its constants are selected before the Euclidean walk and its law.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site)

/-- Separated bracket bounds on the actual common event with its polynomial
probability estimate at exponent ten and source-uniform constants. -/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.LimitShapes.separated_brackets_on_euclidean_event {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let e₁ : Site d := LatticeProb.unit ⟨0, by omega⟩
    let g : Site d → ℝ := CERW.latticeKernel d
    let σ : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (r n * Real.log (r n)) else Real.sqrt (r n)
    let k : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let m : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let y : ℕ → ℕ → Site d := fun n i => ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • e₁
    let f : ℕ → ℕ → Site d → ℝ := fun n i z =>
      if d = 2 then g (z - (y n i + (k n : ℤ) • e₁)) - g (z - y n i) else g (z - y n i)
    ∃ K : CERW.LimitShapes.EventConstants,
      0 < K.cCo ∧ 0 < K.CCo ∧ 0 < K.CLoc ∧ 0 < K.CQuad ∧
      0 < K.CSquare ∧ 0 < K.CMart ∧ 0 < K.CCross ∧
    ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ (CERW.LimitShapes.section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
            ε (fun x => CERW.unitDir (CERW.toSpace x)) K X n)ᶜ ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (-(10 : ℝ))) ∧
        ∀ᵐ ω ∂μ, ω ∈ CERW.LimitShapes.section5Event
            (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε
            (fun x => CERW.unitDir (CERW.toSpace x)) K X n →
          ∀ i j : ℕ, 1 ≤ i → i ≤ m n → 1 ≤ j → j ≤ m n →
            let B : ℝ := CERW.dynkinBracket (CERW.stepProb d ε) (f n i) (f n j)
              (X · ω) n / σ n ^ 2
            (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C * r n ^ (-(1 : ℝ) / 4))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.LimitShapes.EuclideanSeparatedBrackets.separated_brackets_on_euclidean_event hd
