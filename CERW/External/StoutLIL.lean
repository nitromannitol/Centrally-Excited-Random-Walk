import CERW.Model

/-!
# A cited result carried as a hypothesis

Stout (1970), Theorem 2, the lower half of the martingale law of the iterated logarithm, cited at limit-shapes.tex lines 1410, 1519 and 1644.
It is stated as a proposition and carried as an explicit hypothesis by every theorem whose proof
uses it; it is never assumed as an axiom. See `ASSUMPTIONS.md`. The upper half, Stout (1970),
Theorem 1, is proved: `CERW.Generic.Martingale.Lil.stout_upper`, and `CERW.Support.stoutLIL_full`
combines the two halves into the law that the proofs use.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- Stout (1970), Theorem 2: the lower half of the martingale law of the iterated logarithm,
cited at limit-shapes.tex lines 1410, 1519 and 1644. -/
-- FROZEN-STATEMENT-BEGIN
def CERW.External.StoutLIL : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ), Martingale S ℱ μ → (∀ n, MemLp (S n) 2 μ) →
    (∀ ω, S 0 ω = 0) → ∀ B : ℕ → Ω → ℝ, (∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) →
    (∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ B (n + 1) ω) →
    (∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω) atTop atTop) →
    (∀ᵐ ω ∂μ, Tendsto (fun n => B n ω *
        Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ S S n ω)
          (Real.exp (Real.exp 1))))) / Real.sqrt (CERW.predBracket μ ℱ S S n ω))
      atTop (𝓝 0)) →
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      ∃ᶠ n : ℕ in atTop, (1 - δ) * Real.sqrt (2 * CERW.predBracket μ ℱ S S n ω *
        Real.log (Real.log (CERW.predBracket μ ℱ S S n ω))) ≤ S n ω
-- FROZEN-STATEMENT-END
