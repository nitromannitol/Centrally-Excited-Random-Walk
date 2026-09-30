import CERW.Model
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# A cited result carried as a hypothesis

Hall and Heyde (1980), Corollary 3.1, cited at limit-shapes.tex lines 1401 and 1521. It is stated as a proposition and carried as an explicit hypothesis by every theorem whose
proof uses it; it is never assumed as an axiom. See `ASSUMPTIONS.md`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- Hall and Heyde (1980), Corollary 3.1, cited at limit-shapes.tex lines 1401 and 1521. -/
-- FROZEN-STATEMENT-BEGIN
def CERW.External.MartingaleCLT : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ), Martingale S ℱ μ → (∀ n, MemLp (S n) 2 μ) →
    (∀ ω, S 0 ω = 0) → ∀ (s : ℕ → ℝ), (∀ n, 0 < s n) → ∀ v : ℝ≥0,
    (∀ δ : ℝ, 0 < δ → TendstoInMeasure μ
      (fun n => ∑ i ∈ Finset.range n,
        μ[fun ω => ((S (i + 1) ω - S i ω) / s n) ^ 2 *
          (if δ < |S (i + 1) ω - S i ω| / s n then 1 else 0) | ℱ i])
      atTop (fun _ => 0)) →
    TendstoInMeasure μ (fun n => fun ω => CERW.predBracket μ ℱ S S n ω / s n ^ 2) atTop
      (fun _ => (v : ℝ)) →
    TendstoInDistribution (fun n ω => S n ω / s n) atTop id (fun _ => μ) (gaussianReal 0 v)
-- FROZEN-STATEMENT-END
