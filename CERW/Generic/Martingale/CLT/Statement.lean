import CERW.Model
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# The statement of the martingale central limit theorem

Hall and Heyde (1980), Corollary 3.1, in the form the paper uses, cited at limit-shapes.tex lines
1399 and 1519. It is proved, as `CERW.Generic.Martingale.CLT.martingaleCLT_proved`. Until ruling D6
it was the cited External `CERW.External.MartingaleCLT`, carried as a hypothesis.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- Hall and Heyde (1980), Corollary 3.1, the martingale central limit theorem in the form the paper
uses; proved as `CERW.Generic.Martingale.CLT.martingaleCLT_proved`. -/
def CERW.Generic.Martingale.CLT.MartingaleCLT : Prop :=
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
