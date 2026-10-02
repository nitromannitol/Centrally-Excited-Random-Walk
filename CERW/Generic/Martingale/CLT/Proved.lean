import CERW.Generic.Martingale.CLT.Assembly
import CERW.Generic.Martingale.CLT.Truncation
import CERW.Generic.Martingale.CLT.IncrementStep
import CERW.Generic.Martingale.CLT.Compensated
import CERW.Generic.Martingale.CLT.CharFunBound
import CERW.Generic.Martingale.CLT.ArrayTendsto

/-!
# The martingale central limit theorem, proved

The packets of this directory prove, one lemma each, the statements of `Interfaces`. Each packet
theorem takes the lemmas it uses as explicit hypotheses, stated in the polymorphic form of the
corresponding `Statement`. This file discharges those hypotheses in dependency order and applies
the assembly, which gives `CERW.Generic.Martingale.CLT.MartingaleCLT` outright.

Every `Statement` is an `abbrev` over the universe `u` of the sample space, and every packet
theorem quantifies over `Ω : Type u`. A packet theorem is therefore applied with its universe
written out, `compensated_cexp_bound.{u}`, so that the hypothesis it receives and the sample
space it is applied to live in the same universe.
-/

universe u

namespace CERW.Generic.Martingale.CLT

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal

/-- The path bracket is zero at time `0`, nondecreasing, predictable, and almost surely equal to
the predictable bracket. -/
theorem pathBracketProperties_holds : PathBracketPropertiesStatement.{u} := by
  intro Ω m0 μ hμ ℱ M
  exact pathBracket_predictable_nondecreasing_ae_eq_predBracket μ ℱ M

/-- The increment cut off where the path bracket exceeds `c` has conditional mean zero and the
conditional second moment of the increment times the cut-off indicator. -/
theorem truncatedIncrementCondExp_holds : TruncatedIncrementCondExpStatement.{u} := by
  intro Ω m0 μ hμ ℱ M c hc hM hL k
  exact condExp_truncated_increment_eq_zero_and_condExp_sq_eq hM hL c k

/-- The truncated conditional variances sum to at most `c`, and truncation does not increase the
conditional Lindeberg terms. -/
theorem truncatedIncrementBounds_holds : TruncatedIncrementBoundsStatement.{u} := by
  intro Ω m0 μ hμ ℱ M c hc hM hL h0 n δ
  exact sum_condExp_sq_truncated_le_and_lindeberg_term_le hM hL hc n δ

/-- The bound on the compensated exponential built from the predictably truncated martingale. -/
theorem compensatedCexpBound_holds : CompensatedCexpBoundStatement.{u} := by
  intro Ω m0 μ hμ ℱ M c hc hM hL h0 n t δ hδ
  exact compensated_cexp_bound.{u} cexp_increment_step_bound.{u} pathBracketProperties_holds.{u}
    truncatedIncrementCondExp_holds.{u} truncatedIncrementBounds_holds.{u}
    μ ℱ M c hc hM hL h0 n t δ hδ

/-- The characteristic function of the last term of a square-integrable martingale is within an
explicit error of the Gaussian one. -/
theorem charFunMartingaleBound_holds : CharFunMartingaleBoundStatement.{u} := by
  intro Ω m0 μ hμ ℱ M hM hL h0 v hv n t δ η hδ hη hη1
  exact charFun_martingale_bound.{u} compensatedCexpBound_holds.{u}
    truncatedIncrementCondExp_holds.{u} truncatedIncrementBounds_holds.{u}
    μ ℱ M hM hL h0 v hv n t δ η hδ hη hη1

/-- The characteristic functions of the last terms of the rows of a martingale array converge to
the Gaussian one. -/
theorem arrayCharFunTendsto_holds : ArrayCharFunTendstoStatement.{u} :=
  array_charFun_tendsto.{u} charFunMartingaleBound_holds.{u}

/-- Convergence of characteristic functions to the Gaussian one gives convergence in
distribution. -/
theorem tendstoInDistributionOfCharFun_holds : TendstoInDistributionOfCharFunStatement.{u} := by
  intro Ω m0 μ hμ X v hX h
  exact tendstoInDistribution_gaussianReal_of_tendsto_integral_cexp μ X v hX h

/-- **The martingale central limit theorem** of Hall and Heyde (1980), Corollary 3.1, in the form
`CERW.Generic.Martingale.CLT.MartingaleCLT` that the paper uses, proved from Mathlib and the lemmas
of this directory. -/
theorem martingaleCLT_proved : CERW.Generic.Martingale.CLT.MartingaleCLT.{u} :=
  martingaleCLT_holds.{u} arrayCharFunTendsto_holds.{u} tendstoInDistributionOfCharFun_holds.{u}

end CERW.Generic.Martingale.CLT
