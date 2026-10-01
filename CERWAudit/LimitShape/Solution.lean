import Mathlib
import CERW.Frozen.LimitShape
import CERWAudit.LimitShape.SolutionBasic
import CERWAudit.Support.LimitShapeBridge

/-!
# Solution: `LimitShape` (limit shape)

The challenge module `CERWAudit/LimitShape/Challenge.lean` imports only Mathlib and states
`limit_shape` with one intentional `sorry`.  This solution imports the repository `CERW`
together with `CERWAudit.LimitShape.SolutionBasic` — a verbatim copy of the challenge's
statement vocabulary — and proves the byte-identical statement from
`CERW.Frozen.limit_shape` (`CERW/Frozen/LimitShape.lean`) through the bridge in
`CERWAudit/Support/LimitShapeBridge.lean`.

The transport is definitional.  The audit vocabulary (`Site`, `euclidNorm`, `stepProb`,
`localTime`, `departureRange`, `visitedRange`, …) is a token-for-token copy of the
repository's, so the conclusion of the library theorem is definitionally equal to the goal;
the only non-definitional step is packaging the challenge's `IsCERW` structure into the
repository's, which `isCERW_iff` does field by field.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise

namespace CERW
namespace StatementAudit
namespace LimitShape

open CERWAudit.Support.LimitShapeBridge

/-- **Limit shape** (`thm:shape`, `limit-shapes.tex:103-116`): for `d ≥ 2` and `0 < ε < 1/d`,
almost surely, with `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}`: for every `0 < η < 1` and all
sufficiently large `n` the departure range contains the Euclidean ball of radius
`(1 - η) r_n` and is contained in the ball of radius `(1 + η) r_n`; the departure local times
converge to the cone `2 d ε (r_n - |x|)_+` at rate `η r_n`; and every site is visited
infinitely often. -/
theorem limit_shape {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | euclidNorm x < (1 - η) * r n} ⊆ ↑(departureRange (X · ω) n) ∧
        (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | euclidNorm x < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)
    := by
  exact CERW.Frozen.limit_shape hd hε hεd μ X (isCERW_iff.mp hX)

end LimitShape
end StatementAudit
end CERW
