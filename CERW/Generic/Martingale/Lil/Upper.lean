import CERW.Generic.Martingale.Lil.RegBracket
import CERW.Generic.Martingale.Lil.GatedVariance
import CERW.Generic.Martingale.Lil.FirstPassage
import CERW.Generic.Martingale.Lil.MaximalFreedman
import CERW.Generic.Martingale.Lil.TruncatedBlock
import CERW.Generic.Martingale.Lil.Arith
import CERW.Generic.Martingale.Lil.BlockSummable
import CERW.Generic.Martingale.Lil.Pathwise
import CERW.Generic.Martingale.Lil.Assembly

/-!
# The upper half of the martingale law of the iterated logarithm

Stout (1970), Theorem 1, with an `ℱ_n`-measurable bound `B_{n+1}` on the increments: almost surely,
for every `δ > 0`, eventually `S_n ≤ (1 + δ) √(2 ⟨S⟩_n log log ⟨S⟩_n)`. It is the first conjunct
of the law of the iterated logarithm that the revised paper cites, proved here from its steps in
`CERW.Generic.Martingale.Lil.Statements`.
-/

universe u

namespace CERW.Generic.Martingale.Lil

/-- The upper half of Stout's law of the iterated logarithm (Stout 1970, Theorem 1). -/
theorem stout_upper : StoutUpper.{u} :=
  stoutUpper_of reg_bracket
    (truncatedBlock_of gated_variance (maximalFreedman_of gated_variance first_passage))
    lil_arith block_summable (pathwiseUpper_of lil_arith)

end CERW.Generic.Martingale.Lil
