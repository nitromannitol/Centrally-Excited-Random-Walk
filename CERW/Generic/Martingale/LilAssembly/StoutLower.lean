import CERW.Generic.Martingale.LilAssembly.ReductionProof
import CERW.Generic.Martingale.LilAssembly.BlockLowerProof
import CERW.Generic.Martingale.LilAssembly.NiceLower

/-!
# The lower half of Stout's law of the iterated logarithm

The conditional lower bound for the blocks (`block_lower`) gives the lower bound for padded data
(`niceLower_of`), and the reduction (`reduction_of`) turns that into the lower half of the law.
-/

universe u

namespace CERW.Generic.Martingale.LilAssembly

/-- **The lower half of Stout's law of the iterated logarithm**, Stout (1970), Theorem 2, proved
from Mathlib: the proposition `CERW.Generic.Martingale.Lil.StoutLower`. -/
theorem stout_lower : CERW.Generic.Martingale.Lil.StoutLower.{u} :=
  reduction_of.{u} (niceLower_of.{u} block_lower.{u})

end CERW.Generic.Martingale.LilAssembly
