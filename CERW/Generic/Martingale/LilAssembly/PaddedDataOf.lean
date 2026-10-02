import CERW.Generic.Martingale.LilAssembly.PaddedStructure
import CERW.Generic.Martingale.LilAssembly.PaddedRatio
import CERW.Generic.Martingale.LilAssembly.PaddedBlocks

/-!
# The padded data of a martingale with sure data

The thirteen fields of `PaddedData` for the padded process of a martingale with sure data, on the
product with a coin space, are the theorems of `PaddedStructure`, `PaddedRatio` and `PaddedBlocks`.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower

/-- The padded data of a martingale with sure data, on the product with a coin space. -/
theorem paddedData_of {Ω : Type*} {Ξ : Type*} {m0 : MeasurableSpace Ω}
    {mΞ : MeasurableSpace Ξ} (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    [IsProbabilityMeasure ν] (ℱ : Filtration ℕ m0) {𝒦 : ℕ → MeasurableSpace Ξ}
    {ε : ℕ → Ξ → ℝ} (hε : SignSequence ν 𝒦 ε) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B)
    (εg : ℝ) (N : ℕ) :
    PaddedData (μ.prod ν) (liftFiltration ℱ 𝒦 hε.mono hε.le) (padProc μ ℱ S B εg N ε)
      (padB μ ℱ S B εg N) (padVar μ ℱ S B εg N) εg N where
  mart := padData_mart μ ν ℱ hε hS εg N
  memLp := padData_memLp μ ν ℱ hε hS εg N
  zero := padData_zero μ ℱ ε hS εg N
  bPred := padData_bPred μ ν ℱ hε hS εg N
  bInc := Eventually.of_forall fun z n => padData_bInc μ ν ℱ hε hS εg N n z
  bRatio := padData_bRatio μ ν ℱ hS εg N
  vPred := padData_vPred μ ν ℱ hε hS εg N
  vZero := padData_vZero μ ℱ S B εg N
  vMono := padData_vMono μ ℱ S B εg N
  vBracket := padData_vBracket μ ν ℱ hε hS εg N
  vInf := padData_vInf μ ν ℱ hS εg N
  blockInc := padData_blockInc μ ν ℱ hε hS εg N
  jump := padData_jump μ ν ℱ hS εg N

end CERW.Generic.Martingale.LilAssembly
