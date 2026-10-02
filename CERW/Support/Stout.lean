import CERW.Generic.Martingale.Lil.LowerStatement
import CERW.Generic.Martingale.Lil
import CERW.Support.Statements

/-!
# Stout's law of the iterated logarithm from its two halves

The upper half of Stout's law of the iterated logarithm (Stout 1970, Theorem 1) is proved,
`CERW.Generic.Martingale.Lil.stout_upper`. With the lower half
`CERW.Generic.Martingale.Lil.StoutLower` (Theorem 2), which is proved as
`CERW.Generic.Martingale.LilAssembly.stout_lower`, it gives the whole law,
`CERW.Support.Statements.StoutLIL`, which the proofs use.
-/

universe u

namespace CERW.Support

open MeasureTheory Filter Topology ProbabilityTheory

/-- The martingale law of the iterated logarithm, from its proved upper half and its lower half. -/
theorem stoutLIL_full (hL : CERW.Generic.Martingale.Lil.StoutLower.{u}) :
    Statements.StoutLIL.{u} := by
  intro Ω m0 μ hμ ℱ S hS hL2 hS0 B hBm hBinc hP hBt
  filter_upwards [CERW.Generic.Martingale.Lil.stout_upper μ ℱ S hS hL2 hS0 B hBm hBinc hP hBt,
    hL μ ℱ S hS hL2 hS0 B hBm hBinc hP hBt] with ω hU hLo δ hδ
  exact ⟨hU δ hδ, hLo δ hδ⟩

end CERW.Support
