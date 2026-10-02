import CERW.External.StoutLIL
import CERW.Generic.Martingale.Lil
import CERW.Support.Statements

/-!
# Stout's law of the iterated logarithm from its cited lower half

The upper half of Stout's law of the iterated logarithm (Stout 1970, Theorem 1) is proved,
`CERW.Generic.Martingale.Lil.stout_upper`. With the cited lower half `CERW.External.StoutLIL`
(Theorem 2) it gives the whole law, `CERW.Support.Statements.StoutLIL`, which the proofs use.
-/

universe u

namespace CERW.Support

open MeasureTheory Filter Topology ProbabilityTheory

/-- The martingale law of the iterated logarithm, from its proved upper half and its cited lower
half. -/
theorem stoutLIL_full (hL : CERW.External.StoutLIL.{u}) : Statements.StoutLIL.{u} := by
  intro Ω m0 μ hμ ℱ S hS hL2 hS0 B hBm hBinc hP hBt
  filter_upwards [CERW.Generic.Martingale.Lil.stout_upper μ ℱ S hS hL2 hS0 B hBm hBinc hP hBt,
    hL μ ℱ S hS hL2 hS0 B hBm hBinc hP hBt] with ω hU hLo δ hδ
  exact ⟨hU δ hδ, hLo δ hδ⟩

end CERW.Support
