import CERW.Support.Norm.GaugeCoarseVolume
import CERW.Support.Norm.GaugeLocalTime

/-!
# The coarse bounds for the walk driven by the gauge of a convex body

Proposition 4.1 for the centrally excited random walk with drift opposite to subgradients of the
literal Minkowski functional `ψ = gauge K` of a compact convex set `K` with the origin in its
interior (not necessarily symmetric), under the ellipticity condition
`ε max {ψ(e_i), ψ(-e_i)} < 1/d`. The module `GaugeCoarseVolume` proves the cap event, the rough
outer bound, the geometry of the inner radius and the six deterministic bounds, and assembles them
from the local time potential lemma; the module `GaugeLocalTime` proves that lemma. Their
combination has no further hypothesis.
-/

universe u

namespace CERW.Support.Norm.GaugeCoarseClosed

open CERW.Support.Norm.GaugeCoarseVolume

/-- **Proposition 4.1 for the gauge of a convex body.** For every `d ≥ 2`, every compact convex
`K ⊆ ℝ^d` with the origin in its interior, every `ε > 0` with `ε ψ(±e_i) < 1/d`, every `p > 0`,
there are constants `c, C > 0` such that, for every choice of subgradients `ξ(x) ∈ ∂ψ(x)` with
`ξ(0) = 0` and every walk with drift field `ξ`, with probability at least `1 - C n^{-p}`, for every
`n ≥ 2`, the number of departed sites, the largest local time and the largest radius are of order
`r_n^d`, `r_n`, `r_n`, with the constants `c` and `C`. The constants are chosen before the field
`ξ`, the probability space, the walk and `n`. -/
theorem gauge_coarse_bounds : GaugeCoarseBounds.{u} :=
  gauge_coarse_bounds_of_local_time.{u} (@GaugeLocalTime.gauge_local_time_potential.{u})

end CERW.Support.Norm.GaugeCoarseClosed
