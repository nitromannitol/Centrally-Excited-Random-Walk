import CERW.Generic.Martingale.Tilt.Upper
import CERW.Generic.Martingale.Tilt.Lower
import CERW.Generic.Martingale.Tilt.Tail
import CERW.Generic.Martingale.Tilt.Arith
import CERW.Generic.Martingale.Tilt.Assembly

/-!
# The sharp lower tail of a martingale with a pinned bracket

For increments bounded by `b` with total conditional variance in `[v (1 - ρ), v]`,
`P(∑_{t<n} Y t ≥ a) ≥ exp (-(1 + η) a² / (2 v))` once `a² / v` is large and `a b / v`, `ρ` small.
It is the sharp lower tail that the lower half of the martingale law of the iterated logarithm
(Stout 1970, Theorem 2) needs at each block.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

/-- **The sharp lower tail.** -/
theorem sharp_lower_tail : SharpLowerTail.{u} :=
  sharpLowerTail_of (tiltTail_of tilt_upper tilt_lower) tail_arith

end CERW.Generic.Martingale.Tilt
