import CERW.Generic.Martingale.Tilt.LowerOn
import CERW.Generic.Martingale.Tilt.TailOn
import CERW.Generic.Martingale.Tilt.Limit

/-!
# The sharp lower tail at an unbounded horizon

For increments bounded by `b` at all times, with bracket at most `v` at every time and eventually
at least `v (1 - ρ)`, and partial sums eventually equal to `L`,
`P(L ≥ a) ≥ exp (-(1 + η) a² / (2 v))`. This is the form that the blocks of the lower half of the
law of the iterated logarithm use. Each block ends at an almost surely finite stopping time.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

/-- **The sharp lower tail at an unbounded horizon.** -/
theorem sharp_lower_tail_limit : SharpLowerTailLimit.{u} :=
  sharpLowerTailLimit_of (tiltTailOn_of tilt_upper tilt_lower_on) tail_arith

end CERW.Generic.Martingale.Tilt
