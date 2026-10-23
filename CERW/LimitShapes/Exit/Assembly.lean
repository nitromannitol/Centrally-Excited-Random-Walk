import CERW.LimitShapes.Exit.Coarse
import CERW.LimitShapes.Exit.ProbabilityBounds

/-!
# Coarse bounds from the exit-time argument

The two-sided exit estimate and scale inversion give Proposition `prop:coarse`.
-/

universe u

namespace CERW.LimitShapes.Exit

/-- Proposition `prop:coarse` proved by the two-sided exit-time argument. -/
theorem norm_coarse_bounds_via_exit : CERW.Support.Statements.norm_coarse_bounds.{u} :=
  norm_coarse_bounds_of_exit.{u} exit_bounds.{u}

end CERW.LimitShapes.Exit
