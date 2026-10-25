module

public import CERW.LimitShapes.Curvature.OuterEvent
public import CERW.LimitShapes.Curvature.ProfileEvent
public import CERW.LimitShapes.Curvature.FluctuationProbability

@[expose] public section

/-! # Fluctuation rates from the curvature argument

The common-event estimates and Borel--Cantelli prove Theorem `thm:fluctuations`.
-/

universe u

namespace CERW.LimitShapes.Curvature

/-- The full fluctuation theorem obtained from the printed curvature and profile estimates. -/
theorem fluctuation_rates_via_curvature : CERW.Support.Statements.fluctuation_rates.{u} :=
  fluctuation_rates_of_event_bounds outer_on_event
    (profile_on_event_of_bounds exists_positive_on_event exists_outer_width_on_event)

end CERW.LimitShapes.Curvature
