module

public import CERW.LimitShapes.LimitLaws.MomentFluctuations
public import CERW.LimitShapes.LimitLaws.FixedSiteCentering
public import CERW.LimitShapes.LimitLaws.SiteFluctuations

@[expose] public section

/-!
# Moment and site limit laws

The moment law uses the current shape and curvature estimates.
The centering expansion then transfers the martingale limits to local times.
-/
