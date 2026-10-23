import CERW.LimitShapes.Energy.Absorption
import CERW.LimitShapes.Energy.Bracket
import CERW.LimitShapes.Energy.Contact
import CERW.LimitShapes.Energy.DriftBound
import CERW.LimitShapes.Energy.DriftSum
import CERW.LimitShapes.Energy.FarPotential
import CERW.LimitShapes.Energy.GlobalPotential
import CERW.LimitShapes.Energy.Gradient
import CERW.LimitShapes.Energy.Identity
import CERW.LimitShapes.Energy.KernelEnvelope
import CERW.LimitShapes.Energy.LocalError
import CERW.LimitShapes.Energy.PlanarEnvelope
import CERW.LimitShapes.Energy.PlanarPacking
import CERW.LimitShapes.Energy.SiteEnergy
import CERW.LimitShapes.Energy.SiteEstimate
import CERW.LimitShapes.Energy.SitePointwise
import CERW.LimitShapes.Energy.SiteScales
import CERW.LimitShapes.Energy.ValueBound

/-!
# Shifted-square energy estimates

Dynkin and Freedman bounds control the shifted-square energy.
These estimates give the contact potential bound on the common event.
-/
