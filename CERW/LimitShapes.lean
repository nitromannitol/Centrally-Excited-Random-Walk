import CERW.LimitShapes.BulkPotential
import CERW.LimitShapes.BulkProfile
import CERW.LimitShapes.BulkProfileProbability
import CERW.LimitShapes.CommonEvent
import CERW.LimitShapes.ContactApproximation
import CERW.LimitShapes.ContactEvent
import CERW.LimitShapes.ContactPotential
import CERW.LimitShapes.Crossing
import CERW.LimitShapes.Curvature
import CERW.LimitShapes.DynkinBounds
import CERW.LimitShapes.DynkinFreedman
import CERW.LimitShapes.Energy
import CERW.LimitShapes.EuclideanEvent
import CERW.LimitShapes.EuclideanSeparatedBrackets
import CERW.LimitShapes.Event
import CERW.LimitShapes.EventConsequences
import CERW.LimitShapes.Exit
import CERW.LimitShapes.ExitStopping
import CERW.LimitShapes.Frozen
import CERW.LimitShapes.InnerApproximation
import CERW.LimitShapes.InnerProbability
import CERW.LimitShapes.KernelEvents
import CERW.LimitShapes.LimitLaws
import CERW.LimitShapes.LocalApproximation
import CERW.LimitShapes.LocalBracket
import CERW.LimitShapes.LocalTime
import CERW.LimitShapes.LogLower
import CERW.LimitShapes.NormBallPotential
import CERW.LimitShapes.NormRates
import CERW.LimitShapes.PlanarLower
import CERW.LimitShapes.Profile
import CERW.LimitShapes.QuadraticDynkin
import CERW.LimitShapes.QuadraticProbability
import CERW.LimitShapes.QuadraticStopping
import CERW.LimitShapes.RadiusEvents
import CERW.LimitShapes.SeparatedBrackets
import CERW.LimitShapes.Shape
import CERW.LimitShapes.SharpBulk
import CERW.LimitShapes.SharpRadii
import CERW.LimitShapes.ShiftedSquare
import CERW.LimitShapes.SquareDynkin
import CERW.LimitShapes.StoppedQuadraticMartingale

/-!
# Limit shapes and fluctuations

These estimates establish norm and Euclidean limit shapes.
The common-event bounds also yield the fluctuation and limit laws.
-/
