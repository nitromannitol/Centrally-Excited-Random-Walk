import CERW.LimitShapes.Curvature.Annulus
import CERW.LimitShapes.Curvature.AnnulusBound
import CERW.LimitShapes.Curvature.CapBounds
import CERW.LimitShapes.Curvature.CapKernel
import CERW.LimitShapes.Curvature.CapMass
import CERW.LimitShapes.Curvature.Continuity
import CERW.LimitShapes.Curvature.CurvatureIntegralBound
import CERW.LimitShapes.Curvature.Decay
import CERW.LimitShapes.Curvature.EventBorelCantelli
import CERW.LimitShapes.Curvature.EventData
import CERW.LimitShapes.Curvature.EventGeometry
import CERW.LimitShapes.Curvature.EventScales
import CERW.LimitShapes.Curvature.FarPoint
import CERW.LimitShapes.Curvature.FluctuationProbability
import CERW.LimitShapes.Curvature.FluctuationProbabilityAux
import CERW.LimitShapes.Curvature.FluctuationTheorem
import CERW.LimitShapes.Curvature.Global
import CERW.LimitShapes.Curvature.Harmonic
import CERW.LimitShapes.Curvature.HarmonicIntegral
import CERW.LimitShapes.Curvature.HarmonicKernel
import CERW.LimitShapes.Curvature.Mass
import CERW.LimitShapes.Curvature.NearFar
import CERW.LimitShapes.Curvature.NearFarKernel
import CERW.LimitShapes.Curvature.OuterEvent
import CERW.LimitShapes.Curvature.OuterLocalTime
import CERW.LimitShapes.Curvature.OuterProbability
import CERW.LimitShapes.Curvature.OuterScales
import CERW.LimitShapes.Curvature.OuterWidth
import CERW.LimitShapes.Curvature.PositiveBound
import CERW.LimitShapes.Curvature.PositiveEvent
import CERW.LimitShapes.Curvature.PotentialContinuity
import CERW.LimitShapes.Curvature.PotentialDifferentiation
import CERW.LimitShapes.Curvature.PotentialHarmonic
import CERW.LimitShapes.Curvature.PotentialKernel
import CERW.LimitShapes.Curvature.PotentialLaplacian
import CERW.LimitShapes.Curvature.PotentialMaximum
import CERW.LimitShapes.Curvature.ProfileApproximation
import CERW.LimitShapes.Curvature.ProfileEvent
import CERW.LimitShapes.Curvature.ProfilePotential
import CERW.LimitShapes.Curvature.ProfileScales
import CERW.LimitShapes.Curvature.RadialDerivative
import CERW.LimitShapes.Curvature.RadialIntegral
import CERW.LimitShapes.Curvature.RadialIntegralAux
import CERW.LimitShapes.Curvature.SegmentDerivative
import CERW.LimitShapes.Curvature.SeparatedBrackets
import CERW.LimitShapes.Curvature.Width

/-!
# Curvature estimates

The curvature bounds control the signed potential and the outer radius.
They also give the global profile and its fluctuation rates.
-/
