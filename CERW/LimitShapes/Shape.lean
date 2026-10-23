import CERW.LimitShapes.Frozen.NormShapeRates
import CERW.Support.Norm.ShapeRates
import CERW.Support.Main.LimitShape
import CERW.Support.Norm.Section5Localization

/-!
# Norm limit shapes and the Euclidean specialization

The paper's `thm:norm-shape` follows from `prop:norm-shape` by the support assembly.
The paper's `thm:shape` follows by taking the Euclidean norm and its radial subgradient field.
-/

universe u

namespace CERW.LimitShapes

/-- The norm shape theorem follows from the quantitative norm shape rates. -/
theorem norm_shape_from_rates : CERW.Support.Statements.norm_shape.{u} :=
  CERW.Support.Norm.norm_shape_of CERW.LimitShapes.norm_shape_rates

/-- The Euclidean shape theorem is the specialization of the norm shape theorem. -/
theorem limit_shape_from_norm_shape : CERW.Support.Statements.limit_shape.{u} := by
  intro d hd ε hε hεd Ω _ μ _ X hX
  obtain ⟨hNorm, hSubgrad, hZero, hElliptic⟩ :=
    CERW.Support.Main.euclidean_norm_hypotheses hεd
  have hDrift := (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX
  have hShape := norm_shape_from_rates hd hNorm hSubgrad hZero hε hElliptic μ X hDrift
  simpa only [CERW.Support.Norm.Section5Localization.normBallVolume_norm,
    CERW.unitBallVolume, CERW.norm_toSpace] using hShape

end CERW.LimitShapes
