/-
# The disk mass at the `SharpWidth` radius

`CERW/Frozen/SharpWidth.lean` (`thm:sharp`, part (iv)(b), frozen) exhibits the radius
`Real.sqrt (Real.pi / (3 * ε))`: it is the reciprocal of the small-ball scale
`Real.sqrt (3 * δ / π)`
of `oct5.tex:188`, namely `P (Rout - Rin ≤ a √r_n) ≤ 1 - e^{-(3 δ / π) a²}`, at `a = 1`.

This module records that reciprocal identification and the resulting closed-disk mass, so the
Step-4 Gaussian mass `P (|N| ≤ t) = 1 - e^{-t²}` (`oct5.tex:1492`) is available at the radius the
frozen statement uses.  The frozen statement is **not** edited; this is a separate support module.
-/
import CERW.Support.Lower.PlanarGap.GaussDisc

open MeasureTheory ProbabilityTheory Matrix Metric Set
open scoped ENNReal NNReal

namespace CERW.PlanarGap

/-- **The small-ball scale and the `SharpWidth` radius are reciprocal.**  For `δ > 0`,
`√(3δ/π) · √(π/(3δ)) = 1`: the radius of `CERW.Frozen.sharp_width` (with `δ` in place of its `ε`)
is `1 / √(3δ/π)`, the reciprocal of the small-ball scale at `a = 1`. -/
theorem sqrt_threePi_mul_sqrt_pi_three (δ : ℝ) (hδ : 0 < δ) :
    Real.sqrt (3 * δ / Real.pi) * Real.sqrt (Real.pi / (3 * δ)) = 1 := by
  have hx : (0 : ℝ) ≤ 3 * δ / Real.pi := by positivity
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  rw [← Real.sqrt_mul hx]
  rw [show 3 * δ / Real.pi * (Real.pi / (3 * δ)) = 1 by
    field_simp]
  exact Real.sqrt_one

/-- **The disk mass at the `SharpWidth` radius.**  For `δ > 0` the closed-disk mass at radius
`√(π/(3δ))` — the radius of `CERW.Frozen.sharp_width`, with `δ` in place of its `ε` — is
`ofReal (1 - e^{-π/(3δ)})`. -/
theorem multivariateGaussian_halfI_closedBall_sharpWidth (δ : ℝ) (hδ : 0 < δ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (closedBall 0 (Real.sqrt (Real.pi / (3 * δ))))
      = ENNReal.ofReal (1 - Real.exp (-(Real.pi / (3 * δ)))) := by
  rw [multivariateGaussian_halfI_closedBall (Real.sqrt (Real.pi / (3 * δ)))
    (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

/-- **The `3δ/π` small-ball at the `SharpWidth` radius.**  Taking `a := π/(3δ)` in the small-ball
form makes the radius `√(3δ/π) · π/(3δ) = √(π/(3δ))` — the frozen radius — and the mass
`ofReal (1 - e^{-π/(3δ)})`, matching `multivariateGaussian_halfI_closedBall_sharpWidth`. -/
theorem multivariateGaussian_halfI_smallBall_sharpWidth (δ : ℝ) (hδ : 0 < δ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (closedBall 0 (Real.sqrt (3 * δ / Real.pi) * (Real.pi / (3 * δ))))
      = ENNReal.ofReal (1 - Real.exp (-(Real.pi / (3 * δ)))) := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  rw [multivariateGaussian_halfI_smallBall_threePi δ (Real.pi / (3 * δ)) hδ (by positivity)]
  congr 1
  field_simp

end CERW.PlanarGap

#print axioms CERW.PlanarGap.sqrt_threePi_mul_sqrt_pi_three
#print axioms CERW.PlanarGap.multivariateGaussian_halfI_closedBall_sharpWidth
#print axioms CERW.PlanarGap.multivariateGaussian_halfI_smallBall_sharpWidth
