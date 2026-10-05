/-
# The exact 2D centred Gaussian closed-disk mass — law identification

The planar gap constant of `oct4.tex:1488` is reduced to the law
of `Z_n / √n`, which is asymptotically the centred Gaussian on `EuclideanSpace ℝ (Fin 2)` with
covariance `(1/2) I₂`; because `‖N‖² ~ Exp(1)`, the closed-disk mass is
`P(‖N‖ ≤ t) = 1 − e^{−t²}`.

This file lands the *law identification* in full: the actual Gaussian with covariance
`(1/2) I₂` is literally the product of the two one-dimensional laws `gaussianReal 0 (1/2)`
under the standard coordinate equivalence
`WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)` (`Measure.pi`).  The proof is a
characteristic-function comparison (`Measure.ext_of_charFun`): both sides have characteristic
function `exp (−‖t‖²/4)`, using `charFun_multivariateGaussian` on the left and `charFun_pi`
with `charFun_gaussianReal` on the right.

The **disk mass** `μ (closedBall 0 t) = ofReal (1 − exp (−(t²)))` is *not* yet a theorem
here; the obstacle is recorded precisely below.  The one-dimensional radial identity that the
polar computation consumes *is* landed (`integral_zero_to_mul_exp_neg_sq`).

## The exact missing Mathlib inputs (for the disk mass)

1. **A `Measure.pi`-`withDensity` bridge.**  There is no lemma expressing
   `Measure.pi (fun i ↦ μ i.withDensity (f i))` as
   `(Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i))` (nor the `Fin 2` case with
   `Measure.prod`); it is provable from `Measure.pi_eq` on rectangles and a Fubini-for-
   `Measure.pi` identity
   `∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i`
   (the latter is used inside `charFun_pi`), but no packaged statement exists.  It is
   nevertheless *derivable*: the iterated-integral API `MeasureTheory.lmarginal`
   (`MeasureTheory/Integral/Marginal.lean:78`), with `lmarginal_insert'` (`:174`) and
   `lintegral_eq_lmarginal_univ` (`:195`), supplies the `∫⁻` Fubini for `Measure.pi`.  The
   packaged Bochner lemma `integral_fintype_prod_eq_prod`
   (`MeasureTheory/Integral/Pi.lean:106`) is `RCLike`-valued and does not match `withDensity`.
2. **The Lebesgue measure of `(ι → ℝ)` as a product.**  The bridge also needs
   `Measure.pi (fun _ : ι ↦ (volume : Measure ℝ)) = volume` on `ι → ℝ`, in the exact form
   matching the `gaussianReal` density (`gaussianReal μ v = volume.withDensity
   (gaussianPDF μ v)`, `Probability/Distributions/Gaussian/Real.lean:226`).
3. **Transport of a density along a measurable equivalence**, to move the density through
   `WithLp.toLp 2` (which is measure preserving for volume, `PiLp.volume_preserving_toLp`).

With (1)–(3) the disk mass follows from the polar formula
`MeasureTheory.integral_fun_norm_addHaar` (`MeasureTheory/Constructions/HaarToSphere.lean:296`),
`volume_closedBall_fin_two` (`MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:403`) and the
one-dimensional identity below.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import CERW.Support.Lower.PlanarGap.PiWithDensity
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory ProbabilityTheory Matrix Metric Set
open scoped ENNReal NNReal

namespace CERW.PlanarGap

/-- **Law identification.**  The centred Gaussian on `EuclideanSpace ℝ (Fin 2)` with
covariance `(1/2) I₂` is the product of the two one-dimensional laws `gaussianReal 0 (1/2)`,
read through the standard coordinate equivalence `WithLp.toLp 2`.  Proved by comparing
characteristic functions. -/
theorem multivariateGaussian_halfI_eq_pi :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      = (Measure.pi (fun _ : Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0))).map (WithLp.toLp 2) := by
  have hS : ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef :=
    (Matrix.PosSemidef.one (n := Fin 2)).smul (by norm_num)
  have hself : ∀ t : EuclideanSpace ℝ (Fin 2), t.ofLp ⬝ᵥ t.ofLp = ∑ i, (t i) ^ 2 := by
    intro t
    simp [dotProduct, pow_two]
  have hkey : ∀ t : EuclideanSpace ℝ (Fin 2),
      t.ofLp ⬝ᵥ ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec t.ofLp
        = (∑ i, (t i) ^ 2) / 2 := by
    intro t
    rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, hself t]
    ring
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_multivariateGaussian hS, charFun_pi]
  simp only [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  have hsum : (∑ x, (↑(t.ofLp x) * ↑(0 : ℝ) * Complex.I - ↑↑(1 / 2 : ℝ≥0)
        * ↑(t.ofLp x) ^ 2 / 2)) = ((∑ x, ↑(t.ofLp x) ^ 2 : ℂ)) * (-(1 / 4)) := by
    have h : ∀ x ∈ (Finset.univ : Finset (Fin 2)),
        (↑(t.ofLp x) * ↑(0 : ℝ) * Complex.I - ↑↑(1 / 2 : ℝ≥0) * ↑(t.ofLp x) ^ 2 / 2)
          = ↑(t.ofLp x) ^ 2 * (-(1 / 4) : ℂ) := by
      intro x _
      push_cast
      ring
    rw [Finset.sum_congr rfl h, Finset.sum_mul]
  rw [hsum, hkey t, inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  push_cast
  ring

/-- **The one-dimensional radial identity.**  `∫_0^t y e^{−y²} dy = (1 − e^{−t²})/2`, the
factor that the polar formula produces for the covariance `(1/2) I₂`. -/
theorem integral_zero_to_mul_exp_neg_sq (t : ℝ) :
    ∫ y in (0 : ℝ)..t, y * Real.exp (-(y ^ 2)) = (1 - Real.exp (-(t ^ 2))) / 2 := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => -(Real.exp (-(y ^ 2))) / 2)
      (y * Real.exp (-(y ^ 2))) y := by
    intro y
    have h2 : HasDerivAt (fun y : ℝ => -(y ^ 2)) (-(2 * y)) y := by
      have h := (hasDerivAt_pow 2 y).neg
      have hfun : (fun y : ℝ => -(y ^ 2)) = (-fun x : ℝ => x ^ 2) := by ext x; rfl
      rw [hfun]
      simpa using h
    have h3 : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2)))
        (Real.exp (-(y ^ 2)) * -(2 * y)) y := (Real.hasDerivAt_exp _).comp y h2
    have h4 : HasDerivAt (fun y : ℝ => -(Real.exp (-(y ^ 2))) / 2)
        (-(Real.exp (-(y ^ 2)) * -(2 * y)) / 2) y := h3.neg.div_const 2
    convert h4 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
    ((continuous_id.mul (Real.continuous_exp.comp (by fun_prop))).intervalIntegrable 0 t)]
  simp
  ring

/-- **The two-coordinate Gaussian density is radial.**  The product of the two one-dimensional
`N(0, 1/2)` densities at `y` equals `ofReal (π⁻¹ * exp (-‖y‖ ^ 2))`.  The helper is stated
in the
`(Real.sqrt ·)⁻¹` shape in which the unfolded `gaussianPDFReal` prints, so that the
`ENNReal.ofReal` rewriting matches. -/
theorem gaussianPDF_half_prod_eq (y : EuclideanSpace ℝ (Fin 2)) :
    gaussianPDF 0 (1 / 2 : ℝ≥0) (y 0) * gaussianPDF 0 (1 / 2 : ℝ≥0) (y 1)
      = ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(‖y‖ ^ 2))) := by
  have hsq : Real.sqrt (2 * Real.pi * (((1 / 2 : ℝ≥0)) : ℝ)) = Real.sqrt Real.pi := by
    rw [show (2 : ℝ) * Real.pi * (((1 / 2 : ℝ≥0)) : ℝ) = Real.pi by push_cast; ring]
  have hpi : (Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹ = Real.pi⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt Real.pi_nonneg]
  have hE : Real.exp (-(y.ofLp 0 - 0) ^ 2 / (2 * (((1 / 2 : ℝ≥0)) : ℝ)))
        * Real.exp (-(y.ofLp 1 - 0) ^ 2 / (2 * (((1 / 2 : ℝ≥0)) : ℝ)))
      = Real.exp (-(‖y‖ ^ 2)) := by
    rw [show (2 : ℝ) * (((1 / 2 : ℝ≥0)) : ℝ) = 1 by norm_num,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp only [sub_zero, div_one]
    rw [← Real.exp_add]
    congr 1
    ring
  have hreal : (Real.sqrt (2 * Real.pi * (((1 / 2 : ℝ≥0)) : ℝ)))⁻¹
        * Real.exp (-(y.ofLp 0 - 0) ^ 2 / (2 * (((1 / 2 : ℝ≥0)) : ℝ)))
      * ((Real.sqrt (2 * Real.pi * (((1 / 2 : ℝ≥0)) : ℝ)))⁻¹
        * Real.exp (-(y.ofLp 1 - 0) ^ 2 / (2 * (((1 / 2 : ℝ≥0)) : ℝ))))
      = Real.pi⁻¹ * Real.exp (-(‖y‖ ^ 2)) := by
    rw [hsq]
    calc (Real.sqrt Real.pi)⁻¹
            * Real.exp (-(y.ofLp 0 - 0) ^ 2 / (2 * (((1 / 2 : ℝ≥0)) : ℝ)))
          * ((Real.sqrt Real.pi)⁻¹
            * Real.exp (-(y.ofLp 1 - 0) ^ 2 / (2 * (((1 / 2 : ℝ≥0)) : ℝ))))
        = ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹)
            * (Real.exp (-(y.ofLp 0 - 0) ^ 2 / (2 * (((1 / 2 : ℝ≥0)) : ℝ)))
              * Real.exp (-(y.ofLp 1 - 0) ^ 2 / (2 * (((1 / 2 : ℝ≥0)) : ℝ)))) := by
          ring
      _ = Real.pi⁻¹ * Real.exp (-(‖y‖ ^ 2)) := by rw [hpi, hE]
  rw [gaussianPDF, gaussianPDF, gaussianPDFReal, gaussianPDFReal,
    ← ENNReal.ofReal_mul (by positivity)]
  exact congrArg ENNReal.ofReal hreal


/-- **Density of the two-coordinate `Measure.pi` Gaussian.**  The product of two `N(0, 1/2)`
laws is `volume` with the density `gaussianPDF 0 (1/2) (x 0) * gaussianPDF 0 (1/2) (x 1)`.  Proved
from `gaussianReal_of_var_ne_zero`, the `Measure.pi`-`withDensity` bridge and `volume_pi`. -/
theorem pi_gaussianReal_half_eq_withDensity :
    Measure.pi (fun _ : Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0))
      = (volume : Measure (Fin 2 → ℝ)).withDensity
          (fun x => gaussianPDF 0 (1 / 2 : ℝ≥0) (x 0)
            * gaussianPDF 0 (1 / 2 : ℝ≥0) (x 1)) := by
  haveI hsig : SigmaFinite
      ((volume : Measure ℝ).withDensity (gaussianPDF 0 (1 / 2 : ℝ≥0))) := by
    rw [← gaussianReal_of_var_ne_zero (0 : ℝ) (v := 1 / 2) (by norm_num)]
    infer_instance
  simp only [gaussianReal_of_var_ne_zero (0 : ℝ) (v := 1 / 2) (by norm_num)]
  rw [Measure.pi_withDensity_fin_two (fun _ : Fin 2 => gaussianPDF 0 (1 / 2 : ℝ≥0))
    (fun _ => measurable_gaussianPDF _ _), ← volume_pi]

/-- **Density of the planar centred Gaussian.**  `N(0, (1/2) I₂)` is `volume` with the radial
density `ofReal (π⁻¹ * exp (-‖y‖ ^ 2))`.  Proved from the law identification, the
density above,
`PiLp.volume_preserving_toLp`, the density-transport lemma and `gaussianPDF_half_prod_eq`. -/
theorem multivariateGaussian_halfI_eq_withDensity :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      = (volume : Measure (EuclideanSpace ℝ (Fin 2))).withDensity
          (fun y => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(‖y‖ ^ 2)))) := by
  rw [multivariateGaussian_halfI_eq_pi, pi_gaussianReal_half_eq_withDensity]
  have hvol : Measure.map (⇑(MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))
      (volume : Measure (Fin 2 → ℝ)) = (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
    rw [show ⇑(MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) = (WithLp.toLp 2) from rfl]
    exact (PiLp.volume_preserving_toLp (Fin 2)).map_eq
  rw [show (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))
      = (⇑(MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) from rfl]
  have htrans := Measure.map_withDensity_measurableEquiv
    (e := MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) (μ := (volume : Measure (Fin 2 → ℝ)))
    (f := fun x => gaussianPDF 0 (1 / 2 : ℝ≥0) (x 0) * gaussianPDF 0 (1 / 2 : ℝ≥0) (x 1))
    (by fun_prop)
  rw [htrans, hvol]
  congr 1
  funext y
  exact CERW.PlanarGap.gaussianPDF_half_prod_eq y


/-- **The exact 2D Gaussian closed-disk mass.**  For every `t ≥ 0` (including `t = 0`), the
centred planar Gaussian with covariance `(1/2) I₂` gives the closed disk the mass
`1 - exp (-(t^2))`.  Proved from the density `multivariateGaussian_halfI_eq_withDensity`, the
`∫⁻`-to-Bochner conversion, the polar formula `integral_fun_norm_addHaar`,
`EuclideanSpace.volume_ball_fin_two` and `integral_zero_to_mul_exp_neg_sq`. -/
theorem multivariateGaussian_halfI_closedBall (t : ℝ) (ht : 0 ≤ t) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (closedBall 0 t)
      = ENNReal.ofReal (1 - Real.exp (-(t ^ 2))) := by
  have hG : ∀ y : EuclideanSpace ℝ (Fin 2),
      (closedBall (0 : EuclideanSpace ℝ (Fin 2)) t).indicator
          (fun y => Real.pi⁻¹ * Real.exp (-(‖y‖ ^ 2))) y
        = (Set.Iic t).indicator (fun r => Real.pi⁻¹ * Real.exp (-(r ^ 2))) ‖y‖ := by
    intro y
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) t
    · have hy' : ‖y‖ ≤ t := by rwa [mem_closedBall, dist_zero_right] at hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem (mem_Iic.mpr hy')]
    · have hy' : ¬ (‖y‖ ≤ t) := by
        rw [mem_closedBall, dist_zero_right] at hy
        exact hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy' (mem_Iic.mp h))]
  rw [CERW.PlanarGap.multivariateGaussian_halfI_eq_withDensity,
    withDensity_apply _ measurableSet_closedBall,
    ← lintegral_indicator measurableSet_closedBall]
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 2),
      (closedBall (0 : EuclideanSpace ℝ (Fin 2)) t).indicator
          (fun y => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(‖y‖ ^ 2)))) y
        = ENNReal.ofReal ((Set.Iic t).indicator
            (fun r => Real.pi⁻¹ * Real.exp (-(r ^ 2))) ‖y‖) := by
    intro y
    rw [← hG y]
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) t
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]; simp
  rw [lintegral_congr hpt, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_fun_norm_addHaar]
    rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 from by simp]
    simp only [Nat.reduceSub, pow_one]
    have hvol : volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = Real.pi := by
      rw [Measure.real, EuclideanSpace.volume_ball_fin_two]; simp [Real.pi_nonneg]
    rw [hvol]
    have h1 : ∫ y : ℝ in Ioi 0, y • (Set.Iic t).indicator
          (fun r => Real.pi⁻¹ * Real.exp (-(r ^ 2))) y ∂volume
        = Real.pi⁻¹ * (1 - Real.exp (-(t ^ 2))) / 2 := by
      rw [← integral_indicator measurableSet_Ioi]
      trans ∫ y : ℝ, (Set.Ioc 0 t).indicator
          (fun y => y * (Real.pi⁻¹ * Real.exp (-(y ^ 2)))) y ∂volume
      · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [Set.indicator_apply, Set.mem_Ioi, Set.mem_Ioc, Set.mem_Iic]
        split_ifs <;> simp_all [smul_eq_mul]
      · rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le ht]
        have hfac : (∫ y in (0 : ℝ)..t, y * (Real.pi⁻¹ * Real.exp (-(y ^ 2))) ∂volume)
            = Real.pi⁻¹ * ∫ y in (0 : ℝ)..t, y * Real.exp (-(y ^ 2)) ∂volume := by
          rw [← intervalIntegral.integral_const_mul]
          exact intervalIntegral.integral_congr fun y _ => by ring
        rw [hfac, CERW.PlanarGap.integral_zero_to_mul_exp_neg_sq]
        ring
    rw [h1, nsmul_eq_mul, smul_eq_mul]
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  · rw [show (fun y : EuclideanSpace ℝ (Fin 2) =>
        (Set.Iic t).indicator (fun r => Real.pi⁻¹ * Real.exp (-(r ^ 2))) ‖y‖)
      = (fun y => (closedBall (0 : EuclideanSpace ℝ (Fin 2)) t).indicator
          (fun y => Real.pi⁻¹ * Real.exp (-(‖y‖ ^ 2))) y) from funext fun y => (hG y).symm]
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 2) =>
      Real.pi⁻¹ * Real.exp (-(‖y‖ ^ 2))).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) t)
  · exact Filter.Eventually.of_forall fun y => by
      simp only [Set.indicator_apply]
      split_ifs <;> positivity


/-- **The `Exp(1)` law of `‖N‖²`.**  For `u ≥ 0` the squared norm of the planar centred
Gaussian with covariance `(1/2) I₂` has the unit exponential CDF,
`P(‖N‖² ≤ u) = 1 - exp (-u)`.  Immediate
from the closed-disk mass at radius `√u` (`Real.sq_sqrt`). -/
theorem multivariateGaussian_halfI_normSq_le (u : ℝ) (hu : 0 ≤ u) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      {x | ‖x‖ ^ 2 ≤ u} = ENNReal.ofReal (1 - Real.exp (-u)) := by
  have h : {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ^ 2 ≤ u}
      = closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt u) := by
    ext x
    rw [mem_closedBall, dist_zero_right]
    exact ⟨fun hx => (Real.le_sqrt (norm_nonneg x) hu).mpr hx,
      fun hx => by rw [← Real.sq_sqrt hu]; exact pow_le_pow_left₀ (norm_nonneg x) hx 2⟩
  rw [h, CERW.PlanarGap.multivariateGaussian_halfI_closedBall (Real.sqrt u)
    (Real.sqrt_nonneg u), Real.sq_sqrt hu]

/-- **The explicit positive-`a` closed-disk mass.**  The specialisation of
`multivariateGaussian_halfI_closedBall` to the parameter name `a` used by the
planar-width small-ball (`oct5.tex:188`): for `a ≥ 0`, `P(|N| ≤ a) = 1 - e^{-a²}`. -/
theorem multivariateGaussian_halfI_closedBall_pos (a : ℝ) (ha : 0 ≤ a) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (closedBall 0 a)
      = ENNReal.ofReal (1 - Real.exp (-(a ^ 2))) :=
  multivariateGaussian_halfI_closedBall a ha

/-- **The scaling form of the closed-disk mass.**  For `c, a ≥ 0` the mass of the closed ball of
radius `c * a` is `1 - e^{-(c a)²}`; the radius only enters through its square. -/
theorem multivariateGaussian_halfI_closedBall_scale (c a : ℝ) (hc : 0 ≤ c) (ha : 0 ≤ a) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (closedBall 0 (c * a))
      = ENNReal.ofReal (1 - Real.exp (-((c * a) ^ 2))) :=
  multivariateGaussian_halfI_closedBall (c * a) (mul_nonneg hc ha)

/-- **The exact `3δ/π` small-ball** of `oct5.tex:188`.  For `δ > 0` and `a ≥ 0`,
`P(Rout - Rin ≤ a √r_n) ≤ 1 - e^{-(3δ/π) a²}`, i.e. the closed-disk mass at the
radius
`√(3δ/π) · a` equals `ofReal (1 - e^{-(3δ/π) a²})`. -/
theorem multivariateGaussian_halfI_smallBall_threePi (δ a : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (closedBall 0 (Real.sqrt (3 * δ / Real.pi) * a))
      = ENNReal.ofReal (1 - Real.exp (-((3 * δ / Real.pi) * a ^ 2))) := by
  rw [multivariateGaussian_halfI_closedBall (Real.sqrt (3 * δ / Real.pi) * a)
    (mul_nonneg (Real.sqrt_nonneg _) ha)]
  congr 1
  rw [mul_pow, Real.sq_sqrt (by positivity)]

end CERW.PlanarGap
