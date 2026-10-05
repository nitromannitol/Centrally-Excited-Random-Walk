import CERW.Support.Norm.GaugeCellGradient
import CERW.Support.Norm.DriftSite
import CERW.Support.Norm.Freedman

/-!
# The local times and the potential of the walk driven by an asymmetric gauge

`lem:local` of the paper for the centrally excited random walk with drift field `ξ`, a choice of
subgradients of the literal Minkowski functional `ψ_K = gauge K` of a compact convex set `K ⊆ ℝ^d`
with the origin in its interior (not necessarily symmetric), under the ellipticity condition
`ε max {ψ_K(e_i), ψ_K(-e_i)} < 1/d`. The proof is that of the norm case:

* Dynkin's formula for the kernel `b(· - y)` and the walk with drift field, and the interval
  martingale bound from Freedman's inequality at dyadic brackets (`DriftSite`, `Freedman`);
* the Young absorption for the interval maxima;
* the comparison of the source sum with the potential `U_{D_n}` of the cell set, up to
  `O(ε log(R' + 2))`: the gradient is replaced by the Newtonian field, the kernel value by its cell
  integral, and the lattice drift `ξ(x)` by the gradient `∇ψ_K(v)` on the cells, which is the cell
  estimate `lem:cell` for the gauge with the growth of the distributional Laplacian
  (`GaugeCellGradient.gauge_abs_source_sum_sub_normPotential_le`), and the continuity modulus of
  the potential over a cell (`gauge_normPotential_cell_modulus`).

No evenness and no norm is used: the only inputs from the body are the bound `|∇ψ_K| ≤ Λ_ψ`, the
subgradient bounds for the drift field and the asymmetric ellipticity condition.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeLocalTime

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugeLaplacian CERW.Support.Norm.GaugeCellGradient

/-! ### The modulus of the potential over a cell -/

section CellModulus

open CERW CERW.Generic.Kernel CERW.Support.Geometry

variable {d : ℕ}

/-- The integrand `g(v) · (v - y) |v - y|^{-d}` of the potential of the field `g`. -/
private noncomputable def fieldIntegrand (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (y v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ (g v) (v - y) / ‖v - y‖ ^ d

/-- The far-field constant `2^d + 2 d 3^{d-1}`. -/
private def farFieldConstant (d : ℕ) : ℝ := (2 : ℝ) ^ d + 2 * (d : ℝ) * 3 ^ (d - 1)

/-- The potential of a function is the integral of the field integrand of its gradient. -/
private lemma normPotential_eq_integral (d : ℕ) (ε : ℝ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ D y
      = 2 * ε / unitBallVolume d * ∫ v in D, fieldIntegrand (gradient Ψ) y v :=
  rfl


private lemma measurable_fieldIntegrand {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (y : EuclideanSpace ℝ (Fin d)) :
    Measurable (fieldIntegrand g y) := by
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
    measurable_id.sub measurable_const
  exact (hg.inner hsub).div (hsub.norm.pow_const d)

/-- The integrand of the field potential is at most `Λ` times the Newtonian kernel `|v - y|^{1-d}`
when the field has norm at most `Λ`. -/
private lemma abs_fieldIntegrand_le {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {Λ : ℝ} (hg : ∀ v, ‖g v‖ ≤ Λ) (v y : EuclideanSpace ℝ (Fin d)) :
    |fieldIntegrand g y v| ≤ Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
  have hξ := hg v
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hξ
  rcases eq_or_ne v y with rfl | hne
  · simp only [fieldIntegrand, sub_self, inner_zero_right, zero_div, abs_zero]
    exact mul_nonneg hΛ (Real.rpow_nonneg (norm_nonneg _) _)
  · have hw : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < ‖v - y‖ ^ d := pow_pos hw d
    have h1 : |inner ℝ (g v) (v - y)| ≤ ‖g v‖ * ‖v - y‖ := abs_real_inner_le_norm _ _
    have h2 : ‖g v‖ * ‖v - y‖ ≤ Λ * ‖v - y‖ := mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    calc |fieldIntegrand g y v|
        = |inner ℝ (g v) (v - y)| / ‖v - y‖ ^ d := by
          rw [fieldIntegrand, abs_div, abs_of_nonneg hden.le]
      _ ≤ (Λ * ‖v - y‖) / ‖v - y‖ ^ d :=
          div_le_div_of_nonneg_right (h1.trans h2) hden.le
      _ = Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
          rw [mul_div_assoc, div_pow_eq_rpow_sub hw d]

/-- On a set of finite volume the integrand of a bounded measurable field potential is
integrable. -/
private lemma integrableOn_fieldIntegrand (hd : 1 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fieldIntegrand g y) D := by
  obtain ⟨hint, _⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  refine (hint.const_mul Λ).mono' (measurable_fieldIntegrand hg y).aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs]
  exact abs_fieldIntegrand_le hΛ v y

/-- The difference of two field-potential integrands is at most `Λ` times the norm of the
difference of the Newtonian fields when the field has norm at most `Λ`. -/
private lemma abs_fieldIntegrand_sub_le {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {Λ : ℝ} (hg : ∀ v, ‖g v‖ ≤ Λ) (v y z : EuclideanSpace ℝ (Fin d)) :
    |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * ‖newtonField (v - y) - newtonField (v - z)‖ := by
  simp only [fieldIntegrand]
  rw [← inner_newtonField (g v) (v - y), ← inner_newtonField (g v) (v - z), ← inner_sub_right]
  calc |inner ℝ (g v) (newtonField (v - y) - newtonField (v - z))|
      ≤ ‖g v‖ * ‖newtonField (v - y) - newtonField (v - z)‖ := abs_real_inner_le_norm _ _
    _ ≤ Λ * ‖newtonField (v - y) - newtonField (v - z)‖ :=
        mul_le_mul_of_nonneg_right (hg v) (norm_nonneg _)

/-- Integral of `|v - z|^{-d}` over an annulus centred at `z`, obtained from the corresponding
integral at the origin by translation. -/
private lemma integrableOn_annulus_sub_rpow_neg_and_integral_eq (hd : 1 ≤ d)
    (z : EuclideanSpace ℝ (Fin d)) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    IntegrableOn (fun v => ‖v - z‖ ^ (-(d : ℝ))) (Metric.ball z R \ Metric.ball z ρ) ∧
      ∫ v in Metric.ball z R \ Metric.ball z ρ, ‖v - z‖ ^ (-(d : ℝ))
        = d * unitBallVolume d * Real.log (R / ρ) := by
  obtain ⟨hint, hval⟩ := integrableOn_annulus_norm_rpow_and_integral_eq (d := d) hd hρ hρR
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) z
  have hemb := measurableEmbedding_subRight z
  have hset : Metric.ball z R \ Metric.ball z ρ
      = (fun v : EuclideanSpace ℝ (Fin d) => v - z) ⁻¹'
          (Metric.ball 0 R \ Metric.ball 0 ρ) := by
    ext v
    simp only [Set.mem_sdiff, Set.mem_preimage, mem_ball_iff_norm, sub_zero]
  rw [hset]
  refine ⟨?_, ?_⟩
  · exact (hmp.integrableOn_comp_preimage hemb (f := fun v => ‖v‖ ^ (-(d : ℝ)))).mpr hint
  · rw [hmp.setIntegral_preimage_emb hemb (fun v => ‖v‖ ^ (-(d : ℝ))), hval]

/-- Near-field bound: the difference of the field integrands over `D ∩ B(z, 2√d)` is at most
`Λ · 5 d ω_d √d`. -/
private lemma setIntegral_abs_fieldIntegrand_sub_le_near (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y z : EuclideanSpace ℝ (Fin d))
    (hyz : ‖y - z‖ ≤ Real.sqrt d) :
    ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
        |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d) := by
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hsubY : D ∩ Metric.ball z (2 * Real.sqrt d) ⊆ Metric.ball y (3 * Real.sqrt d) := by
    intro v hv
    have hvz : ‖v - z‖ < 2 * Real.sqrt d := by
      have h := hv.2
      rwa [Metric.mem_ball, dist_eq_norm] at h
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖v - y‖ ≤ ‖v - z‖ + ‖z - y‖ := by
          rw [show v - y = (v - z) + (z - y) by abel]
          exact norm_add_le _ _
      _ = ‖v - z‖ + ‖y - z‖ := by rw [norm_sub_rev z y]
      _ < 2 * Real.sqrt d + Real.sqrt d := by linarith
      _ = 3 * Real.sqrt d := by ring
  obtain ⟨hintY, hvalY⟩ :=
    integrableOn_ball_and_integral_eq (d := d) hd1 y (ρ := 3 * Real.sqrt d) (by positivity)
  obtain ⟨hintZ, hvalZ⟩ :=
    integrableOn_ball_and_integral_eq (d := d) hd1 z (ρ := 2 * Real.sqrt d) (by positivity)
  have hgy : IntegrableOn (fun v => ‖v - y‖ ^ (1 - (d : ℝ)))
      (D ∩ Metric.ball z (2 * Real.sqrt d)) := hintY.mono_set hsubY
  have hgz : IntegrableOn (fun v => ‖v - z‖ ^ (1 - (d : ℝ)))
      (D ∩ Metric.ball z (2 * Real.sqrt d)) :=
    hintZ.mono_set Set.inter_subset_right
  have hsum : IntegrableOn
      (fun v => Λ * (‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ))))
      (D ∩ Metric.ball z (2 * Real.sqrt d)) := (hgy.add hgz).const_mul Λ
  have hfyD : IntegrableOn (fieldIntegrand g y) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin y
  have hfzD : IntegrableOn (fieldIntegrand g z) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin z
  have hfs : IntegrableOn (fun v => |fieldIntegrand g y v - fieldIntegrand g z v|)
      (D ∩ Metric.ball z (2 * Real.sqrt d)) :=
    ((hfyD.mono_set Set.inter_subset_left).sub (hfzD.mono_set Set.inter_subset_left)).abs
  calc
    ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
        |fieldIntegrand g y v - fieldIntegrand g z v|
        ≤ ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
            Λ * (‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ))) := by
          refine setIntegral_mono_on hfs hsum (hD.inter measurableSet_ball) (fun v _ => ?_)
          refine (abs_fieldIntegrand_sub_le hΛ v y z).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ hΛ0
          calc ‖newtonField (v - y) - newtonField (v - z)‖
              ≤ ‖newtonField (v - y)‖ + ‖newtonField (v - z)‖ := norm_sub_le _ _
            _ = ‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ)) := by
                rw [norm_newtonField hd, norm_newtonField hd]
      _ = Λ * ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
            (‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ))) := integral_const_mul _ _
      _ = Λ * ((∫ v in D ∩ Metric.ball z (2 * Real.sqrt d), ‖v - y‖ ^ (1 - (d : ℝ)))
            + ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d), ‖v - z‖ ^ (1 - (d : ℝ))) := by
          rw [integral_add hgy hgz]
      _ ≤ Λ * ((∫ v in Metric.ball y (3 * Real.sqrt d), ‖v - y‖ ^ (1 - (d : ℝ)))
            + ∫ v in Metric.ball z (2 * Real.sqrt d), ‖v - z‖ ^ (1 - (d : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hΛ0
          · exact setIntegral_mono_set hintY
              (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg _) _))
              hsubY.eventuallyLE
          · exact setIntegral_mono_set hintZ
              (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg _) _))
              Set.inter_subset_right.eventuallyLE
      _ = Λ * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d) := by
          rw [hvalY, hvalZ]
          ring

/-- The far-field set `D \ B(z, 2√d)` lies in the annulus `B(z, (3 + √d)(R + 2)) \ B(z, 2√d)`. -/
private lemma sdiff_ball_subset_annulus {R : ℝ} (hR : 1 ≤ R) {d : ℕ} (hd1 : 1 ≤ d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hDsub : D ⊆ Metric.ball 0 R)
    (y z : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 2 * R) (hyz : ‖y - z‖ ≤ Real.sqrt d) :
    D \ Metric.ball z (2 * Real.sqrt d) ⊆
      Metric.ball z ((3 + Real.sqrt d) * (R + 2)) \ Metric.ball z (2 * Real.sqrt d) := by
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  intro v hv
  refine ⟨?_, hv.2⟩
  have hvD : v ∈ D := hv.1
  have hvR : ‖v‖ < R := by
    have := hDsub hvD
    rwa [Metric.mem_ball, dist_zero_right] at this
  have hz : ‖z‖ ≤ 2 * R + Real.sqrt d := by
    calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      _ = ‖y - z‖ + ‖y‖ := by rw [norm_sub_rev]
      _ ≤ Real.sqrt d + 2 * R := by linarith
      _ = 2 * R + Real.sqrt d := by ring
  have hlt : ‖v - z‖ < (3 + Real.sqrt d) * (R + 2) := by
    have htri : ‖v - z‖ ≤ ‖v‖ + ‖z‖ := norm_sub_le _ _
    nlinarith [hvR, hz, hRpos, hδpos]
  rwa [Metric.mem_ball, dist_eq_norm]

/-- Pointwise far-field bound: for `‖v - z‖ ≥ 2√d` the difference of the field integrands is at
most `Λ A_d √d ‖v - z‖^{-d}`. -/
private lemma abs_fieldIntegrand_sub_le_far (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) (y z v : EuclideanSpace ℝ (Fin d))
    (hyz : ‖y - z‖ ≤ Real.sqrt d) (hvz : 2 * Real.sqrt d ≤ ‖v - z‖) :
    |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) := by
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hA : 0 ≤ farFieldConstant d := by
    rw [farFieldConstant]; positivity
  have h2δpos : 0 < 2 * Real.sqrt d := by positivity
  have hsub : 2 * ‖(v - y) - (v - z)‖ ≤ ‖v - z‖ := by
    have h1 : (v - y) - (v - z) = z - y := by abel
    rw [h1, norm_sub_rev]
    linarith
  have hK := norm_newtonField_sub_le (a := v - y) (b := v - z) hsub
  have hneg : 0 < ‖v - z‖ := lt_of_lt_of_le h2δpos hvz
  have hnum : farFieldConstant d * ‖(v - y) - (v - z)‖
      ≤ farFieldConstant d * Real.sqrt d := by
    have hle : ‖(v - y) - (v - z)‖ ≤ Real.sqrt d := by
      rw [show (v - y) - (v - z) = z - y by abel, norm_sub_rev]
      exact hyz
    exact mul_le_mul_of_nonneg_left hle hA
  have hden : (0 : ℝ) < ‖v - z‖ ^ d := pow_pos hneg d
  calc |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * ‖newtonField (v - y) - newtonField (v - z)‖ := abs_fieldIntegrand_sub_le hΛ v y z
    _ ≤ Λ * (farFieldConstant d * ‖(v - y) - (v - z)‖ / ‖v - z‖ ^ d) :=
        mul_le_mul_of_nonneg_left hK hΛ0
    _ = Λ * ((farFieldConstant d * ‖(v - y) - (v - z)‖) / ‖v - z‖ ^ d) := by ring
    _ ≤ Λ * ((farFieldConstant d * Real.sqrt d) / ‖v - z‖ ^ d) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hden.le) hΛ0
    _ = Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) := by
        rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, div_eq_mul_inv]
        ring

/-- Far-field bound: the difference of the field integrands over `D \ B(z, 2√d)` is at most
`Λ A_d √d σ_d log(((3 + √d)(R + 2))/(2√d))`. -/
private lemma setIntegral_abs_fieldIntegrand_sub_le_far (hd : 2 ≤ d) {R : ℝ} (hR : 1 ≤ R)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hDsub : D ⊆ Metric.ball 0 R)
    (y z : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 2 * R)
    (hyz : ‖y - z‖ ≤ Real.sqrt d) :
    ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
        |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * farFieldConstant d * Real.sqrt d
        * ((d : ℝ) * unitBallVolume d
          * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hA : 0 ≤ farFieldConstant d := by
    rw [farFieldConstant]; positivity
  have h2δpos : 0 < 2 * Real.sqrt d := by positivity
  have h2δR' : 2 * Real.sqrt d ≤ (3 + Real.sqrt d) * (R + 2) := by
    nlinarith [hR, hδpos]
  have hsubset := sdiff_ball_subset_annulus hR hd1 hDsub y z hy hyz
  obtain ⟨hannInt, hannVal⟩ :=
    integrableOn_annulus_sub_rpow_neg_and_integral_eq (d := d) hd1 z
      (ρ := 2 * Real.sqrt d) (R := (3 + Real.sqrt d) * (R + 2)) h2δpos h2δR'
  have hbig : IntegrableOn
      (fun v => Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)))
      (Metric.ball z ((3 + Real.sqrt d) * (R + 2)) \ Metric.ball z (2 * Real.sqrt d)) :=
    hannInt.const_mul (Λ * farFieldConstant d * Real.sqrt d)
  have hsmall : IntegrableOn
      (fun v => Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)))
      (D \ Metric.ball z (2 * Real.sqrt d)) := hbig.mono_set hsubset
  have hfyD : IntegrableOn (fieldIntegrand g y) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin y
  have hfzD : IntegrableOn (fieldIntegrand g z) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin z
  have hfs : IntegrableOn (fun v => |fieldIntegrand g y v - fieldIntegrand g z v|)
      (D \ Metric.ball z (2 * Real.sqrt d)) :=
    ((hfyD.mono_set Set.sdiff_subset).sub (hfzD.mono_set Set.sdiff_subset)).abs
  have hpt : ∀ v ∈ D \ Metric.ball z (2 * Real.sqrt d),
      |fieldIntegrand g y v - fieldIntegrand g z v|
        ≤ Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) := by
    intro v hv
    have hvz : 2 * Real.sqrt d ≤ ‖v - z‖ := by
      have hnot : ¬ ‖v - z‖ < 2 * Real.sqrt d := by
        intro hlt
        exact hv.2 (by rwa [Metric.mem_ball, dist_eq_norm])
      linarith
    exact abs_fieldIntegrand_sub_le_far hd hΛ y z v hyz hvz
  have hfar1 : ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
        |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
          Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) :=
    setIntegral_mono_on hfs hsmall (hD.diff measurableSet_ball) hpt
  have hcnn : 0 ≤ Λ * farFieldConstant d * Real.sqrt d := by positivity
  have hfar2 : ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
          Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ))
      ≤ ∫ v in Metric.ball z ((3 + Real.sqrt d) * (R + 2)) \ Metric.ball z (2 * Real.sqrt d),
          Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) :=
    setIntegral_mono_set hbig
      (Filter.Eventually.of_forall
        (fun v => mul_nonneg hcnn (Real.rpow_nonneg (norm_nonneg _) _)))
      hsubset.eventuallyLE
  have hfar3 : ∫ v in Metric.ball z ((3 + Real.sqrt d) * (R + 2))
          \ Metric.ball z (2 * Real.sqrt d),
          Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ))
      = Λ * farFieldConstant d * Real.sqrt d
          * ((d : ℝ) * unitBallVolume d
            * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
    rw [integral_const_mul, hannVal]
  exact hfar1.trans (hfar2.trans (le_of_eq hfar3))

/-- Arithmetic bound: for nonnegative `δ` and `A`, `M ≥ 0` and `L ≥ 1`, if `Lf ≤ M + L`, then
`5 δ + A δ Lf ≤ (5 + A (1 + M)) δ L`. -/
private lemma add_mul_le_mul_log {δ A M L Lf : ℝ} (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hL : 1 ≤ L) (hlog : Lf ≤ M + L) :
    5 * δ + A * δ * Lf ≤ (5 + A * (1 + M)) * δ * L := by
  have h1 : 5 * δ ≤ 5 * δ * L := by nlinarith
  have h2 : A * δ * Lf ≤ A * δ * (M + L) :=
    mul_le_mul_of_nonneg_left hlog (mul_nonneg hA hδ)
  have h4 : A * δ * M ≤ A * δ * M * L := by
    have hAM : 0 ≤ A * δ * M := mul_nonneg (mul_nonneg hA hδ) hM
    nlinarith
  nlinarith [h1, h2, h4]

/-- The logarithm of the far-field radius ratio is at most `log (3 + √d) + log (R + 2)`. -/
private lemma log_far_ratio_le {d : ℕ} (hd1 : 1 ≤ d) {R : ℝ} (hR : 1 ≤ R) :
    Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))
      ≤ Real.log (3 + Real.sqrt d) + Real.log (R + 2) := by
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hle : ((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d) ≤ (3 + Real.sqrt d) * (R + 2) :=
    div_le_self (by positivity) (by linarith [hδ1])
  calc Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))
      ≤ Real.log ((3 + Real.sqrt d) * (R + 2)) := Real.log_le_log (by positivity) hle
    _ = Real.log (3 + Real.sqrt d) + Real.log (R + 2) :=
        Real.log_mul (by positivity) (by linarith)

/-- For `R ≥ 1`, `log (R + 2) ≥ 1`. -/
private lemma one_le_log_add_two_of_one_le {R : ℝ} (hR : 1 ≤ R) : 1 ≤ Real.log (R + 2) := by
  have hexp : Real.exp 1 ≤ R + 2 := by
    have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have h := Real.log_le_log (Real.exp_pos 1) hexp
  rwa [Real.log_exp] at h

/-- The coefficient identity: `(2ε/ω) (Λ (5 d ω δ) + Λ A δ (d ω Lf)) = 2 ε d Λ (5 δ + A δ Lf)`. -/
private lemma coefficient_identity {ω ε Λ A δ Lf : ℝ} (n : ℝ) (hω : ω ≠ 0) :
    (2 * ε / ω) * (Λ * (5 * n * ω * δ) + Λ * A * δ * (n * ω * Lf))
      = 2 * ε * n * Λ * (5 * δ + A * δ * Lf) := by
  field_simp

/-- `eq:cellmodulus` for a bounded measurable field: for `D ⊆ B(0, R)` with `R ≥ 1`, and `y, z`
with `|y| ≤ 2R` and `|y - z| ≤ √d`, the potentials of the field differ by at most `C ε log(R + 2)`,
where `C` depends only on `d` and the bound `Λ` of the field. -/
private lemma exists_fieldPotential_cell_modulus (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g y v)
          - 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g z v)|
          ≤ C * ε * Real.log (R + 2) := by
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hδnn : 0 ≤ Real.sqrt d := hδpos.le
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hAnn : 0 ≤ farFieldConstant d := by
    rw [farFieldConstant]; positivity
  have hlogM : 0 ≤ Real.log (3 + Real.sqrt d) := Real.log_nonneg (by linarith [hδpos])
  refine ⟨2 * (d : ℝ) * Λ * Real.sqrt d
    * (5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d))), ?_, ?_⟩
  · have h5 : 0 ≤ 5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)) := by
      have h6 : 0 ≤ farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)) :=
        mul_nonneg hAnn (by linarith)
      linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hΛ0)
      hδnn) h5
  intro ε hε R hR D hD hDsub y z hy hyz
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hDfin : volume D ≠ ⊤ := by
    have hle : volume D ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      measure_mono hDsub
    exact ne_of_lt (lt_of_le_of_lt hle measure_ball_lt_top)
  have hcoef : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hfyD : IntegrableOn (fieldIntegrand g y) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin y
  have hfzD : IntegrableOn (fieldIntegrand g z) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin z
  have hU : 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g y v)
        - 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g z v)
      = (2 * ε / unitBallVolume d)
        * ∫ v in D, (fieldIntegrand g y v - fieldIntegrand g z v) := by
    rw [← mul_sub, ← integral_sub hfyD hfzD]
  have habsInt : |∫ v in D, (fieldIntegrand g y v - fieldIntegrand g z v)|
      ≤ ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v| := by
    have h := norm_integral_le_integral_norm (μ := volume.restrict D)
      (fun v => fieldIntegrand g y v - fieldIntegrand g z v)
    simpa only [Real.norm_eq_abs] using h
  have habsU : |2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g y v)
        - 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g z v)|
      ≤ (2 * ε / unitBallVolume d)
        * ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v| := by
    rw [hU, abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left habsInt hcoef
  have hfsD : IntegrableOn (fun v => |fieldIntegrand g y v - fieldIntegrand g z v|) D :=
    (hfyD.sub hfzD).abs
  have hsplit : ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v|
      = (∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
          |fieldIntegrand g y v - fieldIntegrand g z v|)
        + (∫ v in D \ Metric.ball z (2 * Real.sqrt d),
          |fieldIntegrand g y v - fieldIntegrand g z v|) :=
    (integral_inter_add_sdiff (μ := volume) (s := D) (t := Metric.ball z (2 * Real.sqrt d))
      measurableSet_ball hfsD).symm
  have hnear := setIntegral_abs_fieldIntegrand_sub_le_near (d := d) hd hg hΛ hD hDfin y z hyz
  have hfar := setIntegral_abs_fieldIntegrand_sub_le_far (d := d) hd hR hg hΛ hD hDfin hDsub
    y z hy hyz
  have hintD : ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d)
        + Λ * farFieldConstant d * Real.sqrt d
          * ((d : ℝ) * unitBallVolume d
            * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
    rw [hsplit]
    exact add_le_add hnear hfar
  have hbase : 5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
        * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))
      ≤ (5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
        * Real.sqrt d * Real.log (R + 2) :=
    add_mul_le_mul_log hδnn hAnn hlogM (one_le_log_add_two_of_one_le hR) (log_far_ratio_le hd1 hR)
  have hcoefnn : 0 ≤ 2 * ε * (d : ℝ) * Λ := by positivity
  calc |2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g y v)
        - 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g z v)|
      ≤ (2 * ε / unitBallVolume d)
        * ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v| := habsU
    _ ≤ (2 * ε / unitBallVolume d)
        * (Λ * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d)
          + Λ * farFieldConstant d * Real.sqrt d
            * ((d : ℝ) * unitBallVolume d
              * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d)))) :=
        mul_le_mul_of_nonneg_left hintD hcoef
    _ = 2 * ε * (d : ℝ) * Λ
        * (5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
          * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) :=
        coefficient_identity (d : ℝ) hω.ne'
    _ ≤ 2 * ε * (d : ℝ) * Λ
        * ((5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
          * Real.sqrt d * Real.log (R + 2)) :=
        mul_le_mul_of_nonneg_left hbase hcoefnn
    _ = 2 * (d : ℝ) * Λ * Real.sqrt d
          * (5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
          * ε * Real.log (R + 2) := by ring

/-- `eq:cellmodulus` for the potential of the gauge: for `D ⊆ B(0, R)` with `R ≥ 1`, and `y, z`
with `|y| ≤ 2R` and `|y - z| ≤ √d`, `|U_D(y) - U_D(z)| ≤ C ε log(R + 2)`, with `C` depending only
on `d` and `K`. -/
theorem gauge_normPotential_cell_modulus (hd : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε (gauge K) D y - normPotential d ε (gauge K) D z| ≤
          C * ε * Real.log (R + 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_fieldPotential_cell_modulus hd (measurable_gradient (gauge K))
    (norm_gradient_gauge_le hK hc h0)
  refine ⟨C, hC0, fun ε hε R hR D hD hDsub y z hy hyz => ?_⟩
  simp only [normPotential_eq_integral]
  exact hC ε hε R hR D hD hDsub y z hy hyz

end CellModulus


section DriftDynkin

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.Drift
open CERW.Support.Occupation CERW.Support.LocalTime

variable {d : ℕ}

/-- The interval Dynkin decomposition of `ℓ_{s,t}(y)` for the walk with a drift field, for a path
from the origin. -/
private theorem intervalLocalTime_eq_driftDynkin {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) (ε : ℝ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ0 : ξ 0 = 0) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0) {s t : ℕ} (hst : s ≤ t) (y : Site d) :
    (intervalLocalTime (fun j => X j ω) s t y : ℝ) =
      b (X t ω - y) - b (X s ω - y) +
        ε * (∑ z ∈ departureRange (fun j => X j ω) t \ departureRange (fun j => X j ω) s,
          inner ℝ (ξ z) (centralDiff b (z - y))) -
        (driftDynkin ε ξ (fun z => b (z - y)) X t ω -
          driftDynkin ε ξ (fun z => b (z - y)) X s ω) := by
  have ht := ContactDynkin.localTime_eq_driftDynkin hb ε ξ hξ0 X ω h0 t y
  have hs := ContactDynkin.localTime_eq_driftDynkin hb ε ξ hξ0 X ω h0 s y
  have hadd : ((localTime (fun j => X j ω) s y : ℕ) : ℝ) +
      (intervalLocalTime (fun j => X j ω) s t y : ℝ) =
      ((localTime (fun j => X j ω) t y : ℕ) : ℝ) := by
    exact_mod_cast localTime_add_intervalLocalTime (fun j => X j ω) hst y
  have hsub : departureRange (fun j => X j ω) s ⊆ departureRange (fun j => X j ω) t :=
    departureRange_mono _ hst
  have hsum := Finset.sum_sdiff_eq_sub hsub
    (f := fun z => inner ℝ (ξ z) (centralDiff b (z - y)))
  rw [hsum, mul_sub]
  linarith [ht, hs, hadd]

end DriftDynkin

section IntervalMartingale

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.Drift
open CERW.Support.Occupation CERW.Support.LocalTime

variable {d : ℕ}

/-- The interval maximum is at least one on a nonempty interval. -/
private lemma one_le_intervalMax (x : ℕ → Site d) {s t : ℕ} (hst : s < t) :
    1 ≤ intervalMax x s t := by
  have hs : s ∈ Ico s t := mem_Ico.mpr ⟨le_rfl, hst⟩
  have h1 : 1 ≤ intervalLocalTime x s t (x s) :=
    Finset.card_pos.mpr ⟨s, mem_filter.mpr ⟨hs, rfl⟩⟩
  exact h1.trans (Finset.le_sup (f := intervalLocalTime x s t) (mem_image_of_mem x hs))

/-- A sum over `s ≤ j < t` of a nonnegative function of the position is at most `M_{s,t}` times
the same function summed over the sites visited in `[s, t)`. -/
private lemma sum_Ico_le_intervalMax_mul (x : ℕ → Site d) (s t : ℕ) {g : Site d → ℝ}
    (hg : ∀ z, 0 ≤ g z) :
    ∑ j ∈ Ico s t, g (x j) ≤ (intervalMax x s t : ℝ) * ∑ z ∈ (Ico s t).image x, g z := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Ico s t) (t := (Ico s t).image x) (g := x)
    (f := fun i => g (x i)) (fun i hi => mem_image_of_mem x hi), Finset.mul_sum]
  refine sum_le_sum fun z _ => ?_
  have hinner : ∑ i ∈ (Ico s t).filter (fun i => x i = z), g (x i) =
      (intervalLocalTime x s t z : ℝ) * g z := by
    rw [sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2], sum_const, nsmul_eq_mul]
    rfl
  rw [hinner]
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast intervalLocalTime_le_intervalMax x s t z) (hg z)

/-- The sum of `(1 + |z - y|)^{2-2d}` over any set of sites within `4n` of `y` is `O(log n)`
for `d = 2` and `O(1)` for `d ≥ 3`. -/
private lemma exists_sum_image_le (hd : 2 ≤ d) :
    ∃ D : ℝ, 0 < D ∧ ∀ (x : ℕ → Site d) (n : ℕ), 1 ≤ n → (∀ j, euclidNorm (x j) ≤ j) →
      ∀ y : Site d, euclidNorm y ≤ 3 * n → ∀ s t : ℕ, t ≤ n →
        ∑ z ∈ (Ico s t).image x, (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) ≤
          D * (if d = 2 then Real.log (n + 2) else 1) := by
  by_cases h2 : d = 2
  · obtain ⟨C, hC0, hC⟩ := CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) (by omega)
    refine ⟨2 * C, by positivity, ?_⟩
    intro x n hn hx y hy s t htn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hR : ∀ z ∈ (Ico s t).image x, euclidNorm (z - y) ≤ 4 * n := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hj).2.le.trans htn
      linarith [euclidNorm_sub_le (x j) y, hx j]
    have hexp : (2 - 2 * (d : ℝ)) = -(d : ℝ) := by subst h2; norm_num
    simp only [hexp]
    have h1 := hC ((Ico s t).image x) y (4 * n) (by linarith) hR
    have h3 : Real.log (4 * (n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) := by
      have h4 := Real.log_le_log (by linarith : (0 : ℝ) < 4 * n + 2)
        (by nlinarith : 4 * (n : ℝ) + 2 ≤ ((n : ℝ) + 2) ^ 2)
      rw [Real.log_pow] at h4
      simpa using h4
    rw [if_pos h2]
    calc _ ≤ C * Real.log (4 * (n : ℝ) + 2) := h1
      _ ≤ C * (2 * Real.log ((n : ℝ) + 2)) := mul_le_mul_of_nonneg_left h3 hC0.le
      _ = 2 * C * Real.log ((n : ℝ) + 2) := by ring
  · obtain ⟨C, hC0, hC⟩ :=
      CERW.Generic.Lattice.sum_finset_rpow_two_sub_two_mul_le (d := d) (by omega)
    refine ⟨C, hC0, ?_⟩
    intro x n _ _ y _ s t _
    rw [if_neg h2, mul_one]
    exact hC _ y

/-- The error term `e_n(m) = √m L + L` for `d = 2` and `√(m L) + L` for `d ≥ 3`. -/
private noncomputable def errorBound (d : ℕ) (m L : ℝ) : ℝ :=
  if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L

/-- The error term as `√(m Λ L) + L`, where `Λ = L` for `d = 2` and `Λ = 1` otherwise. -/
private lemma errorBound_eq {m L : ℝ} (hm : 0 ≤ m) (hL : 0 ≤ L) :
    errorBound d m L = Real.sqrt (m * (if d = 2 then L else 1) * L) + L := by
  unfold errorBound
  split_ifs with h
  · rw [show m * L * L = m * (L * L) by ring, Real.sqrt_mul hm, Real.sqrt_mul_self hL]
  · rw [mul_one]

/-- The deterministic step: on a path staying in the ball `|x_j| ≤ j`, the Freedman threshold
`c (√(max(V_t - V_s, 1) L) + B L)` is at most `C e_n(M_{s,t})`. -/
private lemma exists_det_bound (hd : 2 ≤ d) {Cg : ℝ} (hCg : 0 ≤ Cg) {c : ℝ} (hc : 1 ≤ c) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ (x : ℕ → Site d) (n : ℕ), 2 ≤ n → (∀ j, euclidNorm (x j) ≤ j) →
      ∀ y : Site d, euclidNorm y ≤ 3 * n → ∀ s t : ℕ, s < t → t ≤ n →
        c * (Real.sqrt (max (Cg ^ 2 * ∑ j ∈ Ico s t,
              (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) 1 * Real.log (n + 2)) +
            (2 * Cg + 1) * Real.log (n + 2)) ≤
          Cdet * errorBound d (intervalMax x s t) (Real.log (n + 2)) := by
  obtain ⟨D, hD0, hD⟩ := exists_sum_image_le hd
  set A : ℝ := Cg ^ 2 * D with hA
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 < 2 * Cg + 1 := by linarith
  refine ⟨c * (Real.sqrt (A + 1) + (2 * Cg + 1)), by positivity, ?_⟩
  intro x n hn hx y hy s t hst htn
  set L : ℝ := Real.log (n + 2) with hLdef
  have hL1 : 1 ≤ L := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h4 : Real.log 4 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    have h5 : (1 : ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith [this]
    linarith
  have hL0 : 0 ≤ L := by linarith
  set m : ℝ := (intervalMax x s t : ℝ) with hm
  have hm1 : 1 ≤ m := by
    have h := one_le_intervalMax x hst
    rw [hm]
    exact_mod_cast h
  set Λ : ℝ := if d = 2 then L else 1 with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ]
    split_ifs <;> linarith
  have hS : ∑ j ∈ Ico s t, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ)) ≤ m * (D * Λ) :=
    (sum_Ico_le_intervalMax_mul x s t (g := fun z => (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)))
      (fun z => Real.rpow_nonneg (by linarith [euclidNorm_nonneg (z - y)]) _)).trans
      (mul_le_mul_of_nonneg_left (hD x n (by omega) hx y hy s t htn) (Nat.cast_nonneg _))
  have hmΛ : 1 ≤ m * Λ := by nlinarith
  have hmax : max (Cg ^ 2 * ∑ j ∈ Ico s t, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) 1 ≤
      (A + 1) * (m * Λ) := by
    refine max_le ?_ (by nlinarith)
    calc Cg ^ 2 * ∑ j ∈ Ico s t, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))
        ≤ Cg ^ 2 * (m * (D * Λ)) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
      _ = A * (m * Λ) := by rw [hA]; ring
      _ ≤ (A + 1) * (m * Λ) := by nlinarith
  set u : ℝ := Real.sqrt (m * Λ * L) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hsq : Real.sqrt (max (Cg ^ 2 * ∑ j ∈ Ico s t,
      (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) 1 * L) ≤ Real.sqrt (A + 1) * u := by
    rw [hu, ← Real.sqrt_mul (by linarith)]
    refine Real.sqrt_le_sqrt ?_
    calc _ ≤ (A + 1) * (m * Λ) * L := mul_le_mul_of_nonneg_right hmax hL0
      _ = (A + 1) * (m * Λ * L) := by ring
  rw [errorBound_eq (by linarith) hL0]
  have hsA : 0 ≤ Real.sqrt (A + 1) := Real.sqrt_nonneg _
  calc _ ≤ c * (Real.sqrt (A + 1) * u + (2 * Cg + 1) * L) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        linarith
    _ ≤ c * (Real.sqrt (A + 1) + (2 * Cg + 1)) * (u + L) := by
        have : Real.sqrt (A + 1) * u + (2 * Cg + 1) * L ≤
            (Real.sqrt (A + 1) + (2 * Cg + 1)) * (u + L) := by
          nlinarith [mul_nonneg hsA hL0, mul_nonneg hB0.le hu0]
        calc _ ≤ c * ((Real.sqrt (A + 1) + (2 * Cg + 1)) * (u + L)) :=
              mul_le_mul_of_nonneg_left this (by linarith)
          _ = _ := by ring

/-- One interval–target pair: Freedman's inequality at dyadic brackets, followed by the
deterministic step, bounds the probability that `𝓜^y_t - 𝓜^y_s` exceeds `C e_n(M_{s,t})`. -/
private lemma exists_event_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cdet : ℝ, 0 < Cdet ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {ξ : Site d → EuclideanSpace ℝ (Fin d)}
      (_ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) {X : ℕ → Ω → Site d},
      IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        ∀ s t : ℕ, ∀ y : Site d, s < t → t ≤ n → euclidNorm y ≤ 3 * n →
          μ {ω | Cdet * errorBound d (intervalMax (fun j => X j ω) s t) (Real.log (n + 2)) <
              |driftDynkin ε ξ (fun z => b (z - y)) X t ω -
                driftDynkin ε ξ (fun z => b (z - y)) X s ω|} ≤
            ENNReal.ofReal (((Nat.clog 2 ⌈max (Cg ^ 2 * n) 1⌉₊ : ℕ) + 1) *
              (2 * Real.exp (-(K * Real.log (n + 2))))) := by
  have hd1 : 1 ≤ d := by omega
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound hK
  obtain ⟨Cdet, hCdet0, hCdet⟩ := exists_det_bound hd hCg hc1
  refine ⟨Cdet, hCdet0, ?_⟩
  intro Ω _ μ _ ξ hξ X hX n hn s t y hst htn hy
  obtain ⟨M, hM, hbd, hvar, hae⟩ :=
    ContactDynkin.exists_clamped_translate_drift hd1 hε hξ hX hgrad y
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst.le
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hW : (1 : ℝ) ≤ max (Cg ^ 2 * n) 1 := le_max_right _ _
  have hdy := hc hM (V := bracket Cg y X) (stronglyMeasurable_bracket_succ hX.measurable Cg y)
    (bracket_zero Cg y X) (bracket_mono Cg y X) hvar (b := 2 * Cg + 1) (by linarith) s k
    (fun i _ _ ω => hbd i ω) (W := max (Cg ^ 2 * n) 1) (L := Real.log ((n : ℝ) + 2)) hW hL
    (fun ω => (bracket_sub_le hd1 Cg y X (Nat.le_add_right s k) htn ω).trans (le_max_left _ _))
  refine le_trans (measure_mono_ae ?_) hdy
  filter_upwards [hae, ae_euclidNorm_le_drift hd1 hε hξ hX] with ω hω hx hE
  change _ < _ at hE
  change _ < _
  rw [hω (s + k), hω s]
  refine lt_of_le_of_lt ?_ hE
  rw [bracket_sub Cg y X (Nat.le_add_right s k) ω]
  exact hCdet (fun j => X j ω) n hn hx y hy s (s + k) hst htn

/-- The error term is nonnegative. -/
private lemma errorBound_nonneg (m : ℝ) {L : ℝ} (hL : 0 ≤ L) : 0 ≤ errorBound d m L := by
  unfold errorBound
  split_ifs <;> positivity

/-- The arithmetic of the union bound: `(n + 1)² (7 (n + 1))^D · G (n + 1) · 2 e^{-(p + D + 3) L}`
is at most `7^D G 2^{D+4} n^{-p}`. -/
private lemma union_bound_arith {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (D : ℕ) {G : ℝ}
    (hG : 0 ≤ G) :
    (((n : ℝ) + 1) ^ 2 * (7 * ((n : ℝ) + 1)) ^ D) * ((G * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((D + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) ≤
    (7 ^ D * G * 2 ^ (D + 4)) * (n : ℝ) ^ (-p) := by
  have h1 := CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le
    (K := p + ((D + 3 : ℕ) : ℝ)) (by positivity) hn
  have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn (D + 3) p
  have h3 : (0 : ℝ) ≤ 7 ^ D * G * ((n : ℝ) + 1) ^ (D + 3) := by positivity
  calc (((n : ℝ) + 1) ^ 2 * (7 * ((n : ℝ) + 1)) ^ D) * ((G * ((n : ℝ) + 1)) *
        (2 * Real.exp (-((p + ((D + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))
      = (7 ^ D * G * ((n : ℝ) + 1) ^ (D + 3)) *
          (2 * Real.exp (-((p + ((D + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by
        rw [mul_pow]
        ring
    _ ≤ (7 ^ D * G * ((n : ℝ) + 1) ^ (D + 3)) * (2 * (n : ℝ) ^ (-(p + ((D + 3 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = 2 * (7 ^ D * G) * (((n : ℝ) + 1) ^ (D + 3) * (n : ℝ) ^ (-(p + ((D + 3 : ℕ) : ℝ)))) := by
        ring
    _ ≤ 2 * (7 ^ D * G) * (2 ^ (D + 3) * (n : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (7 ^ D * G * 2 ^ (D + 4)) * (n : ℝ) ^ (-p) := by ring

/-- `eq:interval-mart`: under the one-step bound `|b(x + e) - b(x)| ≤ C_g (1 + |x|)^{1-d}`, with
probability at least `1 - Cn^{-p}`, `|𝓜^y_t - 𝓜^y_s| ≤ C e_n(M_{s,t})` for all `0 ≤ s < t ≤ n` and
all `|y| ≤ 3n`. -/
private theorem exists_interval_mart_drift (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {ξ : Site d → EuclideanSpace ℝ (Fin d)} (_ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
      {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ∃ s t : ℕ, ∃ y : Site d, s < t ∧ t ≤ n ∧ euclidNorm y ≤ 3 * n ∧
          C * (if d = 2 then
              Real.sqrt (intervalMax (fun j => X j ω) s t) * Real.log (n + 2) + Real.log (n + 2)
            else Real.sqrt (intervalMax (fun j => X j ω) s t * Real.log (n + 2)) +
              Real.log (n + 2)) <
            |driftDynkin ε ξ (fun z => b (z - y)) X t ω -
              driftDynkin ε ξ (fun z => b (z - y)) X s ω|} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  have hCg := cg_nonneg hd1 hgrad
  obtain ⟨Cdet, hCdet0, hCdet⟩ := exists_event_bound hd hε hgrad
    (K := p + ((d + 3 : ℕ) : ℝ)) (by positivity)
  refine ⟨Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4), by positivity, ?_⟩
  intro Ω _ μ _ ξ hξ X hX n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL0 : 0 ≤ Real.log ((n : ℝ) + 2) := (Real.log_pos (by linarith)).le
  set P : Finset (ℕ × ℕ) := ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun q => q.1 < q.2)
    with hP
  set Y : Finset (Site d) := ballFinset d (3 * (n : ℝ)) with hY
  set B : ℕ × ℕ → Site d → Set Ω := fun q y =>
    {ω | Cdet * errorBound d (intervalMax (fun j => X j ω) q.1 q.2) (Real.log ((n : ℝ) + 2)) <
      |driftDynkin ε ξ (fun z => b (z - y)) X q.2 ω - driftDynkin ε ξ (fun z => b (z - y)) X q.1 ω|}
    with hB
  have hsub : {ω | ∃ s t : ℕ, ∃ y : Site d, s < t ∧ t ≤ n ∧ euclidNorm y ≤ 3 * n ∧
      (Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4)) * (if d = 2 then
              Real.sqrt (intervalMax (fun j => X j ω) s t) * Real.log (n + 2) + Real.log (n + 2)
            else Real.sqrt (intervalMax (fun j => X j ω) s t * Real.log (n + 2)) +
              Real.log (n + 2)) <
            |driftDynkin ε ξ (fun z => b (z - y)) X t ω -
              driftDynkin ε ξ (fun z => b (z - y)) X s ω|} ⊆
      ⋃ q ∈ P, ⋃ y ∈ Y, B q y := by
    rintro ω ⟨s, t, y, hst, htn, hy, hlt⟩
    simp only [Set.mem_iUnion]
    refine ⟨(s, t), ?_, y, ?_, ?_⟩
    · simp only [hP, mem_filter, mem_product, mem_range]
      omega
    · rw [hY, mem_ballFinset_iff]
      exact hy
    · change Cdet * errorBound d _ _ < _
      have he := errorBound_nonneg (d := d) ((intervalMax (fun j => X j ω) s t : ℕ) : ℝ) hL0
      have hlt' : (Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4)) *
          errorBound d (intervalMax (fun j => X j ω) s t) (Real.log ((n : ℝ) + 2)) <
            |driftDynkin ε ξ (fun z => b (z - y)) X t ω -
              driftDynkin ε ξ (fun z => b (z - y)) X s ω| := hlt
      have h7 : 0 ≤ 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4) := by positivity
      nlinarith [mul_nonneg h7 he]
  have hbound : ∀ q ∈ P, ∀ y ∈ Y, μ (B q y) ≤ ENNReal.ofReal (((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
      (2 * Real.exp (-((p + ((d + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) := by
    intro q hq y hy
    have hq' := mem_filter.mp hq
    have h2 : q.2 ≤ n := by
      have := mem_range.mp (mem_product.mp hq'.1).2
      omega
    have hyn : euclidNorm y ≤ 3 * n := mem_ballFinset_iff.mp hy
    refine (hCdet hξ hX n hn q.1 q.2 y hq'.2 h2 hyn).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (clog_ceil_add_one_le Cg n) (by positivity)
  have hPcard : (P.card : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have h1 : P.card ≤ (n + 1) * (n + 1) := by
      refine (card_filter_le _ _).trans ?_
      simp
    exact_mod_cast h1.trans_eq (by ring)
  have hYcard : (Y.card : ℝ) ≤ (7 * ((n : ℝ) + 1)) ^ d :=
    (card_ballFinset_le d (R := 3 * (n : ℝ)) (by positivity)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) d)
  set a : ℝ := ((Cg ^ 2 + 3) * ((n : ℝ) + 1)) *
    (2 * Real.exp (-((p + ((d + 3 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) with ha
  have ha0 : 0 ≤ a := by positivity
  refine (measure_mono hsub).trans ?_
  calc μ (⋃ q ∈ P, ⋃ y ∈ Y, B q y) ≤ ∑ q ∈ P, μ (⋃ y ∈ Y, B q y) := measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ P, ∑ y ∈ Y, μ (B q y) := sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ P, ∑ _y ∈ Y, ENNReal.ofReal a :=
        sum_le_sum fun q hq => sum_le_sum fun y hy => hbound q hq y hy
    _ = ENNReal.ofReal ((P.card : ℝ) * ((Y.card : ℝ) * a)) := by
        simp only [sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (p := (P.card : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_mul (p := (Y.card : ℝ)) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((Cdet + 7 ^ d * (Cg ^ 2 + 3) * 2 ^ (d + 4)) * (n : ℝ) ^ (-p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (P.card : ℝ) * ((Y.card : ℝ) * a) ≤
            (((n : ℝ) + 1) ^ 2 * (7 * ((n : ℝ) + 1)) ^ d) * a := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hPcard hYcard (Nat.cast_nonneg _) (by positivity)) ha0
        have h2 := union_bound_arith hp.le (by omega : 1 ≤ n) d (G := Cg ^ 2 + 3) (by positivity)
        have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
        nlinarith [mul_nonneg hCdet0.le h3]

end IntervalMartingale

section SourcePacking

open MeasureTheory LatticeProb CERW CERW.Support.Law CERW.Generic.Kernel CERW.Support.Occupation
open CERW.Support.LocalTime CERW.Generic.Lattice

variable {d : ℕ}

/-- Each coordinate of the central difference is at most `C (1 + |z|)^{1-d}` once every one-step
increment is at most `Cg (1 + |z|)^{1-d}` and `Cg ≤ C`. -/
private lemma abs_centralDiff_coord_le_of_step {b : Site d → ℝ} {Cg C : ℝ} (hCgC : Cg ≤ C)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) (z : Site d) (i : Fin d) :
    ‖(centralDiff b z) i‖ ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
  have hX : 0 ≤ (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
    Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
  have h1 : |b (z + unit i) - b z| ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
    (hgrad z (unit i) (mem_unitSteps.mpr ⟨i, Or.inl rfl⟩)).trans
      (mul_le_mul_of_nonneg_right hCgC hX)
  have h2 : |b (z - unit i) - b z| ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
    have h : |b (z + -unit i) - b z| ≤ Cg * (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
      hgrad z (-unit i) (mem_unitSteps.mpr ⟨i, Or.inr rfl⟩)
    rw [sub_eq_add_neg z (unit i)]
    exact h.trans (mul_le_mul_of_nonneg_right hCgC hX)
  have h2sym : |b z - b (z - unit i)| ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
    rw [abs_sub_comm]
    exact h2
  have htri : |b (z + unit i) - b (z - unit i)| ≤
      2 * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) := by
    have h := abs_sub_le (b (z + unit i)) (b z) (b (z - unit i))
    linarith
  have hcoord : (centralDiff b z) i = (b (z + unit i) - b (z - unit i)) / 2 := by
    simp only [centralDiff, PiLp.toLp_apply]
  rw [hcoord, Real.norm_eq_abs, abs_div]
  have h2abs : |(2 : ℝ)| = 2 := by norm_num
  rw [h2abs]
  linarith

/-- The Euclidean norm of the central difference is at most `√d (C (1 + |z|)^{1-d})` once every
coordinate is. -/
private lemma norm_centralDiff_le_of_step {b : Site d → ℝ} {Cg C : ℝ} (hCnonneg : 0 ≤ C)
    (hCgC : Cg ≤ C)
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) (z : Site d) :
    ‖centralDiff b z‖ ≤ Real.sqrt d * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) := by
  have hX : 0 ≤ (1 + euclidNorm z) ^ (1 - (d : ℝ)) :=
    Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
  have hc : 0 ≤ C * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := mul_nonneg hCnonneg hX
  have hcoord := abs_centralDiff_coord_le_of_step hCgC hgrad z
  rw [EuclideanSpace.norm_eq]
  calc √(∑ i : Fin d, ‖(centralDiff b z) i‖ ^ 2)
      ≤ √(∑ _i : Fin d, (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
    _ = √((d : ℝ) * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = Real.sqrt d * (C * (1 + euclidNorm z) ^ (1 - (d : ℝ))) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hc]

/-- For a kernel with the one-step bound, `|Σ_{x ∈ F} ξ(x) · Db(x - y)| ≤ C_d |F|^{1/d}` for
every finite `F`, every `y` and every field `ξ` with `|ξ(x)| ≤ Λ`. -/
private theorem exists_abs_sum_inner_drift_centralDiff_le (hd : 2 ≤ d) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (Λ : ℝ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)), (∀ x, ‖ξ x‖ ≤ Λ) →
      ∀ (F : Finset (Site d)) (y : Site d),
        |∑ x ∈ F, inner ℝ (ξ x) (centralDiff b (x - y))| ≤ Cd * (F.card : ℝ) ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, hC₀pos, hC₀⟩ := sum_rpow_one_sub_le_card_rpow (d := d) hd1
  set Cgmax : ℝ := max Cg 0 with hCgmax
  have hCg_le : Cg ≤ Cgmax := by rw [hCgmax]; exact le_max_left _ _
  have hCgmax_nonneg : 0 ≤ Cgmax := by rw [hCgmax]; exact le_max_right _ _
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  refine ⟨Λ' * (Real.sqrt d * Cgmax * C₀), ?_, ?_⟩
  · exact mul_nonneg hΛ'0 (mul_nonneg (mul_nonneg (Real.sqrt_nonneg d) hCgmax_nonneg) hC₀pos.le)
  · intro ξ hξ F y
    have hterm : ∀ x ∈ F,
        |inner ℝ (ξ x) (centralDiff b (x - y))| ≤
          Λ' * (Real.sqrt d * Cgmax) * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by
      intro x _
      have hnorm := norm_centralDiff_le_of_step hCgmax_nonneg hCg_le hgrad (x - y)
      calc |inner ℝ (ξ x) (centralDiff b (x - y))|
          ≤ ‖ξ x‖ * ‖centralDiff b (x - y)‖ := abs_real_inner_le_norm _ _
        _ ≤ Λ' * (Real.sqrt d * (Cgmax * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)))) :=
            mul_le_mul ((hξ x).trans (le_max_left _ _)) hnorm (norm_nonneg _) hΛ'0
        _ = Λ' * (Real.sqrt d * Cgmax) * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by ring
    calc |∑ x ∈ F, inner ℝ (ξ x) (centralDiff b (x - y))|
        ≤ ∑ x ∈ F, |inner ℝ (ξ x) (centralDiff b (x - y))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ F, Λ' * (Real.sqrt d * Cgmax) * (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = Λ' * (Real.sqrt d * Cgmax) * ∑ x ∈ F, (1 + euclidNorm (x - y)) ^ (1 - (d : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ Λ' * (Real.sqrt d * Cgmax) * (C₀ * (F.card : ℝ) ^ ((1 : ℝ) / d)) :=
          mul_le_mul_of_nonneg_left (hC₀ F y)
            (mul_nonneg hΛ'0 (mul_nonneg (Real.sqrt_nonneg d) hCgmax_nonneg))
      _ = Λ' * (Real.sqrt d * Cgmax * C₀) * (F.card : ℝ) ^ ((1 : ℝ) / d) := by ring

end SourcePacking

section Assembly

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.Drift
open CERW.Support.Occupation CERW.Support.LocalTime

/-- A logarithm of a positive number at most `4n + 2` is at most `2 log (n + 2)`. -/
private lemma log_le_two_mul_log {a : ℝ} (n : ℕ) (ha : 0 < a) (h : a ≤ 4 * (n : ℝ) + 2) :
    Real.log a ≤ 2 * Real.log ((n : ℝ) + 2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hle : a ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
  have := Real.log_le_log ha hle
  rwa [Real.log_pow, Nat.cast_ofNat] at this

/-- The Euclidean norm of a difference of sites is at most the sum of the norms. -/
private lemma euclidNorm_sub_le_add {d : ℕ} (x y : Site d) :
    euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := by
  have h := CERW.Support.Occupation.euclidNorm_add_le x (-y)
  rwa [← sub_eq_add_neg, CERW.Generic.Lattice.euclidNorm_neg] at h

/-- The error scale `e_n(m) = B √m + L` with `B = L` for `d = 2` and `B = √L` for `d ≥ 3`. -/
private lemma error_scale_eq {m L : ℝ} (d : ℕ) (hm : 0 ≤ m) :
    (if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L) =
      (if d = 2 then L else Real.sqrt L) * Real.sqrt m + L := by
  by_cases hd : d = 2
  · simp only [hd, if_true]
    ring
  · simp only [hd, if_false]
    rw [Real.sqrt_mul hm]
    ring

/-- The scale `B` of the error, and the scale `λ_n = B²` that dominates `L`. -/
private lemma error_scale_facts {L : ℝ} (d : ℕ) (hL : 1 ≤ L) :
    0 ≤ (if d = 2 then L else Real.sqrt L) ∧
      (if d = 2 then L else Real.sqrt L) ^ 2 = (if d = 2 then L ^ 2 else L) ∧
      L ≤ (if d = 2 then L ^ 2 else L) := by
  split_ifs with hd
  · exact ⟨by linarith, rfl, by nlinarith⟩
  · exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt (by linarith), le_rfl⟩

/-- Some site visited during `[s, t)` attains the interval maximum. -/
private lemma exists_visited_eq_intervalMax {d : ℕ} (x : ℕ → Site d) {s t : ℕ} (hst : s < t) :
    ∃ j, s ≤ j ∧ j < t ∧ intervalLocalTime x s t (x j) = intervalMax x s t := by
  have hne : ((Finset.Ico s t).image x).Nonempty := (Finset.nonempty_Ico.mpr hst).image x
  obtain ⟨y, hy, hsup⟩ := Finset.exists_mem_eq_sup _ hne (intervalLocalTime x s t)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨j, (Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2, hsup.symm⟩

/-- The pathwise bound of `eq:interval` on one interval: the interval Dynkin decomposition, the
packing bound on the fresh sites and the martingale bound give `M ≤ a + B' √M`, which
Young's inequality absorbs. -/
private lemma interval_bound_drift {d : ℕ} {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) {CP Cb CI Bn lam ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ0 : ξ 0 = 0)
    (hCP0 : 0 ≤ CP) (hCb0 : 0 ≤ Cb) (hCI0 : 0 ≤ CI) (hε : 0 ≤ ε) (hBn : 0 ≤ Bn)
    (hBsq : Bn ^ 2 = lam)
    (hCP : ∀ (F : Finset (Site d)) (y : Site d),
      |∑ x ∈ F, inner ℝ (ξ x) (centralDiff b (x - y))| ≤
        CP * (F.card : ℝ) ^ ((1 : ℝ) / d))
    (hCb : ∀ x : Site d, |b x| ≤ Cb * Real.log (euclidNorm x + 2))
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0)
    (hnorm : ∀ j : ℕ, euclidNorm (X j ω) ≤ j) {n : ℕ} (hn : 2 ≤ n)
    (hLlam : Real.log ((n : ℝ) + 2) ≤ lam)
    (hmart : ∀ (s t : ℕ) (y : Site d), s < t → t ≤ n → euclidNorm y ≤ 3 * n →
      |driftDynkin ε ξ (fun z => b (z - y)) X t ω - driftDynkin ε ξ (fun z => b (z - y)) X s ω| ≤
        CI * (Bn * Real.sqrt (intervalMax (fun j => X j ω) s t) + Real.log ((n : ℝ) + 2)))
    (s t : ℕ) (hst : s < t) (htn : t ≤ n) :
    (intervalMax (fun j => X j ω) s t : ℝ) ≤
      (2 * CP + 1) * ε * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) +
        (8 * Cb + 2 * CI + CI ^ 2) * lam := by
  obtain ⟨j, -, hjt, hjmax⟩ := exists_visited_eq_intervalMax (fun j => X j ω) hst
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htR : (t : ℝ) ≤ n := by exact_mod_cast htn
  have hsR : (s : ℝ) ≤ n := by exact_mod_cast (hst.le.trans htn)
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast (hjt.le.trans htn)
  have hL1 := one_le_log_add_two hn
  have hyn : euclidNorm (X j ω) ≤ n := (hnorm j).trans hjR
  have hdyn := intervalLocalTime_eq_driftDynkin hb ε hξ0 X ω h0 hst.le (X j ω)
  have hM : (intervalLocalTime (fun j => X j ω) s t (X j ω) : ℝ) =
      (intervalMax (fun j => X j ω) s t : ℝ) := by exact_mod_cast hjmax
  have hb1 : |b (X t ω - X j ω)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    refine log_le_two_mul_log n (by linarith [euclidNorm_nonneg (X t ω - X j ω)]) ?_
    linarith [euclidNorm_sub_le_add (X t ω) (X j ω), hnorm t]
  have hb2 : |b (X s ω - X j ω)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    refine log_le_two_mul_log n (by linarith [euclidNorm_nonneg (X s ω - X j ω)]) ?_
    linarith [euclidNorm_sub_le_add (X s ω) (X j ω), hnorm s]
  have hsum := hCP (departureRange (fun j => X j ω) t \ departureRange (fun j => X j ω) s)
    (X j ω)
  rw [card_departureRange_sdiff _ hst.le] at hsum
  have hk0 : 0 ≤ (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  generalize (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) = k at hsum hk0 ⊢
  have hmt := hmart s t (X j ω) hst htn (by linarith)
  have hεS := mul_le_mul_of_nonneg_left hsum hε
  have hεS' := mul_le_mul_of_nonneg_left (le_abs_self
    (∑ z ∈ departureRange (fun j => X j ω) t \ departureRange (fun j => X j ω) s,
      inner ℝ (ξ z) (centralDiff b (z - X j ω)))) hε
  rw [hM] at hdyn
  have key : (intervalMax (fun j => X j ω) s t : ℝ) ≤
      Cb * (2 * Real.log ((n : ℝ) + 2)) + Cb * (2 * Real.log ((n : ℝ) + 2)) +
        ε * (CP * k) +
        CI * (Bn * Real.sqrt (intervalMax (fun j => X j ω) s t) +
          Real.log ((n : ℝ) + 2)) := by
    linarith [le_abs_self (b (X t ω - X j ω)), neg_le_abs (b (X s ω - X j ω)),
      neg_le_abs (driftDynkin ε ξ (fun z => b (z - X j ω)) X t ω -
        driftDynkin ε ξ (fun z => b (z - X j ω)) X s ω)]
  have ha0 : 0 ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) + Cb * (2 * Real.log ((n : ℝ) + 2)) +
      ε * (CP * k) +
        CI * Real.log ((n : ℝ) + 2) := by positivity
  have hyoung := CERW.Generic.Young.le_two_mul_add_sq_of_le_add_mul_sqrt (Nat.cast_nonneg _)
    ha0 (mul_nonneg hCI0 hBn) (by linarith [key])
  have hBs : (CI * Bn) ^ 2 = CI ^ 2 * lam := by rw [mul_pow, hBsq]
  nlinarith [mul_le_mul_of_nonneg_left hLlam hCb0, mul_le_mul_of_nonneg_left hLlam hCI0,
    mul_nonneg hε hk0]

/-- Combining the five error terms of the approximate local-time bound: if each term is bounded by
its error scale, then their sum is bounded by the summed scale. -/
private lemma approx_error_combination {Cb CS CM CI Bn ε m logn A B C D E : ℝ}
    (hCb0 : 0 ≤ Cb) (hCS0 : 0 ≤ CS) (hCM0 : 0 ≤ CM)
    (hε : 0 ≤ ε) (hBn : 0 ≤ Bn)
    (hA : |A| ≤ Cb * (2 * logn)) (hB : |B| ≤ Cb * (2 * logn))
    (hC : |C| ≤ CS * ε * (2 * logn)) (hD : |D| ≤ CM * ε * (2 * logn))
    (hE : |E| ≤ CI * (Bn * Real.sqrt m + logn)) :
    |A + B + C + D + E| ≤
      (4 * Cb + 2 * CS * ε + 2 * CM * ε + CI) * (Bn * Real.sqrt m + logn) := by
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  have hC' := abs_le.mp hC
  have hD' := abs_le.mp hD
  have hE' := abs_le.mp hE
  have hK0 : 0 ≤ 4 * Cb + 2 * CS * ε + 2 * CM * ε := by
    have h1 := mul_nonneg hCS0 hε
    have h2 := mul_nonneg hCM0 hε
    linarith
  have hterm : 0 ≤ (4 * Cb + 2 * CS * ε + 2 * CM * ε) * Bn * Real.sqrt m :=
    mul_nonneg (mul_nonneg hK0 hBn) (Real.sqrt_nonneg m)
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> nlinarith [hterm]

/-- The pathwise bound of `eq:approx` at a real point `y`, `|y| ≤ 2n`: at the site `z` of the cell
of `y`, the Dynkin decomposition of `ℓ_n(z)`, the source-sum comparison, the cell modulus and the
martingale bound. -/
private lemma approx_bound_drift {d : ℕ} (hd : 2 ≤ d) {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) {Cb CS CM CI Bn ε : ℝ}
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ0 : ξ 0 = 0)
    (hCb0 : 0 ≤ Cb) (hCS0 : 0 ≤ CS) (hCM0 : 0 ≤ CM) (hCI0 : 0 ≤ CI) (hε : 0 ≤ ε)
    (hBn : 0 ≤ Bn)
    (hCb : ∀ x : Site d, |b x| ≤ Cb * Real.log (euclidNorm x + 2))
    (hCS : ∀ (u : ℕ → Site d) (m : ℕ) (w : Site d) (R' : ℝ), 1 ≤ R' →
      (∀ x ∈ departureRange u m, euclidNorm (x - w) ≤ R') →
        |ε * ∑ x ∈ departureRange u m, inner ℝ (ξ x) (centralDiff b (x - w)) -
            normPotential d ε Ψ (cellSet u m) (toSpace w)| ≤ CS * ε * Real.log (R' + 2))
    (hCM : ∀ R : ℝ, 1 ≤ R → ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
      D ⊆ Metric.ball 0 R → ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R →
        ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε Ψ D y - normPotential d ε Ψ D z| ≤ CM * ε * Real.log (R + 2))
    {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0)
    (hnorm : ∀ j : ℕ, euclidNorm (X j ω) ≤ j) {n : ℕ} (hn : 2 ≤ n) (hsq : Real.sqrt d ≤ n)
    (hmart : ∀ (s t : ℕ) (y : Site d), s < t → t ≤ n → euclidNorm y ≤ 3 * n →
      |driftDynkin ε ξ (fun z => b (z - y)) X t ω - driftDynkin ε ξ (fun z => b (z - y)) X s ω| ≤
        CI * (Bn * Real.sqrt (intervalMax (fun j => X j ω) s t) + Real.log ((n : ℝ) + 2)))
    (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 2 * n) :
    |cellLocalTime (fun j => X j ω) n y - normPotential d ε Ψ (cellSet (fun j => X j ω) n) y| ≤
      (4 * Cb + 2 * CS * ε + 2 * CM * ε + CI) *
        (Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 := one_le_log_add_two hn
  have hyz : ‖y - toSpace (cellCenter y)‖ ≤ Real.sqrt d / 2 :=
    CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter y)
  have hznorm : euclidNorm (cellCenter y) ≤ 3 * n := by
    have h := norm_le_norm_add_norm_sub' (toSpace (cellCenter y)) y
    rw [norm_toSpace, norm_sub_rev] at h
    linarith
  have hH : CERW.maxRadius (fun j => X j ω) n ≤ n := by
    apply Finset.sup'_le
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact (hnorm j).trans (by exact_mod_cast hjn)
  have hcellSet : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball (by omega) (fun j => X j ω) n).trans
      (Metric.ball_subset_ball (by linarith))
  have hdyn := ContactDynkin.localTime_eq_driftDynkin hb ε ξ hξ0 X ω h0 n (cellCenter y)
  have hb1 : |b (X n ω - cellCenter y)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    refine log_le_two_mul_log n (by linarith [euclidNorm_nonneg (X n ω - cellCenter y)]) ?_
    linarith [euclidNorm_sub_le_add (X n ω) (cellCenter y), hnorm n]
  have hb2 : |b (-cellCenter y)| ≤ Cb * (2 * Real.log ((n : ℝ) + 2)) := by
    refine (hCb _).trans (mul_le_mul_of_nonneg_left ?_ hCb0)
    rw [CERW.Generic.Lattice.euclidNorm_neg]
    exact log_le_two_mul_log n (by linarith [euclidNorm_nonneg (cellCenter y)]) (by linarith)
  have hsrc := hCS (fun j => X j ω) n (cellCenter y) (4 * n) (by linarith) (by
    intro w hw
    rw [departureRange] at hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
    linarith [euclidNorm_sub_le_add (X j ω) (cellCenter y), hnorm j])
  have hmod := hCM ((n : ℝ) + Real.sqrt d) (by linarith [Real.sqrt_nonneg (d : ℝ)])
    (cellSet (fun j => X j ω) n) (CERW.Support.Occupation.measurableSet_cellSet _ _) hcellSet
    y (toSpace (cellCenter y)) (by linarith [Real.sqrt_nonneg (d : ℝ)])
    (by linarith [Real.sqrt_nonneg (d : ℝ)])
  have hmt := hmart 0 n (cellCenter y) (by omega) le_rfl hznorm
  rw [driftDynkin_zero, sub_zero] at hmt
  have hmono : Real.sqrt (intervalMax (fun j => X j ω) 0 n) ≤
      Real.sqrt (maxLocalTime (fun j => X j ω) n) :=
    Real.sqrt_le_sqrt (Nat.cast_le.mpr
      (CERW.Support.Occupation.intervalMax_le_maxLocalTime _ le_rfl))
  have hmt' : |driftDynkin ε ξ (fun z => b (z - cellCenter y)) X n ω| ≤
      CI * (Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2)) :=
    hmt.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hmono hBn) le_rfl) hCI0)
  have hlog1 : Real.log (4 * (n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) :=
    log_le_two_mul_log n (by linarith) le_rfl
  have hlog2 : Real.log ((n : ℝ) + Real.sqrt d + 2) ≤ 2 * Real.log ((n : ℝ) + 2) :=
    log_le_two_mul_log n (by linarith [Real.sqrt_nonneg (d : ℝ)]) (by linarith)
  have hsrc' : |ε * ∑ x ∈ departureRange (fun j => X j ω) n,
      inner ℝ (ξ x) (centralDiff b (x - cellCenter y)) -
        normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace (cellCenter y))| ≤
      CS * ε * (2 * Real.log ((n : ℝ) + 2)) :=
    hsrc.trans (mul_le_mul_of_nonneg_left hlog1 (mul_nonneg hCS0 hε))
  have hmod' : |normPotential d ε Ψ (cellSet (fun j => X j ω) n) y -
      normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace (cellCenter y))| ≤
      CM * ε * (2 * Real.log ((n : ℝ) + 2)) :=
    hmod.trans (mul_le_mul_of_nonneg_left hlog2 (mul_nonneg hCM0 hε))
  have hE : Real.log ((n : ℝ) + 2) ≤
      Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2) := by
    linarith [mul_nonneg hBn (Real.sqrt_nonneg (maxLocalTime (fun j => X j ω) n : ℝ))]
  have hlead : (4 * Cb + 2 * CS * ε + 2 * CM * ε) * Real.log ((n : ℝ) + 2) ≤
      (4 * Cb + 2 * CS * ε + 2 * CM * ε) *
        (Bn * Real.sqrt (maxLocalTime (fun j => X j ω) n) + Real.log ((n : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have hcell : cellLocalTime (fun j => X j ω) n y =
      (localTime (fun j => X j ω) n (cellCenter y) : ℝ) := rfl
  rw [hcell, hdyn]
  have hdecomp : b (X n ω - cellCenter y) - b (-cellCenter y) +
      ε * (∑ z ∈ departureRange (fun j => X j ω) n,
        inner ℝ (ξ z) (centralDiff b (z - cellCenter y))) -
        driftDynkin ε ξ (fun z => b (z - cellCenter y)) X n ω -
        normPotential d ε Ψ (cellSet (fun j => X j ω) n) y =
      b (X n ω - cellCenter y) + (-b (-cellCenter y)) +
        (ε * (∑ z ∈ departureRange (fun j => X j ω) n,
          inner ℝ (ξ z) (centralDiff b (z - cellCenter y))) -
          normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace (cellCenter y))) +
        (normPotential d ε Ψ (cellSet (fun j => X j ω) n) (toSpace (cellCenter y)) -
          normPotential d ε Ψ (cellSet (fun j => X j ω) n) y) +
        (-driftDynkin ε ξ (fun z => b (z - cellCenter y)) X n ω) := by ring
  rw [hdecomp]
  exact approx_error_combination hCb0 hCS0 hCM0 hε hBn hb1
    (by rwa [abs_neg]) hsrc' (by rwa [abs_sub_comm]) (by rwa [abs_neg])

/-- For `n ≥ 2`: `0 < log n` and `log (n + 2) ≤ 2 log n`. -/
private lemma log_add_two_le_two_mul_log {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.log n ∧ Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨Real.log_pos (by linarith), ?_⟩
  have h1 := Real.log_le_log (by linarith : (0 : ℝ) < n + 2)
    (by nlinarith : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2)
  rwa [Real.log_pow, Nat.cast_ofNat] at h1

/-- The scale `λ_n` of `eq:interval` is at most `4 (log n)²`. -/
private lemma lam_le_four_mul_log_sq {d : ℕ} {L ℓ : ℝ} (hL1 : 1 ≤ L) (hLℓ : L ≤ 2 * ℓ) :
    (if d = 2 then L ^ 2 else L) ≤ 4 * ℓ ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have h1 : L ^ 2 ≤ (2 * ℓ) ^ 2 := pow_le_pow_left₀ hL0 hLℓ 2
  have h2 : L ≤ L ^ 2 := by nlinarith
  have h3 : (2 * ℓ) ^ 2 = 4 * ℓ ^ 2 := by ring
  split_ifs
  · exact h1.trans h3.le
  · exact h2.trans (h1.trans h3.le)

/-- The error scale `e_n(M)` is at most twice the `log n` form of the statement. -/
private lemma error_scale_le_log {d : ℕ} {M L ℓ C₂ C : ℝ} (hM0 : 0 ≤ M) (hℓ0 : 0 < ℓ)
    (hL1 : 1 ≤ L) (hLℓ : L ≤ 2 * ℓ) (hC₂0 : 0 ≤ C₂) (hC : 2 * C₂ ≤ C) :
    C₂ * ((if d = 2 then L else Real.sqrt L) * Real.sqrt M + L) ≤
      C * ℓ + C * (if d = 2 then Real.sqrt M * ℓ else Real.sqrt (M * ℓ)) := by
  have hL0 : 0 ≤ L := by linarith
  have hsM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  by_cases hd2 : d = 2
  · simp only [hd2, if_true]
    have h1 : L * Real.sqrt M ≤ 2 * ℓ * Real.sqrt M := mul_le_mul_of_nonneg_right hLℓ hsM
    have h2 : L * Real.sqrt M + L ≤ 2 * (ℓ + Real.sqrt M * ℓ) := by linarith
    have h3 : 0 ≤ ℓ + Real.sqrt M * ℓ := by positivity
    calc C₂ * (L * Real.sqrt M + L) ≤ C₂ * (2 * (ℓ + Real.sqrt M * ℓ)) :=
          mul_le_mul_of_nonneg_left h2 hC₂0
      _ = (2 * C₂) * (ℓ + Real.sqrt M * ℓ) := by ring
      _ ≤ C * (ℓ + Real.sqrt M * ℓ) := mul_le_mul_of_nonneg_right hC h3
      _ = C * ℓ + C * (Real.sqrt M * ℓ) := by ring
  · simp only [hd2, if_false]
    have hMℓ : 0 ≤ M * ℓ := mul_nonneg hM0 hℓ0.le
    have h4 : Real.sqrt (4 * (M * ℓ)) = 2 * Real.sqrt (M * ℓ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrt : Real.sqrt L * Real.sqrt M ≤ 2 * Real.sqrt (M * ℓ) := by
      rw [← Real.sqrt_mul hL0, ← h4]
      refine Real.sqrt_le_sqrt ?_
      have h5 : L * M ≤ 2 * ℓ * M := mul_le_mul_of_nonneg_right hLℓ hM0
      linarith
    have h2 : Real.sqrt L * Real.sqrt M + L ≤ 2 * (ℓ + Real.sqrt (M * ℓ)) := by linarith
    have h3 : 0 ≤ ℓ + Real.sqrt (M * ℓ) := by positivity
    calc C₂ * (Real.sqrt L * Real.sqrt M + L) ≤ C₂ * (2 * (ℓ + Real.sqrt (M * ℓ))) :=
          mul_le_mul_of_nonneg_left h2 hC₂0
      _ = (2 * C₂) * (ℓ + Real.sqrt (M * ℓ)) := by ring
      _ ≤ C * (ℓ + Real.sqrt (M * ℓ)) := mul_le_mul_of_nonneg_right hC h3
      _ = C * ℓ + C * Real.sqrt (M * ℓ) := by ring

/-- **Lemma `lem:local` for the walk driven by the gauge of a convex body.** Let `K` be a compact
convex set with the origin in its interior and `ψ_K = gauge K` its Minkowski functional, not
necessarily even. For `ε > 0` with `ε max {ψ_K(e_i), ψ_K(-e_i)} < 1/d`, every `p > 0` and every
choice of subgradients `ξ(x) ∈ ∂ψ_K(x)` with `ξ(0) = 0`, there is `C` such that for the walk
`IsDriftCERW μ ε ξ X` the largest local time, the interval maxima and the approximation of the
cell local time by the potential `U_{D_n}` of the cell set hold simultaneously with probability at
least `1 - C n^{-p}`, for every `n ≥ 2`. -/
theorem gauge_local_time_potential {d : ℕ} (hd : 2 ≤ d) :
    ∀ {K : Set (EuclideanSpace ℝ (Fin d))}, IsCompact K → Convex ℝ K →
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K →
    ∀ ε : ℝ, 0 < ε →
    (∀ i : Fin d, ε * gauge K (CERW.coordVec i) < 1 / (d : ℝ) ∧
      ε * gauge K (-CERW.coordVec i) < 1 / (d : ℝ)) →
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient (gauge K) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ((CERW.maxLocalTime (X · ω) n : ℝ)
                    ≤ C * ((CERW.departureRange (X · ω) n).card : ℝ) ^ ((1 : ℝ) / d)
                      + C * Real.log n ^ 2 ∧
                  (∀ s t : ℕ, s < t → t ≤ n →
                    (CERW.intervalMax (X · ω) s t : ℝ)
                      ≤ C * (CERW.freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / d)
                        + C * Real.log n ^ 2) ∧
                  ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
                    |CERW.cellLocalTime (X · ω) n y
                        - CERW.normPotential d ε (gauge K) (CERW.cellSet (X · ω) n) y|
                      ≤ C * Real.log n + C *
                        (if d = 2 then Real.sqrt (CERW.maxLocalTime (X · ω) n) * Real.log n
                          else Real.sqrt (CERW.maxLocalTime (X · ω) n * Real.log n)))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro K hK hc h0 ε hε hell p hp
  have hd1 : 1 ≤ d := by omega
  obtain ⟨b, h, hKF⟩ := exists_kernelFacts hd
  obtain ⟨R, Ca, hR, hgradA⟩ := hKF.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hKF.gradBound
  obtain ⟨Cb, hCb⟩ := hKF.growth
  obtain ⟨CP, hCP0, hCP⟩ :=
    exists_abs_sum_inner_drift_centralDiff_le hd hgrad (normMax (gauge K))
  obtain ⟨CS, hCS0, hCS⟩ :=
    gauge_abs_source_sum_sub_normPotential_le hd hR hgradA hgrad hK hc h0
  obtain ⟨CM, hCM0, hCM⟩ := gauge_normPotential_cell_modulus hd hK hc h0
  have hCb' : ∀ x : Site d, |b x| ≤ |Cb| * Real.log (euclidNorm x + 2) := fun x =>
    (hCb x).trans (mul_le_mul_of_nonneg_right (le_abs_self Cb)
      (Real.log_nonneg (by linarith [euclidNorm_nonneg x])))
  obtain ⟨CI, hCI0, hCI⟩ := exists_interval_mart_drift.{u} hd hε.le hgrad hp
  set n₀ : ℕ := ⌈Real.sqrt d⌉₊ + 2 with hn₀
  set C₁ : ℝ := 8 * |Cb| + 2 * CI + CI ^ 2 with hC₁
  set C₂ : ℝ := 4 * |Cb| + 2 * CS * ε + 2 * CM * ε + CI with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hnp : 0 ≤ (n₀ : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set Cint : ℝ := (2 * CP + 1) * ε with hCint
  have hCint0 : 0 ≤ Cint := by positivity
  refine ⟨Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hξ' : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) :=
    drift_coord_bound_gauge hε.le hell hξ hξ0
  have hξΛ : ∀ x, ‖ξ x‖ ≤ normMax (gauge K) := norm_selection_le hK h0 hξ hξ0
  by_cases hn₀le : n₀ ≤ n
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hL1 := one_le_log_add_two hn
    obtain ⟨hBn, hBsq, hLlam⟩ := error_scale_facts d hL1
    have hlam0 : 0 ≤ (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) :=
      by linarith
    have hsq : Real.sqrt d ≤ n := by
      have h1 := Nat.le_ceil (Real.sqrt d)
      have h2 : ((⌈Real.sqrt d⌉₊ : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (by omega : ⌈Real.sqrt d⌉₊ ≤ n)
      linarith
    -- the logarithms
    obtain ⟨hℓ0, hLℓ⟩ := log_add_two_le_two_mul_log hn
    have hlamℓ : (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) ≤
        4 * Real.log n ^ 2 := lam_le_four_mul_log_sq hL1 hLℓ
    have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j : ℕ, euclidNorm (X j ω) ≤ j)} = 0 := by
      refine ae_iff.mp ?_
      filter_upwards [ae_iff.mpr hX.start, ae_euclidNorm_le_drift hd1 hε.le hξ' hX] with ω h0 h1
      exact ⟨h0, h1⟩
    refine measure_le_of_subset_union (fun ω hω => ?_) (hCI hξ' hX n hn) hnull
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hA', hN'⟩ := hcon
    simp only [Set.mem_setOf_eq, not_not] at hN'
    obtain ⟨h0, hnorm⟩ := hN'
    simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hA'
    have hmart : ∀ (s t : ℕ) (y : Site d), s < t → t ≤ n → euclidNorm y ≤ 3 * n →
        |driftDynkin ε ξ (fun z => b (z - y)) X t ω - driftDynkin ε ξ (fun z => b (z - y)) X s ω| ≤
          CI * ((if d = 2 then Real.log ((n : ℝ) + 2) else Real.sqrt (Real.log ((n : ℝ) + 2))) *
            Real.sqrt (intervalMax (fun j => X j ω) s t) + Real.log ((n : ℝ) + 2)) := by
      intro s t y hst htn hy
      rw [← error_scale_eq d (Nat.cast_nonneg _)]
      exact hA' s t y hst htn hy
    have hint : ∀ s t : ℕ, s < t → t ≤ n → (intervalMax (fun j => X j ω) s t : ℝ) ≤
        Cint * (freshCount (fun j => X j ω) s t : ℝ) ^ ((1 : ℝ) / d) +
          C₁ * (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) :=
      fun s t hst htn => interval_bound_drift hKF.poisson hξ0 hCP0 (abs_nonneg Cb) hCI0.le hε.le
        hBn hBsq (hCP ξ hξΛ) hCb' X ω h0 hnorm hn hLlam hmart s t hst htn
    have hC₁le : C₁ * (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2)) ≤
        (Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p) * Real.log n ^ 2 := by
      calc C₁ * (if d = 2 then Real.log ((n : ℝ) + 2) ^ 2 else Real.log ((n : ℝ) + 2))
          ≤ C₁ * (4 * Real.log n ^ 2) := mul_le_mul_of_nonneg_left hlamℓ hC₁0
        _ = (4 * C₁) * Real.log n ^ 2 := by ring
        _ ≤ (Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p) * Real.log n ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hCint_le : Cint ≤ Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p := by linarith
    refine hω ⟨?_, fun s t hst htn => ?_, fun y hy => ?_⟩
    · have h1 : maxLocalTime (fun j => X j ω) n ≤ intervalMax (fun j => X j ω) 0 n :=
        Finset.sup_le fun z _ => by
          rw [← CERW.Support.Occupation.intervalLocalTime_zero]
          exact intervalLocalTime_le_intervalMax _ 0 n z
      have h2 := hint 0 n (by omega) le_rfl
      rw [CERW.Support.Occupation.freshCount_zero] at h2
      refine (Nat.cast_le.mpr h1).trans (h2.trans (add_le_add ?_ hC₁le))
      exact mul_le_mul_of_nonneg_right hCint_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · refine (hint s t hst htn).trans (add_le_add ?_ hC₁le)
      exact mul_le_mul_of_nonneg_right hCint_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · have hM0 : (0 : ℝ) ≤ maxLocalTime (fun j => X j ω) n := Nat.cast_nonneg _
      have h := approx_bound_drift hd hKF.poisson hξ0 (abs_nonneg Cb) hCS0 hCM0 hCI0.le hε.le hBn
        hCb'
        (fun u m w R' hR' hu => hCS ε hε.le ξ hξ hξ0 u m w R' hR' hu)
        (fun R hR D hD hDsub y z hy hyz => hCM ε hε.le R hR D hD hDsub y z hy hyz)
        X ω h0 hnorm hn hsq hmart y hy
      refine h.trans ?_
      have hC₂' : 4 * |Cb| + 2 * CS * ε + 2 * CM * ε + CI = C₂ := rfl
      rw [hC₂']
      have hC₂le : 2 * C₂ ≤ Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p := by linarith
      have := error_scale_le_log (d := d) (M := (maxLocalTime (fun j => X j ω) n : ℝ))
        (L := Real.log ((n : ℝ) + 2)) (ℓ := Real.log n) hM0 hℓ0 hL1 hLℓ hC₂0 hC₂le
      exact this
  · exact (prob_le_one).trans (ENNReal.one_le_ofReal.mpr
      (one_le_mul_rpow_neg hp (by omega) (not_le.mp hn₀le).le (by
        have : (n₀ : ℝ) ^ p ≤ Cint + 4 * C₁ + 2 * C₂ + CI + (n₀ : ℝ) ^ p := by linarith
        exact this)))


end Assembly

/-! ### Consumption at bodies that are not symmetric -/

section Consumption

open CERW.Support.Norm.GaugePotential (cornerTriangle isCompact_cornerTriangle
  convex_cornerTriangle zero_mem_interior_cornerTriangle gauge_cornerTriangle_eq)

/-- The discretization of the potential at an arbitrary compact convex body, for all `ε ≥ 0`, all
subgradient selections and all lattice paths: the source sum
`ε Σ_{x ∈ A_n} ξ(x) · Db(x - y)` of the Dynkin formula for the lattice kernel `b` differs from the
potential `U_{D_n}(y)` of the cell set by at most `C ε log(R' + 2)`. -/
theorem gauge_source_sum_discretization {d : ℕ} (hd : 2 ≤ d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ b : Site d → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient (gauge K) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ) (y : Site d) (R' : ℝ), 1 ≤ R' →
        (∀ x ∈ CERW.departureRange X n, euclidNorm (x - y) ≤ R') →
          |ε * ∑ x ∈ CERW.departureRange X n,
                inner ℝ (ξ x) (CERW.Support.Law.centralDiff b (x - y)) -
              CERW.normPotential d ε (gauge K) (CERW.cellSet X n) (CERW.toSpace y)| ≤
            C * ε * Real.log (R' + 2) := by
  obtain ⟨b, h, hKf⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  obtain ⟨R, Ca, hR, hgradA⟩ := hKf.gradAsymp
  obtain ⟨Cg, hgrad⟩ := hKf.gradBound
  obtain ⟨C, hC0, hC⟩ := gauge_abs_source_sum_sub_normPotential_le hd hR hgradA hgrad hK hc h0
  exact ⟨b, C, hC0, fun ε hε ξ hξ hξ0 X n y R' hR' hcellR =>
    hC ε hε ξ hξ hξ0 X n y R' hR' hcellR⟩

/-- **Consumption of the local-time estimate at the non-even planar body `cutDisc`, `ε = 1/4`.**
A subgradient selection and an actual walk `IsDriftCERW μ (1/4) ξ X` exist, and for this selection
every walk of this law satisfies, for every `p > 0` and `n ≥ 2`, the local-time and potential
estimates of `lem:local` with probability at least `1 - C n^{-p}`, the potential being that of the
gradient of the gauge of `cutDisc`, which is not a norm. -/
theorem cutDisc_local_time_potential {p : ℝ} (hp : 0 < p) :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        CERW.IsSubgradient (gauge cutDisc) (CERW.toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ ((CERW.maxLocalTime (X · ω) n : ℝ)
                      ≤ C * ((CERW.departureRange (X · ω) n).card : ℝ) ^
                          ((1 : ℝ) / ((2 : ℕ) : ℝ))
                        + C * Real.log n ^ 2 ∧
                    (∀ s t : ℕ, s < t → t ≤ n →
                      (CERW.intervalMax (X · ω) s t : ℝ)
                        ≤ C * (CERW.freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))
                          + C * Real.log n ^ 2) ∧
                    ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ ≤ 2 * n →
                      |CERW.cellLocalTime (X · ω) n y
                          - CERW.normPotential 2 (1 / 4 : ℝ) (gauge cutDisc)
                              (CERW.cellSet (X · ω) n) y|
                        ≤ C * Real.log n + C *
                          (if (2 : ℕ) = 2 then
                            Real.sqrt (CERW.maxLocalTime (X · ω) n) * Real.log n
                            else Real.sqrt (CERW.maxLocalTime (X · ω) n * Real.log n)))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hell : ∀ i : Fin 2,
      (1 / 4 : ℝ) * gauge cutDisc (CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ) ∧
      (1 / 4 : ℝ) * gauge cutDisc (-CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ) :=
    fun i => cutDisc_ellipticity i
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cutDisc zero_mem_interior_cutDisc (by norm_num) hell
  obtain ⟨C, hC, hbound⟩ := gauge_local_time_potential (d := 2) le_rfl
    isCompact_cutDisc convex_cutDisc zero_mem_interior_cutDisc (1 / 4 : ℝ) (by norm_num) hell p hp
  exact ⟨ξ, hξ, hξ0, hwalk, C, hC, fun μ _ X hX n hn => hbound ξ hξ hξ0 μ X hX n hn⟩

/-- **Consumption of the local-time estimate at a body with corners, `ε = 1/4`.** The gauge of the
triangle `cornerTriangle` is not differentiable along the ray through the vertex `(-1,-1)` and is
not even; a subgradient selection and an actual walk `IsDriftCERW μ (1/4) ξ X` exist, and every
walk of this law satisfies the local-time and potential estimates of `lem:local` with probability
at least `1 - C n^{-p}`, for every `p > 0` and `n ≥ 2`. -/
theorem cornerTriangle_local_time_potential {p : ℝ} (hp : 0 < p) :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        CERW.IsSubgradient (gauge cornerTriangle) (CERW.toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X → ∀ n : ℕ, 2 ≤ n →
          μ {ω | ¬ ((CERW.maxLocalTime (X · ω) n : ℝ)
                      ≤ C * ((CERW.departureRange (X · ω) n).card : ℝ) ^
                          ((1 : ℝ) / ((2 : ℕ) : ℝ))
                        + C * Real.log n ^ 2 ∧
                    (∀ s t : ℕ, s < t → t ≤ n →
                      (CERW.intervalMax (X · ω) s t : ℝ)
                        ≤ C * (CERW.freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))
                          + C * Real.log n ^ 2) ∧
                    ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ ≤ 2 * n →
                      |CERW.cellLocalTime (X · ω) n y
                          - CERW.normPotential 2 (1 / 4 : ℝ) (gauge cornerTriangle)
                              (CERW.cellSet (X · ω) n) y|
                        ≤ C * Real.log n + C *
                          (if (2 : ℕ) = 2 then
                            Real.sqrt (CERW.maxLocalTime (X · ω) n) * Real.log n
                            else Real.sqrt (CERW.maxLocalTime (X · ω) n * Real.log n)))}
            ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hell : ∀ i : Fin 2,
      (1 / 4 : ℝ) * gauge cornerTriangle (CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ) ∧
      (1 / 4 : ℝ) * gauge cornerTriangle (-CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ) :=
    by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, gauge_cornerTriangle_eq]
      norm_num [CERW.coordVec]
    · simp only [Fin.mk_one, gauge_cornerTriangle_eq]
      norm_num [CERW.coordVec]
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := exists_isDriftCERW_gauge (d := 2) (by norm_num)
    convex_cornerTriangle zero_mem_interior_cornerTriangle (by norm_num) hell
  obtain ⟨C, hC, hbound⟩ := gauge_local_time_potential (d := 2) le_rfl
    isCompact_cornerTriangle convex_cornerTriangle zero_mem_interior_cornerTriangle
    (1 / 4 : ℝ) (by norm_num) hell p hp
  exact ⟨ξ, hξ, hξ0, hwalk, C, hC, fun μ _ X hX n hn => hbound ξ hξ hξ0 μ X hX n hn⟩

/-- The discretization of the potential at the non-even planar body `cutDisc`, for every `ε ≥ 0`,
every subgradient selection and every lattice path. -/
theorem cutDisc_source_sum_discretization :
    ∃ b : Site 2 → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε →
      ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 →
          CERW.IsSubgradient (gauge cutDisc) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site 2) (n : ℕ) (y : Site 2) (R' : ℝ), 1 ≤ R' →
        (∀ x ∈ CERW.departureRange X n, euclidNorm (x - y) ≤ R') →
          |ε * ∑ x ∈ CERW.departureRange X n,
                inner ℝ (ξ x) (CERW.Support.Law.centralDiff b (x - y)) -
              CERW.normPotential 2 ε (gauge cutDisc) (CERW.cellSet X n) (CERW.toSpace y)| ≤
            C * ε * Real.log (R' + 2) :=
  gauge_source_sum_discretization (d := 2) le_rfl
    isCompact_cutDisc convex_cutDisc zero_mem_interior_cutDisc

/-- The discretization of the potential at the triangle `cornerTriangle`, for every `ε ≥ 0`, every
subgradient selection and every lattice path. -/
theorem cornerTriangle_source_sum_discretization :
    ∃ b : Site 2 → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε →
      ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 →
          CERW.IsSubgradient (gauge cornerTriangle) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site 2) (n : ℕ) (y : Site 2) (R' : ℝ), 1 ≤ R' →
        (∀ x ∈ CERW.departureRange X n, euclidNorm (x - y) ≤ R') →
          |ε * ∑ x ∈ CERW.departureRange X n,
                inner ℝ (ξ x) (CERW.Support.Law.centralDiff b (x - y)) -
              CERW.normPotential 2 ε (gauge cornerTriangle) (CERW.cellSet X n) (CERW.toSpace y)| ≤
            C * ε * Real.log (R' + 2) :=
  gauge_source_sum_discretization (d := 2) le_rfl
    isCompact_cornerTriangle convex_cornerTriangle zero_mem_interior_cornerTriangle

end Consumption

end CERW.Support.Norm.GaugeLocalTime
