import CERW.Support.Drift
import CERW.Generic.Norm
import CERW.Generic.Kernel.LogRadial
import CERW.Model.NormPotential
import CERW.Support.Geometry.Bound
import CERW.Support.LocalTime.DynkinLocal
import CERW.Support.LocalTime.LocalMart
import CERW.Support.LocalTime.ReplaceCell

/-!
# The Dynkin decomposition at a site and the cell modulus for the norm walk

The facts about the walk with a drift field `ξ` and the potential of a norm that are used by both
the local time estimates and the contact bound of the norm walk:

* `ContactModulus.exists_normPotential_cell_modulus` is `eq:cellmodulus`: the potential `U_D` of a
  norm varies by at most `C ε log (R + 2)` over a cell, for `D ⊆ B(0, R)`;
* `ContactDynkin.localTime_eq_driftDynkin` is `eq:dynkin` at a site, pathwise: the local time at `y`
  is `b(X_n - y) - b(-y) + ε Σ_{x ∈ A_n} ξ(x) · Db(x - y) - 𝓜^y_n`;
* `ContactDynkin.ae_abs_driftDynkin_translate_succ_sub_le`,
  `ContactDynkin.condExp_sq_driftDynkin_translate_le` and
  `ContactDynkin.exists_clamped_translate_drift` give the increments and the conditional variances
  of the translated Dynkin martingale of the drift walk, and a clamped version with the bracket
  `Σ C_g² (1 + |X_t - y|)^{2-2d}`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.ContactModulus

open CERW CERW.Generic.Norm CERW.Generic.Kernel CERW.Support.Geometry

variable {d : ℕ}

/-- The integrand `g(v) · (v - y) |v - y|^{-d}` of the potential of the field `g`. -/
private noncomputable def fieldIntegrand (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (y v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ (g v) (v - y) / ‖v - y‖ ^ d

/-- The far-field constant `2^d + 2 d 3^{d-1}`. -/
private def farFieldConstant (d : ℕ) : ℝ := (2 : ℝ) ^ d + 2 * (d : ℝ) * 3 ^ (d - 1)

/-- The potential of a norm is the integral of the field integrand of its gradient. -/
private lemma normPotential_eq_integral (d : ℕ) (ε : ℝ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ D y
      = 2 * ε / unitBallVolume d * ∫ v in D, fieldIntegrand (gradient Ψ) y v :=
  rfl

/-- The gradient of a function on `ℝ^d` is measurable. -/
private lemma measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- For `d ≥ 1`, `Λ_Ψ ≥ 0`. -/
private lemma normMax_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d) :
    0 ≤ normMax Ψ := by
  have h1 := normMin_pos_mul_le hΨ hd
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h2 := le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  have h3 := h1.2 (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h2 h3
  linarith [h1.1]

/-- The gradient of a norm has Euclidean norm at most `Λ_Ψ` everywhere: where `Ψ` is
differentiable it is a subgradient, and elsewhere it is `0`. -/
private lemma norm_gradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
    (v : EuclideanSpace ℝ (Fin d)) : ‖gradient Ψ v‖ ≤ normMax Ψ := by
  by_cases hv : DifferentiableAt ℝ Ψ v
  · have h := (subgradient_euler hΨ (gradient_isSubgradient hΨ hv)).2 (gradient Ψ v)
    have h2 := le_normMax_mul hΨ (gradient Ψ v)
    rw [real_inner_self_eq_norm_mul_norm] at h
    have h3 : ‖gradient Ψ v‖ * ‖gradient Ψ v‖ ≤ normMax Ψ * ‖gradient Ψ v‖ := h.trans h2
    rcases eq_or_lt_of_le (norm_nonneg (gradient Ψ v)) with h0 | h0
    · rw [← h0]
      exact normMax_nonneg hΨ hd
    · exact le_of_mul_le_mul_right h3 h0
  · have h0 : gradient Ψ v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, norm_zero]
    exact normMax_nonneg hΨ hd

/-- A measurable field weighted by the Newtonian kernel has a measurable integrand. -/
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
private lemma one_le_log_add_two {R : ℝ} (hR : 1 ≤ R) : 1 ≤ Real.log (R + 2) := by
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
    add_mul_le_mul_log hδnn hAnn hlogM (one_le_log_add_two hR) (log_far_ratio_le hd1 hR)
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

/-- `eq:cellmodulus` for the potential of a norm: for `D ⊆ B(0, R)` with `R ≥ 1`, and `y, z` with
`|y| ≤ 2R` and `|y - z| ≤ √d`, `|U_D(y) - U_D(z)| ≤ C ε log(R + 2)`, with `C` depending only on
`d` and `Ψ`. -/
theorem exists_normPotential_cell_modulus {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε Ψ D y - normPotential d ε Ψ D z| ≤ C * ε * Real.log (R + 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_fieldPotential_cell_modulus hd (measurable_gradient Ψ)
    (norm_gradient_le hΨ (by omega : 1 ≤ d))
  refine ⟨C, hC0, fun ε hε R hR D hD hDsub y z hy hyz => ?_⟩
  simp only [normPotential_eq_integral]
  exact hC ε hε R hR D hD hDsub y z hy hyz

end CERW.Support.Norm.ContactModulus

namespace CERW.Support.Norm.ContactDynkin

open LatticeProb CERW CERW.Support.Law CERW.Support.Occupation CERW.Support.Drift Finset

variable {d : ℕ}

/-- The next-step mean of the translated kernel at time `j` minus its current value is the visit
indicator at `y` minus the first-departure drift of the drift field `ξ`. -/
private theorem driftNextMean_sub_self {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (y : Site d) (j : ℕ) :
    driftNextMean ε ξ (fun z => b (z - y)) x j - b (x j - y) =
      (if x j = y then 1 else 0) -
        (if x j ≠ 0 ∧ x j ∉ (range j).image x then
          ε * inner ℝ (ξ (x j)) (centralDiff b (x j - y)) else 0) := by
  rw [show driftNextMean ε ξ (fun z => b (z - y)) x j =
        walkOp (fun z => b (z - y)) (x j) -
          (if x j ≠ 0 ∧ x j ∉ (range j).image x then
            ε * inner ℝ (ξ (x j)) (centralDiff (fun z => b (z - y)) (x j)) else 0)
      from sum_driftStepProb_mul ε ξ x j (fun z => b (z - y)),
    CERW.Support.LocalTime.walkOp_comp_sub, CERW.Support.LocalTime.centralDiff_comp_sub,
    sub_right_comm, hb (x j - y)]
  simp only [sub_eq_zero]

/-- The first-departure drift sum of the path `X` over first visits equals the drift sum over its
departure range, because the drift field vanishes at the origin. -/
private theorem sum_fresh_drift (b : Site d → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (hξ0 : ξ 0 = 0) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ) (y : Site d) :
    ∑ j ∈ range n,
        (if X j ω ≠ 0 ∧ X j ω ∉ (range j).image (fun i => X i ω) then
          ε * inner ℝ (ξ (X j ω)) (centralDiff b (X j ω - y)) else 0) =
      ε * ∑ z ∈ departureRange (fun i => X i ω) n, inner ℝ (ξ z) (centralDiff b (z - y)) := by
  rw [sum_fresh_ne_zero_eq_sum_departureRange (fun i => X i ω) n
    (fun z => ε * inner ℝ (ξ z) (centralDiff b (z - y))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z = 0
  · subst z
    simp [hξ0]
  · simp [hz]

/-- `eq:dynkin` for the walk with a drift field, pathwise: if `(P - I) b = 1_{0}`, the drift field
vanishes at the origin and the path starts at the origin, then
`ℓ_n(y) = b(X_n - y) - b(-y) + ε Σ_{x ∈ A_n} ξ(x) · Db(x - y) - 𝓜^y_n`,
where `𝓜^y` is the Dynkin martingale of `b(· - y)`. -/
theorem localTime_eq_driftDynkin {b : Site d → ℝ}
    (hb : ∀ x, walkOp b x - b x = if x = 0 then 1 else 0) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (hξ0 : ξ 0 = 0) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) (h0 : X 0 ω = 0) (n : ℕ) (y : Site d) :
    (localTime (fun j => X j ω) n y : ℝ) =
      b (X n ω - y) - b (-y) +
        ε * (∑ z ∈ departureRange (fun j => X j ω) n, inner ℝ (ξ z) (centralDiff b (z - y))) -
        driftDynkin ε ξ (fun z => b (z - y)) X n ω := by
  have hstep :
      ∑ j ∈ range n,
          (driftNextMean ε ξ (fun z => b (z - y)) (fun i => X i ω) j - b (X j ω - y)) =
        (localTime (fun j => X j ω) n y : ℝ) -
          ε * ∑ z ∈ departureRange (fun j => X j ω) n,
              inner ℝ (ξ z) (centralDiff b (z - y)) := by
    simp_rw [driftNextMean_sub_self hb ε ξ (fun i => X i ω) y]
    rw [Finset.sum_sub_distrib, sum_ite_eq_localTime, sum_fresh_drift b ε ξ hξ0 X ω n y]
  simp only [driftDynkin]
  rw [h0, zero_sub, hstep]
  ring

end CERW.Support.Norm.ContactDynkin

namespace CERW.Support.Norm.ContactDynkin

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law CERW.Support.Drift
  CERW.Support.LocalTime

variable {d : ℕ}

/-- The increments of the translated Dynkin martingale of the drift walk are at most
`2 C_g (1 + |X_t - y|)^{1-d}`, almost surely. -/
theorem ae_abs_driftDynkin_translate_succ_sub_le (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (y : Site d) :
    ∀ᵐ ω ∂μ, ∀ t, |driftDynkin ε ξ (fun z => b (z - y)) X (t + 1) ω -
      driftDynkin ε ξ (fun z => b (z - y)) X t ω| ≤
        2 * (Cg * (1 + euclidNorm (X t ω - y)) ^ (1 - (d : ℝ))) := by
  filter_upwards [ae_abs_driftDynkin_succ_sub_le hd hε hξ hX (fun z => b (z - y))] with ω hω
  intro t
  exact hω t (Cg * (1 + euclidNorm (X t ω - y)) ^ (1 - (d : ℝ))) fun e he => by
    rw [add_sub_right_comm]
    exact hgrad (X t ω - y) e he

/-- The conditional variances of the translated Dynkin martingale of the drift walk are at most
`C_g² (1 + |X_t - y|)^{2-2d}`. -/
theorem condExp_sq_driftDynkin_translate_le (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (y : Site d) (t : ℕ) :
    μ[fun ω => (driftDynkin ε ξ (fun z => b (z - y)) X (t + 1) ω -
        driftDynkin ε ξ (fun z => b (z - y)) X t ω) ^ 2 | pathFiltration hX.measurable t] ≤ᵐ[μ]
      fun ω => Cg ^ 2 * (1 + euclidNorm (X t ω - y)) ^ (2 - 2 * (d : ℝ)) := by
  have hCg : 0 ≤ Cg := cg_nonneg hd hgrad
  filter_upwards [condExp_sq_driftDynkin_succ_sub_le hd hε hξ hX (fun z => b (z - y)) t] with ω hω
  refine hω.trans ?_
  set ρ : ℝ := euclidNorm (X t ω - y) with hρ
  set B : ℝ := Cg * (1 + ρ) ^ (1 - (d : ℝ)) with hBdef
  have hbase : 0 ≤ (1 + ρ : ℝ) := by
    rw [hρ]
    linarith [euclidNorm_nonneg (X t ω - y)]
  have hB : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg hCg (Real.rpow_nonneg hbase _)
  have hterm : ∀ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
        (b ((X t ω + e) - y) - b (X t ω - y)) ^ 2 ≤
      driftStepProb d ε ξ (fun j => X j ω) t e * B ^ 2 := by
    intro e he
    refine mul_le_mul_of_nonneg_left ?_ (driftStepProb_nonneg hε hξ _ t e)
    have hosc := hgrad (X t ω - y) e he
    calc (b ((X t ω + e) - y) - b (X t ω - y)) ^ 2
        = (b ((X t ω - y) + e) - b (X t ω - y)) ^ 2 := by rw [add_sub_right_comm]
      _ = |b ((X t ω - y) + e) - b (X t ω - y)| ^ 2 := (sq_abs _).symm
      _ ≤ B ^ 2 := by
          rw [hBdef]
          exact pow_le_pow_left₀ (abs_nonneg _) hosc 2
  have hsum : ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
        (b ((X t ω + e) - y) - b (X t ω - y)) ^ 2 ≤ B ^ 2 := by
    calc ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
          (b ((X t ω + e) - y) - b (X t ω - y)) ^ 2
        ≤ ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e * B ^ 2 :=
            Finset.sum_le_sum hterm
      _ = B ^ 2 := by rw [← Finset.sum_mul, sum_driftStepProb hd ε ξ _ t, one_mul]
  refine hsum.trans ?_
  have hsqrpow : ((1 + ρ) ^ (1 - (d : ℝ))) ^ 2 = (1 + ρ) ^ (2 - 2 * (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase]
    congr 1
    push_cast
    ring
  rw [hBdef, mul_pow, hsqrpow]

/-- The translated Dynkin martingale of the drift walk agrees almost surely with a martingale
whose increments are at most `2 C_g + 1` everywhere and whose conditional variances are at most
the bracket increments. -/
theorem exists_clamped_translate_drift (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (y : Site d) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2 * Cg + 1) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun ω => bracket Cg y X (j + 1) ω - bracket Cg y X j ω) ∧
      ∀ᵐ ω ∂μ, ∀ i, M i ω = driftDynkin ε ξ (fun z => b (z - y)) X i ω := by
  have hCg := cg_nonneg hd hgrad
  have hmart := martingale_driftDynkin hd hε hξ hX (fun z => b (z - y))
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |driftDynkin ε ξ (fun z => b (z - y)) X (i + 1) ω -
      driftDynkin ε ξ (fun z => b (z - y)) X i ω| ≤ 2 * Cg + 1 := fun i =>
    (ae_abs_driftDynkin_translate_succ_sub_le hd hε hξ hX hgrad y).mono fun ω hω => by
      have h1 : (1 + euclidNorm (X i ω - y)) ^ (1 - (d : ℝ)) ≤ 1 :=
        rpow_one_add_le_one (euclidNorm_nonneg _) (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      have h2 := hω i
      nlinarith
  obtain ⟨M, hM, hbd, -, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart
    (b := 2 * Cg + 1) (by linarith) hinc
  refine ⟨M, hM, hbd, fun j => ?_, hae⟩
  have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
      fun ω => (driftDynkin ε ξ (fun z => b (z - y)) X (j + 1) ω -
        driftDynkin ε ξ (fun z => b (z - y)) X j ω) ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω, hω]
  refine (condExp_congr_ae hsq).trans_le ?_
  filter_upwards [condExp_sq_driftDynkin_translate_le hd hε hξ hX hgrad y j] with ω hω
  rw [bracket_succ_sub]
  exact hω

end CERW.Support.Norm.ContactDynkin
