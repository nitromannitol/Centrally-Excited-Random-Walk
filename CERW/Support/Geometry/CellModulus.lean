import CERW.Generic.Kernel.NewtonField
import CERW.Generic.Kernel.LogRadial
import CERW.Support.Geometry.Bound

/-!
# The potential varies by `O(L)` across a cell

`eq:cellmodulus`: `|U_D(y) - U_D(z)| ≤ C ε log(R + 2)` when `D ⊆ B(0, R)`, `R ≥ 1`,
`|y| ≤ 2R` and
`|y - z| ≤ √d`. Near `z` (`|v - z| < 2√d`), each kernel has integral `O_d(1)`. Away from `z`,
`|K(v - y) - K(v - z)| ≤ C_d |v - z|^{-d}` because `|y - z| ≤ √d`, and
`∫_{2√d ≤ |v - z| < (3 + √d) R} |v - z|^{-d} = O(log(R + 2))`.
-/

namespace CERW.Support.Geometry

open MeasureTheory CERW CERW.Generic.Kernel

variable {d : ℕ}

/-- The integrand `u_v · (v - y) |v - y|^{-d}` of the potential `U_D(y)`. -/
private noncomputable def potentialIntegrand (d : ℕ) (y : EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d

/-- The far-field constant `2^d + 2 d 3^{d-1}`. -/
private def farFieldConstant (d : ℕ) : ℝ := (2 : ℝ) ^ d + 2 * (d : ℝ) * 3 ^ (d - 1)

/-- The potential is the integral of `potentialIntegrand`. -/
private lemma potential_eq_integral (d : ℕ) (ε : ℝ) (D : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y = 2 * ε / unitBallVolume d * ∫ v in D, potentialIntegrand d y v :=
  rfl

/-- The difference of the potential integrands is bounded by the difference of the Newtonian
fields. -/
private lemma abs_potentialIntegrand_sub_le (v y z : EuclideanSpace ℝ (Fin d)) :
    |potentialIntegrand d y v - potentialIntegrand d z v|
      ≤ ‖newtonField (v - y) - newtonField (v - z)‖ := by
  simp only [potentialIntegrand]
  rw [← inner_newtonField (unitDir v) (v - y),
    ← inner_newtonField (unitDir v) (v - z), ← inner_sub_right]
  calc |inner ℝ (unitDir v) (newtonField (v - y) - newtonField (v - z))|
      ≤ ‖unitDir v‖ * ‖newtonField (v - y) - newtonField (v - z)‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖newtonField (v - y) - newtonField (v - z)‖ :=
        mul_le_mul_of_nonneg_right (norm_unitDir_le v) (norm_nonneg _)
    _ = ‖newtonField (v - y) - newtonField (v - z)‖ := one_mul _

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

/-- Near-field bound: the difference of the potential integrands over `D ∩ B(z, 2√d)` is at most
`5 d ω_d √d`. -/
private lemma setIntegral_abs_potentialIntegrand_sub_le_near (hd : 2 ≤ d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y z : EuclideanSpace ℝ (Fin d))
    (hyz : ‖y - z‖ ≤ Real.sqrt d) :
    ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
        |potentialIntegrand d y v - potentialIntegrand d z v|
      ≤ 5 * (d : ℝ) * unitBallVolume d * Real.sqrt d := by
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
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
  have hg : IntegrableOn (fun v => ‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ)))
      (D ∩ Metric.ball z (2 * Real.sqrt d)) := hgy.add hgz
  have hfyD : IntegrableOn (potentialIntegrand d y) D :=
    integrableOn_potentialIntegrand hd1 hD hDfin y
  have hfzD : IntegrableOn (potentialIntegrand d z) D :=
    integrableOn_potentialIntegrand hd1 hD hDfin z
  have hfs : IntegrableOn (fun v => |potentialIntegrand d y v - potentialIntegrand d z v|)
      (D ∩ Metric.ball z (2 * Real.sqrt d)) :=
    ((hfyD.mono_set Set.inter_subset_left).sub (hfzD.mono_set Set.inter_subset_left)).abs
  calc
    ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
        |potentialIntegrand d y v - potentialIntegrand d z v|
        ≤ ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
            (‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ))) := by
          refine setIntegral_mono_on hfs hg (hD.inter measurableSet_ball) (fun v _ => ?_)
          refine (abs_potentialIntegrand_sub_le v y z).trans ?_
          calc ‖newtonField (v - y) - newtonField (v - z)‖
              ≤ ‖newtonField (v - y)‖ + ‖newtonField (v - z)‖ := norm_sub_le _ _
            _ = ‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ)) := by
                rw [norm_newtonField hd, norm_newtonField hd]
      _ = (∫ v in D ∩ Metric.ball z (2 * Real.sqrt d), ‖v - y‖ ^ (1 - (d : ℝ)))
            + ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d), ‖v - z‖ ^ (1 - (d : ℝ)) :=
          integral_add hgy hgz
      _ ≤ (∫ v in Metric.ball y (3 * Real.sqrt d), ‖v - y‖ ^ (1 - (d : ℝ)))
            + ∫ v in Metric.ball z (2 * Real.sqrt d), ‖v - z‖ ^ (1 - (d : ℝ)) := by
          refine add_le_add ?_ ?_
          · exact setIntegral_mono_set hintY
              (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg _) _))
              hsubY.eventuallyLE
          · exact setIntegral_mono_set hintZ
              (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg _) _))
              Set.inter_subset_right.eventuallyLE
      _ = 5 * (d : ℝ) * unitBallVolume d * Real.sqrt d := by
          rw [hvalY, hvalZ]
          ring

/-- Far-field bound: the difference of the potential integrands over
`D \ B(z, 2√d)` is at most `A_d √d σ_d log(((3 + √d)(R + 2))/(2√d))`. -/
private lemma setIntegral_abs_potentialIntegrand_sub_le_far (hd : 2 ≤ d) {R : ℝ} (hR : 1 ≤ R)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hDsub : D ⊆ Metric.ball 0 R)
    (y z : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 2 * R)
    (hyz : ‖y - z‖ ≤ Real.sqrt d) :
    ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
        |potentialIntegrand d y v - potentialIntegrand d z v|
      ≤ farFieldConstant d * Real.sqrt d
        * ((d : ℝ) * unitBallVolume d
          * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hA : 0 ≤ farFieldConstant d := by
    rw [farFieldConstant]; positivity
  have h2δpos : 0 < 2 * Real.sqrt d := by positivity
  have hR'pos : 0 < (3 + Real.sqrt d) * (R + 2) := by positivity
  have h2δR' : 2 * Real.sqrt d ≤ (3 + Real.sqrt d) * (R + 2) := by
    nlinarith [hR, hδpos]
  have hsubset : D \ Metric.ball z (2 * Real.sqrt d) ⊆
      Metric.ball z ((3 + Real.sqrt d) * (R + 2)) \ Metric.ball z (2 * Real.sqrt d) := by
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
  obtain ⟨hannInt, hannVal⟩ :=
    integrableOn_annulus_sub_rpow_neg_and_integral_eq (d := d) hd1 z
      (ρ := 2 * Real.sqrt d) (R := (3 + Real.sqrt d) * (R + 2)) h2δpos h2δR'
  have hbig : IntegrableOn (fun v => farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)))
      (Metric.ball z ((3 + Real.sqrt d) * (R + 2)) \ Metric.ball z (2 * Real.sqrt d)) :=
    hannInt.const_mul (farFieldConstant d * Real.sqrt d)
  have hsmall : IntegrableOn
      (fun v => farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)))
      (D \ Metric.ball z (2 * Real.sqrt d)) := hbig.mono_set hsubset
  have hfyD : IntegrableOn (potentialIntegrand d y) D :=
    integrableOn_potentialIntegrand hd1 hD hDfin y
  have hfzD : IntegrableOn (potentialIntegrand d z) D :=
    integrableOn_potentialIntegrand hd1 hD hDfin z
  have hfs : IntegrableOn (fun v => |potentialIntegrand d y v - potentialIntegrand d z v|)
      (D \ Metric.ball z (2 * Real.sqrt d)) :=
    ((hfyD.mono_set Set.sdiff_subset).sub (hfzD.mono_set Set.sdiff_subset)).abs
  have hpt : ∀ v ∈ D \ Metric.ball z (2 * Real.sqrt d),
      |potentialIntegrand d y v - potentialIntegrand d z v|
        ≤ farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) := by
    intro v hv
    have hvz : 2 * Real.sqrt d ≤ ‖v - z‖ := by
      have hnot : ¬ ‖v - z‖ < 2 * Real.sqrt d := by
        intro hlt
        exact hv.2 (by rwa [Metric.mem_ball, dist_eq_norm])
      linarith
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
    calc |potentialIntegrand d y v - potentialIntegrand d z v|
        ≤ ‖newtonField (v - y) - newtonField (v - z)‖ := abs_potentialIntegrand_sub_le v y z
      _ ≤ farFieldConstant d * ‖(v - y) - (v - z)‖ / ‖v - z‖ ^ d := hK
      _ = (farFieldConstant d * ‖(v - y) - (v - z)‖) / ‖v - z‖ ^ d := by ring
      _ ≤ (farFieldConstant d * Real.sqrt d) / ‖v - z‖ ^ d :=
          div_le_div_of_nonneg_right hnum hden.le
      _ = farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) := by
          rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, div_eq_mul_inv]
  have hfar1 : ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
        |potentialIntegrand d y v - potentialIntegrand d z v|
      ≤ ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
          farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) :=
    setIntegral_mono_on hfs hsmall (hD.diff measurableSet_ball) hpt
  have hfar2 : ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
          farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ))
      ≤ ∫ v in Metric.ball z ((3 + Real.sqrt d) * (R + 2)) \ Metric.ball z (2 * Real.sqrt d),
          farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) :=
    setIntegral_mono_set hbig (Filter.Eventually.of_forall (fun v => by positivity))
      hsubset.eventuallyLE
  have hfar3 : ∫ v in Metric.ball z ((3 + Real.sqrt d) * (R + 2))
          \ Metric.ball z (2 * Real.sqrt d),
          farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ))
      = farFieldConstant d * Real.sqrt d
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

/-- `eq:cellmodulus`: for `D ⊆ B(0, R)` with `R ≥ 1`, and `y, z` with `|y| ≤ 2R` and
`|y - z| ≤ √d`, `|U_D(y) - U_D(z)| ≤ C_d ε log(R + 2)`. -/
theorem exists_potential_cell_modulus (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |potential d ε D y - potential d ε D z| ≤ C * ε * Real.log (R + 2) := by
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hδnn : 0 ≤ Real.sqrt d := hδpos.le
  have hAnn : 0 ≤ farFieldConstant d := by
    rw [farFieldConstant]; positivity
  let C : ℝ := 2 * (d : ℝ) * Real.sqrt d
    * (5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
  refine ⟨C, ?_, ?_⟩
  · have hlog3 : 0 ≤ Real.log (3 + Real.sqrt d) := Real.log_nonneg (by linarith [hδpos])
    have h5 : 0 ≤ 5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)) := by nlinarith
    change 0 ≤ 2 * (d : ℝ) * Real.sqrt d
      * (5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hδnn) h5
  intro ε hε R hR D hD hDsub y z hy hyz
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hωne : unitBallVolume d ≠ 0 := hω.ne'
  have hDfin : volume D ≠ ⊤ := by
    have hle : volume D ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      measure_mono hDsub
    exact ne_of_lt (lt_of_le_of_lt hle measure_ball_lt_top)
  have hcoef : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hfyD : IntegrableOn (potentialIntegrand d y) D :=
    integrableOn_potentialIntegrand hd1 hD hDfin y
  have hfzD : IntegrableOn (potentialIntegrand d z) D :=
    integrableOn_potentialIntegrand hd1 hD hDfin z
  have hU : potential d ε D y - potential d ε D z
      = (2 * ε / unitBallVolume d)
        * ∫ v in D, (potentialIntegrand d y v - potentialIntegrand d z v) := by
    rw [potential_eq_integral, potential_eq_integral, ← mul_sub, ← integral_sub hfyD hfzD]
  have habsInt : |∫ v in D, (potentialIntegrand d y v - potentialIntegrand d z v)|
      ≤ ∫ v in D, |potentialIntegrand d y v - potentialIntegrand d z v| := by
    have h := norm_integral_le_integral_norm (μ := volume.restrict D)
      (fun v => potentialIntegrand d y v - potentialIntegrand d z v)
    simpa only [Real.norm_eq_abs] using h
  have habsU : |potential d ε D y - potential d ε D z|
      ≤ (2 * ε / unitBallVolume d)
        * ∫ v in D, |potentialIntegrand d y v - potentialIntegrand d z v| := by
    rw [hU, abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left habsInt hcoef
  have hfsD : IntegrableOn (fun v => |potentialIntegrand d y v - potentialIntegrand d z v|) D :=
    (hfyD.sub hfzD).abs
  have hsplit : ∫ v in D, |potentialIntegrand d y v - potentialIntegrand d z v|
      = (∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
          |potentialIntegrand d y v - potentialIntegrand d z v|)
        + (∫ v in D \ Metric.ball z (2 * Real.sqrt d),
          |potentialIntegrand d y v - potentialIntegrand d z v|) :=
    (integral_inter_add_sdiff (μ := volume) (s := D) (t := Metric.ball z (2 * Real.sqrt d))
      measurableSet_ball hfsD).symm
  have hnear := setIntegral_abs_potentialIntegrand_sub_le_near (d := d) hd
    hD hDfin y z hyz
  have hfar := setIntegral_abs_potentialIntegrand_sub_le_far (d := d) hd
    hR hD hDfin hDsub y z hy hyz
  have hintD : ∫ v in D, |potentialIntegrand d y v - potentialIntegrand d z v|
      ≤ 5 * (d : ℝ) * unitBallVolume d * Real.sqrt d
        + farFieldConstant d * Real.sqrt d
          * ((d : ℝ) * unitBallVolume d
            * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
    rw [hsplit]
    exact add_le_add hnear hfar
  have hmain : |potential d ε D y - potential d ε D z|
      ≤ (2 * ε / unitBallVolume d)
        * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d
          + farFieldConstant d * Real.sqrt d
            * ((d : ℝ) * unitBallVolume d
              * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d)))) :=
    habsU.trans (mul_le_mul_of_nonneg_left hintD hcoef)
  have hlog_far : Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))
      ≤ Real.log (3 + Real.sqrt d) + Real.log (R + 2) := by
    have hle : ((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d) ≤ (3 + Real.sqrt d) * (R + 2) :=
      div_le_self (by positivity) (by linarith [hδ1])
    calc Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))
        ≤ Real.log ((3 + Real.sqrt d) * (R + 2)) := Real.log_le_log (by positivity) hle
      _ = Real.log (3 + Real.sqrt d) + Real.log (R + 2) :=
          Real.log_mul (by positivity) (by linarith)
  have hlogM : 0 ≤ Real.log (3 + Real.sqrt d) := Real.log_nonneg (by linarith [hδpos])
  have hlogR : 1 ≤ Real.log (R + 2) := by
    have hexp : Real.exp 1 ≤ R + 2 := by
      have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hbase : 5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
        * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))
      ≤ (5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
        * Real.sqrt d * Real.log (R + 2) :=
    add_mul_le_mul_log hδnn hAnn hlogM hlogR hlog_far
  have hcoef2 : (2 * ε / unitBallVolume d) * ((d : ℝ) * unitBallVolume d)
      = 2 * (d : ℝ) * ε := by
    calc (2 * ε / unitBallVolume d) * ((d : ℝ) * unitBallVolume d)
        = (2 * ε * (d : ℝ) * unitBallVolume d) / unitBallVolume d := by ring
      _ = 2 * ε * (d : ℝ) := mul_div_cancel_right₀ _ hωne
      _ = 2 * (d : ℝ) * ε := by ring
  have hfac : (2 * ε / unitBallVolume d)
        * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d
          + farFieldConstant d * Real.sqrt d
            * ((d : ℝ) * unitBallVolume d
              * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))))
      = 2 * ε * (d : ℝ)
        * (5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
          * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
    calc (2 * ε / unitBallVolume d)
          * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d
            + farFieldConstant d * Real.sqrt d
              * ((d : ℝ) * unitBallVolume d
                * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))))
        = (2 * ε / unitBallVolume d)
          * (((d : ℝ) * unitBallVolume d)
            * (5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
              * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d)))) := by ring
      _ = ((2 * ε / unitBallVolume d) * ((d : ℝ) * unitBallVolume d))
          * (5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
            * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by ring
      _ = (2 * (d : ℝ) * ε)
          * (5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
            * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
          rw [hcoef2]
      _ = 2 * ε * (d : ℝ)
          * (5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
            * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by ring
  calc |potential d ε D y - potential d ε D z|
      ≤ (2 * ε / unitBallVolume d)
        * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d
          + farFieldConstant d * Real.sqrt d
            * ((d : ℝ) * unitBallVolume d
              * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d)))) := hmain
    _ = 2 * ε * (d : ℝ)
        * (5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
          * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := hfac
    _ ≤ 2 * ε * (d : ℝ)
        * ((5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
          * Real.sqrt d * Real.log (R + 2)) :=
        mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = C * ε * Real.log (R + 2) := by dsimp only [C]; ring

end CERW.Support.Geometry
