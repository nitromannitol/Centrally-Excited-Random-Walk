module

public import CERW.Support.Outer.Radius.ExteriorEnvelope

@[expose] public section

/-!
# Probe Geometry

A probe outside the range bounds the positive exterior potential. Its geometric separation gives a
bound on the mass of a spherical cap.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

section

open CERW.Generic.Kernel CERW.Support.Geometry

/-- On a bounded set the function `|v - y|^{2-d}` is integrable for `d ≥ 2`. -/
lemma gma_integrableOn_rpow (hd : 2 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hEb : Bornology.IsBounded E) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => ‖v - y‖ ^ (2 - (d : ℝ))) E := by
  obtain ⟨ρ, hρ⟩ := hEb.subset_ball y
  have hρ1 : 0 < max ρ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsub : E ⊆ Metric.ball y (max ρ 1) :=
    hρ.trans (Metric.ball_subset_ball (le_max_left _ _))
  have hd2 : (d : ℝ) - 2 < d := by linarith
  have h0 := (integrableOn_ball_rpow_neg_and_integral_eq (d := d) (by omega) hd2 hρ1).1
  simp only [neg_sub] at h0
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) y
  have hemb := measurableEmbedding_subRight y
  have h1 : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v - y‖ ^ (2 - (d : ℝ)))
      (Metric.ball y (max ρ 1)) := by
    rw [ball_eq_preimage_sub]
    exact (hmp.integrableOn_comp_preimage hemb (f := fun v => ‖v‖ ^ (2 - (d : ℝ)))).mpr h0
  exact h1.mono_set hsub

/-- The positive potential at a point beyond the support: `u_v·(v-y) ≤ |v-y|²/(2|v|)`. -/
theorem positivePotential_le_of_outside (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    {b R : ℝ} (hb : 0 < b) (hsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ R})
    {y : EuclideanSpace ℝ (Fin d)} (hy : R ≤ ‖y‖) :
    positivePotential d ε E y ≤
      ε / (unitBallVolume d * b) * ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ)) := by
  have hω := unitBallVolume_pos d
  have hint := gma_integrableOn_rpow hd hEb y
  have hpt : ∀ v ∈ E, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 ≤
      (2 * b)⁻¹ * ‖v - y‖ ^ (2 - (d : ℝ)) := by
    intro v hv
    obtain ⟨hbv, hvR⟩ := hsub hv
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, norm_zero] at hbv
      linarith
    have hvy : ‖v‖ ≤ ‖y‖ := hvR.trans hy
    have hnn : 0 ≤ (2 * b)⁻¹ * ‖v - y‖ ^ (2 - (d : ℝ)) :=
      mul_nonneg (inv_nonneg.mpr (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)
    refine max_le ?_ hnn
    by_cases hne : v = y
    · have h0 : inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d = 0 := by
        rw [hne]
        simp
      rw [h0]
      exact hnn
    · have hs : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have h1 := inner_unitDir_sub_le_sq_div hv0 hvy
      have hs2 : ‖v - y‖ ^ (2 - (d : ℝ)) = ‖v - y‖ ^ 2 / ‖v - y‖ ^ d := by
        rw [Real.rpow_sub hs, Real.rpow_two, Real.rpow_natCast]
      calc inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d
          ≤ (‖v - y‖ ^ 2 / (2 * ‖v‖)) / ‖v - y‖ ^ d :=
            div_le_div_of_nonneg_right h1 (pow_pos hs d).le
        _ ≤ (‖v - y‖ ^ 2 / (2 * b)) / ‖v - y‖ ^ d := by
            refine div_le_div_of_nonneg_right ?_ (pow_pos hs d).le
            exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        _ = (2 * b)⁻¹ * ‖v - y‖ ^ (2 - (d : ℝ)) := by
            rw [hs2]
            field_simp
  have hmono : ∫ v in E, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 ≤
      ∫ v in E, (2 * b)⁻¹ * ‖v - y‖ ^ (2 - (d : ℝ)) := by
    refine integral_mono_of_nonneg ?_ (hint.const_mul _) ?_
    · exact Filter.Eventually.of_forall fun v => le_max_right _ _
    · exact (ae_restrict_iff' hE).mpr (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  unfold positivePotential
  calc 2 * ε / unitBallVolume d *
        ∫ v in E, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      ≤ 2 * ε / unitBallVolume d * ((2 * b)⁻¹ * ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ε / (unitBallVolume d * b) * ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ)) := by ring

/-- For a point `v` of the cap of the ball of radius `t` about `c u`, the probe `(c + 4t) u`
satisfies `u_v · (v - (c + 4t) u) ≤ -t` and `|v - (c + 4t) u| ≤ 5t`. -/
lemma gma_probe_bounds {c t : ℝ} (ht : 0 < t) (htc : 2 * t ≤ c)
    {u v : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1) (hv0 : v ≠ 0) (hvc : ‖v‖ ≤ c)
    (hvB : ‖v - c • u‖ < t) :
    inner ℝ (unitDir v) (v - (c + 4 * t) • u) ≤ -t ∧ ‖v - (c + 4 * t) • u‖ ≤ 5 * t := by
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hIu : c - t ≤ inner ℝ v u := by
    have h1 : inner ℝ v u = inner ℝ (v - c • u) u + c := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
      ring
    have h2 : |inner ℝ (v - c • u) u| ≤ ‖v - c • u‖ * ‖u‖ := abs_real_inner_le_norm _ _
    rw [hu, mul_one] at h2
    have h3 := neg_abs_le (inner ℝ (v - c • u) u)
    linarith
  have hinner : inner ℝ (unitDir v) (v - (c + 4 * t) • u) =
      ‖v‖ - (c + 4 * t) * inner ℝ v u / ‖v‖ := by
    rw [unitDir, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_smul_right]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hinner]
    have h1 : (‖v‖ + t) * ‖v‖ ≤ (c + t) * c :=
      mul_le_mul (add_le_add_left hvc t) hvc hr.le (by linarith)
    have h2 : (c + t) * c ≤ (c + 4 * t) * (c - t) := by
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htc)]
    have h3 : (c + 4 * t) * (c - t) ≤ (c + 4 * t) * inner ℝ v u :=
      mul_le_mul_of_nonneg_left hIu (by linarith)
    have h4 : ‖v‖ + t ≤ (c + 4 * t) * inner ℝ v u / ‖v‖ := by
      rw [le_div_iff₀ hr]
      linarith
    linarith
  · have h1 : v - (c + 4 * t) • u = (v - c • u) - (4 * t) • u := by
      rw [add_smul, sub_sub]
    rw [h1]
    calc ‖(v - c • u) - (4 * t) • u‖ ≤ ‖v - c • u‖ + ‖(4 * t) • u‖ := norm_sub_le _ _
      _ ≤ t + 4 * t := by
        rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      _ = 5 * t := by ring

/-- Step 2 of the higher-dimensional proof: a probe potential bound bounds the volume of a cap. -/
theorem cap_mass_of_probe (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    {b w t lo hi : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w}) (hb : 0 < b)
    (ht : 0 < t) (htb : 2 * t ≤ b + w) {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ = 1)
    (hlow : -lo ≤ potential d ε E (((b + w + 4 * t) : ℝ) • u))
    (hhi : positivePotential d ε E (((b + w + 4 * t) : ℝ) • u) ≤ hi) :
    (volume (E ∩ Metric.ball (((b + w) : ℝ) • u) t)).toReal ≤
      unitBallVolume d / (2 * ε) * 5 ^ d * (lo + hi) * t ^ (d - 1) := by
  have hω := unitBallVolume_pos d
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  set y : EuclideanSpace ℝ (Fin d) := ((b + w + 4 * t : ℝ)) • u with hy
  have hint := integrableOn_potentialIntegrand (d := d) (by omega) hE hEfin y
  set B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball (((b + w) : ℝ) • u) t with hB
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  set κ : ℝ := t / (5 * t) ^ d with hκ
  have hκpos : 0 < κ := by positivity
  have hpt : ∀ v ∈ E, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d ≤
      max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 - B.indicator (fun _ => κ) v := by
    intro v hv
    by_cases hvB : v ∈ B
    · rw [Set.indicator_of_mem hvB]
      obtain ⟨hb1, hb2⟩ := hsub hv
      have hv0 : v ≠ 0 := by
        intro h
        rw [h, norm_zero] at hb1
        linarith
      obtain ⟨h1, h2⟩ := gma_probe_bounds (c := b + w) ht htb hu hv0 hb2
        (by rwa [hB, Metric.mem_ball, dist_eq_norm] at hvB)
      have h1' : inner ℝ (unitDir v) (v - y) ≤ -t := h1
      have hs : 0 < ‖v - y‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        intro h
        rw [h] at h1'
        simp only [sub_self, inner_zero_right] at h1'
        linarith
      have hf : inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d ≤ -κ := by
        calc inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d ≤ (-t) / ‖v - y‖ ^ d :=
              div_le_div_of_nonneg_right h1' (pow_pos hs d).le
          _ = -(t / ‖v - y‖ ^ d) := neg_div _ _
          _ ≤ -κ := by
              refine neg_le_neg ?_
              exact div_le_div_of_nonneg_left ht.le (pow_pos hs d)
                (pow_le_pow_left₀ hs.le h2 d)
      have := le_max_right (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      linarith
    · rw [Set.indicator_of_notMem hvB, sub_zero]
      exact le_max_left _ _
  have hposint : IntegrableOn (fun v => max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0) E :=
    hint.pos_part
  have hindint : IntegrableOn (fun v => B.indicator (fun _ => κ) v) E :=
    (integrableOn_const hEfin).indicator hBm
  have hmono : ∫ v in E, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d ≤
      ∫ v in E, (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 -
        B.indicator (fun _ => κ) v) :=
    setIntegral_mono_on hint (hposint.sub hindint) hE hpt
  rw [integral_sub hposint hindint, setIntegral_indicator hBm, setIntegral_const] at hmono
  have hK0 : 0 < 2 * ε / unitBallVolume d := by positivity
  have hmono' := mul_le_mul_of_nonneg_left hmono hK0.le
  have hpot : potential d ε E y = 2 * ε / unitBallVolume d *
      ∫ v in E, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := rfl
  have hpos : positivePotential d ε E y = 2 * ε / unitBallVolume d *
      ∫ v in E, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0 := rfl
  rw [measureReal_def, smul_eq_mul, mul_sub] at hmono'
  have hV : (volume (E ∩ B)).toReal * (2 * ε / unitBallVolume d * κ) ≤ lo + hi := by
    rw [← hpot] at hmono'
    rw [← hpos] at hmono'
    nlinarith
  have hfinal : (lo + hi) / (2 * ε / unitBallVolume d * κ) =
      unitBallVolume d / (2 * ε) * 5 ^ d * (lo + hi) * t ^ (d - 1) := by
    have htd : t ^ d = t ^ (d - 1) * t := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hκ, mul_pow, htd]
    field_simp
  rw [← hfinal]
  exact (le_div_iff₀ (by positivity)).mpr hV

end

end CERW.Support.Outer.Radius
