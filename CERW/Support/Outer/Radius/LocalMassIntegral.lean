module

public import CERW.Support.Outer.Radius.CapMass

@[expose] public section

/-!
# Local Mass Integral

A choice of integration scale bounds a radial power integral from local and total mass. The
resulting bound also gives boundedness of the family of integrals.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The layer-cake bound with a cut scale `s ≥ w`:
`∫_E |v-y|^{2-d} ≤ (d-2) ω_d w²/2 + (d-2) lam (s-w) + m s^{2-d}`, in `[0, ∞]`-valued form. -/
lemma gmb_lintegral_bound (hd : 3 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) {w lam m s : ℝ} (hw : 0 < w)
    (hlam : 0 < lam) (hm : 0 < m) (hws : w ≤ s)
    (hloc : ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ), w ≤ t →
      (volume (E ∩ Metric.ball y t)).toReal ≤ lam * t ^ (d - 1))
    (hmass : (volume E).toReal ≤ m) (y : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ))) ≤
      ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 +
        ((d : ℝ) - 2) * lam * (s - w) + m * s ^ (2 - (d : ℝ))) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < (d : ℝ) - 2 := by linarith
  have hs : 0 < s := hw.trans_le hws
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  set f : ℝ → ENNReal := fun t => ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ))) with hf
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.mul (measurable_id.pow_const _)
  set B1 : ℝ → ENNReal := (Set.Ioc 0 w).indicator
    (fun t => ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * t)) with hB1
  set B2 : ℝ → ENNReal := (Set.Ioc w s).indicator
    (fun _ => ENNReal.ofReal (((d : ℝ) - 2) * lam)) with hB2
  set B3 : ℝ → ENNReal := (Set.Ioi s).indicator (fun t => ENNReal.ofReal m * f t) with hB3
  have hB1m : Measurable B1 := by
    refine Measurable.indicator ?_ measurableSet_Ioc
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)
  have hB2m : Measurable B2 := measurable_const.indicator measurableSet_Ioc
  have hB3m : Measurable B3 := (measurable_const.mul hfm).indicator measurableSet_Ioi
  have hfin : ∀ t, volume (E ∩ Metric.ball y t) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top hEfin (measure_mono Set.inter_subset_left)
  have hpt : ∀ t, f t * volume (E ∩ Metric.ball y t) ≤ B1 t + B2 t + B3 t := by
    intro t
    by_cases ht0 : t ≤ 0
    · have : Metric.ball y t = ∅ := Metric.ball_eq_empty.mpr ht0
      simp [this]
    have ht0 := not_le.mp ht0
    by_cases htw : t ≤ w
    · have hB2z : B2 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioc w s => (not_le.mpr h.1) htw) _
      have hB3z : B3 t = 0 :=
        Set.indicator_of_notMem
          (fun h : t ∈ Set.Ioi s => (not_le.mpr h) (htw.trans hws)) _
      have hB1e : B1 t = ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * t) :=
        Set.indicator_of_mem (show t ∈ Set.Ioc 0 w from ⟨ht0, htw⟩) _
      rw [hB2z, hB3z, hB1e, add_zero, add_zero]
      have hid := gmb_rpow_mul_pow d ht0
      calc f t * volume (E ∩ Metric.ball y t) ≤ f t * volume (Metric.ball y t) := by
            gcongr
            exact Set.inter_subset_right
        _ = ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ)) * (unitBallVolume d * t ^ d)) := by
            rw [gmb_volume_ball (by omega) y ht0.le, hf]
            exact (ENNReal.ofReal_mul (mul_nonneg hp.le (Real.rpow_nonneg ht0.le _))).symm
        _ = ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * t) := by
            congr 1
            calc ((d : ℝ) - 2) * t ^ (1 - (d : ℝ)) * (unitBallVolume d * t ^ d)
                = ((d : ℝ) - 2) * unitBallVolume d * (t ^ (1 - (d : ℝ)) * t ^ d) := by ring
              _ = ((d : ℝ) - 2) * unitBallVolume d * t := by rw [hid]
    by_cases hts : t ≤ s
    · have hB1z : B1 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioc 0 w => htw h.2) _
      have hB3z : B3 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioi s => (not_le.mpr h) hts) _
      have hB2e : B2 t = ENNReal.ofReal (((d : ℝ) - 2) * lam) :=
        Set.indicator_of_mem (show t ∈ Set.Ioc w s from ⟨not_le.mp htw, hts⟩) _
      rw [hB1z, hB3z, hB2e, zero_add, add_zero]
      have hid := gmb_rpow_mul_pow_pred (d := d) (by omega) ht0
      have hvol : volume (E ∩ Metric.ball y t) ≤ ENNReal.ofReal (lam * t ^ (d - 1)) :=
        (ENNReal.le_ofReal_iff_toReal_le (hfin t) (by positivity)).mpr
          (hloc y t (not_le.mp htw).le)
      calc f t * volume (E ∩ Metric.ball y t)
          ≤ f t * ENNReal.ofReal (lam * t ^ (d - 1)) := by gcongr
        _ = ENNReal.ofReal (((d : ℝ) - 2) * t ^ (1 - (d : ℝ)) * (lam * t ^ (d - 1))) :=
            (ENNReal.ofReal_mul (mul_nonneg hp.le (Real.rpow_nonneg ht0.le _))).symm
        _ = ENNReal.ofReal (((d : ℝ) - 2) * lam) := by
            congr 1
            calc ((d : ℝ) - 2) * t ^ (1 - (d : ℝ)) * (lam * t ^ (d - 1))
                = ((d : ℝ) - 2) * lam * (t ^ (1 - (d : ℝ)) * t ^ (d - 1)) := by ring
              _ = ((d : ℝ) - 2) * lam := by rw [hid, mul_one]
    · have hB1z : B1 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioc 0 w => hts (h.2.trans hws)) _
      have hB2z : B2 t = 0 :=
        Set.indicator_of_notMem (fun h : t ∈ Set.Ioc w s => hts h.2) _
      have hB3e : B3 t = ENNReal.ofReal m * f t :=
        Set.indicator_of_mem (show t ∈ Set.Ioi s from not_le.mp hts) _
      rw [hB1z, hB2z, hB3e, zero_add, zero_add, mul_comm]
      have hvol : volume (E ∩ Metric.ball y t) ≤ ENNReal.ofReal m :=
        (ENNReal.le_ofReal_iff_toReal_le (hfin t) hm.le).mpr
          ((ENNReal.toReal_mono hEfin (measure_mono Set.inter_subset_left)).trans hmass)
      gcongr
  have hA : 0 ≤ ((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 := by positivity
  have hB : 0 ≤ ((d : ℝ) - 2) * lam * (s - w) :=
    mul_nonneg (mul_nonneg hp.le hlam.le) (sub_nonneg.mpr hws)
  have hC : 0 ≤ m * s ^ (2 - (d : ℝ)) := mul_nonneg hm.le (Real.rpow_nonneg hs.le _)
  have hI1 : (∫⁻ t, B1 t) = ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2) := by
    have hint : IntegrableOn (fun t : ℝ => ((d : ℝ) - 2) * unitBallVolume d * t)
        (Set.Ioc 0 w) := (continuous_const.mul continuous_id).integrableOn_Ioc
    rw [hB1, lintegral_indicator measurableSet_Ioc,
      ← ofReal_integral_eq_lintegral_ofReal hint]
    · congr 1
      rw [← intervalIntegral.integral_of_le hw.le, intervalIntegral.integral_const_mul,
        integral_id]
      ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg (mul_nonneg hp.le hω.le) ht.1.le
  have hI2 : (∫⁻ t, B2 t) = ENNReal.ofReal (((d : ℝ) - 2) * lam * (s - w)) := by
    rw [hB2, lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc,
      ← ENNReal.ofReal_mul (mul_nonneg hp.le hlam.le)]
  have hI3 : (∫⁻ t, B3 t) = ENNReal.ofReal (m * s ^ (2 - (d : ℝ))) := by
    rw [hB3, lintegral_indicator measurableSet_Ioi, lintegral_const_mul _ hfm, hf,
      gmb_lintegral_tail hd hs, ← ENNReal.ofReal_mul hm.le]
  calc ∫⁻ v in E, ENNReal.ofReal (‖v - y‖ ^ (2 - (d : ℝ)))
      ≤ ∫⁻ t, f t * volume (E ∩ Metric.ball y t) := gmb_layer_cake hd hE y
    _ ≤ ∫⁻ t, (B1 t + B2 t + B3 t) := lintegral_mono hpt
    _ = (∫⁻ t, B1 t) + (∫⁻ t, B2 t) + ∫⁻ t, B3 t := by
        rw [lintegral_add_left (f := fun t => B1 t + B2 t) (hB1m.add hB2m),
          lintegral_add_left (f := B1) hB1m]
    _ = ENNReal.ofReal (((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 +
        ((d : ℝ) - 2) * lam * (s - w) + m * s ^ (2 - (d : ℝ))) := by
        rw [hI1, hI2, hI3, ← ENNReal.ofReal_add hA hB, ← ENNReal.ofReal_add (add_nonneg hA hB) hC]

/-- The optimal cut scale of the layer-cake bound: there is `s ≥ w` with
`(d-2) lam (s-w) + m s^{2-d} ≤ (d-1) lam^{(d-2)/(d-1)} m^{1/(d-1)}`. -/
lemma gmb_choose_scale (hd : 3 ≤ d) {w lam m : ℝ} (hw : 0 < w) (hlam : 0 < lam)
    (hm : 0 < m) :
    ∃ s : ℝ, w ≤ s ∧ ((d : ℝ) - 2) * lam * (s - w) + m * s ^ (2 - (d : ℝ)) ≤
      ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : (d : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨s0, hs0def⟩ : ∃ s0 : ℝ, s0 = (m / lam) ^ ((1 : ℝ) / ((d : ℝ) - 1)) := ⟨_, rfl⟩
  have hmlam : 0 < m / lam := div_pos hm hlam
  have hs0 : 0 < s0 := hs0def ▸ Real.rpow_pos_of_pos hmlam _
  have hs0q : s0 ^ ((d : ℝ) - 1) = m / lam := by
    rw [hs0def, ← Real.rpow_mul hmlam.le, one_div, inv_mul_cancel₀ hq, Real.rpow_one]
  have hm_eq : m = lam * s0 ^ ((d : ℝ) - 1) := by
    rw [hs0q]
    field_simp
  have hms : m * s0 ^ (2 - (d : ℝ)) = lam * s0 := by
    rw [hm_eq, mul_assoc, ← Real.rpow_add hs0]
    have : ((d : ℝ) - 1) + (2 - (d : ℝ)) = 1 := by ring
    rw [this, Real.rpow_one]
  have hlams0 : lam * s0 =
      lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
    have hsum : ((d : ℝ) - 2) / ((d : ℝ) - 1) + (1 : ℝ) / ((d : ℝ) - 1) = 1 := by
      field_simp
      ring
    have hl : lam = lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        lam ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
      rw [← Real.rpow_add hlam, hsum, Real.rpow_one]
    have hl1 : 0 < lam ^ ((1 : ℝ) / ((d : ℝ) - 1)) := Real.rpow_pos_of_pos hlam _
    rw [hs0def, Real.div_rpow hm.le hlam.le]
    calc lam * (m ^ ((1 : ℝ) / ((d : ℝ) - 1)) / lam ^ ((1 : ℝ) / ((d : ℝ) - 1)))
        = (lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * lam ^ ((1 : ℝ) / ((d : ℝ) - 1))) *
          (m ^ ((1 : ℝ) / ((d : ℝ) - 1)) / lam ^ ((1 : ℝ) / ((d : ℝ) - 1))) := by
          rw [← hl]
      _ = lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
          field_simp
  have hK : ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
      m ^ ((1 : ℝ) / ((d : ℝ) - 1)) = ((d : ℝ) - 1) * (lam * s0) := by
    rw [hlams0]
    ring
  have hlm : 0 < lam * s0 := mul_pos hlam hs0
  by_cases hcase : w ≤ s0
  · refine ⟨s0, hcase, ?_⟩
    rw [hK, hms]
    have h1 : 0 ≤ ((d : ℝ) - 2) * (lam * w) :=
      mul_nonneg (by linarith) (mul_nonneg hlam.le hw.le)
    linarith
  · have hlt : s0 < w := not_le.mp hcase
    refine ⟨w, le_rfl, ?_⟩
    rw [sub_self, mul_zero, zero_add, hK]
    have h1 : w ^ (2 - (d : ℝ)) ≤ s0 ^ (2 - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hs0 hlt.le (by linarith)
    calc m * w ^ (2 - (d : ℝ)) ≤ m * s0 ^ (2 - (d : ℝ)) := by gcongr
      _ = lam * s0 := hms
      _ ≤ ((d : ℝ) - 1) * (lam * s0) := le_mul_of_one_le_left hlm.le (by linarith)

/-- Step 4 of the higher-dimensional proof: the layer-cake bound for `∫_E |v-y|^{2-d}` from the
local mass bound at scales `t ≥ w` and the total mass. -/
theorem integral_rpow_le_of_local_mass (hd : 3 ≤ d)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    {w lam m : ℝ} (hw : 0 < w) (hlam : 0 < lam) (hm : 0 < m)
    (hloc : ∀ (y : EuclideanSpace ℝ (Fin d)) (t : ℝ), w ≤ t →
      (volume (E ∩ Metric.ball y t)).toReal ≤ lam * t ^ (d - 1))
    (hmass : (volume E).toReal ≤ m) (y : EuclideanSpace ℝ (Fin d)) :
    ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ)) ≤
      ((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 +
        ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  obtain ⟨s, hws, hs⟩ := gmb_choose_scale hd hw hlam hm
  have hlint := gmb_lintegral_bound hd hE hEfin hw hlam hm hws hloc hmass y
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hR : 0 ≤ ((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 +
      ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
    have h1 : 0 ≤ ((d : ℝ) - 2) * unitBallVolume d * w ^ 2 / 2 := by
      have : 0 ≤ (d : ℝ) - 2 := by linarith
      positivity
    have h2 : 0 ≤ ((d : ℝ) - 1) * lam ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        m ^ ((1 : ℝ) / ((d : ℝ) - 1)) := by
      have : 0 ≤ (d : ℝ) - 1 := by linarith
      positivity
    exact add_nonneg h1 h2
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v - y‖ ^ (2 - (d : ℝ))) :=
    (measurable_id.sub_const y).norm.pow_const _
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun v => Real.rpow_nonneg (norm_nonneg _) _)
    hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hR (hlint.trans (ENNReal.ofReal_le_ofReal ?_))
  linarith

/-- The integrals `∫_E |v-y|^{2-d}` are bounded uniformly in `y` for a bounded set `E`. -/
theorem integral_rpow_bddAbove (hd : 3 ≤ d) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) :
    BddAbove (Set.range fun y : EuclideanSpace ℝ (Fin d) => ∫ v in E, ‖v - y‖ ^ (2 - (d : ℝ))) := by
  have hm : 0 < (volume E).toReal + 1 := by positivity
  refine ⟨((d : ℝ) - 2) * unitBallVolume d * 1 ^ 2 / 2 +
    ((d : ℝ) - 1) * ((volume E).toReal + 1) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
      ((volume E).toReal + 1) ^ ((1 : ℝ) / ((d : ℝ) - 1)), ?_⟩
  rintro _ ⟨y, rfl⟩
  refine integral_rpow_le_of_local_mass hd hE hEb (w := 1) (lam := (volume E).toReal + 1)
    one_pos hm hm ?_ (by linarith) y
  intro y' t ht
  calc (volume (E ∩ Metric.ball y' t)).toReal ≤ (volume E).toReal :=
        ENNReal.toReal_mono hEb.measure_lt_top.ne (measure_mono Set.inter_subset_left)
    _ ≤ (volume E).toReal + 1 := by linarith
    _ ≤ ((volume E).toReal + 1) * t ^ (d - 1) :=
        le_mul_of_one_le_right hm.le (one_le_pow₀ ht)

/-! ### The exterior analysis for `d ≥ 3` -/

end CERW.Support.Outer.Radius
