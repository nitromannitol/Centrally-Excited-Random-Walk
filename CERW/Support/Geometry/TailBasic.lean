import CERW.Model.Potential

/-!
# The weighted exterior volume: sign, integrability, monotonicity

For a bounded measurable set `D`, `F(s) = σ_d^{-1} ∫_{D ∩ {|v| > s}} |v|^{1-d} dv` is
nonnegative, its integrand is integrable beyond every positive radius, and `F` is
nonincreasing on `(0, ∞)` (`eq:Fdef`).
-/

namespace CERW.Support.Geometry

open MeasureTheory CERW

open scoped ENNReal

variable {d : ℕ}

/-- The weighted exterior volume is nonnegative. -/
theorem tail_nonneg (D : Set (EuclideanSpace ℝ (Fin d))) (s : ℝ) : 0 ≤ tail d D s := by
  rw [tail]
  refine mul_nonneg
    (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le)) ?_
  exact setIntegral_nonneg_of_ae
    (Filter.Eventually.of_forall fun v => Real.rpow_nonneg (norm_nonneg v) _)

/-- On a bounded measurable set the weight `|v|^{1-d}` is integrable beyond any positive
radius. -/
theorem integrableOn_tail {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (D ∩ {v | s < ‖v‖}) := by
  rcases d with _ | n
  · simp only [Nat.cast_zero, sub_zero, Real.rpow_one]
    have hset : MeasurableSet (D ∩ {v : EuclideanSpace ℝ (Fin 0) | s < ‖v‖}) :=
      hD.inter (measurableSet_lt measurable_const measurable_norm)
    have hfinite : volume (D ∩ {v : EuclideanSpace ℝ (Fin 0) | s < ‖v‖}) < ∞ :=
      lt_of_le_of_lt (measure_mono Set.inter_subset_left) hDb.measure_lt_top
    obtain ⟨r, hr⟩ := hDb.subset_closedBall (0 : EuclideanSpace ℝ (Fin 0))
    refine IntegrableOn.of_bound hfinite (continuous_norm.continuousOn.aestronglyMeasurable hset)
      r ?_
    refine ae_restrict_of_forall_mem hset ?_
    intro a ha
    have hle : ‖a‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hr ha.1
    simpa using hle
  · have hset : MeasurableSet (D ∩ {v : EuclideanSpace ℝ (Fin (n + 1)) | s < ‖v‖}) :=
      hD.inter (measurableSet_lt measurable_const measurable_norm)
    have hfinite : volume (D ∩ {v : EuclideanSpace ℝ (Fin (n + 1)) | s < ‖v‖}) < ∞ :=
      lt_of_le_of_lt (measure_mono Set.inter_subset_left) hDb.measure_lt_top
    have hc : 1 - ((n + 1 : ℕ) : ℝ) ≤ 0 := by
      have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      linarith
    refine IntegrableOn.of_bound hfinite ?_ (s ^ (1 - ((n + 1 : ℕ) : ℝ))) ?_
    · exact (continuous_norm.continuousOn.rpow_const
        (fun x hx => Or.inl (ne_of_gt (lt_trans hs hx.2)))).aestronglyMeasurable hset
    · refine ae_restrict_of_forall_mem hset ?_
      intro a ha
      have hle : ‖a‖ ^ (1 - ((n + 1 : ℕ) : ℝ)) ≤ s ^ (1 - ((n + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hs (le_of_lt ha.2) hc
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg a) _)] using hle

/-- The weighted exterior volume is nonincreasing on `(0, ∞)`. -/
theorem tail_antitoneOn {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) : AntitoneOn (tail d D) (Set.Ioi 0) := by
  intro s hs s' hs' hsle
  have hc : 0 ≤ (d * unitBallVolume d : ℝ)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le)
  have hsub : D ∩ {v | s' < ‖v‖} ⊆ D ∩ {v | s < ‖v‖} :=
    Set.inter_subset_inter_right D fun v hv => lt_of_le_of_lt hsle hv
  have hmeas : MeasurableSet (D ∩ {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖}) :=
    hD.inter (measurableSet_lt measurable_const measurable_norm)
  have hInt : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (D ∩ {v | s < ‖v‖}) := integrableOn_tail hD hDb hs
  have hmono : ∫ v in D ∩ {v | s' < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ))
      ≤ ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) := by
    refine setIntegral_mono_set hInt ?_ ?_
    · exact ae_restrict_of_forall_mem hmeas fun v _ => Real.rpow_nonneg (norm_nonneg v) _
    · exact Filter.Eventually.of_forall fun v hv => hsub hv
  simp only [tail]
  exact mul_le_mul_of_nonneg_left hmono hc

end CERW.Support.Geometry
