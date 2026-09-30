import CERW.Support.Geometry.TailBasic

/-!
# The weighted exterior volume: bounds and increments

`F(s) ≤ |D| / (σ_d s^{d-1})` (`eq:Fmass`), `F` vanishes beyond any radius containing `D`, and
the increment `F(s) - F(s')` is the weighted volume of the annulus `s < |v| ≤ s'`.
-/

namespace CERW.Support.Geometry

open MeasureTheory CERW

open scoped ENNReal

variable {d : ℕ}

/-- The bound of `eq:Fmass`: `F(s) ≤ |D| / (σ_d s^{d-1})` for `s > 0`, `d ≥ 1`. -/
theorem tail_le (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {s : ℝ} (hs : 0 < s) :
    tail d D s ≤ (volume D).toReal / (d * unitBallVolume d * s ^ ((d : ℝ) - 1)) := by
  have hset : MeasurableSet (D ∩ {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖}) :=
    hD.inter (measurableSet_lt measurable_const measurable_norm)
  have hfin : volume (D ∩ {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖}) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hDb.measure_lt_top).ne
  have hexp : 1 - (d : ℝ) ≤ 0 := by
    have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hInt : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (D ∩ {v | s < ‖v‖}) := integrableOn_tail hD hDb hs
  have hIntc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => s ^ (1 - (d : ℝ)))
      (D ∩ {v | s < ‖v‖}) := integrableOn_const hfin
  have hmono : ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ))
      ≤ ∫ v in D ∩ {v | s < ‖v‖}, s ^ (1 - (d : ℝ)) := by
    refine setIntegral_mono_on hInt hIntc hset ?_
    intro v hv
    exact Real.rpow_le_rpow_of_nonpos hs (le_of_lt hv.2) hexp
  have hconst : ∫ v in D ∩ {v | s < ‖v‖}, s ^ (1 - (d : ℝ))
      = (volume (D ∩ {v | s < ‖v‖})).toReal * s ^ (1 - (d : ℝ)) := by
    rw [setIntegral_const, smul_eq_mul]
    rfl
  have hmeasure : (volume (D ∩ {v | s < ‖v‖})).toReal ≤ (volume D).toReal :=
    measureReal_mono Set.inter_subset_left hDb.measure_lt_top.ne
  have hfactor : 0 ≤ (d * unitBallVolume d)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le)
  calc
    tail d D s = (d * unitBallVolume d)⁻¹ *
        ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) := rfl
    _ ≤ (d * unitBallVolume d)⁻¹ *
        ∫ v in D ∩ {v | s < ‖v‖}, s ^ (1 - (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hmono hfactor
    _ = (d * unitBallVolume d)⁻¹ *
        ((volume (D ∩ {v | s < ‖v‖})).toReal * s ^ (1 - (d : ℝ))) := by
          rw [hconst]
    _ ≤ (d * unitBallVolume d)⁻¹ *
        ((volume D).toReal * s ^ (1 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hmeasure (Real.rpow_nonneg (le_of_lt hs) _)) hfactor
    _ = (volume D).toReal / (d * unitBallVolume d * s ^ ((d : ℝ) - 1)) := by
          have h1 : 1 - (d : ℝ) = -((d : ℝ) - 1) := by ring
          rw [h1, Real.rpow_neg (le_of_lt hs) ((d : ℝ) - 1), div_eq_mul_inv, mul_inv]
          ring

/-- `F` vanishes beyond any radius whose closed ball contains `D`. -/
theorem tail_eq_zero_of_subset {D : Set (EuclideanSpace ℝ (Fin d))} {S s : ℝ}
    (hDS : D ⊆ Metric.closedBall 0 S) (hS : S ≤ s) : tail d D s = 0 := by
  have hempty : D ∩ {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hle : ‖v‖ ≤ S := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hDS hv.1
    exact not_lt_of_ge (le_trans hle hS) hv.2
  rw [tail, hempty, setIntegral_empty, mul_zero]

/-- The increment of `F` across `(s, s']` is the weighted volume of the annulus. -/
theorem tail_sub_tail {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {s s' : ℝ} (hs : 0 < s) (hss' : s ≤ s') :
    tail d D s - tail d D s' = (d * unitBallVolume d)⁻¹ *
      ∫ v in D ∩ {v | s < ‖v‖ ∧ ‖v‖ ≤ s'}, ‖v‖ ^ (1 - (d : ℝ)) := by
  have hBmeas : MeasurableSet (D ∩ {v : EuclideanSpace ℝ (Fin d) | s' < ‖v‖}) :=
    hD.inter (measurableSet_lt measurable_const measurable_norm)
  have hdisj : Disjoint (D ∩ {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖ ∧ ‖v‖ ≤ s'})
      (D ∩ {v : EuclideanSpace ℝ (Fin d) | s' < ‖v‖}) := by
    rw [Set.disjoint_left]
    intro v hvA hvB
    exact not_lt_of_ge hvA.2.2 hvB.2
  have hIntT : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (D ∩ {v | s < ‖v‖}) := integrableOn_tail hD hDb hs
  have hAsub : D ∩ {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖ ∧ ‖v‖ ≤ s'}
      ⊆ D ∩ {v | s < ‖v‖} :=
    Set.inter_subset_inter_right D fun v hv => hv.1
  have hBsub : D ∩ {v : EuclideanSpace ℝ (Fin d) | s' < ‖v‖} ⊆ D ∩ {v | s < ‖v‖} :=
    Set.inter_subset_inter_right D fun v hv => lt_of_le_of_lt hss' hv
  have hIntA : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (D ∩ {v | s < ‖v‖ ∧ ‖v‖ ≤ s'}) := hIntT.mono_set hAsub
  have hIntB : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ)))
      (D ∩ {v | s' < ‖v‖}) := hIntT.mono_set hBsub
  have hset : D ∩ {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖}
      = (D ∩ {v | s < ‖v‖ ∧ ‖v‖ ≤ s'}) ∪ (D ∩ {v | s' < ‖v‖}) := by
    ext v
    constructor
    · intro hv
      rcases lt_or_ge s' ‖v‖ with hlt | hle
      · exact Or.inr ⟨hv.1, hlt⟩
      · exact Or.inl ⟨hv.1, hv.2, hle⟩
    · rintro (⟨hd, hlt, hle⟩ | ⟨hd, hlt⟩)
      · exact ⟨hd, hlt⟩
      · exact ⟨hd, lt_of_le_of_lt hss' hlt⟩
  have hunion : (∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)))
      = (∫ v in D ∩ {v | s < ‖v‖ ∧ ‖v‖ ≤ s'}, ‖v‖ ^ (1 - (d : ℝ)))
        + (∫ v in D ∩ {v | s' < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ))) := by
    rw [hset]
    exact setIntegral_union hdisj hBmeas hIntA hIntB
  rw [tail, tail, hunion]
  ring

end CERW.Support.Geometry
