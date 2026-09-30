import CERW.Generic.Kernel.Integrable

/-!
# The sup bound of the potential

The integrand of `U_D(y)` is at most `|v - y|^{1-d}` in absolute value. On a measurable set of
finite volume it is therefore integrable, and the bathtub bound
`∫_D |v - y|^{1-d} ≤ σ_d (|D|/ω_d)^{1/d}` gives `eq:potential-bound` with the explicit constant
`|U_D(y)| ≤ 2dε ω_d^{-1/d} |D|^{1/d}`.
-/

namespace CERW.Support.Geometry

open MeasureTheory CERW CERW.Generic.Kernel

variable {d : ℕ}

/-- For `t > 0`, the quotient `t / t ^ d` equals the real power `t ^ (1 - d)`. -/
lemma div_pow_eq_rpow_sub {t : ℝ} (ht : 0 < t) (d : ℕ) :
    t / t ^ d = t ^ (1 - (d : ℝ)) := by
  have h₁ : t / t ^ d = t ^ (1 : ℝ) / t ^ (d : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_one]
  rw [h₁, ← Real.rpow_sub ht (1 : ℝ) (d : ℝ)]

/-- The arithmetic identity behind the potential bound:
`(2ε/ω) * (d ω (R/ω)^{1/d}) = 2 d ε ω^{-1/d} R^{1/d}` for `ω > 0` and `R ≥ 0`. -/
lemma potential_bound_algebra (d : ℕ) {ω R ε : ℝ} (hω : 0 < ω) (hR : 0 ≤ R) :
    (2 * ε / ω) * (d * ω * (R / ω) ^ ((1 : ℝ) / d)) =
      2 * d * ε * ω ^ (-(1 : ℝ) / d) * R ^ ((1 : ℝ) / d) := by
  have hb : 0 < ω ^ ((1 : ℝ) / d) := Real.rpow_pos_of_pos hω _
  rw [Real.div_rpow hR hω.le ((1 : ℝ) / d), neg_div, Real.rpow_neg hω.le]
  field_simp [hω.ne', hb.ne']

/-- The potential's integrand is at most the Newtonian kernel `|v - y|^{1-d}`. -/
theorem abs_potentialIntegrand_le (v y : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d| ≤ ‖v - y‖ ^ (1 - (d : ℝ)) := by
  rcases eq_or_ne v y with rfl | hne
  · simp only [sub_self, inner_zero_right, zero_div, abs_zero]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · have hw : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < ‖v - y‖ ^ d := pow_pos hw d
    have h1 : |inner ℝ (unitDir v) (v - y)| ≤ ‖unitDir v‖ * ‖v - y‖ :=
      abs_real_inner_le_norm _ _
    have h2 : ‖unitDir v‖ * ‖v - y‖ ≤ 1 * ‖v - y‖ :=
      mul_le_mul_of_nonneg_right (norm_unitDir_le v) (norm_nonneg _)
    calc
      |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d|
          = |inner ℝ (unitDir v) (v - y)| / ‖v - y‖ ^ d := by
            rw [abs_div, abs_of_nonneg hden.le]
      _ ≤ (‖unitDir v‖ * ‖v - y‖) / ‖v - y‖ ^ d :=
            div_le_div_of_nonneg_right h1 hden.le
      _ ≤ (1 * ‖v - y‖) / ‖v - y‖ ^ d :=
            div_le_div_of_nonneg_right h2 hden.le
      _ = ‖v - y‖ ^ (1 - (d : ℝ)) := by
            rw [one_mul]
            exact div_pow_eq_rpow_sub hw d

/-- On a measurable set of finite volume the potential's integrand is integrable. -/
theorem integrableOn_potentialIntegrand (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) D := by
  obtain ⟨hint, _⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) := by
    have hdir : Measurable (fun v : EuclideanSpace ℝ (Fin d) => unitDir v) := by
      change Measurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖⁻¹ • v)
      fun_prop
    have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
      measurable_id.sub measurable_const
    exact (hdir.inner hsub).div (hsub.norm.pow_const d)
  refine hint.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs]
  exact abs_potentialIntegrand_le v y

/-- `eq:potential-bound`: `|U_D(y)| ≤ 2dε ω_d^{-1/d} |D|^{1/d}` for every `y`. -/
theorem abs_potential_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    |potential d ε D y| ≤
      2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) * (volume D).toReal ^ ((1 : ℝ) / d) := by
  obtain ⟨hint, hbound⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  have hω := unitBallVolume_pos d
  have hR : 0 ≤ (volume D).toReal := ENNReal.toReal_nonneg
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hpot : potential d ε D y = (2 * ε / unitBallVolume d) *
      ∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := rfl
  have hnorm : |∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d| ≤
      ∫ v in D, ‖v - y‖ ^ (1 - (d : ℝ)) := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards with v
    rw [Real.norm_eq_abs]
    exact abs_potentialIntegrand_le v y
  calc
    |potential d ε D y|
        = |(2 * ε / unitBallVolume d) *
            ∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d| := by rw [hpot]
    _ = |2 * ε / unitBallVolume d| *
          |∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d| := by rw [abs_mul]
    _ = (2 * ε / unitBallVolume d) *
          |∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d| := by
          rw [abs_of_nonneg hc]
    _ ≤ (2 * ε / unitBallVolume d) * (∫ v in D, ‖v - y‖ ^ (1 - (d : ℝ))) :=
          mul_le_mul_of_nonneg_left hnorm hc
    _ ≤ (2 * ε / unitBallVolume d) *
          (d * unitBallVolume d * ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)) :=
          mul_le_mul_of_nonneg_left hbound hc
    _ = 2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) * (volume D).toReal ^ ((1 : ℝ) / d) :=
          potential_bound_algebra d hω hR

end CERW.Support.Geometry
