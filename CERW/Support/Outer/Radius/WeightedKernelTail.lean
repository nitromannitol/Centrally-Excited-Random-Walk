import CERW.Support.Outer.Radius.CellWeights

/-!
# Weighted Kernel Tail

Near and far regions bound the radial weight integrated against the truncated distance. Combining
them gives the kernel tail estimate.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The potential of a finite-volume set `D` at a point at distance at least `R ≥ 1` from every
point of `D` is at most `(2ε/ω_d) |D| / R` in absolute value. -/
lemma ev_abs_potential_le_of_far (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hDfin : volume D ≠ ⊤) {R : ℝ} (hR : 1 ≤ R)
    {ζ : EuclideanSpace ℝ (Fin d)} (hfar : ∀ v ∈ D, R ≤ ‖v - ζ‖) :
    |potential d ε D ζ| ≤ 2 * ε / unitBallVolume d * ((volume D).toReal / R) := by
  have hω := unitBallVolume_pos d
  have hbd : ∀ v ∈ D, ‖inner ℝ (unitDir v) (v - ζ) / ‖v - ζ‖ ^ d‖ ≤ 1 / R := by
    intro v hv
    have hw := hfar v hv
    have hw1 : 1 ≤ ‖v - ζ‖ := hR.trans hw
    have hwpos : 0 < ‖v - ζ‖ := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hwpos d)]
    have h1 : |inner ℝ (unitDir v) (v - ζ)| ≤ ‖v - ζ‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (norm_unitDir_le v))
    have h2 : ‖v - ζ‖ ^ 2 ≤ ‖v - ζ‖ ^ d := pow_le_pow_right₀ hw1 hd
    rw [div_le_div_iff₀ (pow_pos hwpos d) (by linarith)]
    calc |inner ℝ (unitDir v) (v - ζ)| * R ≤ ‖v - ζ‖ * ‖v - ζ‖ :=
          mul_le_mul h1 hw (by linarith) hwpos.le
      _ = ‖v - ζ‖ ^ 2 := by ring
      _ ≤ ‖v - ζ‖ ^ d := h2
      _ = 1 * ‖v - ζ‖ ^ d := (one_mul _).symm
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) hDfin.lt_top hbd
  have hreal : volume.real D = (volume D).toReal := rfl
  rw [hreal] at hint
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  unfold potential
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← Real.norm_eq_abs]
  calc ‖∫ v in D, inner ℝ (unitDir v) (v - ζ) / ‖v - ζ‖ ^ d‖
      ≤ 1 / R * (volume D).toReal := hint
    _ = (volume D).toReal / R := by ring

/-- Near the origin the integrand of the radial estimate is at most `(1 + |ζ|)^{-d}`. -/
lemma ev_chi_mul_min_le_near (hd : 3 ≤ d) (b : ℝ) (ζ : EuclideanSpace ℝ (Fin d)) :
    ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤ (1 + ‖ζ‖) ^ (-(d : ℝ)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 1 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  have hx0 : 0 < 1 + ‖ζ‖ := by linarith
  calc ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤ ev_chi d ‖ζ‖ * ‖ζ‖ :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (ev_chi_nonneg _)
    _ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * ‖ζ‖ := by rw [ev_chi_norm]
    _ ≤ (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * (1 + ‖ζ‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hx0.le _)
    _ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ) + 1) := (Real.rpow_add_one hx0.ne' _).symm
    _ ≤ (1 + ‖ζ‖) ^ (-(d : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- Far from the origin the integrand of the radial estimate is at most `b |ζ|^{2-2d}`. -/
lemma ev_chi_mul_min_le_far (hd : 1 ≤ d) {b : ℝ} (hb : 0 ≤ b)
    {ζ : EuclideanSpace ℝ (Fin d)} (hζ : 0 < ‖ζ‖) :
    ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤ b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) ≤ ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) :=
    Real.rpow_le_rpow_of_nonpos hζ (by linarith) (by linarith)
  rw [ev_chi_norm, show 2 - 2 * (d : ℝ) = -(2 * (d : ℝ) - 2) by ring]
  calc (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) * min b ‖ζ‖
      ≤ (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) * b :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg (by linarith [hζ]) _)
    _ ≤ ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) * b := mul_le_mul_of_nonneg_right h1 hb
    _ = b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) := by ring

/-- The radial estimate `∫ χ(|ζ|) min(b, |ζ|) dζ ≤ σ_d (log(1 + T) + 1)` with `T = max 1 b` and
`σ_d = d ω_d`. -/
lemma ev_integral_chi_mul_min_le (hd : 3 ≤ d) {b : ℝ} (hb : 0 ≤ b) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), ev_chi d ‖ζ‖ * min b ‖ζ‖ ≤
      d * unitBallVolume d * (Real.log (1 + max 1 b) + 1) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set T : ℝ := max 1 b with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTb : b ≤ T := le_max_right _ _
  have hTpos : 0 < T := by linarith
  have hω := unitBallVolume_pos d
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => ev_chi d ‖ζ‖ * min b ‖ζ‖ with hf
  have hfm : Measurable f :=
    (ev_measurable_chi.comp measurable_norm).mul (measurable_const.min measurable_norm)
  have hf0 : ∀ ζ, 0 ≤ f ζ := fun ζ => mul_nonneg (ev_chi_nonneg _) (le_min hb (norm_nonneg ζ))
  obtain ⟨hI1, hJ1⟩ :=
    CERW.Generic.Kernel.integrableOn_ball_one_add_norm_rpow_and_integral_le (d := d)
      (by omega) hTpos
  obtain ⟨hI2, hJ2⟩ :=
    CERW.Generic.Kernel.integrableOn_compl_ball_rpow_neg_and_integral_eq (d := d)
      (s := 2 * (d : ℝ) - 2) (ρ := T) (by omega) (by linarith) hTpos
  have hfb : IntegrableOn f (Metric.ball 0 T) :=
    hI1.mono' hfm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball fun ζ _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ζ)]
        exact ev_chi_mul_min_le_near hd b ζ)
  have hfc : IntegrableOn f (Metric.ball 0 T)ᶜ :=
    (hI2.const_mul b).mono' hfm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball.compl fun ζ hζ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ζ)]
        have hζT : T ≤ ‖ζ‖ := by
          rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hζ
          exact hζ
        exact ev_chi_mul_min_le_far (by omega) hb (by linarith))
  have hfint : Integrable f := by
    have := hfb.union hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have hA : ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ ≤
      d * unitBallVolume d * Real.log (1 + T) :=
    (setIntegral_mono_on hfb hI1 measurableSet_ball fun ζ _ =>
      ev_chi_mul_min_le_near hd b ζ).trans hJ1
  have hexp : (d : ℝ) - (2 * (d : ℝ) - 2) ≤ -1 := by linarith
  have hbT : b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ 1 := by
    have h1 : T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ T ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT1 hexp
    rw [Real.rpow_neg_one] at h1
    calc b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ T * T⁻¹ :=
          mul_le_mul hTb h1 (Real.rpow_nonneg hTpos.le _) hTpos.le
      _ = 1 := mul_inv_cancel₀ hTpos.ne'
  have hB : ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ ≤
      d * unitBallVolume d := by
    have hdiv : (1 : ℝ) ≤ 2 * (d : ℝ) - 2 - d := by linarith
    calc ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ
        ≤ ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ,
            b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) :=
          setIntegral_mono_on hfc (hI2.const_mul b) measurableSet_ball.compl fun ζ hζ => by
            have hζT : T ≤ ‖ζ‖ := by
              rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hζ
              exact hζ
            exact ev_chi_mul_min_le_far (by omega) hb (by linarith)
      _ = b * (d * unitBallVolume d * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) /
            (2 * (d : ℝ) - 2 - d)) := by rw [integral_const_mul, hJ2]
      _ = d * unitBallVolume d * (b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2))) /
            (2 * (d : ℝ) - 2 - d) := by ring
      _ ≤ d * unitBallVolume d * 1 / (2 * (d : ℝ) - 2 - d) := by
          gcongr
      _ ≤ d * unitBallVolume d := by
          rw [mul_one, div_le_iff₀ (by linarith)]
          have : 0 ≤ (d : ℝ) * unitBallVolume d := by positivity
          calc (d : ℝ) * unitBallVolume d = d * unitBallVolume d * 1 := (mul_one _).symm
            _ ≤ d * unitBallVolume d * (2 * (d : ℝ) - 2 - d) :=
                mul_le_mul_of_nonneg_left hdiv this
  rw [← integral_add_compl measurableSet_ball hfint]
  calc (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ) +
        ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ
      ≤ d * unitBallVolume d * Real.log (1 + T) + d * unitBallVolume d := add_le_add hA hB
    _ = d * unitBallVolume d * (Real.log (1 + T) + 1) := by ring

end CERW.Support.Outer.Radius
