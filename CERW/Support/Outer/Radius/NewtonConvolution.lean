import CERW.Support.Outer.Radius.WeightedNewtonField

/-!
# Newton Convolution

Radial averaging bounds the convolution of the potential by its positive part. This gives the Newton
convolution estimate used outside the inner ball.
The retained labels `eq:newton-convolution`
refer to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

section

open CERW.Generic.Kernel CERW.Generic.Newton

/-- The mass of a radial weight in a centred ball lies between `0` and the total mass. -/
lemma nw_ball_weight_bounds {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) (s : ℝ) :
    0 ≤ ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ∧
      ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ≤
        ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ :=
  ⟨integral_nonneg fun _ => hχ0 _,
    setIntegral_le_integral hχi (Filter.Eventually.of_forall fun _ => hχ0 _)⟩

/-- Fubini and Newton's theorem for the radial weight, without a sign condition: the weighted
field potential of `F` for the field `u_v` has integral at most the total weight times the integral
over `F` of the positive part of `u_v · (v - y₀) |v - y₀|^{-d}`. -/
lemma nw_weighted_fieldPotential_le (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F)
    (hFfin : volume F ≠ ⊤) (y₀ : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d),
        χ ‖ζ‖ * ∫ v in F, inner ℝ (unitDir v) (newtonField (v - y₀ - ζ)) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
        ∫ v in F, max (inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d) 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hg : Measurable (unitDir : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    measurable_norm.inv.smul measurable_id
  have hI := nw_integrable_weight_fieldPair hd hχm hχ0 hM hχi hg norm_unitDir_le hFfin y₀
  have hcm : ∀ ζ : EuclideanSpace ℝ (Fin d),
      χ ‖ζ‖ * ∫ v in F, inner ℝ (unitDir v) (newtonField (v - y₀ - ζ)) =
        ∫ v in F, χ ‖ζ‖ * inner ℝ (unitDir v) (newtonField (v - y₀ - ζ)) := fun ζ =>
    (integral_const_mul _ _).symm
  simp_rw [hcm]
  rw [← integral_integral_swap (f := fun (v ζ : EuclideanSpace ℝ (Fin d)) =>
    χ ‖ζ‖ * inner ℝ (unitDir v) (newtonField (v - y₀ - ζ))) hI]
  have hgi : Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
        max (inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d) 0)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict F) :=
    ((CERW.Support.Geometry.integrableOn_potentialIntegrand (by omega) hF hFfin
      y₀).pos_part).const_mul _
  rw [← integral_const_mul]
  refine integral_mono_ae hI.integral_prod_left hgi ?_
  have hne : ∀ᵐ v : EuclideanSpace ℝ (Fin d), v ≠ y₀ := by
    rw [ae_iff]
    simp
  rw [Filter.EventuallyLE, ae_restrict_iff' hF]
  filter_upwards [hne] with v hv _
  rw [nw_integral_weight_inner_newtonField hd hχm hχ0 hM hχi (sub_ne_zero.mpr hv) (unitDir v)]
  obtain ⟨hm0, hm1⟩ := nw_ball_weight_bounds hχ0 hχi ‖v - y₀‖
  exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hm0).trans
    (mul_le_mul_of_nonneg_right hm1 (le_max_right _ _))

/-- `eq:newton-convolution` for a bounded integrable radial weight `χ ≥ 0`: the weighted potential
`∫ χ(|ζ|) U_D(y - ζ) dζ` is at most `(∫ χ(|ζ|) dζ) U_D^+(y)`. -/
lemma nw_weighted_potential_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * potential d ε D (y - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * positivePotential d ε D y := by
  have hle := nw_weighted_fieldPotential_le hd hχm hχ0 hM hχi hD hDfin y
  have hc : 0 ≤ 2 * ε / unitBallVolume d :=
    div_nonneg (mul_nonneg zero_le_two hε) (unitBallVolume_pos d).le
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun t =>
    χ ‖t‖ * ∫ v in D, inner ℝ (unitDir v) (newtonField (v - y - t)) with hh
  have hfun : (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * potential d ε D (y - ζ)) =
      fun ζ => (2 * ε / unitBallVolume d) * h (-ζ) := by
    funext ζ
    have hv : ∀ v : EuclideanSpace ℝ (Fin d), v - y - -ζ = v - (y - ζ) := fun v => by abel
    simp only [hh, potential, norm_neg, hv, inner_newtonField]
    ring
  rw [hfun, integral_const_mul, integral_neg_eq_self h volume]
  calc (2 * ε / unitBallVolume d) * ∫ t : EuclideanSpace ℝ (Fin d), h t
      ≤ (2 * ε / unitBallVolume d) * ((∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
          ∫ v in D, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0) :=
        mul_le_mul_of_nonneg_left hle hc
    _ = (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * positivePotential d ε D y := by
        rw [positivePotential]
        ring

/-- Newton's theorem for the radial convolution: `(χ * U_D)(y) ≤ ‖χ‖₁ U_D^+(y)`. -/
theorem newton_conv (hd : 3 ≤ d) : NewtonConv d := by
  intro ε hε D hD hDb y
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hexp : 2 - 2 * (d : ℝ) ≤ 0 := by linarith
  have hχm : Measurable (fun s : ℝ => (1 + |s|) ^ (2 - 2 * (d : ℝ))) := by fun_prop
  have hχ0 : ∀ s : ℝ, 0 ≤ (1 + |s|) ^ (2 - 2 * (d : ℝ)) := fun s =>
    Real.rpow_nonneg (add_nonneg zero_le_one (abs_nonneg s)) _
  have hχ1 : ∀ s : ℝ, (1 + |s|) ^ (2 - 2 * (d : ℝ)) ≤ 1 := fun s =>
    Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (abs_nonneg s)) hexp
  have hr : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < 2 * d - 2 := by
    rw [finrank_euclideanSpace_fin]
    linarith
  have he : (2 : ℝ) - 2 * d = -(2 * d - 2) := by ring
  have hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      (1 + |‖ζ‖|) ^ (2 - 2 * (d : ℝ))) := by
    simp only [abs_norm, he]
    exact integrable_one_add_norm hr
  have h := nw_weighted_potential_le (by omega) hε hχm hχ0 hχ1 hχi hD hDb.measure_lt_top.ne y
  simpa only [abs_norm] using h

/-! ### The envelope of the local times, `d ≥ 3` -/

end

end CERW.Support.Outer.Radius
