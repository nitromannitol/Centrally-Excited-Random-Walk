import CERW.Support.Outer.Radius.SphericalNewtonField

/-!
# Weighted Newton Field

Radial weights preserve integrability of the Newton field and its kernel. The weighted field
integral is computed by integration over balls.
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

/-- The weight `χ(|ζ|)` times the kernel `|a - ζ|^{1-d}` is integrable, with integral at most
`M d ω_d + ∫ χ(|ζ|) dζ`: inside the unit ball around `a` the weight is at most `M` and the kernel
has integral `d ω_d`, outside the kernel is at most one. -/
lemma nw_integrable_weight_mul_kernel (hd : 1 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (a : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤
        M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ := by
  obtain ⟨hint, hval⟩ := integrableOn_ball_and_integral_eq hd a one_pos
  have hind := hint.integrable_indicator (Metric.isOpen_ball.measurableSet)
  have hGi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖) :=
    (hind.const_mul M).add hχi
  have hmeas : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) :=
    (hχm.comp measurable_norm).mul ((measurable_const.sub measurable_id).norm.pow_const _)
  have hle : ∀ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤
      M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖ := by
    intro ζ
    have hk : 0 ≤ ‖a - ζ‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hsw : ‖a - ζ‖ = ‖ζ - a‖ := norm_sub_rev a ζ
    by_cases hζ : ζ ∈ Metric.ball a 1
    · rw [Set.indicator_of_mem hζ, ← hsw]
      have h1 : χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ M * ‖a - ζ‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (hM _) hk
      linarith [hχ0 ‖ζ‖]
    · rw [Set.indicator_of_notMem hζ]
      have hge : 1 ≤ ‖a - ζ‖ := by
        rw [hsw]
        simpa [Metric.mem_ball, dist_eq_norm] using hζ
      have hk1 : ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hge (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      have h1 : χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ χ ‖ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left hk1 (hχ0 _)
      linarith
  have hfi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) := by
    refine hGi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hχ0 _) (Real.rpow_nonneg (norm_nonneg _) _))]
    exact hle ζ
  refine ⟨hfi, ?_⟩
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d),
          (M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖) :=
        integral_mono hfi hGi hle
    _ = M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ := by
        rw [integral_add (hind.const_mul M) hχi, integral_const_mul,
          integral_indicator Metric.isOpen_ball.measurableSet, hval, mul_one]

/-- Pointwise bound of the radial weight times the field `⟨ξ, K(w - ζ)⟩` by `|ξ|` times the
weighted kernel `χ(|ζ|) |w - ζ|^{1-d}`. -/
lemma nw_norm_weight_inner_le (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (w ξ ζ : EuclideanSpace ℝ (Fin d)) :
    ‖χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))‖ ≤
      ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 _), Real.norm_eq_abs]
  have h1 : |inner ℝ ξ (newtonField (w - ζ))| ≤ ‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)) := by
    rw [← norm_newtonField hd]
    exact abs_real_inner_le_norm _ _
  calc χ ‖ζ‖ * |inner ℝ ξ (newtonField (w - ζ))|
      ≤ χ ‖ζ‖ * (‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := mul_le_mul_of_nonneg_left h1 (hχ0 _)
    _ = ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by ring

/-- The radial weight times the field `⟨ξ, K(w - ζ)⟩` is integrable. -/
lemma nw_integrable_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (w ξ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) := by
  have hk := (nw_integrable_weight_mul_kernel (by omega) hχm hχ0 hM hχi w).1
  have hmeas : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) :=
    (hχm.comp measurable_norm).mul
      (measurable_const.inner (measurable_newtonField.comp (measurable_const.sub measurable_id)))
  exact (hk.const_mul ‖ξ‖).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => nw_norm_weight_inner_le hd hχ0 w ξ ζ)

/-- The mass of a radial weight in a centred ball, in polar coordinates:
`∫_{B(0,s)} χ(|ζ|) dζ = d ω_d ∫_0^s r^{d-1} χ(r) dr`. -/
lemma nw_integral_ball_weight (hd : 1 ≤ d) (χ : ℝ → ℝ) (s : ℝ) :
    ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ =
      d * unitBallVolume d *
        ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * (Set.Iio s).indicator χ r := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s).indicator (fun ζ => χ ‖ζ‖) =
      fun ζ => (Set.Iio s).indicator χ ‖ζ‖ := by
    funext ζ
    by_cases hζ : ‖ζ‖ < s <;> simp [Set.indicator, hζ]
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, hind,
    integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))), hfin]
  simp only [unitBallVolume, Measure.real, nsmul_eq_mul, smul_eq_mul]
  ring

/-- Newton's theorem for a radial weight: for `w ≠ 0` and any vector `ξ`,
`∫ χ(|ζ|) ⟨ξ, K(w - ζ)⟩ dζ = (∫_{B(0,|w|)} χ(|ζ|) dζ) ⟨ξ, w⟩ / |w|^d`. -/
lemma nw_integral_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ)) =
      (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) *
        (inner ℝ ξ w / ‖w‖ ^ d) := by
  have hint := nw_integrable_weight_inner_newtonField hd hχm hχ0 hM hχi w ξ
  rw [integral_eq_integral_Ioi_sphere (by omega) hint, nw_integral_ball_weight (by omega)]
  have hae : ∀ᵐ r : ℝ ∂(volume : Measure ℝ), r ≠ ‖w‖ := by
    rw [ae_iff]
    simp
  have hpt : ∀ᵐ r : ℝ ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)),
      r ^ (d - 1) * ∫ θ, χ ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ *
          inner ℝ ξ (newtonField (w - r • (θ : EuclideanSpace ℝ (Fin d))))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        d * unitBallVolume d * (inner ℝ ξ w / ‖w‖ ^ d) *
          (r ^ (d - 1) * (Set.Iio ‖w‖).indicator χ r) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with r hr hr0
    have hr0' : 0 < r := hr0
    have hθ : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := fun θ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0', mem_sphere_zero_iff_norm.mp θ.2, mul_one]
    simp_rw [hθ]
    rw [integral_const_mul, nw_integral_sphere_inner_newtonField_vec hd hw hr0' hr.symm ξ]
    by_cases hlt : r < ‖w‖
    · simp only [hlt, if_true, Set.indicator_of_mem (Set.mem_Iio.mpr hlt)]
      ring
    · simp only [hlt, if_false, Set.indicator_of_notMem (mt Set.mem_Iio.mp hlt)]
      ring
  rw [integral_congr_ae hpt, integral_const_mul]
  ring

/-- For each position `v`, the radial weight times the field `⟨g(v), K(v - y₀ - ζ)⟩` is integrable
in `ζ`, uniformly in `v`, and jointly integrable in `(v, ζ)` over `F × ℝ^d` for a set `F` of finite
volume. -/
lemma nw_integrable_weight_fieldPair (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {F : Set (EuclideanSpace ℝ (Fin d))} (hFfin : volume F ≠ ⊤)
    (y₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y₀ - p.2)))
      (((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict F).prod volume) := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y₀ - p.2))) :=
    (hχm.comp measurable_snd.norm).mul ((hg.comp measurable_fst).inner
      (measurable_newtonField.comp ((measurable_fst.sub_const y₀).sub measurable_snd)))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun v =>
    nw_integrable_weight_inner_newtonField hd hχm hχ0 hM hχi (v - y₀) (g v), ?_⟩
  refine Integrable.mono' (integrableOn_const hFfin (C := Λ * (M * (d * unitBallVolume d) +
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖)))
    hmeas.norm.aestronglyMeasurable.integral_prod_right' (Filter.Eventually.of_forall fun v => ?_)
  obtain ⟨hki, hkle⟩ := nw_integrable_weight_mul_kernel (by omega) hχm hχ0 hM hχi (v - y₀)
  have hfi := nw_integrable_weight_inner_newtonField hd hχm hχ0 hM hχi (v - y₀) (g v)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ζ => norm_nonneg _)]
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), ‖χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y₀ - ζ))‖
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), Λ * (χ ‖ζ‖ * ‖v - y₀ - ζ‖ ^ (1 - (d : ℝ))) := by
        refine integral_mono hfi.norm (hki.const_mul Λ) fun ζ => ?_
        exact (nw_norm_weight_inner_le hd hχ0 (v - y₀) (g v) ζ).trans
          (mul_le_mul_of_nonneg_right (hΛ v) (mul_nonneg (hχ0 _) (Real.rpow_nonneg
            (norm_nonneg _) _)))
    _ = Λ * ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖v - y₀ - ζ‖ ^ (1 - (d : ℝ)) :=
        integral_const_mul _ _
    _ ≤ Λ * (M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hkle hΛ0

end

end CERW.Support.Outer.Radius
