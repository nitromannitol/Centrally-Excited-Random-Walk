import CERW.Support.Norm.RadialNewtonAE
import CERW.Frozen.NormBallPotential
import CERW.Model.NormPotential
import CERW.Generic.Norm.Gradient
import CERW.Generic.Norm.Sphere
import CERW.Generic.Norm.Subgradient
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The potential convolution at every point, and the contact convolution

`RadialNewtonAE.ae_integral_weight_smul_newtonField_eq_univ` is `eq:radial-convolution`
(`oct5.tex:759-762`, Newton's theorem for a nonnegative integrable radial function `χ`), valid for
Lebesgue almost every point. This module proves the three displays that follow it
(`oct5.tex:763-771`), which pass from the almost everywhere identity to the potential `U_D` of a
bounded measurable set `D`.

* `eq:newton-convolution`, for **every** `y ∈ ℝ^d`:
  `(χ * U_D)(y) = (2ε/ω_d) ∫_D ∇Ψ(v) · (v - y)/|v - y|^d m(|v - y|) dv`, where
  `m(s) = ∫_{|ζ| < s} χ`. The source obtains it from `eq:radial-convolution` with `v - y` in place
  of `y`, the symmetry of `χ` and Fubini's theorem, which applies because `χ` is integrable and
  `sup_w ∫_D |v - w|^{1-d} dv < ∞`. Here `integrable_prod_weight_kernel` proves that the product
  of the weight and the Newton kernel is integrable for the product of Lebesgue measure on `D` and
  Lebesgue measure on `ℝ^d`, from the uniform bound on the integral of the kernel over `D` and the
  integrability of `χ`; no bound and no moment is assumed on `χ`. The identity
  `eq:radial-convolution` is then used only for almost every `v ∈ D`, after the translation
  `v ↦ v - y` (which preserves Lebesgue measure), so the conclusion holds at the single point `y`:
  `integral_weight_field_eq` (a bounded measurable field in place of `∇Ψ`) and
  `normPotential_convolution_eq` (the potential of a norm).
* `eq:contact-convolution`: at a contact point `y₀` of `D` (`Ψ(y₀) = b` and `{Ψ < b} ⊆ D`), the
  integrand of `eq:newton-convolution` for `E = D ∖ {Ψ < b}` is nonnegative by the convexity
  inequality `eq:contact-convexity`, and `0 ≤ m ≤ ‖χ‖₁`; hence `(χ * U_E)(y₀) ≤ ‖χ‖₁ U_E(y₀)`, and
  `U_E(y₀) = U_D(y₀)` by `lem:ballpotential` (`contact_convolution_le`).
* The source takes for `χ` a nonnegative integrable radial function on `ℝ^d`. Such a function
  agrees, for Lebesgue almost every point, with a function of the norm with a Borel profile
  (`exists_borel_profile`); this changes neither the convolution nor `m`. So the two statements
  above hold for every nonnegative integrable radial function
  (`normPotential_convolution_eq_radial`, `contact_convolution_le_radial`,
  `convolution_normPotential_eq_radial`).
-/

open MeasureTheory
open scoped Topology

namespace CERW.Support.Norm.RadialNewtonConvolution

open CERW CERW.Generic.Kernel CERW.Generic.Norm

variable {d : ℕ}

/-! ## The integral of the radial weight over the ball -/

/-- The mass `s ↦ ∫_{|ζ| < s} χ(|ζ|) dζ` of a nonnegative radial weight is monotone, hence
measurable. -/
theorem measurable_ballMass {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) :
    Measurable (fun s : ℝ => ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖) := by
  refine Monotone.measurable fun s t hst => ?_
  exact setIntegral_mono_set hχi.integrableOn (Filter.Eventually.of_forall fun _ => hχ0 _)
    (Filter.Eventually.of_forall (Metric.ball_subset_ball hst))

/-- The mass of a nonnegative radial weight in a centred ball lies between `0` and the total
mass. -/
theorem ballMass_bounds {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) (s : ℝ) :
    0 ≤ ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ∧
      ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ≤
        ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ :=
  ⟨integral_nonneg fun _ => hχ0 _,
    setIntegral_le_integral hχi (Filter.Eventually.of_forall fun _ => hχ0 _)⟩

/-! ## Integrability of the weight times the Newton kernel on `D × ℝ^d` -/

/-- **The weight times the Newton kernel is integrable on `D × ℝ^d`.** Let `d ≥ 2`, let `χ` be a
nonnegative integrable radial weight, let `D` be a measurable set of finite volume, and let
`y ∈ ℝ^d`. The function `(v, ζ) ↦ χ(|ζ|) |v - y - ζ|^{1-d}` is integrable for the product of
Lebesgue measure on `D` and Lebesgue measure on `ℝ^d`. The slice over `D` at `ζ` has integral at
most `χ(|ζ|)` times the bound `d ω_d (|D|/ω_d)^{1/d}`, uniform in the centre `y + ζ`
(`CERW.Generic.Kernel.integrableOn_and_setIntegral_le`), and `χ` is integrable. -/
theorem integrable_prod_weight_kernel (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        χ ‖p.2‖ * ‖p.1 - y - p.2‖ ^ (1 - (d : ℝ)))
      ((volume.restrict D).prod volume) := by
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * ‖p.1 - y - p.2‖ ^ (1 - (d : ℝ))) :=
    (hχm.comp measurable_snd.norm).mul
      (((measurable_fst.sub_const y).sub measurable_snd).norm.pow_const _)
  have hslice : ∀ ζ : EuclideanSpace ℝ (Fin d),
      IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖v - y - ζ‖ ^ (1 - (d : ℝ))) D ∧
        ∫ v in D, χ ‖ζ‖ * ‖v - y - ζ‖ ^ (1 - (d : ℝ)) ≤
          χ ‖ζ‖ * newtonKernelVolumeBound D := by
    intro ζ
    obtain ⟨hint, hle⟩ :=
      CERW.Generic.Kernel.integrableOn_and_setIntegral_le (d := d) (by omega) hD hDfin (y + ζ)
    have hsub : ∀ v : EuclideanSpace ℝ (Fin d), v - y - ζ = v - (y + ζ) := fun v => by abel
    simp_rw [hsub]
    refine ⟨hint.const_mul (χ ‖ζ‖), ?_⟩
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hle (hχ0 _)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun ζ => (hslice ζ).1, ?_⟩
  have hbound : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * newtonKernelVolumeBound D) volume :=
    hχi.mul_const _
  refine hbound.mono'
    (((hmeas.aestronglyMeasurable.prod_swap).norm).integral_prod_right') ?_
  filter_upwards with ζ
  have hcongr : (∫ v in D, ‖χ ‖ζ‖ * ‖v - y - ζ‖ ^ (1 - (d : ℝ))‖)
      = ∫ v in D, χ ‖ζ‖ * ‖v - y - ζ‖ ^ (1 - (d : ℝ)) :=
    setIntegral_congr_fun hD fun v _ =>
      Real.norm_of_nonneg (mul_nonneg (hχ0 _) (Real.rpow_nonneg (norm_nonneg _) _))
  rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _), hcongr]
  exact (hslice ζ).2

/-- The weight times a bounded measurable field paired with the Newton field is integrable on
`D × ℝ^d`. -/
theorem integrable_prod_weight_field (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y - p.2)))
      ((volume.restrict D).prod volume) := by
  have hI := (integrable_prod_weight_kernel hd hχm hχ0 hχi hD hDfin y).const_mul Λ
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y - p.2))) :=
    (hχm.comp measurable_snd.norm).mul ((hg.comp measurable_fst).inner
      (measurable_newtonField.comp ((measurable_fst.sub_const y).sub measurable_snd)))
  refine hI.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [norm_mul, Real.norm_of_nonneg (hχ0 _)]
  calc χ ‖p.2‖ * ‖inner ℝ (g p.1) (newtonField (p.1 - y - p.2))‖
      ≤ χ ‖p.2‖ * (Λ * ‖p.1 - y - p.2‖ ^ (1 - (d : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (hχ0 _)
        rw [← norm_newtonField hd]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hΛ _) (norm_nonneg _))
    _ = Λ * (χ ‖p.2‖ * ‖p.1 - y - p.2‖ ^ (1 - (d : ℝ))) := by ring

/-! ## The identity at every point -/

/-- **`eq:newton-convolution` for a bounded measurable field, at every point.** Let `d ≥ 2`, let `χ`
be a nonnegative integrable radial weight (a measurable profile `χ : ℝ → ℝ`; no bound and no
moment), let `g` be a bounded measurable vector field, let `D` be a measurable set of finite
volume and let `y ∈ ℝ^d` be **any** point. Then `ζ ↦ χ(|ζ|) ∫_D ⟨g(v), K(v - y - ζ)⟩ dv` is
integrable and
`∫ χ(|ζ|) ∫_D ⟨g(v), K(v - y - ζ)⟩ dv dζ = ∫_D m(|v - y|) ⟨g(v), K(v - y)⟩ dv`,
with `K(x) = x/|x|^d` and `m(s) = ∫_{|ζ| < s} χ(|ζ|) dζ`. The proof applies the global almost
everywhere identity `eq:radial-convolution` of `RadialNewtonAE` after the translation `v ↦ v - y`,
for almost every `v ∈ D`, and Fubini's theorem. -/
theorem integral_weight_field_eq (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ∫ v in D, inner ℝ (g v) (newtonField (v - y - ζ))) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ∫ v in D, inner ℝ (g v) (newtonField (v - y - ζ)) =
      ∫ v in D, (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, χ ‖ζ‖) *
        inner ℝ (g v) (newtonField (v - y)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hI := integrable_prod_weight_field hd hχm hχ0 hχi hg hΛ hD hDfin y
  have hcm : ∀ ζ : EuclideanSpace ℝ (Fin d),
      χ ‖ζ‖ * ∫ v in D, inner ℝ (g v) (newtonField (v - y - ζ)) =
        ∫ v in D, χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y - ζ)) := fun ζ =>
    (integral_const_mul _ _).symm
  simp_rw [hcm]
  refine ⟨hI.integral_prod_right, ?_⟩
  rw [← integral_integral_swap (f := fun (v ζ : EuclideanSpace ℝ (Fin d)) =>
    χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y - ζ))) hI]
  refine integral_congr_ae ?_
  -- the almost every point statement of `eq:radial-convolution`, translated by `y`
  have hglob := ae_integral_weight_smul_newtonField_eq_univ hd hχm hχ0 hχi
  have hshift : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v - y ≠ 0 →
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ • newtonField (d := d) (v - y - ζ) =
        (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, χ ‖ζ‖) •
          ((‖v - y‖ ^ d)⁻¹ • (v - y)) :=
    (measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d)))
      y).quasiMeasurePreserving.ae hglob
  have hsliceInt := (integrable_prod_weight_kernel hd hχm hχ0 hχi hD hDfin y).prod_right_ae
  have hne : ∀ᵐ v : EuclideanSpace ℝ (Fin d), v ≠ y := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_of_ae hshift, hsliceInt, ae_restrict_of_ae hne] with v hv hvslice hvne
  have hw : v - y ≠ 0 := sub_ne_zero.mpr hvne
  have h1 : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖) := hχm.comp measurable_norm
  have h2 : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) => newtonField (d := d) (v - y - ζ)) :=
    measurable_newtonField.comp (measurable_const.sub measurable_id)
  have hvec : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ • newtonField (d := d) (v - y - ζ)) := by
    refine hvslice.mono' (h1.smul h2).aestronglyMeasurable ?_
    filter_upwards with ζ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 _), norm_newtonField hd]
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y - ζ))
      = ∫ ζ : EuclideanSpace ℝ (Fin d),
          inner ℝ (g v) (χ ‖ζ‖ • newtonField (d := d) (v - y - ζ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
        simp only [real_inner_smul_right]
    _ = inner ℝ (g v) (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ • newtonField (d := d) (v - y - ζ)) :=
        integral_inner hvec (g v)
    _ = (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, χ ‖ζ‖) *
          inner ℝ (g v) (newtonField (v - y)) := by
        rw [hv hw, real_inner_smul_right]
        rfl

/-! ## The potential of a norm -/

/-- The gradient of a norm is a measurable field. -/
theorem measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- For `d ≥ 1`, `Λ_Ψ ≥ 0`. -/
theorem normMax_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d) :
    0 ≤ normMax Ψ := by
  have h1 := normMin_pos_mul_le hΨ hd
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h2 := le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  have h3 := h1.2 (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h2 h3
  linarith [h1.1]

/-- The gradient of a norm has Euclidean norm at most `Λ_Ψ` everywhere: where `Ψ` is differentiable
it is a subgradient, and elsewhere it is `0`. -/
theorem norm_gradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
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

/-- **`eq:newton-convolution` for a norm, at every point.** Let `d ≥ 2`, let `Ψ` be a norm, let `ε`
be real, let `χ` be a nonnegative integrable radial weight (a measurable profile `χ : ℝ → ℝ`, no
bound and no moment), let `D` be a bounded measurable set, and let `y ∈ ℝ^d` be any point. Then
`ζ ↦ χ(|ζ|) U_D(y - ζ)` is integrable and
`(χ * U_D)(y) = (2ε/ω_d) ∫_D ∇Ψ(v) · (v - y)/|v - y|^d m(|v - y|) dv`
with `m(s) = ∫_{|ζ| < s} χ(|ζ|) dζ`. -/
theorem normPotential_convolution_eq (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (ε : ℝ) {χ : ℝ → ℝ} (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε Ψ D (y - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε Ψ D (y - ζ) =
      2 * ε / unitBallVolume d * ∫ v in D,
        inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d *
          ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, χ ‖ζ‖ := by
  obtain ⟨hint, heq⟩ := integral_weight_field_eq hd hχm hχ0 hχi (measurable_gradient Ψ)
    (norm_gradient_le hΨ (by omega)) hD hDb.measure_lt_top.ne y
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun t =>
    χ ‖t‖ * ∫ v in D, inner ℝ (gradient Ψ v) (newtonField (v - y - t)) with hh
  have hfun : (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε Ψ D (y - ζ)) =
      fun ζ => (2 * ε / unitBallVolume d) * h (-ζ) := by
    funext ζ
    have hv : ∀ v : EuclideanSpace ℝ (Fin d), v - y - -ζ = v - (y - ζ) := fun v => by abel
    simp only [hh, normPotential, norm_neg, hv, inner_newtonField]
    ring
  rw [hfun]
  refine ⟨(hint.comp_neg).const_mul _, ?_⟩
  rw [integral_const_mul, integral_neg_eq_self h volume, hh]
  simp only [hh] at heq
  rw [heq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [inner_newtonField]
  ring

/-! ## The contact convolution inequality -/

/-- The integrand `⟨g(v), v - y⟩/|v - y|^d` of a bounded measurable field is integrable on every
set of finite volume. -/
theorem integrableOn_field_kernel (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) D := by
  obtain ⟨hint, -⟩ := CERW.Generic.Kernel.integrableOn_and_setIntegral_le (d := d) (by omega)
    hD hDfin y
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
    measurable_id.sub measurable_const
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) :=
    (hg.inner hsub).div (hsub.norm.pow_const d)
  refine (hint.const_mul Λ).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  rw [← inner_newtonField, Real.norm_eq_abs]
  calc |inner ℝ (g v) (newtonField (v - y))|
      ≤ ‖g v‖ * ‖newtonField (v - y)‖ := abs_real_inner_le_norm _ _
    _ ≤ Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
        rw [norm_newtonField hd]
        exact mul_le_mul_of_nonneg_right (hΛ v) (Real.rpow_nonneg (norm_nonneg _) _)

/-- If `Ψ(y₀) ≤ Ψ(v)`, then `⟨∇Ψ(v), v - y₀⟩ ≥ 0`: Euler's relation `⟨∇Ψ(v), v⟩ = Ψ(v)` and the
subgradient bound `⟨∇Ψ(v), y₀⟩ ≤ Ψ(y₀)` where `Ψ` is differentiable, and `∇Ψ(v) = 0` elsewhere.
This is `eq:contact-convexity` of the source. -/
theorem inner_gradient_sub_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {v y₀ : EuclideanSpace ℝ (Fin d)} (h : Ψ y₀ ≤ Ψ v) :
    0 ≤ inner ℝ (gradient Ψ v) (v - y₀) := by
  by_cases hv : DifferentiableAt ℝ Ψ v
  · have h1 := subgradient_euler hΨ (gradient_isSubgradient hΨ hv)
    rw [inner_sub_right, h1.1]
    have := h1.2 y₀
    linarith
  · have h0 : gradient Ψ v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, inner_zero_left]

/-- The potential of a set splits over a measurable subset `B`: `U_D = U_B + U_{D \ B}`. -/
theorem normPotential_union_diff (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    (ε : ℝ) {D B : Set (EuclideanSpace ℝ (Fin d))} (hBD : B ⊆ D) (hBm : MeasurableSet B)
    (hDm : MeasurableSet D) (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ D y = normPotential d ε Ψ B y + normPotential d ε Ψ (D \ B) y := by
  have hg := measurable_gradient Ψ
  have hΛ := norm_gradient_le hΨ (by omega : 1 ≤ d)
  have hBfin : volume B ≠ ⊤ := (measure_mono hBD).trans_lt hDfin.lt_top |>.ne
  have hDBfin : volume (D \ B) ≠ ⊤ :=
    (measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top |>.ne
  unfold normPotential
  rw [← mul_add, ← setIntegral_union Set.disjoint_sdiff_right (hDm.diff hBm)
    (integrableOn_field_kernel hd hg hΛ hBm hBfin y)
    (integrableOn_field_kernel hd hg hΛ (hDm.diff hBm) hDBfin y), Set.union_sdiff_cancel hBD]

/-- **`eq:contact-convolution`.** Let `d ≥ 2`, let `Ψ` be a norm, `ε ≥ 0`, let `χ` be a nonnegative
integrable radial weight (a measurable profile; no bound and no moment), let `D` be a bounded
measurable set, let `b` be real with `{Ψ < b} ⊆ D`, and let `y₀` satisfy `Ψ(y₀) = b` (a contact
point).
With `E = D \ {Ψ < b}`, the function `ζ ↦ χ(|ζ|) U_E(y₀ - ζ)` is integrable,
`(χ * U_E)(y₀) ≤ ‖χ‖₁ U_D(y₀)`, and `U_E(y₀) = U_D(y₀)` (`lem:ballpotential`). The proof uses
`normPotential_convolution_eq` at the point `y₀`, the sign `⟨∇Ψ(v), v - y₀⟩ ≥ 0` on `E`
(`inner_gradient_sub_nonneg`, from `Ψ(y₀) = b ≤ Ψ(v)` there), and `0 ≤ m ≤ ‖χ‖₁`. -/
theorem contact_convolution_le (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 ≤ ε) {χ : ℝ → ℝ} (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    {b : ℝ} (hBD : {v | Ψ v < b} ⊆ D) {y₀ : EuclideanSpace ℝ (Fin d)}
    (hy₀ : Ψ y₀ = b) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * normPotential d ε Ψ (D \ {v | Ψ v < b}) (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε Ψ (D \ {v | Ψ v < b}) (y₀ - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * normPotential d ε Ψ D y₀ ∧
    normPotential d ε Ψ (D \ {v | Ψ v < b}) y₀ = normPotential d ε Ψ D y₀ := by
  have hBm : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} :=
    measurableSet_lt (norm_continuous hΨ).measurable measurable_const
  have hEm : MeasurableSet (D \ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b}) := hD.diff hBm
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hEfin : volume (D \ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b}) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top).ne
  have hsplit := normPotential_union_diff hd hΨ ε hBD hBm hD hDfin y₀
  have hU0 : normPotential d ε Ψ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} y₀ = 0 := by
    rcases lt_or_ge 0 b with hb | hb
    · rw [CERW.Frozen.norm_ball_potential hd hΨ ε hb y₀, hy₀]
      simp
    · have hempty : {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} = ∅ := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact hb.trans ((map_zero_nonneg_neg hΨ).2.1 v)
      rw [hempty]
      simp [normPotential]
  have hUE : normPotential d ε Ψ (D \ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b}) y₀ =
      normPotential d ε Ψ D y₀ := by
    rw [hsplit, hU0, zero_add]
  obtain ⟨hint, heq⟩ := normPotential_convolution_eq hd hΨ ε hχm hχ0 hχi hEm
    (hDb.subset Set.sdiff_subset) y₀
  refine ⟨hint, ?_, hUE⟩
  rw [heq, ← hUE]
  set E := D \ {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} with hE
  have hg := measurable_gradient Ψ
  have hΛ := norm_gradient_le hΨ (by omega : 1 ≤ d)
  have hq := integrableOn_field_kernel hd hg hΛ hEm hEfin y₀
  have hm := measurable_ballMass hχ0 hχi
  have hpos : ∀ v ∈ E, 0 ≤ inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d := fun v hv =>
    div_nonneg (inner_gradient_sub_nonneg hΨ (by
      have : ¬ Ψ v < b := hv.2
      rw [hy₀]
      exact not_lt.mp this)) (pow_nonneg (norm_nonneg _) _)
  have hqm : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d *
        ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y₀‖, χ ‖ζ‖) E := by
    refine Integrable.mul_bdd (c := ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) hq
      (hm.comp (measurable_id.sub measurable_const).norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    obtain ⟨h0, h1⟩ := ballMass_bounds hχ0 hχi ‖v - y₀‖
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have hle : ∫ v in E, inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d *
        ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y₀‖, χ ‖ζ‖ ≤
      ∫ v in E, (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
        (inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d) := by
    refine setIntegral_mono_on hqm (hq.const_mul _) hEm fun v hv => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (ballMass_bounds hχ0 hχi _).2 (hpos v hv)
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  unfold normPotential
  calc 2 * ε / unitBallVolume d * ∫ v in E, inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d *
        ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y₀‖, χ ‖ζ‖
      ≤ 2 * ε / unitBallVolume d * ∫ v in E, (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
          (inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d) :=
        mul_le_mul_of_nonneg_left hle hc
    _ = (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
          (2 * ε / unitBallVolume d *
            ∫ v in E, inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d) := by
        rw [integral_const_mul]
        ring

/-! ## A nonnegative integrable radial function has a Borel profile -/

/-- **Borel profile of a radial function.** The source takes for `χ` a nonnegative integrable
radial function on `ℝ^d`: `f x = f y` whenever `|x| = |y|`, with no measurability assumed on the
function `r ↦ f(r e₀)` of the radius. Its integrability makes `f` almost everywhere strongly
measurable, and in polar coordinates (Lebesgue measure is `σ ⊗ r^{d-1} dr`) the function
`(θ, r) ↦ f(rθ) = f(r e₀)` depends on `r` alone, so its section at one `θ` is almost everywhere
strongly measurable for `r^{d-1} dr`. Hence there is a Borel function `χ : ℝ → ℝ`, nonnegative,
with `f(ζ) = χ(|ζ|)` for Lebesgue almost every `ζ`. -/
theorem exists_borel_profile (hd : 2 ≤ d) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hrad : ∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) :
    ∃ χ : ℝ → ℝ, Measurable χ ∧ (∀ s, 0 ≤ χ s) ∧
      ∀ᵐ ζ : EuclideanSpace ℝ (Fin d) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        f ζ = χ ‖ζ‖ := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  set e₀ : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, by omega⟩ 1 with he₀
  have he₀n : ‖e₀‖ = 1 := by simp [he₀, PiLp.norm_single]
  set χ₀ : ℝ → ℝ := fun r => f (r • e₀) with hχ₀
  have hfeq : ∀ x, f x = χ₀ ‖x‖ := fun x =>
    hrad x _ (by rw [norm_smul, he₀n, Real.norm_eq_abs, abs_norm, mul_one])
  have hχ₀0 : ∀ r, 0 ≤ χ₀ r := fun r => hf0 _
  -- the polar form of `f` is integrable, hence has almost everywhere strongly measurable sections
  have hG := CERW.Generic.Newton.integrable_prod_polar hfi
  have hμ : (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere ≠ 0 := by
    intro h
    have h1 := Measure.toSphere_apply_univ (volume : Measure (EuclideanSpace ℝ (Fin d)))
    rw [h, finrank_euclideanSpace_fin] at h1
    simp only [Measure.coe_zero, Pi.zero_apply] at h1
    have hpos : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
      (Metric.measure_ball_pos volume _ one_pos).ne'
    exact mul_ne_zero (by exact_mod_cast (by omega : d ≠ 0)) hpos h1.symm
  haveI := ae_neBot.2 hμ
  obtain ⟨θ, hθ⟩ := hG.aestronglyMeasurable.prodMk_left.exists
  have hsec : AEStronglyMeasurable (fun r : Set.Ioi (0 : ℝ) => χ₀ r.1)
      (Measure.volumeIoiPow (d - 1)) := by
    refine hθ.congr (Filter.Eventually.of_forall fun r => ?_)
    have hr : ‖r.1 • (θ : EuclideanSpace ℝ (Fin d))‖ = r.1 := by
      rw [norm_smul, mem_sphere_zero_iff_norm.mp θ.2, mul_one, Real.norm_eq_abs,
        abs_of_pos r.2]
    show f (r.1 • (θ : EuclideanSpace ℝ (Fin d))) = χ₀ r.1
    rw [hfeq, hr]
  set φ : Set.Ioi (0 : ℝ) → ℝ := hsec.mk _ with hφ
  have hφm : Measurable φ := hsec.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ r ∂(Measure.volumeIoiPow (d - 1)), χ₀ r.1 = φ r := hsec.ae_eq_mk
  let χ : ℝ → ℝ := fun r => if hr : r ∈ Set.Ioi (0 : ℝ) then max (φ ⟨r, hr⟩) 0 else 0
  have hχm : Measurable χ :=
    Measurable.dite (f := fun r : Set.Ioi (0 : ℝ) => max (φ r) 0) (hφm.max measurable_const)
      (g := fun _ => (0 : ℝ)) measurable_const measurableSet_Ioi
  have hχ0 : ∀ s, 0 ≤ χ s := fun s => by
    by_cases hs : s ∈ Set.Ioi (0 : ℝ)
    · simp only [χ, dif_pos hs]
      exact le_max_right _ _
    · simp only [χ, dif_neg hs]
      exact le_rfl
  refine ⟨χ, hχm, hχ0, ?_⟩
  -- transport the almost everywhere equality of the sections through the polar coordinates
  have hprod : ∀ᵐ p ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
      (Measure.volumeIoiPow (d - 1))), χ₀ p.2.1 = φ p.2 :=
    (Measure.quasiMeasurePreserving_snd).ae hae
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure (EuclideanSpace ℝ (Fin d)))
  rw [hfin] at hmp
  have hcomap := hmp.quasiMeasurePreserving.ae hprod
  have hsub : ∀ᵐ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin d)))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).comap (↑)), f x.1 = χ ‖x.1‖ := by
    filter_upwards [hcomap] with x hx
    have hx0 : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 x.2
    have hpos : 0 < ‖x.1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
    have hsnd : ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d))) x).2 =
        ⟨‖x.1‖, hpos⟩ :=
      Subtype.ext (by simp [homeomorphUnitSphereProd_apply_snd_coe])
    rw [hsnd] at hx
    have hx' : χ₀ ‖x.1‖ = φ ⟨‖x.1‖, hpos⟩ := hx
    rw [hfeq x.1]
    simp only [χ, dif_pos (show ‖x.1‖ ∈ Set.Ioi (0 : ℝ) from hpos)]
    rw [← hx']
    exact (max_eq_left (hχ₀0 _)).symm
  have hres := (ae_restrict_iff_subtype
    (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin d))).compl
    (p := fun x => f x = χ ‖x‖)).2 hsub
  rwa [restrict_compl_singleton] at hres

/-! ## The identities for every nonnegative integrable radial function -/

/-- The mass of a radial function in a centred ball does not depend on the choice of the profile:
almost everywhere equal weights have equal masses. -/
theorem ballMass_congr {f : EuclideanSpace ℝ (Fin d) → ℝ} {χ : ℝ → ℝ}
    (hae : ∀ᵐ ζ : EuclideanSpace ℝ (Fin d) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      f ζ = χ ‖ζ‖) (s : ℝ) :
    ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, f ζ =
      ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ :=
  integral_congr_ae (ae_restrict_of_ae hae)

/-- **`eq:newton-convolution` for every nonnegative integrable radial function, at every point.**
Let `d ≥ 2`, let `Ψ` be a norm, let `ε` be real, let `f : ℝ^d → ℝ` be nonnegative, integrable and
radial (`f x = f y` whenever `|x| = |y|`; no measurable profile, no bound, no moment), let `D` be a
bounded measurable set and let `y ∈ ℝ^d` be any point. Then `ζ ↦ f(ζ) U_D(y - ζ)` is integrable and
`(f * U_D)(y) = (2ε/ω_d) ∫_D ∇Ψ(v) · (v - y)/|v - y|^d m(|v - y|) dv`, `m(s) = ∫_{|ζ| < s} f`. -/
theorem normPotential_convolution_eq_radial (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (ε : ℝ) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hrad : ∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => f ζ * normPotential d ε Ψ D (y - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), f ζ * normPotential d ε Ψ D (y - ζ) =
      2 * ε / unitBallVolume d * ∫ v in D,
        inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d *
          ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, f ζ := by
  obtain ⟨χ, hχm, hχ0, hae⟩ := exists_borel_profile hd hrad hf0 hfi
  have hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖) := hfi.congr hae
  obtain ⟨hint, heq⟩ := normPotential_convolution_eq hd hΨ ε hχm hχ0 hχi hD hDb y
  have hcongr : (fun ζ : EuclideanSpace ℝ (Fin d) => f ζ * normPotential d ε Ψ D (y - ζ)) =ᵐ[volume]
      fun ζ => χ ‖ζ‖ * normPotential d ε Ψ D (y - ζ) :=
    hae.mono fun ζ h => by simp only [h]
  refine ⟨hint.congr hcongr.symm, ?_⟩
  rw [integral_congr_ae hcongr, heq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [ballMass_congr hae]

/-- **`eq:contact-convolution` for every nonnegative integrable radial function.** The statement
of `contact_convolution_le` for a nonnegative integrable radial function `f : ℝ^d → ℝ`. -/
theorem contact_convolution_le_radial (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 ≤ ε) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hrad : ∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {b : ℝ} (hBD : {v | Ψ v < b} ⊆ D)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : Ψ y₀ = b) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      f ζ * normPotential d ε Ψ (D \ {v | Ψ v < b}) (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), f ζ * normPotential d ε Ψ (D \ {v | Ψ v < b}) (y₀ - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) * normPotential d ε Ψ D y₀ ∧
    normPotential d ε Ψ (D \ {v | Ψ v < b}) y₀ = normPotential d ε Ψ D y₀ := by
  obtain ⟨χ, hχm, hχ0, hae⟩ := exists_borel_profile hd hrad hf0 hfi
  have hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖) := hfi.congr hae
  obtain ⟨hint, hle, hUE⟩ := contact_convolution_le hd hΨ hε hχm hχ0 hχi hD hDb hBD hy₀
  have hcongr : (fun ζ : EuclideanSpace ℝ (Fin d) =>
      f ζ * normPotential d ε Ψ (D \ {v | Ψ v < b}) (y₀ - ζ)) =ᵐ[volume]
      fun ζ => χ ‖ζ‖ * normPotential d ε Ψ (D \ {v | Ψ v < b}) (y₀ - ζ) :=
    hae.mono fun ζ h => by simp only [h]
  refine ⟨hint.congr hcongr.symm, ?_, hUE⟩
  rw [integral_congr_ae hcongr, integral_congr_ae hae]
  exact hle

/-- **`eq:newton-convolution` in the form of the convolution of Mathlib.** The convolution
`(f * U_D)(y) = ∫ f(ζ) U_D(y - ζ) dζ` of a nonnegative integrable radial function with the potential
of a bounded measurable set, at every point. -/
theorem convolution_normPotential_eq_radial (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (ε : ℝ) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hrad : ∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) (y : EuclideanSpace ℝ (Fin d)) :
    convolution f (normPotential d ε Ψ D) (ContinuousLinearMap.mul ℝ ℝ) volume y =
      2 * ε / unitBallVolume d * ∫ v in D,
        inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d *
          ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, f ζ := by
  rw [convolution_def]
  exact (normPotential_convolution_eq_radial hd hΨ ε hrad hf0 hfi hD hDb y).2

end CERW.Support.Norm.RadialNewtonConvolution
