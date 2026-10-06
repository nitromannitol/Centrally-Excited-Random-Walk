/-
# The radial Newton convolution with an unrestricted nonnegative radial weight

`CERW.Support.Norm.integral_weight_inner_newtonField` (`ContactPotential.lean`) proves the scalar
radial Newton convolution identity for a radial weight `χ` that carries a global bound
`hM : ∀ s, χ s ≤ M`.  The source (`oct5.tex:755-768`, `eq:radial-convolution`) instead takes only a
nonnegative integrable radial weight, and asserts the vector identity for almost every spatial
point.  This module supplies the analytic first stage of that statement: on every measurable set
of finite volume, and so in particular on every bounded ball, the joint function
`(w, ζ) ↦ χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - d)` is integrable for the product measure with the unrestricted
weight.

The key input is the uniform bound `CERW.Generic.Kernel.integrableOn_and_setIntegral_le`: for a
measurable `D` of finite volume and every centre `y`, `∫_D ‖v - y‖ ^ (1 - d) ≤ σ_d (|D|/ω_d)^{1/d}`,
with a constant that does not depend on `y`.  Joint integrability is then Fubini applied to the
product of `volume.restrict D` with `volume`; the almost-everywhere slice integrability is the
right-hand marginal of that product integral.
-/
import CERW.Support.Norm.RadialNewtonLocalEstimate
import CERW.Generic.Kernel.Integrable
import CERW.Generic.Kernel.Modulus
import CERW.Generic.Newton.Polar
import CERW.Model.Space
import CERW.Support.Geometry.Newton
import CERW.Support.Geometry.Bound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped Pointwise Topology

namespace CERW.Support.Norm

/-- The uniform bound on the integral of the Newton kernel over a set of finite volume:
`Λ = d ω_d (|D| / ω_d)^{1/d}`.  It bounds `∫_D ‖v - y‖ ^ (1 - d) dv` for every centre `y`. -/
noncomputable def newtonKernelVolumeBound {d : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (d : ℝ) * CERW.unitBallVolume d *
    ((volume D).toReal / CERW.unitBallVolume d) ^ ((1 : ℝ) / d)

/-- The uniform kernel bound is nonnegative. -/
theorem newtonKernelVolumeBound_nonneg {d : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin d))) : 0 ≤ newtonKernelVolumeBound D := by
  unfold newtonKernelVolumeBound
  have hω := CERW.unitBallVolume_pos d
  positivity

/-- **Weighted Newton kernel on a set of finite volume.**  For `d ≥ 2`, a nonnegative integrable
radial weight `χ` and a measurable set `D` of finite volume, the function
`v ↦ χ ‖y‖ * ‖v - y‖ ^ (1 - d)` is integrable on `D` for every centre `y`, and its integral is at
most `χ ‖y‖` times the uniform kernel bound `newtonKernelVolumeBound D`.  No bound is imposed on
`χ`. -/
theorem integrableOn_weight_mul_newtonKernel {d : ℕ} (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχ0 : ∀ s, 0 ≤ χ s)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => χ ‖y‖ * ‖v - y‖ ^ (1 - (d : ℝ))) D ∧
      ∫ v in D, χ ‖y‖ * ‖v - y‖ ^ (1 - (d : ℝ)) ≤
        χ ‖y‖ * newtonKernelVolumeBound D := by
  obtain ⟨hint, hle⟩ :=
    CERW.Generic.Kernel.integrableOn_and_setIntegral_le (d := d) (by omega) hD hDfin y
  refine ⟨hint.const_mul (χ ‖y‖), ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hle (hχ0 _)

/-- **Joint integrability of the weighted Newton kernel.**  For `d ≥ 2`, a nonnegative integrable
radial weight `χ` and a measurable set `D` of finite volume, the function
`(w, ζ) ↦ χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - d)` is integrable for `(volume.restrict D).prod volume`: the
Fubini hypothesis of the radial Newton convolution holds with the unrestricted weight. -/
theorem integrable_weight_newtonKernel_prod {d : ℕ} (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        χ ‖p.2‖ * ‖p.1 - p.2‖ ^ (1 - (d : ℝ)))
      ((volume.restrict D).prod volume) := by
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * ‖p.1 - p.2‖ ^ (1 - (d : ℝ))) :=
    (hχm.comp measurable_snd.norm).mul
      ((measurable_fst.sub measurable_snd).norm.pow_const _)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun ζ =>
    (integrableOn_weight_mul_newtonKernel hd hχ0 hD hDfin ζ).1, ?_⟩
  have hbound : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * newtonKernelVolumeBound D) volume :=
    hχi.mul_const _
  refine hbound.mono'
    (((hmeas.aestronglyMeasurable.prod_swap).norm).integral_prod_right') ?_
  filter_upwards with ζ
  have hslice := (integrableOn_weight_mul_newtonKernel hd hχ0 hD hDfin ζ).2
  have hcongr : (∫ w in D, ‖χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))‖)
      = ∫ w in D, χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)) :=
    setIntegral_congr_fun hD fun w _ =>
      Real.norm_of_nonneg (mul_nonneg (hχ0 _) (Real.rpow_nonneg (norm_nonneg _) _))
  rw [Real.norm_of_nonneg (integral_nonneg fun w => norm_nonneg _), hcongr]
  exact hslice

/-- **Almost-everywhere integrability of the weighted Newton kernel.**  For `d ≥ 2` and a
nonnegative integrable radial weight `χ`, for almost every `w` in any measurable set `D` of finite
volume the slice `ζ ↦ χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - d)` is integrable.  This is the almost-everywhere
integrability input of the radial Newton identity; the exceptional set is the complement of the
right-hand marginal of the product integral of `integrable_weight_newtonKernel_prod`. -/
theorem ae_integrable_weight_newtonKernel {d : ℕ} (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) :
    ∀ᵐ w ∂(volume.restrict D),
      Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)))
        volume :=
  (integrable_weight_newtonKernel_prod hd hχm hχ0 hχi hD hDfin).prod_right_ae

/-- **Almost-everywhere integrability of the weighted Newton field.**  For `d ≥ 2`, a nonnegative
integrable radial weight `χ` and a measurable set `D` of finite volume, for almost every `w ∈ D`
the vector-valued slice `ζ ↦ χ ‖ζ‖ • newtonField (w - ζ)` is integrable.  Its norm is the scalar
slice of `ae_integrable_weight_newtonKernel`, by `norm_newtonField`. -/
theorem ae_integrable_weight_smul_newtonField {d : ℕ} (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) :
    ∀ᵐ w ∂(volume.restrict D),
      Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
        (χ ‖ζ‖ : ℝ) • CERW.Generic.Kernel.newtonField (d := d) (w - ζ))
        volume := by
  filter_upwards [ae_integrable_weight_newtonKernel hd hχm hχ0 hχi hD hDfin] with w hw
  have h1 : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖) :=
    hχm.comp measurable_norm
  have h2 : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      CERW.Generic.Kernel.newtonField (d := d) (w - ζ)) :=
    CERW.Generic.Kernel.measurable_newtonField.comp (measurable_const.sub measurable_id)
  refine hw.mono' (h1.smul h2).aestronglyMeasurable ?_
  filter_upwards with ζ
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 _),
    CERW.Generic.Kernel.norm_newtonField hd]

/-!
# Bounded radial Newton identity (copied provenance)

The lemmas below are the bounded-weight scalar radial Newton identity of
`CERW/Support/Norm/ContactPotential.lean` (namespace `CERW.Support.Norm.ContactConv`, private),
copied verbatim modulo the enclosing namespace so that the almost-everywhere truncation argument
below can consume the completed bounded identity.  Provenance: `ContactPotential.lean` lines
1985-2312; only the enclosing namespace changed.
-/
namespace RadialBounded

open MeasureTheory CERW CERW.Generic.Kernel CERW.Support.Geometry CERW.Generic.Newton

variable {d : ℕ}
noncomputable def sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  ⟨A θ, by simp⟩

/-- The action of a linear isometry on the unit sphere is measurable. -/
lemma measurable_sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measurable (sphereMap A) :=
  ((A.continuous.comp continuous_subtype_val).subtype_mk _).measurable

/-- Surface measure on the unit sphere is invariant under linear isometries. -/
lemma map_sphereMap_toSphere
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measure.map (sphereMap A) (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  ext S hS
  rw [Measure.map_apply (measurable_sphereMap A) hS,
    Measure.toSphere_apply' _ ((measurable_sphereMap A) hS), Measure.toSphere_apply' _ hS]
  congr 1
  have hset : Set.Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap A ⁻¹' S) : Set (EuclideanSpace ℝ (Fin d))) =
      A ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨sphereMap A θ, hθ, rfl⟩, ?_⟩
      simp [sphereMap]
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, h⟩
      refine ⟨t, ht, _, ⟨⟨A.symm θ, by simp⟩, ?_, rfl⟩, ?_⟩
      · simpa [sphereMap] using hθ
      · have h' : t • (θ : EuclideanSpace ℝ (Fin d)) = A x := h
        show t • A.symm (θ : EuclideanSpace ℝ (Fin d)) = x
        rw [← A.symm.map_smul, h', A.symm_apply_apply]
  rw [hset]
  exact (LinearIsometryEquiv.measurePreserving A).measure_preimage_equiv
    (f := A.toMeasurableEquiv) _

/-- Integrals over the unit sphere are invariant under linear isometries. -/
lemma integral_sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {f : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ} (hf : Measurable f) :
    ∫ θ, f (sphereMap A θ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ θ, f θ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have h := integral_map (measurable_sphereMap A).aemeasurable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (f := f)
    (by rw [map_sphereMap_toSphere]; exact hf.aestronglyMeasurable)
  rw [map_sphereMap_toSphere] at h
  exact h.symm

/-- The Newtonian field commutes with linear isometries. -/
lemma newtonField_map (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : newtonField (A x) = A (newtonField x) := by
  simp only [newtonField, A.norm_map, LinearIsometryEquiv.map_smul]

/-- The sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is measurable. -/
lemma measurable_inner_newtonField (ξ v : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))) :=
  measurable_const.inner (measurable_newtonField.comp
    (measurable_const.sub (measurable_subtype_coe.const_smul s)))

/-- The component of the spherical average of the Newtonian field orthogonal to `v` vanishes:
a reflection fixing `v` and reversing `w ⟂ v` preserves surface measure. -/
lemma integral_sphere_inner_newtonField_perp {v w : EuclideanSpace ℝ (Fin d)}
    (hvw : inner ℝ w v = 0) (s : ℝ) :
    ∫ θ, inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere = 0 := by
  set R := Submodule.reflection (ℝ ∙ w)ᗮ with hR
  have hRv : R v = v :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hvw)
  have hRw : R w = -w := Submodule.reflection_orthogonalComplement_singleton_eq_neg w
  have h := integral_sphereMap R (measurable_inner_newtonField w v s)
  have hpt : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ w (newtonField (v - s • (sphereMap R θ : EuclideanSpace ℝ (Fin d)))) =
        -inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    intro θ
    have h1 : v - s • (sphereMap R θ : EuclideanSpace ℝ (Fin d)) =
        R (v - s • (θ : EuclideanSpace ℝ (Fin d))) := by
      rw [R.map_sub, R.map_smul, hRv]
      rfl
    rw [h1, newtonField_map, ← R.inner_map_map w, hRw, hR, Submodule.reflection_reflection,
      inner_neg_left]
  simp_rw [hpt, integral_neg] at h
  linarith

/-- The Newtonian field is continuous away from the origin. -/
lemma continuousAt_newtonField_of_ne {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    ContinuousAt (newtonField : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) x :=
  ((continuous_norm.pow d).continuousAt.inv₀
    (pow_ne_zero d (norm_ne_zero_iff.mpr hx))).smul continuousAt_id

/-- For `|v| ≠ s` the sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is integrable, being continuous on a
compact space. -/
lemma integrable_inner_newtonField (ξ : EuclideanSpace ℝ (Fin d))
    {v : EuclideanSpace ℝ (Fin d)} {s : ℝ} (hs : 0 < s) (hvs : ‖v‖ ≠ s) :
    Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))))
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  haveI : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hcont : Continuous (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      simp
    have hne : v - s • (θ : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro h
      have hv : v = s • (θ : EuclideanSpace ℝ (Fin d)) := sub_eq_zero.mp h
      apply hvs
      rw [hv, norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hs, mul_one]
    have hc : ContinuousAt (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        v - s • (θ : EuclideanSpace ℝ (Fin d))) θ :=
      continuousAt_const.sub (continuousAt_subtype_val.const_smul s)
    exact ContinuousAt.comp_of_eq (g := newtonField)
      (f := fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        v - s • (θ : EuclideanSpace ℝ (Fin d))) (continuousAt_newtonField_of_ne hne) hc rfl
  exact Continuous.integrable_of_hasCompactSupport (continuous_const.inner hcont)
    (HasCompactSupport.of_compactSpace _)

/-- The kernel average `eq:kernel-average` against an arbitrary vector `ξ`: for `v ≠ 0`, `s > 0` and
`|v| ≠ s`, `∫_S ξ · K(v - sθ) dσ(θ) = σ_d |v|^{-d} (ξ · v) 1{s < |v|}`. -/
lemma integral_sphere_inner_newtonField_vec (hd : 2 ≤ d)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) {s : ℝ} (hs : 0 < s) (hvs : ‖v‖ ≠ s)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ θ, inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      if s < ‖v‖ then d * unitBallVolume d * (inner ℝ ξ v / ‖v‖ ^ d) else 0 := by
  have hrpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvv : inner ℝ v v = ‖v‖ * ‖v‖ := real_inner_self_eq_norm_mul_norm v
  set a : ℝ := inner ℝ ξ (unitDir v) with ha_def
  have ha : a = ‖v‖⁻¹ * inner ℝ ξ v := by
    rw [ha_def, unitDir, real_inner_smul_right]
  set w : EuclideanSpace ℝ (Fin d) := ξ - a • unitDir v with hw_def
  have hperp : inner ℝ w v = 0 := by
    rw [hw_def, inner_sub_left, real_inner_smul_left, unitDir, real_inner_smul_left, hvv, ha]
    field_simp
    ring
  have hdecomp : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) =
        a * inner ℝ (unitDir v) (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) +
          inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    intro θ
    rw [hw_def, inner_sub_left, real_inner_smul_left]
    ring
  simp_rw [hdecomp]
  rw [integral_add ((integrable_inner_newtonField (unitDir v) hs hvs).const_mul a)
    (integrable_inner_newtonField w hs hvs), integral_const_mul,
    integral_sphere_inner_newtonField hd hv hs hvs, integral_sphere_inner_newtonField_perp hperp,
    add_zero]
  split_ifs
  · rw [ha, ← div_pow_eq_rpow_sub hrpos d]
    field_simp
  · simp


/-- The weight `χ(|ζ|)` times the kernel `|a - ζ|^{1-d}` is integrable, with integral at most
`M d ω_d + ∫ χ(|ζ|) dζ`: inside the unit ball around `a` the weight is at most `M` and the kernel
has integral `d ω_d`, outside the kernel is at most one. -/
lemma integrable_weight_mul_kernel (hd : 1 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
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
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ0 _) (Real.rpow_nonneg (norm_nonneg _) _))]
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
lemma norm_weight_inner_le (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (w ξ ζ : EuclideanSpace ℝ (Fin d)) :
    ‖χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))‖ ≤ ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 _), Real.norm_eq_abs]
  have h1 : |inner ℝ ξ (newtonField (w - ζ))| ≤ ‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)) := by
    rw [← norm_newtonField hd]
    exact abs_real_inner_le_norm _ _
  calc χ ‖ζ‖ * |inner ℝ ξ (newtonField (w - ζ))|
      ≤ χ ‖ζ‖ * (‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := mul_le_mul_of_nonneg_left h1 (hχ0 _)
    _ = ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by ring

/-- The radial weight times the field `⟨ξ, K(w - ζ)⟩` is integrable. -/
lemma integrable_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (w ξ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) := by
  have hk := (integrable_weight_mul_kernel (by omega) hχm hχ0 hM hχi w).1
  have hmeas : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) :=
    (hχm.comp measurable_norm).mul
      (measurable_const.inner (measurable_newtonField.comp (measurable_const.sub measurable_id)))
  exact (hk.const_mul ‖ξ‖).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => norm_weight_inner_le hd hχ0 w ξ ζ)

/-- The mass of a radial weight in a centred ball, in polar coordinates:
`∫_{B(0,s)} χ(|ζ|) dζ = d ω_d ∫_0^s r^{d-1} χ(r) dr`. -/
lemma integral_ball_weight (hd : 1 ≤ d) (χ : ℝ → ℝ) (s : ℝ) :
    ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ =
      d * unitBallVolume d * ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * (Set.Iio s).indicator χ r := by
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
lemma integral_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ)) =
      (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) *
        (inner ℝ ξ w / ‖w‖ ^ d) := by
  have hint := integrable_weight_inner_newtonField hd hχm hχ0 hM hχi w ξ
  rw [integral_eq_integral_Ioi_sphere (by omega) hint, integral_ball_weight (by omega)]
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
    rw [integral_const_mul, integral_sphere_inner_newtonField_vec hd hw hr0' hr.symm ξ]
    by_cases hlt : r < ‖w‖
    · simp only [hlt, if_true, Set.indicator_of_mem (Set.mem_Iio.mpr hlt)]
      ring
    · simp only [hlt, if_false, Set.indicator_of_notMem (mt Set.mem_Iio.mp hlt)]
      ring
  rw [integral_congr_ae hpt, integral_const_mul]
  ring
end RadialBounded

open Filter CERW CERW.Generic.Kernel

/-- The truncation `s ↦ min (χ s) n` of a nonnegative integrable radial weight is integrable. -/
theorem integrable_min_weight {d : ℕ} {χ : ℝ → ℝ} (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) (n : ℕ) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => min (χ ‖ζ‖) (n : ℝ)) := by
  refine hχi.mono' (((hχm.comp measurable_norm).min measurable_const).aestronglyMeasurable) ?_
  filter_upwards with ζ
  rw [Real.norm_of_nonneg (le_min (hχ0 _) (Nat.cast_nonneg n))]
  exact min_le_left _ _

/-- The truncation `min (χ s) n` increases to `χ s`. -/
theorem tendsto_min_weight (χ : ℝ → ℝ) (s : ℝ) :
    Tendsto (fun n : ℕ => min (χ s) (n : ℝ)) atTop (𝓝 (χ s)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (Nat.ceil (χ s))] with n hn
  exact (min_eq_left ((Nat.le_ceil (χ s)).trans (by exact_mod_cast hn))).symm

/-- **The radial Newton identity at a good point.**  At a point `w ≠ 0` where the weighted
Newton kernel is integrable, the bounded truncations `min (χ ‖·‖) n` satisfy the radial Newton
identity for every truncation by the completed bounded identity, and dominated convergence passes
the identity to the unrestricted nonnegative integrable weight `χ`. -/
theorem integral_weight_inner_newtonField_of_integrable {d : ℕ} (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0)
    (hwi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)))) :
    ∀ ξ : EuclideanSpace ℝ (Fin d),
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * inner ℝ ξ (newtonField (d := d) (w - ζ)) =
        (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) *
          (inner ℝ ξ w / ‖w‖ ^ d) := by
  intro ξ
  have hLHS : Tendsto
      (fun n : ℕ => ∫ ζ : EuclideanSpace ℝ (Fin d),
        min (χ ‖ζ‖) (n : ℝ) * inner ℝ ξ (newtonField (d := d) (w - ζ)))
      atTop (𝓝 (∫ ζ : EuclideanSpace ℝ (Fin d),
        χ ‖ζ‖ * inner ℝ ξ (newtonField (d := d) (w - ζ)))) := by
    refine tendsto_integral_of_dominated_convergence
      (bound := fun ζ : EuclideanSpace ℝ (Fin d) =>
        ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)))) ?_ ?_ ?_ ?_
    · intro n
      exact (((hχm.comp measurable_norm).min measurable_const).mul
        (measurable_const.inner ((measurable_newtonField (d := d)).comp
          (measurable_const.sub measurable_id)))).aestronglyMeasurable
    · exact hwi.const_mul ‖ξ‖
    · intro n
      filter_upwards with ζ
      have hnn : 0 ≤ min (χ ‖ζ‖) (n : ℝ) := le_min (hχ0 _) (Nat.cast_nonneg n)
      rw [norm_mul, Real.norm_of_nonneg hnn]
      calc min (χ ‖ζ‖) (n : ℝ) * ‖inner ℝ ξ (newtonField (d := d) (w - ζ))‖
          ≤ χ ‖ζ‖ * (‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) :=
            mul_le_mul (min_le_left _ _) (by
              rw [Real.norm_eq_abs, ← norm_newtonField (d := d) hd]
              exact abs_real_inner_le_norm _ _) (norm_nonneg _) (hχ0 _)
        _ = ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by ring
    · filter_upwards with ζ
      exact (tendsto_min_weight χ ‖ζ‖).mul_const _
  have hRHS : Tendsto
      (fun n : ℕ => (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖,
          min (χ ‖ζ‖) (n : ℝ)) * (inner ℝ ξ w / ‖w‖ ^ d))
      atTop (𝓝 ((∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) *
        (inner ℝ ξ w / ‖w‖ ^ d))) := by
    have hm : Tendsto
        (fun n : ℕ => ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖,
          min (χ ‖ζ‖) (n : ℝ)) atTop
        (𝓝 (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖)) := by
      refine tendsto_integral_of_dominated_convergence
        (bound := fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖) ?_ ?_ ?_ ?_
      · intro n
        exact ((hχm.comp measurable_norm).min measurable_const).aestronglyMeasurable
      · exact hχi.integrableOn
      · intro n
        filter_upwards with ζ
        rw [Real.norm_of_nonneg (le_min (hχ0 _) (Nat.cast_nonneg n))]
        exact min_le_left _ _
      · filter_upwards with ζ
        exact tendsto_min_weight χ ‖ζ‖
    exact hm.mul_const _
  refine tendsto_nhds_unique hLHS ?_
  refine hRHS.congr' ?_
  filter_upwards with n
  exact (RadialBounded.integral_weight_inner_newtonField (d := d) hd
    (χ := fun s => min (χ s) (n : ℝ)) (M := (n : ℝ))
    (hχm.min measurable_const) (fun s => le_min (hχ0 s) (Nat.cast_nonneg n))
    (fun s => min_le_right _ _) (integrable_min_weight hχm hχ0 hχi n) hw ξ).symm

/-- **Almost-everywhere scalar radial Newton identity.**  For a nonnegative integrable radial
weight `χ`, for almost every `w` in a measurable set `D` of finite volume the scalar radial Newton
identity of `eq:radial-convolution` holds for every test vector `ξ`. -/
theorem ae_integral_weight_inner_newtonField {d : ℕ} (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) :
    ∀ᵐ w ∂(volume.restrict D), w ≠ 0 →
      ∀ ξ : EuclideanSpace ℝ (Fin d),
        ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * inner ℝ ξ (newtonField (d := d) (w - ζ)) =
          (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) *
            (inner ℝ ξ w / ‖w‖ ^ d) := by
  filter_upwards [ae_integrable_weight_smul_newtonField hd hχm hχ0 hχi hD hDfin]
    with w hw
  intro hw0
  have hwi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) :=
    hw.norm.congr (Filter.Eventually.of_forall fun ζ => by
      change ‖χ ‖ζ‖ • newtonField (d := d) (w - ζ)‖ = χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 ‖ζ‖), norm_newtonField (d := d) hd])
  exact integral_weight_inner_newtonField_of_integrable hd hχm hχ0 hχi hw0 hwi

/-- **Almost-everywhere vector radial Newton identity.**  This is `eq:radial-convolution`: for a
nonnegative integrable radial weight `χ`, for almost every `w` in a measurable set `D` of finite
volume the vector identity `∫ χ(|ζ|) K(w - ζ) dζ = m(|w|) w/|w|^d` holds. -/
theorem ae_integral_weight_smul_newtonField_eq {d : ℕ} (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) :
    ∀ᵐ w ∂(volume.restrict D), w ≠ 0 →
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ • newtonField (d := d) (w - ζ) =
        (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) •
          ((‖w‖ ^ d)⁻¹ • w) := by
  filter_upwards [ae_integrable_weight_smul_newtonField hd hχm hχ0 hχi hD hDfin,
    ae_integral_weight_inner_newtonField hd hχm hχ0 hχi hD hDfin] with w hw hsc
  intro hw0
  refine ext_inner_left ℝ fun ξ => ?_
  have hleft : ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * inner ℝ ξ (newtonField (d := d) (w - ζ)) =
      inner ℝ ξ (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ • newtonField (d := d) (w - ζ)) := by
    rw [← integral_inner hw ξ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    change χ ‖ζ‖ * inner ℝ ξ (newtonField (d := d) (w - ζ)) =
      inner ℝ ξ (χ ‖ζ‖ • newtonField (d := d) (w - ζ))
    rw [real_inner_smul_right]
  rw [← hleft, hsc hw0 ξ, real_inner_smul_right]
  congr 1
  rw [real_inner_smul_right, div_eq_inv_mul, mul_comm]

/-- **Global almost-everywhere vector radial Newton identity.**  The finite-volume statement is
exhausted along the nested balls `B(0, n)`, whose union is all of `ℝ^d`; a countable union of null
sets is null, so `eq:radial-convolution` holds almost everywhere with respect to Lebesgue measure
on `ℝ^d`, including the convention that the single point `w = 0` is null. -/
theorem ae_integral_weight_smul_newtonField_eq_univ {d : ℕ} (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) :
    ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), w ≠ 0 →
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ • newtonField (d := d) (w - ζ) =
        (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) •
          ((‖w‖ ^ d)⁻¹ • w) := by
  let Q : EuclideanSpace ℝ (Fin d) → Prop := fun w => w ≠ 0 →
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ • newtonField (d := d) (w - ζ) =
      (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) •
        ((‖w‖ ^ d)⁻¹ • w)
  have hball : ∀ n : ℕ,
      ∀ᵐ w ∂(volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (n : ℝ))), Q w :=
    fun n => ae_integral_weight_smul_newtonField_eq hd hχm hχ0 hχi measurableSet_ball
      measure_ball_lt_top.ne
  have huniv : (⋃ n : ℕ, Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (n : ℝ)) = Set.univ := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨Nat.ceil ‖w‖ + 1, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖w‖ ≤ (Nat.ceil ‖w‖ : ℝ) := Nat.le_ceil ‖w‖
      _ < ((Nat.ceil ‖w‖ + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hzero : ∀ n : ℕ,
      volume ({w : EuclideanSpace ℝ (Fin d) | ¬ Q w} ∩
        Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (n : ℝ)) = 0 := by
    intro n
    have h := ae_iff.mp (hball n)
    rwa [Measure.restrict_apply' measurableSet_ball] at h
  rw [ae_iff]
  have hcover : {w : EuclideanSpace ℝ (Fin d) | ¬ Q w} =
      ⋃ n : ℕ,
        ({w : EuclideanSpace ℝ (Fin d) | ¬ Q w} ∩
          Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (n : ℝ)) := by
    conv_lhs => rw [← Set.inter_univ {w : EuclideanSpace ℝ (Fin d) | ¬ Q w}, ← huniv]
    rw [Set.inter_iUnion]
  rw [hcover]
  exact measure_iUnion_null fun n => hzero n

end CERW.Support.Norm
