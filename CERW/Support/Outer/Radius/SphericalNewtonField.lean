import CERW.Support.Outer.Radius.InnerGeometry

/-!
# Spherical Newton Field

Spherical averaging identifies the component of the Newton field along an arbitrary vector.
Measurability and integrability justify the spherical integrals.
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

/-- A linear isometry of `ℝ^d` acts on the Euclidean unit sphere. -/
noncomputable def nw_sphereMap
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  ⟨A θ, by simp⟩

/-- The action of a linear isometry on the unit sphere is measurable. -/
lemma nw_measurable_sphereMap
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measurable (nw_sphereMap A) :=
  ((A.continuous.comp continuous_subtype_val).subtype_mk _).measurable

/-- Surface measure on the unit sphere is invariant under linear isometries. -/
lemma nw_map_sphereMap_toSphere
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measure.map (nw_sphereMap A) (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  ext S hS
  rw [Measure.map_apply (nw_measurable_sphereMap A) hS,
    Measure.toSphere_apply' _ ((nw_measurable_sphereMap A) hS), Measure.toSphere_apply' _ hS]
  congr 1
  have hset : Set.Ioo (0 : ℝ) 1 •
      ((↑) '' (nw_sphereMap A ⁻¹' S) : Set (EuclideanSpace ℝ (Fin d))) =
      A ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨nw_sphereMap A θ, hθ, rfl⟩, ?_⟩
      simp [nw_sphereMap]
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, h⟩
      refine ⟨t, ht, _, ⟨⟨A.symm θ, by simp⟩, ?_, rfl⟩, ?_⟩
      · simpa [nw_sphereMap] using hθ
      · have h' : t • (θ : EuclideanSpace ℝ (Fin d)) = A x := h
        show t • A.symm (θ : EuclideanSpace ℝ (Fin d)) = x
        rw [← A.symm.map_smul, h', A.symm_apply_apply]
  rw [hset]
  exact (LinearIsometryEquiv.measurePreserving A).measure_preimage_equiv
    (f := A.toMeasurableEquiv) _

/-- Integrals over the unit sphere are invariant under linear isometries. -/
lemma nw_integral_sphereMap
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {f : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ} (hf : Measurable f) :
    ∫ θ, f (nw_sphereMap A θ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ θ, f θ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have h := integral_map (nw_measurable_sphereMap A).aemeasurable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (f := f)
    (by rw [nw_map_sphereMap_toSphere]; exact hf.aestronglyMeasurable)
  rw [nw_map_sphereMap_toSphere] at h
  exact h.symm

/-- The Newtonian field commutes with linear isometries. -/
lemma nw_newtonField_map
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : newtonField (A x) = A (newtonField x) := by
  simp only [newtonField, A.norm_map, LinearIsometryEquiv.map_smul]

/-- The sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is measurable. -/
lemma nw_measurable_inner_newtonField (ξ v : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))) :=
  measurable_const.inner (measurable_newtonField.comp
    (measurable_const.sub (measurable_subtype_coe.const_smul s)))

/-- The component of the spherical average of the Newtonian field orthogonal to `v` vanishes:
a reflection fixing `v` and reversing `w ⟂ v` preserves surface measure. -/
lemma nw_integral_sphere_inner_newtonField_perp {v w : EuclideanSpace ℝ (Fin d)}
    (hvw : inner ℝ w v = 0) (s : ℝ) :
    ∫ θ, inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere = 0 := by
  set R := Submodule.reflection (ℝ ∙ w)ᗮ with hR
  have hRv : R v = v :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hvw)
  have hRw : R w = -w := Submodule.reflection_orthogonalComplement_singleton_eq_neg w
  have h := nw_integral_sphereMap R (nw_measurable_inner_newtonField w v s)
  have hpt : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ w (newtonField (v - s • (nw_sphereMap R θ : EuclideanSpace ℝ (Fin d)))) =
        -inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    intro θ
    have h1 : v - s • (nw_sphereMap R θ : EuclideanSpace ℝ (Fin d)) =
        R (v - s • (θ : EuclideanSpace ℝ (Fin d))) := by
      rw [R.map_sub, R.map_smul, hRv]
      rfl
    rw [h1, nw_newtonField_map, ← R.inner_map_map w, hRw, hR, Submodule.reflection_reflection,
      inner_neg_left]
  simp_rw [hpt, integral_neg] at h
  linarith

/-- The Newtonian field is continuous away from the origin. -/
lemma nw_continuousAt_newtonField_of_ne {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    ContinuousAt (newtonField : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) x :=
  ((continuous_norm.pow d).continuousAt.inv₀
    (pow_ne_zero d (norm_ne_zero_iff.mpr hx))).smul continuousAt_id

/-- For `|v| ≠ s` the sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is integrable, being continuous on a
compact space. -/
lemma nw_integrable_inner_newtonField (ξ : EuclideanSpace ℝ (Fin d))
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
        v - s • (θ : EuclideanSpace ℝ (Fin d))) (nw_continuousAt_newtonField_of_ne hne) hc rfl
  exact Continuous.integrable_of_hasCompactSupport (continuous_const.inner hcont)
    (HasCompactSupport.of_compactSpace _)

/-- The kernel average against an arbitrary vector `ξ`: for `v ≠ 0`, `s > 0`
and `|v| ≠ s`, `∫_S ξ · K(v - sθ) dσ(θ) = σ_d |v|^{-d} (ξ · v) 1{s < |v|}`. -/
lemma nw_integral_sphere_inner_newtonField_vec (hd : 2 ≤ d)
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
  rw [integral_add ((nw_integrable_inner_newtonField (unitDir v) hs hvs).const_mul a)
    (nw_integrable_inner_newtonField w hs hvs), integral_const_mul,
    CERW.Support.Geometry.integral_sphere_inner_newtonField hd hv hs hvs,
    nw_integral_sphere_inner_newtonField_perp hperp, add_zero]
  split_ifs
  · rw [ha, ← CERW.Support.Geometry.div_pow_eq_rpow_sub hrpos d]
    field_simp
  · simp

end

end CERW.Support.Outer.Radius
