import CERW.Model
import CERW.Generic.Norm
import CERW.Generic.Kernel.Modulus
import CERW.Support.Geometry.Newton
import CERW.Support.Geometry.Holder

/-!
# The geometry of the norm potential

`lem:geometry` of the paper for the potential
`U_D(y) = (2ε/ω_d) ∫_D ∇Ψ(v) · (v - y) |v - y|^{-d} dv` of a norm `Ψ` (`CERW.normPotential`).
The proof generalizes the Euclidean case (`CERW/Support/Geometry/`): the direction field
`u_v = v/|v|` is replaced by the gradient of `Ψ`, which is measurable and bounded by `Λ_Ψ`, so the
bound `eq:potential-bound` and the Hölder bound `eq:holder` hold with the constant multiplied by
`Λ_Ψ`. The spherical average `eq:newton` uses the kernel average against an arbitrary vector `ξ`:
the component of `∫_S K(v - sθ) dσ(θ)` orthogonal to `v` vanishes by a reflection fixing `v`, and
its radial component is the Euclidean kernel average. Euler's relation `∇Ψ(v) · v = Ψ(v)` then
turns the integrand into `Ψ(v) |v|^{-d}`, and `c_Ψ |v| ≤ Ψ(v) ≤ Λ_Ψ |v|` gives the comparison with
the weighted exterior volume.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

open CERW CERW.Generic.Norm CERW.Generic.Kernel CERW.Support.Geometry

variable {d : ℕ}

/-- A measurable field weighted by the Newtonian kernel has a measurable integrand. -/
private lemma measurable_fieldIntegrand {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (y : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun v : EuclideanSpace ℝ (Fin d) => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) := by
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
    measurable_id.sub measurable_const
  exact (hg.inner hsub).div (hsub.norm.pow_const d)

/-- The integrand of the field potential is at most `Λ` times the Newtonian kernel `|v - y|^{1-d}`
when the field has norm at most `Λ`. -/
private lemma abs_fieldIntegrand_le {Λ : ℝ} {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ ≤ Λ)
    (v y : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ ξ (v - y) / ‖v - y‖ ^ d| ≤ Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
  have hΛ : 0 ≤ Λ := (norm_nonneg ξ).trans hξ
  rcases eq_or_ne v y with rfl | hne
  · simp only [sub_self, inner_zero_right, zero_div, abs_zero]
    exact mul_nonneg hΛ (Real.rpow_nonneg (norm_nonneg _) _)
  · have hw : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < ‖v - y‖ ^ d := pow_pos hw d
    have h1 : |inner ℝ ξ (v - y)| ≤ ‖ξ‖ * ‖v - y‖ := abs_real_inner_le_norm _ _
    have h2 : ‖ξ‖ * ‖v - y‖ ≤ Λ * ‖v - y‖ := mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    calc |inner ℝ ξ (v - y) / ‖v - y‖ ^ d|
        = |inner ℝ ξ (v - y)| / ‖v - y‖ ^ d := by rw [abs_div, abs_of_nonneg hden.le]
      _ ≤ (Λ * ‖v - y‖) / ‖v - y‖ ^ d :=
          div_le_div_of_nonneg_right (h1.trans h2) hden.le
      _ = Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
          rw [mul_div_assoc, div_pow_eq_rpow_sub hw d]

/-- On a set of finite volume the integrand of a bounded measurable field potential is
integrable. -/
private lemma integrableOn_fieldIntegrand (hd : 1 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) D := by
  obtain ⟨hint, _⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  refine (hint.const_mul Λ).mono' (measurable_fieldIntegrand hg y).aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs]
  exact abs_fieldIntegrand_le (hΛ v) v y

/-- `eq:potential-bound` for a bounded measurable field: the potential
`(2ε/ω_d) ∫_D g(v) · (v - y) |v - y|^{-d} dv` is at most `Λ · 2dε ω_d^{-1/d} |D|^{1/d}` in absolute
value. -/
private lemma abs_fieldPotential_le (hd : 1 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {Λ : ℝ} (hΛ : ∀ v, ‖g v‖ ≤ Λ)
    {ε : ℝ} (hε : 0 ≤ ε) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    |2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d| ≤
      Λ * (2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) * (volume D).toReal ^ ((1 : ℝ) / d)) := by
  obtain ⟨hint, hbound⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  have hω := unitBallVolume_pos d
  have hR : 0 ≤ (volume D).toReal := ENNReal.toReal_nonneg
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hnorm : |∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d| ≤
      Λ * ∫ v in D, ‖v - y‖ ^ (1 - (d : ℝ)) := by
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hint.const_mul Λ) ?_
    filter_upwards with v
    rw [Real.norm_eq_abs]
    exact abs_fieldIntegrand_le (hΛ v) v y
  calc |2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d|
      = (2 * ε / unitBallVolume d) *
          |∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d| := by
        rw [abs_mul, abs_of_nonneg hc]
    _ ≤ (2 * ε / unitBallVolume d) * (Λ * ∫ v in D, ‖v - y‖ ^ (1 - (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hnorm hc
    _ ≤ (2 * ε / unitBallVolume d) *
          (Λ * (d * unitBallVolume d * ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound hΛ0) hc
    _ = Λ * ((2 * ε / unitBallVolume d) *
          (d * unitBallVolume d * ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d))) := by
        ring
    _ = Λ * (2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) *
          (volume D).toReal ^ ((1 : ℝ) / d)) := by
        rw [potential_bound_algebra d hω hR]

/-- The difference of two field-potential integrands is at most the norm of the difference of the
Newtonian fields when the field has norm at most one. -/
private lemma abs_fieldIntegrand_sub_le {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ ≤ 1)
    (y z v : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ ξ (v - y) / ‖v - y‖ ^ d - inner ℝ ξ (v - z) / ‖v - z‖ ^ d| ≤
      ‖newtonField (v - y) - newtonField (v - z)‖ := by
  rw [← inner_newtonField, ← inner_newtonField, ← inner_sub_right]
  calc |inner ℝ ξ (newtonField (v - y) - newtonField (v - z))|
      ≤ ‖ξ‖ * ‖newtonField (v - y) - newtonField (v - z)‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖newtonField (v - y) - newtonField (v - z)‖ :=
        mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    _ = ‖newtonField (v - y) - newtonField (v - z)‖ := one_mul _

/-- `eq:holder` for a measurable field of norm at most one: the field potentials satisfy
`|U(y) - U(z)| ≤ C_d ε |D|^{1/(2d)} |y - z|^{1/2}`. -/
private lemma exists_fieldPotential_holder_one (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)},
      Measurable g → (∀ v, ‖g v‖ ≤ 1) → ∀ {ε : ℝ}, 0 ≤ ε →
      ∀ {D : Set (EuclideanSpace ℝ (Fin d))}, MeasurableSet D → volume D ≠ ⊤ →
      ∀ y z : EuclideanSpace ℝ (Fin d),
        |2 * ε / unitBallVolume d * (∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) -
            2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - z) / ‖v - z‖ ^ d| ≤
          C * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d - 1 := by linarith
  have hω := unitBallVolume_pos d
  obtain ⟨C, hC0, hC⟩ := exists_kernel_modulus hd
  refine ⟨2 / unitBallVolume d * C ^ ((2 * (d : ℝ) - 1) / (2 * d)), by positivity, ?_⟩
  intro g hg hg1 ε hε D hD hDfin y z
  obtain ⟨hgi, hgint⟩ := hC y z
  have hpq : (2 * (d : ℝ)).HolderConjugate (2 * d / (2 * d - 1)) := by
    refine Real.holderConjugate_iff.mpr ⟨by linarith, ?_⟩
    field_simp
    ring
  have hgm : AEStronglyMeasurable (fun v => ‖newtonField (v - y) - newtonField (v - z)‖) volume :=
    (((measurable_newtonField.comp (measurable_id.sub_const y)).sub
      (measurable_newtonField.comp (measurable_id.sub_const z))).norm).aestronglyMeasurable
  have hH := abs_setIntegral_le_rpow_mul_rpow hpq hDfin
    (f := fun v => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d -
      inner ℝ (g v) (v - z) / ‖v - z‖ ^ d)
    (fun v => abs_fieldIntegrand_sub_le (hg1 v) y z v) hgm hgi
  have hsub : 2 * ε / unitBallVolume d * (∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) -
      2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - z) / ‖v - z‖ ^ d =
      2 * ε / unitBallVolume d *
      ∫ v in D, (inner ℝ (g v) (v - y) / ‖v - y‖ ^ d -
        inner ℝ (g v) (v - z) / ‖v - z‖ ^ d) := by
    rw [integral_sub (integrableOn_fieldIntegrand (by omega) hg hg1 hD hDfin y)
      (integrableOn_fieldIntegrand (by omega) hg hg1 hD hDfin z)]
    ring
  have hmod : (∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^ (2 * (d : ℝ) / (2 * d - 1))) ^
      (1 / (2 * (d : ℝ) / (2 * d - 1))) ≤
        C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
    have h1 : 1 / (2 * (d : ℝ) / (2 * d - 1)) = (2 * d - 1) / (2 * d) := by
      field_simp
    have hnn : 0 ≤ ∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^
        (2 * (d : ℝ) / (2 * d - 1)) :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    calc (∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^ (2 * (d : ℝ) / (2 * d - 1))) ^
          (1 / (2 * (d : ℝ) / (2 * d - 1)))
        ≤ (C * ‖y - z‖ ^ ((d : ℝ) / (2 * d - 1))) ^ ((2 * (d : ℝ) - 1) / (2 * d)) := by
          rw [h1]
          exact Real.rpow_le_rpow hnn hgint (by positivity)
      _ = C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
          rw [Real.mul_rpow hC0 (Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_mul
            (norm_nonneg _)]
          congr 2
          rw [div_mul_div_comm, div_eq_div_iff (mul_pos hden (by positivity)).ne' two_ne_zero]
          ring
  rw [hsub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ε / unitBallVolume d)]
  calc 2 * ε / unitBallVolume d * |∫ v in D, (inner ℝ (g v) (v - y) / ‖v - y‖ ^ d -
        inner ℝ (g v) (v - z) / ‖v - z‖ ^ d)|
      ≤ 2 * ε / unitBallVolume d * ((volume D).toReal ^ (1 / (2 * (d : ℝ))) *
          (C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2))) := by
        gcongr
        exact hH.trans (by gcongr)
    _ = 2 / unitBallVolume d * C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ε *
          (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
        ring

/-- `eq:holder` for a measurable field of norm at most `Λ > 0`:
`|U(y) - U(z)| ≤ Λ C_d ε |D|^{1/(2d)} |y - z|^{1/2}`. -/
private lemma exists_fieldPotential_holder (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)},
      Measurable g → ∀ {Λ : ℝ}, 0 < Λ → (∀ v, ‖g v‖ ≤ Λ) → ∀ {ε : ℝ}, 0 ≤ ε →
      ∀ {D : Set (EuclideanSpace ℝ (Fin d))}, MeasurableSet D → volume D ≠ ⊤ →
      ∀ y z : EuclideanSpace ℝ (Fin d),
        |2 * ε / unitBallVolume d * (∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) -
            2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - z) / ‖v - z‖ ^ d| ≤
          Λ * (C * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_fieldPotential_holder_one hd
  refine ⟨C, hC0, ?_⟩
  intro g hg Λ hΛ hgΛ ε hε D hD hDfin y z
  set g' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun v => Λ⁻¹ • g v with hg'
  have hg'm : Measurable g' := hg.const_smul Λ⁻¹
  have hg'b : ∀ v, ‖g' v‖ ≤ 1 := by
    intro v
    rw [hg', norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hΛ]
    calc Λ⁻¹ * ‖g v‖ ≤ Λ⁻¹ * Λ := mul_le_mul_of_nonneg_left (hgΛ v) (inv_nonneg.mpr hΛ.le)
      _ = 1 := inv_mul_cancel₀ hΛ.ne'
  have hscale : ∀ w : EuclideanSpace ℝ (Fin d),
      ∫ v in D, inner ℝ (g v) (v - w) / ‖v - w‖ ^ d =
        Λ * ∫ v in D, inner ℝ (g' v) (v - w) / ‖v - w‖ ^ d := by
    intro w
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hgv : g v = Λ • g' v := by
      rw [hg', smul_smul, mul_inv_cancel₀ hΛ.ne', one_smul]
    simp only [hgv, real_inner_smul_left]
    ring
  have h := hC hg'm hg'b hε hD hDfin y z
  rw [hscale y, hscale z]
  have hrew : 2 * ε / unitBallVolume d * (Λ * ∫ v in D, inner ℝ (g' v) (v - y) / ‖v - y‖ ^ d) -
      2 * ε / unitBallVolume d * (Λ * ∫ v in D, inner ℝ (g' v) (v - z) / ‖v - z‖ ^ d) =
      Λ * (2 * ε / unitBallVolume d * (∫ v in D, inner ℝ (g' v) (v - y) / ‖v - y‖ ^ d) -
        2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g' v) (v - z) / ‖v - z‖ ^ d) := by
    ring
  rw [hrew, abs_mul, abs_of_pos hΛ]
  exact mul_le_mul_of_nonneg_left h hΛ.le

/-- A linear isometry of `ℝ^d` acts on the Euclidean unit sphere. -/
private noncomputable def sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  ⟨A θ, by simp⟩

/-- The action of a linear isometry on the unit sphere is measurable. -/
private lemma measurable_sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measurable (sphereMap A) :=
  ((A.continuous.comp continuous_subtype_val).subtype_mk _).measurable

/-- Surface measure on the unit sphere is invariant under linear isometries. -/
private lemma map_sphereMap_toSphere
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
private lemma integral_sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {f : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ} (hf : Measurable f) :
    ∫ θ, f (sphereMap A θ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ θ, f θ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have h := integral_map (measurable_sphereMap A).aemeasurable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (f := f)
    (by rw [map_sphereMap_toSphere]; exact hf.aestronglyMeasurable)
  rw [map_sphereMap_toSphere] at h
  exact h.symm

/-- The Newtonian field commutes with linear isometries. -/
private lemma newtonField_map (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : newtonField (A x) = A (newtonField x) := by
  simp only [newtonField, A.norm_map, LinearIsometryEquiv.map_smul]

/-- The sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is measurable. -/
private lemma measurable_inner_newtonField (ξ v : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))) :=
  measurable_const.inner (measurable_newtonField.comp
    (measurable_const.sub (measurable_subtype_coe.const_smul s)))

/-- The component of the spherical average of the Newtonian field orthogonal to `v` vanishes:
a reflection fixing `v` and reversing `w ⟂ v` preserves surface measure. -/
private lemma integral_sphere_inner_newtonField_perp {v w : EuclideanSpace ℝ (Fin d)}
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
private lemma continuousAt_newtonField_of_ne {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    ContinuousAt (newtonField : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) x :=
  ((continuous_norm.pow d).continuousAt.inv₀
    (pow_ne_zero d (norm_ne_zero_iff.mpr hx))).smul continuousAt_id

/-- For `|v| ≠ s` the sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is integrable, being continuous on a
compact space. -/
private lemma integrable_inner_newtonField (ξ : EuclideanSpace ℝ (Fin d))
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
private lemma integral_sphere_inner_newtonField_vec (hd : 2 ≤ d)
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

/-- The field potential's integrand, as a function of the sphere point `θ` and the position `v`,
is integrable for the product of the sphere measure and Lebesgue measure restricted to a measurable
set of finite volume. -/
private lemma integrable_fieldPair (hd : 1 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (s : ℝ) :
    Integrable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
        EuclideanSpace ℝ (Fin d) =>
      inner ℝ (g p.2) (p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))) /
        ‖p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))‖ ^ d)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict D)) := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hmeas : Measurable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
      EuclideanSpace ℝ (Fin d) =>
      inner ℝ (g p.2) (p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))) /
        ‖p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))‖ ^ d) := by
    have hsub : Measurable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
        EuclideanSpace ℝ (Fin d) => p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))) :=
      measurable_snd.sub ((measurable_subtype_coe.comp measurable_fst).const_smul s)
    exact ((hg.comp measurable_snd).inner hsub).div (hsub.norm.pow_const d)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun θ =>
    integrableOn_fieldIntegrand hd hg hΛ hD hDfin (s • (θ : EuclideanSpace ℝ (Fin d))), ?_⟩
  refine Integrable.mono' (integrable_const (Λ * (d * unitBallVolume d *
    ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d))))
    hmeas.norm.aestronglyMeasurable.integral_prod_right' ?_
  refine Filter.Eventually.of_forall fun θ => ?_
  obtain ⟨hint, hle⟩ := integrableOn_and_setIntegral_le hd hD hDfin
    (s • (θ : EuclideanSpace ℝ (Fin d)))
  have hint' := integrableOn_fieldIntegrand hd hg hΛ hD hDfin (s • (θ : EuclideanSpace ℝ (Fin d)))
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hle hΛ0)
  rw [← integral_const_mul]
  refine setIntegral_mono hint'.norm (hint.const_mul Λ) fun v => ?_
  rw [Real.norm_eq_abs]
  exact abs_fieldIntegrand_le (hΛ v) v _

/-- Lebesgue-almost every point is nonzero and has norm different from a given radius. -/
private lemma ae_ne_zero_and_norm_ne (hd : 2 ≤ d) (s : ℝ) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ≠ 0 ∧ ‖v‖ ≠ s := by
  haveI : NeZero d := ⟨by omega⟩
  have h0 : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ≠ 0 := by
    rw [ae_iff]
    simp
  have h1 : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ‖v‖ ≠ s := by
    rw [ae_iff]
    have := Measure.addHaar_sphere (volume : Measure (EuclideanSpace ℝ (Fin d))) 0 s
    simpa [Metric.sphere] using this
  filter_upwards [h0, h1] with v hv0 hv1 using ⟨hv0, hv1⟩

/-- The spherical integral of a field potential of `D` at radius `s` is the weighted exterior
integral of the field's radial component, by Fubini and the kernel average. -/
private lemma integral_sphere_fieldPotential (hd : 2 ≤ d) (ε : ℝ)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) {s : ℝ} (hs : 0 < s) :
    ∫ θ, (2 * ε / unitBallVolume d *
        ∫ v in D, inner ℝ (g v) (v - s • (θ : EuclideanSpace ℝ (Fin d))) /
          ‖v - s • (θ : EuclideanSpace ℝ (Fin d))‖ ^ d)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * ε / unitBallVolume d * ∫ v in D,
        (if s < ‖v‖ then d * unitBallVolume d * (inner ℝ (g v) v / ‖v‖ ^ d) else 0) := by
  have hnull := ae_ne_zero_and_norm_ne hd s
  rw [integral_const_mul]
  congr 1
  rw [integral_integral_swap (integrable_fieldPair (by omega) hg hΛ hD hDfin s)]
  refine setIntegral_congr_ae hD (hnull.mono fun v hv _ => ?_)
  have h := integral_sphere_inner_newtonField_vec hd hv.1 hs hv.2 (g v)
  simp_rw [inner_newtonField] at h
  exact h

/-- The gradient of a function on `ℝ^d` is measurable. -/
private lemma measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- For `d ≥ 1`, `Λ_Ψ ≥ 0`. -/
private lemma normMax_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d) :
    0 ≤ normMax Ψ := by
  have h1 := normMin_pos_mul_le hΨ hd
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h2 := le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  have h3 := h1.2 (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h2 h3
  linarith [h1.1]

/-- The gradient of a norm has Euclidean norm at most `Λ_Ψ` everywhere: where `Ψ` is
differentiable it is a subgradient, and elsewhere it is `0`. -/
private lemma norm_gradient_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) (hd : 1 ≤ d)
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

/-- `eq:newton` for a norm: the spherical integral of the norm potential of `D` at radius `s` is
`σ_d` times the exterior integral of `Ψ(v)/|v|^d`, using Euler's relation `∇Ψ(v) · v = Ψ(v)`. -/
private lemma integral_sphere_normPotential (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) (ε : ℝ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {s : ℝ} (hs : 0 < s) :
    ∫ θ, normPotential d ε Ψ D (s • (θ : EuclideanSpace ℝ (Fin d)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * ε / unitBallVolume d * (d * unitBallVolume d *
        ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d) := by
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hset : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖} :=
    measurableSet_lt measurable_const measurable_norm
  have h1 := integral_sphere_fieldPotential hd ε (measurable_gradient Ψ)
    (norm_gradient_le hΨ (by omega)) hD hDfin hs
  unfold normPotential
  rw [h1]
  congr 1
  have heuler : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ∈ D →
      (if s < ‖v‖ then d * unitBallVolume d * (inner ℝ (gradient Ψ v) v / ‖v‖ ^ d) else 0) =
        {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖}.indicator
          (fun v => d * unitBallVolume d * (Ψ v / ‖v‖ ^ d)) v := by
    filter_upwards [ae_differentiableAt hΨ] with v hv _
    rw [(subgradient_euler hΨ (gradient_isSubgradient hΨ hv)).1, Set.indicator_apply]
    rfl
  rw [setIntegral_congr_ae hD heuler, setIntegral_indicator hset, integral_const_mul]

/-- On a bounded measurable set beyond a positive radius, `Ψ(v)/|v|^d` is integrable. -/
private lemma integrableOn_norm_div_pow {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun v => Ψ v / ‖v‖ ^ d) (D ∩ {v | s < ‖v‖}) := by
  have hset : MeasurableSet (D ∩ {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖}) :=
    hD.inter (measurableSet_lt measurable_const measurable_norm)
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) => Ψ v / ‖v‖ ^ d) :=
    (norm_continuous hΨ).measurable.div (measurable_norm.pow_const d)
  refine ((integrableOn_tail hD hDb hs).const_mul (normMax Ψ)).mono'
    hmeas.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem hset fun v hv => ?_
  have hvpos : 0 < ‖v‖ := hs.trans hv.2
  have hden : 0 < ‖v‖ ^ d := pow_pos hvpos d
  have hnn : 0 ≤ Ψ v := (map_zero_nonneg_neg hΨ).2.1 v
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnn hden.le), ← div_pow_eq_rpow_sub hvpos d,
    ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (le_normMax_mul hΨ v) hden.le

/-- The exterior integral of `Ψ(v)/|v|^d` lies between `c_Ψ` and `Λ_Ψ` times the exterior integral
of `|v|^{1-d}`. -/
private lemma norm_div_pow_integral_bounds (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {s : ℝ} (hs : 0 < s) :
    normMin Ψ * ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) ≤
        ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d ∧
      ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d ≤
        normMax Ψ * ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) := by
  have hset : MeasurableSet (D ∩ {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖}) :=
    hD.inter (measurableSet_lt measurable_const measurable_norm)
  have hI := integrableOn_norm_div_pow hΨ hD hDb hs
  have hJ := integrableOn_tail hD hDb hs
  rw [← integral_const_mul, ← integral_const_mul]
  refine ⟨setIntegral_mono_on (hJ.const_mul _) hI hset fun v hv => ?_,
    setIntegral_mono_on hI (hJ.const_mul _) hset fun v hv => ?_⟩
  · have hvpos : 0 < ‖v‖ := hs.trans hv.2
    have hden : 0 < ‖v‖ ^ d := pow_pos hvpos d
    rw [← div_pow_eq_rpow_sub hvpos d, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right ((normMin_pos_mul_le hΨ hd).2 v) hden.le
  · have hvpos : 0 < ‖v‖ := hs.trans hv.2
    have hden : 0 < ‖v‖ ^ d := pow_pos hvpos d
    rw [← div_pow_eq_rpow_sub hvpos d, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_normMax_mul hΨ v) hden.le

/-- `lem:geometry` for the norm potential: there is `C(d, Ψ) > 0` such that, for every `ε > 0` and
bounded measurable `D` of volume `R`, `‖U_D‖_∞ ≤ C ε R^{1/d}`,
`|U_D(y) - U_D(z)| ≤ C ε R^{1/(2d)} |y - z|^{1/2}`, and the spherical mean of `U_D` at radius `s`
is `B = (2ε/ω_d) ∫_{D ∩ {|v| > s}} Ψ(v) |v|^{-d} dv`, which lies between `2dε c_Ψ F(s)` and
`2dε Λ_Ψ F(s)` and equals `2dε F(s)` for the Euclidean norm. -/
theorem norm_potential_geometry {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
        let R : ℝ := (volume D).toReal
        (∀ y, |CERW.normPotential d ε Ψ D y| ≤ C * ε * R ^ ((1 : ℝ) / d)) ∧
        (∀ y z, |CERW.normPotential d ε Ψ D y - CERW.normPotential d ε Ψ D z|
            ≤ C * ε * R ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
        (∀ s : ℝ, 0 < s →
          let A : ℝ := (d * ωd)⁻¹ * ∫ θ,
              CERW.normPotential d ε Ψ D (s • (θ : EuclideanSpace ℝ (Fin d)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
          let B : ℝ := 2 * ε / ωd * ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d
          A = B ∧ 2 * d * ε * CERW.normMin Ψ * CERW.tail d D s ≤ B ∧
            B ≤ 2 * d * ε * CERW.normMax Ψ * CERW.tail d D s ∧
            ((∀ v, Ψ v = ‖v‖) → B = 2 * d * ε * CERW.tail d D s)) := by
  intro ωd Ψ hΨ
  have hd1 : 1 ≤ d := by omega
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hωd : ωd = unitBallVolume d := rfl
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact this.ne'
  obtain ⟨hcpos, hcle⟩ := normMin_pos_mul_le hΨ hd1
  have hΛpos : 0 < normMax Ψ := by
    have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
      simp [coordVec, PiLp.norm_single]
    have h2 := le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
    have h3 := hcle (coordVec (⟨0, by omega⟩ : Fin d))
    rw [hn] at h2 h3
    linarith
  have hgm : Measurable (gradient Ψ) := measurable_gradient Ψ
  have hgb : ∀ v, ‖gradient Ψ v‖ ≤ normMax Ψ := norm_gradient_le hΨ hd1
  obtain ⟨CH, hCH0, hCH⟩ := exists_fieldPotential_holder hd
  set CB : ℝ := 2 * d * unitBallVolume d ^ (-(1 : ℝ) / d) with hCB
  have hCB0 : 0 ≤ CB := by positivity
  refine ⟨normMax Ψ * CB + normMax Ψ * CH + 1, by positivity, fun ε hε D hD hDb => ?_⟩
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hR0 : 0 ≤ (volume D).toReal := ENNReal.toReal_nonneg
  refine ⟨fun y => ?_, fun y z => ?_, fun s hs => ?_⟩
  · calc |normPotential d ε Ψ D y|
        ≤ normMax Ψ * (2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) *
            (volume D).toReal ^ ((1 : ℝ) / d)) :=
          abs_fieldPotential_le hd1 hgb hε.le hD hDfin y
      _ = normMax Ψ * CB * ε * (volume D).toReal ^ ((1 : ℝ) / d) := by rw [hCB]; ring
      _ ≤ (normMax Ψ * CB + normMax Ψ * CH + 1) * ε * (volume D).toReal ^ ((1 : ℝ) / d) := by
          have := Real.rpow_nonneg hR0 ((1 : ℝ) / d)
          gcongr
          have := mul_nonneg hΛpos.le hCH0
          linarith
  · calc |normPotential d ε Ψ D y - normPotential d ε Ψ D z|
        ≤ normMax Ψ * (CH * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) *
            ‖y - z‖ ^ ((1 : ℝ) / 2)) :=
          hCH hgm hΛpos hgb hε.le hD hDfin y z
      _ = normMax Ψ * CH * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) *
            ‖y - z‖ ^ ((1 : ℝ) / 2) := by ring
      _ ≤ (normMax Ψ * CB + normMax Ψ * CH + 1) * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) *
            ‖y - z‖ ^ ((1 : ℝ) / 2) := by
          have h1 := Real.rpow_nonneg hR0 ((1 : ℝ) / (2 * d))
          have h2 := Real.rpow_nonneg (norm_nonneg (y - z)) ((1 : ℝ) / 2)
          gcongr
          have := mul_nonneg hΛpos.le hCB0
          linarith
  · intro A B
    obtain ⟨hlow, hhigh⟩ := norm_div_pow_integral_bounds hd1 hΨ hD hDb hs
    have hAB : A = B := by
      have h := integral_sphere_normPotential hd hΨ ε hD hDb hs
      simp only [A, B, hωd]
      rw [h]
      field_simp
    have htail : ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) =
        d * unitBallVolume d * tail d D s := by
      simp only [tail]
      field_simp
    have hBdef : B = 2 * ε / unitBallVolume d * ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d := rfl
    refine ⟨hAB, ?_, ?_, ?_⟩
    · rw [hBdef]
      calc 2 * d * ε * normMin Ψ * tail d D s
          = 2 * ε / unitBallVolume d *
              (normMin Ψ * ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ))) := by
            rw [htail]
            field_simp
        _ ≤ 2 * ε / unitBallVolume d * ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d :=
            mul_le_mul_of_nonneg_left hlow (by positivity)
    · rw [hBdef]
      calc 2 * ε / unitBallVolume d * ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d
          ≤ 2 * ε / unitBallVolume d *
              (normMax Ψ * ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ))) :=
            mul_le_mul_of_nonneg_left hhigh (by positivity)
        _ = 2 * d * ε * normMax Ψ * tail d D s := by
            rw [htail]
            field_simp
    · intro hEuc
      rw [hBdef]
      have hcongr : ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d =
          ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ)) := by
        refine setIntegral_congr_fun (hD.inter (measurableSet_lt measurable_const measurable_norm))
          fun v hv => ?_
        have hvpos : 0 < ‖v‖ := hs.trans hv.2
        simp only [hEuc v]
        exact div_pow_eq_rpow_sub hvpos d
      rw [hcongr, htail]
      field_simp

end CERW.Support.Norm
