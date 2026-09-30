import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Polar coordinates in `ℝ^d`

Lebesgue measure on `ℝ^d \ {0}` is the product of the sphere measure `σ = volume.toSphere` (of
total mass `σ_d = d ω_d`) with the radial measure `r^{d-1} dr` on `(0, ∞)`. For integrable `f`,
`∫ f = ∫_0^∞ r^{d-1} ∫_{S^{d-1}} f(rθ) dσ(θ) dr`. The inner integral is defined for almost
every `r`, and the radial function is integrable. This is the Fubini step of the Newton plan behind
`eq:kernel-average`.
-/

namespace CERW.Generic.Newton

open MeasureTheory Set

variable {d : ℕ}

/-- The polar-coordinate change of variables sends the integrand `f` to a function that is
integrable for the product of the sphere measure and the radial measure. -/
lemma integrable_prod_polar {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Integrable f) :
    Integrable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0 : ℝ) =>
        f (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d))))
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
        (Measure.volumeIoiPow (d - 1))) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure (EuclideanSpace ℝ (Fin d)))
  rw [hfin] at hmp
  have h1 := hmp.integrable_comp_emb
    (g := fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0 : ℝ) =>
      f (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d)))) (Homeomorph.measurableEmbedding _)
  rw [← h1]
  have h2 : (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0 : ℝ) =>
      f (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d)))) ∘
        (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d))) =
      fun x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin d))) => f x.1 := by
    funext x
    have hx : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 x.2
    simp [smul_smul, hx]
  rw [h2]
  exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hf.integrableOn

/-- Polar coordinates: for integrable `f`, `∫ f = ∫_{r > 0} r^{d-1} ∫_S f(rθ) dσ(θ) dr`. -/
theorem integral_eq_integral_Ioi_sphere (hd : 1 ≤ d) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Integrable f) :
    ∫ v, f v = ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) *
      ∫ θ, f (r • (θ : EuclideanSpace ℝ (Fin d)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  haveI : NeZero d := ⟨Nat.one_le_iff_ne_zero.1 hd⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure (EuclideanSpace ℝ (Fin d)))
  rw [hfin] at hmp
  have hg := integrable_prod_polar hf
  calc ∫ v, f v
      = ∫ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin d))), f x.1
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).comap Subtype.val := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl f,
          restrict_compl_singleton]
    _ = ∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0 : ℝ),
          f (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
            (Measure.volumeIoiPow (d - 1)) := by
        rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _)
          (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0 : ℝ) =>
            f (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d))))]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hx : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.2 x.2
        simp [smul_smul, hx]
    _ = ∫ r : Ioi (0 : ℝ), ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          f (r.1 • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
          ∂Measure.volumeIoiPow (d - 1) := integral_prod_symm _ hg
    _ = _ := by
        simp only [Measure.volumeIoiPow, ENNReal.ofReal]
        rw [integral_withDensity_eq_integral_smul,
          integral_subtype_comap measurableSet_Ioi fun a : ℝ => Real.toNNReal (a ^ (d - 1)) •
            ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
              f (a • (θ : EuclideanSpace ℝ (Fin d)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere,
          setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
        · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]
          rfl
        · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- For integrable `f`, the function `θ ↦ f(rθ)` is integrable on the sphere for almost every
`r > 0`, and the radial function `r ↦ r^{d-1} ∫_S f(rθ) dσ(θ)` is integrable on `(0, ∞)`. -/
theorem integrable_sphere_of_integrable {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Integrable f) :
    (∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))), Integrable
      (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        f (r • (θ : EuclideanSpace ℝ (Fin d))))
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) ∧
    IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      ∫ θ, f (r • (θ : EuclideanSpace ℝ (Fin d)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (Set.Ioi 0) := by
  have hg := integrable_prod_polar hf
  constructor
  · have h1 := hg.prod_left_ae
    rw [Measure.volumeIoiPow, ae_withDensity_iff (by fun_prop)] at h1
    rw [ae_restrict_iff_subtype measurableSet_Ioi]
    refine h1.mono fun r hr => hr ?_
    simpa using pow_pos r.2.out (d - 1)
  · have h1 : Integrable (fun r : Ioi (0 : ℝ) =>
        ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          f (r.1 • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere)
        (Measure.volumeIoiPow (d - 1)) := hg.swap.integral_prod_left
    rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul'
      (by fun_prop) (by simp)] at h1
    refine (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).2 (h1.congr ?_)
    refine Filter.Eventually.of_forall fun r => ?_
    simp [ENNReal.toReal_ofReal, pow_nonneg r.2.out.le]

end CERW.Generic.Newton
