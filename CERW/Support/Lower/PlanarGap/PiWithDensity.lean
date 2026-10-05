/-
# The `Measure.pi`–`withDensity` bridge (two coordinates)

Packet `cerw-ds3-pi-withdensity`.  This is the single measure-theoretic input that the exact
2D Gaussian closed-disk mass (`GaussDisc.lean`) was missing: for a finite index type and
measurable nonnegative densities, the product measure of the densities is the density of the
product of the products.

Mathlib (at the pinned revision) has no packaged statement of this form.  It is proved here for
two coordinates, which is what the disk mass consumes, via:

* `measurePreserving_piFinTwo` (`Mathlib/MeasureTheory/Constructions/Pi.lean:852`): the coordinate
  equivalence `MeasurableEquiv.piFinTwo` carries `Measure.pi` to `Measure.prod`;
* `lintegral_prod` (`Mathlib/MeasureTheory/Measure/Prod.lean:1006`): Tonelli on a product measure;
* `Measure.pi_eq` (`Mathlib/MeasureTheory/Constructions/Pi.lean:278`): two product measures agree
  once they agree on measurable rectangles;
* `withDensity_apply` and the pointwise identity
  `(Set.univ.pi s).indicator (∏ᵢ fᵢ) = (s 0).indicator f₀ * (s 1).indicator f₁`.

The general-`ι` statement is not proved here (the `Measure.pi_eq` induction over complements is
lengthy); the two-coordinate form suffices for the disk mass, and the file is otherwise generic
(any measurable space `α` and any sigma-finite `ν`).

## What the disk mass still needs

With the bridge above, `Measure.pi (fun _ : Fin 2 => gaussianReal 0 (1/2))` is a
`volume.withDensity` of the two-coordinate Gaussian density.  To turn that into the
closed-disk mass one still needs

1. **density transport** along the measurable equivalence `WithLp.toLp 2` — there is no packaged
   `map_withDensity` lemma in the pinned Mathlib (only the Radon–Nikodym and Jacobian variants);
   the statement `(μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm)` is a short
   proof;
2. the algebra
   `∏ i, gaussianPDF 0 (1/2) (x i) = ENNReal.ofReal (π⁻¹ * exp (-‖toLp 2 x‖ ^ 2))`
   (i.e. `gaussianPDFReal 0 (1/2) y = (Real.sqrt π)⁻¹ * exp (-(y^2))`);
3. the lintegral→Bochner conversion plus the polar formula
   `MeasureTheory.integral_fun_norm_addHaar` on `EuclideanSpace ℝ (Fin 2)` with
   `volume_closedBall_fin_two` (`volume.real (ball 0 1) = π`) and
   `LatticeProb`-independent `integral_zero_to_mul_exp_neg_sq` (`GaussDisc.lean`).
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

/-- **Tonelli for `Measure.pi` over `Fin 2`.**  For measurable nonnegative `g₀, g₁` and a
sigma-finite measure `ν`, the integral over the product `Measure.pi` of the product
`g₀ (x 0) * g₁ (x 1)` is the product of the one-dimensional integrals. -/
theorem lintegral_piFinTwo_prod {α : Type*} [MeasurableSpace α] {ν : Measure α} [SigmaFinite ν]
    (g₀ g₁ : α → ℝ≥0∞) (hg₀ : Measurable g₀) (hg₁ : Measurable g₁) :
    ∫⁻ x : Fin 2 → α, g₀ (x 0) * g₁ (x 1) ∂(Measure.pi fun _ : Fin 2 => ν)
      = (∫⁻ y, g₀ y ∂ν) * ∫⁻ y, g₁ y ∂ν := by
  calc ∫⁻ x : Fin 2 → α, g₀ (x 0) * g₁ (x 1) ∂(Measure.pi fun _ : Fin 2 => ν)
      = ∫⁻ x, (fun p : α × α => g₀ p.1 * g₁ p.2)
          (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => α) x) ∂(Measure.pi fun _ => ν) := by
        refine lintegral_congr fun x => ?_
        simp [MeasurableEquiv.piFinTwo_apply]
    _ = ∫⁻ p : α × α, g₀ p.1 * g₁ p.2 ∂(ν.prod ν) :=
        ((measurePreserving_piFinTwo (fun _ : Fin 2 => ν)).lintegral_map_equiv
          (fun p : α × α => g₀ p.1 * g₁ p.2)).symm
    _ = (∫⁻ y, g₀ y ∂ν) * ∫⁻ y, g₁ y ∂ν := by
        rw [show (fun p : α × α => g₀ p.1 * g₁ p.2)
              = (g₀ ∘ Prod.fst * g₁ ∘ Prod.snd) from rfl,
          lintegral_prod _
            ((hg₀.comp measurable_fst).mul (hg₁.comp measurable_snd)).aemeasurable]
        trans ∫⁻ x, ∫⁻ y, g₀ x * g₁ y ∂ν ∂ν
        · exact lintegral_congr fun x => lintegral_congr fun _ => rfl
        · simp only [lintegral_const_mul _ hg₁, lintegral_mul_const _ hg₀]

/-- **The `Measure.pi`–`withDensity` bridge for two coordinates.**  The product measure of the
densities `f i` w.r.t. `ν` is the density, w.r.t. the product `Measure.pi` of `ν`, of the product
of the densities. -/
theorem Measure.pi_withDensity_fin_two {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [SigmaFinite ν] (f : Fin 2 → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite (ν.withDensity (f i))] :
    Measure.pi (fun i : Fin 2 => ν.withDensity (f i))
      = (Measure.pi fun _ : Fin 2 => ν).withDensity
          (fun x => f 0 (x 0) * f 1 (x 1)) := by
  refine Measure.pi_eq (μ := fun i : Fin 2 => ν.withDensity (f i))
    (μ' := (Measure.pi fun _ : Fin 2 => ν).withDensity (fun x => f 0 (x 0) * f 1 (x 1)))
    fun s hs => ?_
  have hpt : ∀ x : Fin 2 → α,
      (Set.univ.pi s).indicator (fun x => f 0 (x 0) * f 1 (x 1)) x
        = (s 0).indicator (f 0) (x 0) * (s 1).indicator (f 1) (x 1) := by
    intro x
    by_cases h0 : x 0 ∈ s 0 <;> by_cases h1 : x 1 ∈ s 1 <;>
      simp [Set.indicator, h0, h1, Fin.forall_fin_two]
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs), lintegral_congr hpt,
    lintegral_piFinTwo_prod _ _ ((hf 0).indicator (hs 0)) ((hf 1).indicator (hs 1)),
    lintegral_indicator (hs 0), lintegral_indicator (hs 1), Fin.prod_univ_two]
  simp only [withDensity_apply _ (hs 0), withDensity_apply _ (hs 1)]

/-- **Density transport along a measurable equivalence.**  Pushing a density forward along a
measurable equivalence pushes the base measure forward and pulls the density back.  Needed to move
the two-coordinate Gaussian density from `Fin 2 → ℝ` (whose default norm is the sup norm) to
`EuclideanSpace ℝ (Fin 2)` (the Euclidean norm the disk mass uses); the pinned Mathlib has
no
packaged form of this (`map_withDensity` appears only in Radon–Nikodym and Jacobian variants). -/
theorem Measure.map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) (μ : Measure α)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs, ← lintegral_indicator (hs.preimage e.measurable),
    ← lintegral_indicator hs]
  have hm : ∫⁻ a, s.indicator (fun a => f (e.symm a)) a ∂Measure.map (⇑e) μ
      = ∫⁻ a, s.indicator (fun a => f (e.symm a)) (e a) ∂μ :=
    lintegral_map (by exact (hf.comp e.symm.measurable).indicator hs) e.measurable
  rw [hm]
  refine lintegral_congr fun x => ?_
  by_cases hx : e x ∈ s <;> simp [Set.indicator, hx, Set.mem_preimage]

end MeasureTheory

#print axioms MeasureTheory.lintegral_piFinTwo_prod
#print axioms MeasureTheory.Measure.pi_withDensity_fin_two
#print axioms MeasureTheory.Measure.map_withDensity_measurableEquiv
