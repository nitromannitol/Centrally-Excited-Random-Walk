import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional expectation on a product with an independent factor

A random variable that depends only on the first coordinate of a product space has the same
conditional expectation given the join of a sub-σ-algebra of the first factor and any
sub-σ-algebra of the second factor as it has given the first sub-σ-algebra alone. This lifts a
martingale to a martingale for the filtration that adjoins an independent filtration.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory

section Lift

variable {Ω : Type*} {Ξ : Type*}

/-- The join of a sub-σ-algebra of the first factor and a sub-σ-algebra of the second. -/
@[reducible]
def joinSigma (𝒢 : MeasurableSpace Ω) (ℋ : MeasurableSpace Ξ) :
    MeasurableSpace (Ω × Ξ) :=
  𝒢.comap Prod.fst ⊔ ℋ.comap Prod.snd

/-- The join of sub-σ-algebras is a sub-σ-algebra of the product σ-algebra. -/
theorem joinSigma_le {𝒢 : MeasurableSpace Ω} {m0 : MeasurableSpace Ω}
    {ℋ : MeasurableSpace Ξ} {mΞ : MeasurableSpace Ξ} (h𝒢 : 𝒢 ≤ m0) (hℋ : ℋ ≤ mΞ) :
    joinSigma 𝒢 ℋ ≤ @Prod.instMeasurableSpace Ω Ξ m0 mΞ := by
  have hfst : @Measurable _ _ (@Prod.instMeasurableSpace Ω Ξ m0 mΞ) m0 Prod.fst := measurable_fst
  have hsnd : @Measurable _ _ (@Prod.instMeasurableSpace Ω Ξ m0 mΞ) mΞ Prod.snd := measurable_snd
  exact sup_le ((MeasurableSpace.comap_mono h𝒢).trans hfst.comap_le)
    ((MeasurableSpace.comap_mono hℋ).trans hsnd.comap_le)

/-- A function of the first coordinate whose integral vanishes over every set of a sub-σ-algebra
of the first factor has vanishing integral over every set of the join of that sub-σ-algebra with
a sub-σ-algebra of the second factor. -/
private lemma setIntegral_comp_fst_joinSigma_eq_zero {𝒢 : MeasurableSpace Ω}
    {m0 : MeasurableSpace Ω} {ℋ : MeasurableSpace Ξ} {mΞ : MeasurableSpace Ξ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (h𝒢 : 𝒢 ≤ m0) (hℋ : ℋ ≤ mΞ) {H : Ω → ℝ} (hH : Integrable H μ)
    (h0 : ∀ A, MeasurableSet[𝒢] A → ∫ x in A, H x ∂μ = 0) :
    ∀ s, MeasurableSet[joinSigma 𝒢 ℋ] s → ∫ z in s, H z.1 ∂(μ.prod ν) = 0 := by
  have hH' : Integrable (fun z : Ω × Ξ => H z.1) (μ.prod ν) := hH.comp_fst ν
  have hJ : joinSigma 𝒢 ℋ ≤ @Prod.instMeasurableSpace Ω Ξ m0 mΞ := joinSigma_le h𝒢 hℋ
  have htot : ∫ z, H z.1 ∂(μ.prod ν) = 0 := by
    have h1 : ∫ x, H x ∂μ = 0 := by simpa using h0 Set.univ (@MeasurableSet.univ _ 𝒢)
    rw [integral_fun_fst, h1, smul_zero]
  intro s hs
  refine @MeasurableSpace.induction_on_inter (Ω × Ξ) (joinSigma 𝒢 ℋ)
    (fun s _ => ∫ z in s, H z.1 ∂(μ.prod ν) = 0)
    (Set.image2 (· ×ˢ ·) {s | MeasurableSet[𝒢] s} {t | MeasurableSet[ℋ] t})
    (@generateFrom_prod Ω Ξ 𝒢 ℋ).symm (@isPiSystem_prod Ω Ξ 𝒢 ℋ) ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    have h := setIntegral_prod_mul (μ := μ) (ν := ν) H (fun _ => (1 : ℝ)) A B
    simp only [mul_one] at h
    rw [h, h0 A hA, zero_mul]
  · intro t htm ih
    rw [setIntegral_compl (hJ _ htm) hH', ih, htot, sub_zero]
  · intro g hdisj hgm ih
    rw [integral_iUnion (fun i => hJ _ (hgm i)) hdisj hH'.integrableOn]
    simp [ih]

/-- Conditioning a function of the first coordinate on the join of a sub-σ-algebra of the first
factor and a sub-σ-algebra of the second factor only uses the first sub-σ-algebra. -/
theorem condExp_comp_fst_joinSigma {𝒢 : MeasurableSpace Ω} {m0 : MeasurableSpace Ω}
    {ℋ : MeasurableSpace Ξ} {mΞ : MeasurableSpace Ξ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (h𝒢 : 𝒢 ≤ m0) (hℋ : ℋ ≤ mΞ) {f : Ω → ℝ}
    (hf : Integrable f μ) :
    (μ.prod ν)[fun z => f z.1 | joinSigma 𝒢 ℋ] =ᵐ[μ.prod ν] fun z => (μ[f | 𝒢]) z.1 := by
  have hJ : joinSigma 𝒢 ℋ ≤ @Prod.instMeasurableSpace Ω Ξ m0 mΞ := joinSigma_le h𝒢 hℋ
  have hg_int : Integrable (fun z : Ω × Ξ => (μ[f | 𝒢]) z.1) (μ.prod ν) :=
    integrable_condExp.comp_fst ν
  have hfst : @Measurable _ _ (joinSigma 𝒢 ℋ) 𝒢 Prod.fst := Measurable.of_comap_le le_sup_left
  refine (ae_eq_condExp_of_forall_setIntegral_eq hJ (hf.comp_fst ν)
    (fun s _ _ => hg_int.integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_condExp.comp_measurable hfst).aestronglyMeasurable).symm
  have h := setIntegral_comp_fst_joinSigma_eq_zero μ ν h𝒢 hℋ
    (H := fun x => f x - (μ[f | 𝒢]) x) (hf.sub integrable_condExp)
    (fun A hA => by
      rw [integral_sub hf.integrableOn integrable_condExp.integrableOn,
        setIntegral_condExp h𝒢 hf hA, sub_self]) s hs
  rw [integral_sub (hf.comp_fst ν).integrableOn hg_int.integrableOn, sub_eq_zero] at h
  exact h.symm

/-- The filtration on the product whose `n`-th σ-algebra joins `ℱ n` with `𝒦 n`. -/
def liftFiltration {m0 : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ} (ℱ : Filtration ℕ m0)
    (𝒦 : ℕ → MeasurableSpace Ξ) (h𝒦 : Monotone 𝒦) (h𝒦le : ∀ n, 𝒦 n ≤ mΞ) :
    Filtration ℕ (@Prod.instMeasurableSpace Ω Ξ m0 mΞ) where
  seq n := joinSigma (ℱ n) (𝒦 n)
  mono' := fun _ _ hnm => sup_le_sup (MeasurableSpace.comap_mono (ℱ.mono hnm))
    (MeasurableSpace.comap_mono (h𝒦 hnm))
  le' := fun n => joinSigma_le (ℱ.le n) (h𝒦le n)

/-- A martingale of the first factor is a martingale of the product for the joined filtration. -/
theorem martingale_comp_fst {m0 : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) (𝒦 : ℕ → MeasurableSpace Ξ) (h𝒦 : Monotone 𝒦)
    (h𝒦le : ∀ n, 𝒦 n ≤ mΞ) {S : ℕ → Ω → ℝ} (hS : Martingale S ℱ μ) :
    Martingale (fun n z => S n z.1) (liftFiltration ℱ 𝒦 h𝒦 h𝒦le) (μ.prod ν) := by
  refine ⟨fun n => ?_, fun i j hij => ?_⟩
  · have hfst : @Measurable _ _ (joinSigma (ℱ n) (𝒦 n)) (ℱ n) Prod.fst :=
      Measurable.of_comap_le le_sup_left
    exact (hS.1 n).comp_measurable hfst
  · have h := condExp_comp_fst_joinSigma μ ν (ℱ.le i) (h𝒦le i) (hS.integrable j)
    exact h.trans (Measure.quasiMeasurePreserving_fst.ae_eq_comp (hS.2 i j hij))

end Lift

end CERW.Generic.Martingale.LilLower
