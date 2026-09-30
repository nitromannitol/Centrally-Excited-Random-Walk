import CERW.Support.Drift.Existence
import CERW.Support.Law.CondStep
import Mathlib.Probability.Kernel.CondDistrib

/-!
# The one-step conditional law of the walk with a drift field

As `CERW.Support.Law.condExp_next` for the Euclidean walk: under `IsDriftCERW`, the pair (path up
to time `n`, position at time `n + 1`) has the law of the path composed with `driftStepKernel`, so
`E[f(X_{n+1}) | ℱ_n] = Σ_e p_n(e) f(X_n + e)` almost surely for bounded `f`, with `ℱ` the natural
filtration of the walk.
-/

namespace CERW.Support.Drift

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The joint law of the past path and the next position is the law of the past path
composed with the one-step kernel. -/
theorem map_pastPath_prod_drift {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) (n : ℕ)
    [IsMarkovKernel (driftStepKernel (d := d) ε ξ n)] :
    μ.map (fun ω => (pastPath X n ω, X (n + 1) ω)) =
      (μ.map (pastPath X n)) ⊗ₘ driftStepKernel ε ξ n := by
  classical
  have hmeasY := measurable_pastPath hX.measurable n
  have hmeas : Measurable (fun ω => (pastPath X n ω, X (n + 1) ω)) :=
    hmeasY.prodMk (hX.measurable (n + 1))
  apply Measure.ext_of_singleton
  rintro ⟨p, z⟩
  set x : ℕ → Site d := fun j => if j = n + 1 then z else extendPath p j with hx
  have hxle : ∀ j ≤ n, x j = extendPath p j := fun j hj => by
    simp only [hx, if_neg (by omega : j ≠ n + 1)]
  have h1 : (fun ω => (pastPath X n ω, X (n + 1) ω)) ⁻¹' {(p, z)} =
      {ω | ∀ j ≤ n + 1, X j ω = x j} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp, hz⟩ j hj
      rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
      · rw [hxle j (Nat.lt_succ_iff.mp hjn), extendPath_of_le p (Nat.lt_succ_iff.mp hjn), ← hp]
        rfl
      · rw [le_antisymm hj hjn, hz]
        simp [hx]
    · intro h
      refine ⟨funext fun i => ?_, ?_⟩
      · have hi : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.2
        rw [show pastPath X n ω i = X i ω from rfl, h i (Nat.le_succ_of_le hi), hxle i hi,
          extendPath_of_le p hi]
      · rw [h (n + 1) le_rfl]
        simp [hx]
  have h2 : pastPath X n ⁻¹' {p} = {ω | ∀ j ≤ n, X j ω = x j} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro hp j hj
      rw [hxle j hj, extendPath_of_le p hj, ← hp]
      rfl
    · intro h
      funext i
      have hi : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.2
      rw [show pastPath X n ω i = X i ω from rfl, h i hi, hxle i hi, extendPath_of_le p hi]
  rw [Measure.map_apply hmeas (measurableSet_singleton _), h1, ← Set.singleton_prod_singleton,
    Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton, Measure.map_apply hmeasY (measurableSet_singleton _), h2,
    hX.step n x, mul_comm]
  congr 1
  change _ = driftNextLaw ε ξ n p {z}
  have hxn : x n = extendPath p n := hxle n le_rfl
  have hxz : x (n + 1) = z := by simp [hx]
  rw [driftNextLaw_singleton, hxz, hxn, driftStepProb_congr hxle]

/-- The conditional expectation of a bounded function of the next position given the past
is its mean under `driftStepProb`: `E[f(X_{n+1}) | ℱ_n] = Σ_e p_n(e) f(X_n + e)` almost surely. -/
theorem condExp_next_drift (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X)
    (f : Site d → ℝ) (hf : ∃ C, ∀ z, |f z| ≤ C) (n : ℕ) :
    μ[fun ω => f (X (n + 1) ω) | pathFiltration hX.measurable n] =ᵐ[μ]
      fun ω => ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) n e * f (X n ω + e) := by
  haveI : IsMarkovKernel (driftStepKernel (d := d) ε ξ n) :=
    isMarkovKernel_driftStepKernel hd hε hξ n
  obtain ⟨C, hC⟩ := hf
  have hmeasY := measurable_pastPath hX.measurable n
  have hfm : Measurable f := measurable_of_countable f
  have hint : Integrable (fun a => f (X (n + 1) a)) μ :=
    Integrable.of_bound (hfm.comp (hX.measurable (n + 1))).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hC _)
  have hcond := condExp_ae_eq_integral_condDistrib hmeasY (hX.measurable (n + 1)).aemeasurable
    hfm.stronglyMeasurable hint
  have hker := condDistrib_ae_eq_of_measure_eq_compProd (μ := μ) (Y := X (n + 1))
    (pastPath X n) (hX.measurable (n + 1)).aemeasurable (map_pastPath_prod_drift hX n)
  have hker' : ∀ᵐ ω ∂μ, condDistrib (X (n + 1)) (pastPath X n) μ (pastPath X n ω) =
      driftStepKernel ε ξ n (pastPath X n ω) := ae_of_ae_map hmeasY.aemeasurable hker
  refine hcond.trans ?_
  filter_upwards [hker'] with ω hω
  rw [hω]
  change ∫ y, f y ∂(driftNextLaw ε ξ n (pastPath X n ω)) = _
  have hdirac : ∀ e ∈ unitSteps d, Integrable f
      (ENNReal.ofReal (driftStepProb d ε ξ (extendPath (pastPath X n ω)) n e) •
        Measure.dirac (extendPath (pastPath X n ω) n + e)) :=
    fun e _ => (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  rw [driftNextLaw, integral_finsetSum_measure hdirac]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hext : ∀ j ≤ n, extendPath (pastPath X n ω) j = X j ω := fun j hj => by
    rw [extendPath_of_le _ hj]
    rfl
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (driftStepProb_nonneg hε hξ _ n e),
    smul_eq_mul, driftStepProb_congr hext, hext n le_rfl]


end CERW.Support.Drift
