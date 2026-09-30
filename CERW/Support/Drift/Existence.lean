import CERW.Model.DriftLaw
import CERW.Support.Law.Existence
import CERW.Support.Drift.StepProb
import CERW.Support.Drift.Bridge
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The centrally excited random walk with a drift field exists

For `d ≥ 1`, `0 ≤ ε` and a drift field with `ε |ξ_i(z)| ≤ 1/d`, there is a probability space
carrying a process that satisfies `IsDriftCERW`: the Ionescu-Tulcea trajectory measure on
`ℕ → ℤ^d` whose kernel at time `n` is the law `driftStepProb` of the next step given the path,
exactly as in `CERW.Support.Law.exists_isCERW`. For a norm `Ψ` with subgradients `ξ` and
`ε max_i Ψ(e_i) < 1/d`, the hypothesis holds because `|ξ_i| ≤ Ψ(e_i)`; this is the non-vacuity
witness for the walk with norm `Ψ`.
-/

namespace CERW.Support.Drift

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law

variable {d : ℕ}

/-- The law of the position at time `n + 1` given the path `x 0, …, x n`, for the walk with drift
field `ξ`. -/
noncomputable def driftNextLaw (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (n : ℕ) (x : (i : Iic n) → Site d) : Measure (Site d) :=
  ∑ e ∈ unitSteps d,
    ENNReal.ofReal (driftStepProb d ε ξ (extendPath x) n e) • Measure.dirac (extendPath x n + e)

/-- The Ionescu-Tulcea kernel at time `n`: the path so far determines the law of the next
position through `nextLaw`. -/
noncomputable def driftStepKernel (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    Kernel ((i : Iic n) → Site d) (Site d) :=
  Kernel.ofFunOfCountable (driftNextLaw ε ξ n)

/-- The next-position law assigns to `z` the one-step probability of the step from `x n`
to `z`. -/
theorem driftNextLaw_singleton (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (n : ℕ) (x : (i : Iic n) → Site d) (z : Site d) :
    driftNextLaw ε ξ n x {z} = ENNReal.ofReal (driftStepProb d ε ξ (extendPath x) n (z - extendPath x n)) := by
  classical
  have hdirac : ∀ e : Site d, Measure.dirac (extendPath x n + e) {z} =
      if e = z - extendPath x n then 1 else 0 := by
    intro e
    rw [Measure.dirac_apply, Set.indicator_apply]
    simp only [Set.mem_singleton_iff, Pi.one_apply, eq_sub_iff_add_eq']
  simp only [driftNextLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    hdirac, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [driftStepProb_eq_zero ε ξ _ n h, ENNReal.ofReal_zero]

/-- For `d ≥ 1` and `0 ≤ ε < 1/d` the next-position law is a probability measure. -/
theorem isProbabilityMeasure_driftNextLaw (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) (n : ℕ)
    (x : (i : Iic n) → Site d) : IsProbabilityMeasure (driftNextLaw ε ξ n x) := by
  constructor
  simp only [driftNextLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun e _ => driftStepProb_nonneg hε hξ _ n e,
    sum_driftStepProb hd ε ξ _ n, ENNReal.ofReal_one]

/-- For `d ≥ 1` and `0 ≤ ε < 1/d` every kernel `stepKernel ε n` is Markov. -/
theorem isMarkovKernel_driftStepKernel (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) (n : ℕ) :
    IsMarkovKernel (driftStepKernel (d := d) ε ξ n) :=
  ⟨fun x => isProbabilityMeasure_driftNextLaw hd hε hξ n x⟩

/-- Centrally excited random walk exists: for `d ≥ 1` and `0 ≤ ε < 1/d` there are a
probability space and a process on it satisfying `IsCERW`. -/
theorem exists_isDriftCERW (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X := by
  classical
  haveI : ∀ n, IsMarkovKernel (driftStepKernel (d := d) ε ξ n) :=
    isMarkovKernel_driftStepKernel hd hε hξ
  set μ : Measure (ℕ → Site d) :=
    Kernel.trajMeasure (X := fun _ => Site d) (Measure.dirac 0) (driftStepKernel ε ξ) with hμ
  refine ⟨ℕ → Site d, inferInstance, μ, inferInstance, fun n ω => ω n,
    ⟨fun n => measurable_pi_apply n, ?_, ?_⟩⟩
  · -- the time-zero marginal of the trajectory measure is the initial law
    have hmarg : μ.map (Preorder.frestrictLe 0) =
        (Measure.dirac (0 : Site d)).map (MeasurableEquiv.piUnique _).symm := by
      rw [hμ, Kernel.trajMeasure, Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
    have hset : {ω : ℕ → Site d | ω 0 ≠ 0} =
        Preorder.frestrictLe 0 ⁻¹' {p | p ⟨0, Finset.mem_Iic.mpr le_rfl⟩ ≠ 0} := rfl
    rw [hset, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) (MeasurableSet.of_discrete),
      hmarg, Measure.map_dirac' (MeasurableEquiv.measurable _), Measure.dirac_apply]
    simp
  · intro n x
    set p : (i : Iic n) → Site d := fun i => x i with hp
    have hkey := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => Site d) (κ := driftStepKernel ε ξ) (μ₀ := Measure.dirac 0) (a := n)
    have hsucc : {ω : ℕ → Site d | ∀ j ≤ n + 1, ω j = x j} =
        (fun ω : ℕ → Site d => (Preorder.frestrictLe n ω, ω (n + 1))) ⁻¹'
          (({p} : Set ((i : Iic n) → Site d)) ×ˢ ({x (n + 1)} : Set (Site d))) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · intro h
        refine ⟨funext fun i => h i (Nat.le_succ_of_le (Finset.mem_Iic.mp i.2)), h (n + 1) le_rfl⟩
      · rintro ⟨h₁, h₂⟩ j hj
        rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
        · exact congrFun h₁ ⟨j, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hjn)⟩
        · rw [le_antisymm hj hjn]
          exact h₂
    have hle : {ω : ℕ → Site d | ∀ j ≤ n, ω j = x j} =
        Preorder.frestrictLe (π := fun _ : ℕ => Site d) n ⁻¹'
          ({p} : Set ((i : Iic n) → Site d)) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => funext fun i => h i (Finset.mem_Iic.mp i.2),
        fun h j hj => congrFun h ⟨j, Finset.mem_Iic.mpr hj⟩⟩
    have hext : ∀ j ≤ n, extendPath p j = x j := fun j hj => by
      rw [extendPath_of_le p hj]
    rw [hsucc, ← Measure.map_apply (by fun_prop) (MeasurableSet.of_discrete), ← hkey,
      Measure.compProd_apply_prod (MeasurableSet.of_discrete) (MeasurableSet.of_discrete),
      lintegral_singleton, hle, ← Measure.map_apply (Preorder.measurable_frestrictLe n)
        (MeasurableSet.of_discrete), mul_comm]
    congr 1
    change driftNextLaw ε ξ n p {x (n + 1)} = _
    rw [driftNextLaw_singleton, driftStepProb_congr hext, hext n le_rfl]

end CERW.Support.Drift
