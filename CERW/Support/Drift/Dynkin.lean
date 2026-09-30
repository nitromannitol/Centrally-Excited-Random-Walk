import CERW.Support.Drift.CondStep
import CERW.Support.Law.CoordinateDrift
import CERW.Support.Law.Dynkin
import CERW.Support.Law.StepMean
import CERW.Model.Martingales

/-!
# The Dynkin martingale of the walk with a drift field

The conditional means of a function after one step, and the Dynkin martingale
`f(X_t) - f(X_0) - Σ_{j<t} (Σ_e p_j(e) f(X_j + e) - f(X_j))`, for the one-step law
`driftStepProb` of the walk with drift field `ξ`, as in `CERW.Support.Law.Dynkin` for the
Euclidean walk. A first departure from `x` averages `f` to `P f(y) - ε ξ(x) · D f(y)`. The
definitions and lemmas that do not depend on the step law (`walkOp`, `centralDiff`,
`sum_mul_sub_mean_sq`, `extendPath_pastPath`, `stronglyMeasurable_comp_pastPath`, …) are those of
`CERW.Support.Law`. The pathwise martingale `CERW.dynkinMart` of the model files is the process
`driftDynkin`, for the drift law and for the Euclidean law.
-/

namespace CERW.Support.Drift

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law

variable {d : ℕ} {Ω : Type*}

/-- The inner product of a direction `w` with the central difference `D f(y)` is the coordinate
sum `Σ_i w_i (f(y+e_i)-f(y-e_i))/2`. -/
theorem inner_centralDiff_drift (w : EuclideanSpace ℝ (Fin d)) (y : Site d) (f : Site d → ℝ) :
    inner ℝ w (centralDiff f y) =
      ∑ i : Fin d, w i * ((f (y + unit i) - f (y - unit i)) / 2) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, centralDiff, PiLp.toLp_apply]

/-- A first departure with drift direction `w` averages `f` to `P f(y) - ε w · D f(y)`. -/
theorem sum_driftFirstStep_mul (ε : ℝ) (w : EuclideanSpace ℝ (Fin d)) (f : Site d → ℝ)
    (y : Site d) :
    ∑ e ∈ unitSteps d, driftFirstStep d ε w e * f (y + e) =
      walkOp f y - ε * inner ℝ w (centralDiff f y) := by
  rw [inner_centralDiff_drift, sum_unitSteps]
  have hpair : ∀ i : Fin d,
      driftFirstStep d ε w (unit i) * f (y + unit i) +
          driftFirstStep d ε w (-unit i) * f (y + -unit i) =
        (1 / (2 * d)) * (f (y + unit i) + f (y - unit i)) -
          ε * (w i * ((f (y + unit i) - f (y - unit i)) / 2)) := by
    intro i
    rw [driftFirstStep_unit, driftFirstStep_neg_unit, sub_eq_add_neg]
    ring_nf
  have hA : ∑ i : Fin d, (1 / (2 * d)) * (f (y + unit i) + f (y - unit i)) =
      walkOp f y := by
    rw [← Finset.mul_sum, walkOp, nbrSum, div_eq_mul_inv]
    ring
  simp_rw [hpair, Finset.sum_sub_distrib, hA, ← Finset.mul_sum]

/-- The mean of `f` after the next step of the path `x` at time `n`: a simple random walk mean,
corrected by `-ε ξ(x_n) · D f` at a first departure from a nonzero site. -/
theorem sum_driftStepProb_mul (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) (n : ℕ) (f : Site d → ℝ) :
    ∑ e ∈ unitSteps d, driftStepProb d ε ξ x n e * f (x n + e) =
      walkOp f (x n) - (if x n ≠ 0 ∧ x n ∉ (Finset.range n).image x then
        ε * inner ℝ (ξ (x n)) (centralDiff f (x n)) else 0) := by
  unfold driftStepProb
  split_ifs with h
  · rw [sum_driftFirstStep_mul]
  · rw [sum_srwStep_mul]
    ring

/-- The mean of `f` after the next step of the path `x` at time `j`. -/
noncomputable def driftNextMean (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (f : Site d → ℝ) (x : ℕ → Site d) (j : ℕ) : ℝ :=
  ∑ e ∈ unitSteps d, driftStepProb d ε ξ x j e * f (x j + e)

/-- The Dynkin martingale `f(X_t) - f(X_0) - Σ_{j<t} (Σ_e p_j(e) f(X_j + e) - f(X_j))`. -/
noncomputable def driftDynkin (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (f : Site d → ℝ)
    (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) : ℝ :=
  f (X t ω) - f (X 0 ω) -
    ∑ j ∈ range t, (driftNextMean ε ξ f (fun i => X i ω) j - f (X j ω))

/-- The increment of the Dynkin martingale is the new value of `f` minus its predicted mean. -/
theorem driftDynkin_succ_sub (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (f : Site d → ℝ)
    (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) :
    driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω =
      f (X (t + 1) ω) - driftNextMean ε ξ f (fun i => X i ω) t := by
  simp only [driftDynkin, sum_range_succ]
  ring

/-- The Dynkin martingale starts at `0`. -/
@[simp]
theorem driftDynkin_zero (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (f : Site d → ℝ)
    (X : ℕ → Ω → Site d) (ω : Ω) :
    driftDynkin ε ξ f X 0 ω = 0 := by
  simp [driftDynkin]

/-- The next-step mean depends on the path only up to the current time. -/
theorem driftNextMean_congr (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (f : Site d → ℝ)
    {x y : ℕ → Site d} {j : ℕ} (h : ∀ i ≤ j, x i = y i) :
    driftNextMean ε ξ f x j = driftNextMean ε ξ f y j := by
  simp only [driftNextMean, driftStepProb_congr h, h j le_rfl]

/-- The Dynkin martingale at time `t` as a function of the path `x_0, …, x_t`. -/
noncomputable def driftDynkinPath (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (f : Site d → ℝ) (t : ℕ) (p : (i : Iic t) → Site d) : ℝ :=
  f (extendPath p t) - f (extendPath p 0) -
    ∑ j ∈ range t, (driftNextMean ε ξ f (extendPath p) j - f (extendPath p j))

/-- The next-step mean along the walk, as a function of the past path. -/
theorem driftNextMean_pastPath (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (f : Site d → ℝ) (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) :
    driftNextMean ε ξ f (fun j => X j ω) t =
      driftNextMean ε ξ f (extendPath (pastPath X t ω)) t :=
  driftNextMean_congr ε ξ f fun _ hi => (extendPath_pastPath X hi ω).symm

/-- The Dynkin martingale at time `t` is a function of the past path. -/
theorem driftDynkin_eq_pastPath (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (f : Site d → ℝ) (X : ℕ → Ω → Site d) (t : ℕ) :
    driftDynkin ε ξ f X t = fun ω => driftDynkinPath ε ξ f t (pastPath X t ω) := by
  funext ω
  simp only [driftDynkin, driftDynkinPath]
  rw [extendPath_pastPath X le_rfl, extendPath_pastPath X (Nat.zero_le t)]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hjt : j ≤ t := (mem_range.mp hj).le
  rw [extendPath_pastPath X hjt,
    driftNextMean_congr ε ξ f fun _ hi => (extendPath_pastPath X (hi.trans hjt) ω).symm]

/-- The coordinate `x ↦ x_k` has next-step mean `x_k - ε ξ(x)_k` at a first departure from
`x ≠ 0`, and `x_k` otherwise. -/
theorem driftNextMean_coord (hd : 1 ≤ d) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) (t : ℕ) (k : Fin d) :
    driftNextMean ε ξ (fun z : Site d => ((z k : ℤ) : ℝ)) x t =
      ((x t k : ℤ) : ℝ) - (if x t ≠ 0 ∧ x t ∉ (Finset.range t).image x then
        ε * ξ (x t) k else 0) := by
  rw [driftNextMean, sum_driftStepProb_mul ε ξ x t (fun z : Site d => ((z k : ℤ) : ℝ)),
    walkOp_coord hd, centralDiff_coord, EuclideanSpace.inner_single_right]
  simp

/-- The conditional mean `Σ_e p(e) (f(X_j + e) - f(X_j))` of the model is the next-step mean
minus `f(X_j)`, for the drift one-step law. -/
theorem stepMean_driftStepProb (hd : 1 ≤ d) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (f : Site d → ℝ) (x : ℕ → Site d) (j : ℕ) :
    stepMean (driftStepProb d ε ξ) f x j = driftNextMean ε ξ f x j - f (x j) := by
  simp only [stepMean, driftNextMean, mul_sub, sum_sub_distrib, ← sum_mul,
    sum_driftStepProb hd ε ξ x j, one_mul]

/-- The pathwise Dynkin martingale of the model for the drift one-step law is `driftDynkin`. -/
theorem dynkinMart_driftStepProb_eq_driftDynkin (hd : 1 ≤ d) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (f : Site d → ℝ) (X : ℕ → Ω → Site d) (t : ℕ)
    (ω : Ω) :
    dynkinMart (driftStepProb d ε ξ) f (fun j => X j ω) t = driftDynkin ε ξ f X t ω := by
  simp only [dynkinMart, driftDynkin, stepMean_driftStepProb hd]

/-- The conditional mean `Σ_e p(e) (f(X_j + e) - f(X_j))` of the model is the next-step mean
minus `f(X_j)`, for the Euclidean one-step law. -/
theorem stepMean_stepProb (hd : 1 ≤ d) (ε : ℝ) (f : Site d → ℝ) (x : ℕ → Site d) (j : ℕ) :
    stepMean (stepProb d ε) f x j = nextMean ε f x j - f (x j) := by
  simp only [stepMean, nextMean, mul_sub, sum_sub_distrib, ← sum_mul,
    sum_stepProb hd ε x j, one_mul]

/-- The pathwise Dynkin martingale of the model for the Euclidean one-step law is `dynkin`. -/
theorem dynkinMart_stepProb_eq_dynkin (hd : 1 ≤ d) (ε : ℝ) (f : Site d → ℝ)
    (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) :
    dynkinMart (stepProb d ε) f (fun j => X j ω) t = dynkin ε f X t ω := by
  simp only [dynkinMart, dynkin, stepMean_stepProb hd]

variable [MeasurableSpace Ω]

section Law

variable {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → Site d}

/-- The conditional expectation of a function of the past path and the next position is its
mean over the next step: `E[h(X_{0..n}, X_{n+1}) | ℱ_n] = Σ_e p_n(e) h(X_{0..n}, X_n + e)`. -/
theorem condExp_path_next_drift (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) (n : ℕ) (h : ((i : Iic n) → Site d) → Site d → ℝ)
    (hint : Integrable (fun ω => h (pastPath X n ω) (X (n + 1) ω)) μ) :
    μ[fun ω => h (pastPath X n ω) (X (n + 1) ω) | pathFiltration hX.measurable n] =ᵐ[μ]
      fun ω => ∑ e ∈ unitSteps d,
        driftStepProb d ε ξ (fun j => X j ω) n e * h (pastPath X n ω) (X n ω + e) := by
  haveI : IsMarkovKernel (driftStepKernel (d := d) ε ξ n) :=
    isMarkovKernel_driftStepKernel hd hε hξ n
  have hmeasY := measurable_pastPath hX.measurable n
  have hfm : StronglyMeasurable (Function.uncurry h) :=
    (measurable_of_countable _).stronglyMeasurable
  have hcond := condExp_prod_ae_eq_integral_condDistrib hmeasY
    (hX.measurable (n + 1)).aemeasurable hfm hint
  have hker := condDistrib_ae_eq_of_measure_eq_compProd (μ := μ) (Y := X (n + 1))
    (pastPath X n) (hX.measurable (n + 1)).aemeasurable (map_pastPath_prod_drift hX n)
  have hker' : ∀ᵐ ω ∂μ, condDistrib (X (n + 1)) (pastPath X n) μ (pastPath X n ω) =
      driftStepKernel ε ξ n (pastPath X n ω) := ae_of_ae_map hmeasY.aemeasurable hker
  refine hcond.trans ?_
  filter_upwards [hker'] with ω hω
  rw [hω]
  change ∫ y, h (pastPath X n ω) y ∂(driftNextLaw ε ξ n (pastPath X n ω)) = _
  have hdirac : ∀ e ∈ unitSteps d, Integrable (h (pastPath X n ω))
      (ENNReal.ofReal (driftStepProb d ε ξ (extendPath (pastPath X n ω)) n e) •
        Measure.dirac (extendPath (pastPath X n ω) n + e)) :=
    fun e _ => (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  rw [driftNextLaw, integral_finsetSum_measure hdirac]
  refine sum_congr rfl fun e _ => ?_
  have hext : ∀ j ≤ n, extendPath (pastPath X n ω) j = X j ω :=
    fun j hj => extendPath_pastPath X hj ω
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (driftStepProb_nonneg hε hξ _ n e),
    smul_eq_mul, driftStepProb_congr hext, hext n le_rfl]

/-- Almost surely every step of the walk is a unit step. -/
theorem ae_sub_mem_unitSteps_drift (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) (n : ℕ) : ∀ᵐ ω ∂μ, X (n + 1) ω - X n ω ∈ unitSteps d := by
  classical
  haveI : IsMarkovKernel (driftStepKernel (d := d) ε ξ n) :=
    isMarkovKernel_driftStepKernel hd hε hξ n
  have hmeasY := measurable_pastPath hX.measurable n
  have hmeas : Measurable (fun ω => (pastPath X n ω, X (n + 1) ω)) :=
    hmeasY.prodMk (hX.measurable (n + 1))
  set S : Set (((i : Iic n) → Site d) × Site d) :=
    {q | q.2 - extendPath q.1 n ∉ unitSteps d} with hS
  have hSm : MeasurableSet S := (Set.to_countable S).measurableSet
  have hpre : {ω | ¬ (X (n + 1) ω - X n ω ∈ unitSteps d)} =
      (fun ω => (pastPath X n ω, X (n + 1) ω)) ⁻¹' S := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS, extendPath_pastPath X le_rfl ω]
  have hzero : ∀ p, driftStepKernel ε ξ n p (Prod.mk p ⁻¹' S) = 0 := by
    intro p
    change driftNextLaw ε ξ n p _ = 0
    simp only [driftNextLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul]
    refine sum_eq_zero fun e he => ?_
    rw [Measure.dirac_apply, Set.indicator_of_notMem, mul_zero]
    simp [hS, he]
  rw [ae_iff, hpre, ← Measure.map_apply hmeas hSm, map_pastPath_prod_drift hX n,
    Measure.compProd_apply hSm]
  simp [hzero]

/-- Almost surely the walk is within distance `n` of the origin at every time `n`. -/
theorem ae_euclidNorm_le_drift (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) : ∀ᵐ ω ∂μ, ∀ n, euclidNorm (X n ω) ≤ n := by
  have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  have hs : ∀ᵐ ω ∂μ, ∀ n, X (n + 1) ω - X n ω ∈ unitSteps d :=
    ae_all_iff.mpr (ae_sub_mem_unitSteps_drift hd hε hξ hX)
  filter_upwards [h0, hs] with ω h0 hs n
  exact CERW.Support.Occupation.euclidNorm_le_of_steps (fun j => X j ω) h0 hs n

/-- Every function of the past path and the next position is integrable: almost surely both
range over finite sets, because `|X_j| ≤ j`. -/
theorem integrable_path_next_drift (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) (n : ℕ) (G : ((i : Iic n) → Site d) → Site d → ℝ) :
    Integrable (fun ω => G (pastPath X n ω) (X (n + 1) ω)) μ := by
  classical
  set T := Fintype.piFinset (fun _ : Iic n => ballFinset d n) ×ˢ ballFinset d ((n : ℝ) + 1)
  refine Integrable.of_bound (C := ∑ q ∈ T, |G q.1 q.2|)
    ((measurable_of_countable (Function.uncurry G)).comp
      ((measurable_pastPath hX.measurable n).prodMk
        (hX.measurable (n + 1)))).aestronglyMeasurable ?_
  filter_upwards [ae_euclidNorm_le_drift hd hε hξ hX] with ω hω
  have hmem : (pastPath X n ω, X (n + 1) ω) ∈ T := by
    refine mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
    · rw [mem_ballFinset_iff]
      exact (hω i).trans (by exact_mod_cast mem_Iic.mp i.2)
    · rw [mem_ballFinset_iff]
      exact_mod_cast hω (n + 1)
  rw [Real.norm_eq_abs]
  exact single_le_sum (f := fun q => |G q.1 q.2|) (fun _ _ => abs_nonneg _) hmem

/-- For every `f : ℤ^d → ℝ`, the Dynkin process is a martingale for the natural filtration. -/
theorem martingale_driftDynkin (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) (f : Site d → ℝ) :
    Martingale (driftDynkin ε ξ f X) (pathFiltration hX.measurable) μ := by
  have hint : ∀ t, Integrable (driftDynkin ε ξ f X t) μ := fun t => by
    rw [driftDynkin_eq_pastPath]
    exact integrable_path_next_drift hd hε hξ hX t fun p _ => driftDynkinPath ε ξ f t p
  refine martingale_of_condExp_sub_eq_zero_nat (fun t => ?_) hint fun t => ?_
  · rw [driftDynkin_eq_pastPath]
    exact stronglyMeasurable_comp_pastPath hX.measurable t (driftDynkinPath ε ξ f t)
  · have hinc : driftDynkin ε ξ f X (t + 1) - driftDynkin ε ξ f X t = fun ω =>
        f (X (t + 1) ω) - driftNextMean ε ξ f (extendPath (pastPath X t ω)) t := by
      funext ω
      rw [Pi.sub_apply, driftDynkin_succ_sub, driftNextMean_pastPath]
    have hint1 : Integrable (fun ω => f (X (t + 1) ω)) μ :=
      integrable_path_next_drift hd hε hξ hX t fun _ z => f z
    have hint2 : Integrable (fun ω => driftNextMean ε ξ f (extendPath (pastPath X t ω)) t) μ :=
      integrable_path_next_drift hd hε hξ hX t fun p _ =>
        driftNextMean ε ξ f (extendPath p) t
    have hnext := condExp_path_next_drift hd hε hξ hX t (fun _ z => f z) hint1
    have hmeas := condExp_of_stronglyMeasurable ((pathFiltration hX.measurable).le t)
      (stronglyMeasurable_comp_pastPath hX.measurable t
        fun p => driftNextMean ε ξ f (extendPath p) t) hint2
    rw [hinc]
    refine (condExp_sub hint1 hint2 _).trans ?_
    rw [hmeas]
    filter_upwards [hnext] with ω hω
    rw [Pi.sub_apply, hω, Pi.zero_apply, ← driftNextMean_pastPath]
    simp only [driftNextMean, sub_self]

/-- Almost surely, an increment of the Dynkin martingale at time `t` is at most twice any bound
on the one-step oscillation of `f` at `X_t`. -/
theorem ae_abs_driftDynkin_succ_sub_le (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) (f : Site d → ℝ) :
    ∀ᵐ ω ∂μ, ∀ t (B : ℝ), (∀ e ∈ unitSteps d, |f (X t ω + e) - f (X t ω)| ≤ B) →
      |driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω| ≤ 2 * B := by
  filter_upwards [ae_all_iff.mpr (ae_sub_mem_unitSteps_drift hd hε hξ hX)] with ω hs t B hB
  have hp1 : ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e = 1 :=
    sum_driftStepProb hd ε ξ _ t
  have hsplit : driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω =
      (f (X t ω + (X (t + 1) ω - X t ω)) - f (X t ω)) -
        ∑ e ∈ unitSteps d,
          driftStepProb d ε ξ (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω)) := by
    rw [driftDynkin_succ_sub, add_sub_cancel]
    simp only [driftNextMean, mul_sub, sum_sub_distrib, ← sum_mul, hp1]
    ring
  rw [hsplit]
  have hsum : |∑ e ∈ unitSteps d,
      driftStepProb d ε ξ (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))| ≤ B := by
    calc |∑ e ∈ unitSteps d,
          driftStepProb d ε ξ (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))|
        ≤ ∑ e ∈ unitSteps d,
            |driftStepProb d ε ξ (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e * B := by
          refine sum_le_sum fun e he => ?_
          rw [abs_mul, abs_of_nonneg (driftStepProb_nonneg hε hξ _ t e)]
          exact mul_le_mul_of_nonneg_left (hB e he) (driftStepProb_nonneg hε hξ _ t e)
      _ = B := by rw [← sum_mul, hp1, one_mul]
  calc |(f (X t ω + (X (t + 1) ω - X t ω)) - f (X t ω)) -
        ∑ e ∈ unitSteps d,
          driftStepProb d ε ξ (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))|
      ≤ |f (X t ω + (X (t + 1) ω - X t ω)) - f (X t ω)| +
        |∑ e ∈ unitSteps d,
          driftStepProb d ε ξ (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))| :=
        abs_sub _ _
    _ ≤ B + B := add_le_add (hB _ (hs t)) hsum
    _ = 2 * B := by ring

/-- The conditional variance of an increment of the Dynkin martingale is at most the one-step
mean square oscillation `Σ_e p_t(e) (f(X_t + e) - f(X_t))²`. -/
theorem condExp_sq_driftDynkin_succ_sub_le (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) (f : Site d → ℝ) (t : ℕ) :
    μ[fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) ^ 2 |
        pathFiltration hX.measurable t] ≤ᵐ[μ]
      fun ω => ∑ e ∈ unitSteps d,
        driftStepProb d ε ξ (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω)) ^ 2 := by
  set h : ((i : Iic t) → Site d) → Site d → ℝ :=
    fun p z => (f z - driftNextMean ε ξ f (extendPath p) t) ^ 2 with hh
  have hsq : (fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) ^ 2) =
      fun ω => h (pastPath X t ω) (X (t + 1) ω) := by
    funext ω
    rw [driftDynkin_succ_sub, driftNextMean_pastPath]
  have hint := integrable_path_next_drift hd hε hξ hX t h
  rw [hsq]
  filter_upwards [condExp_path_next_drift hd hε hξ hX t h hint] with ω hω
  rw [hω]
  simp only [hh, ← driftNextMean_pastPath]
  have hvar := sum_mul_sub_mean_sq (unitSteps d)
    (fun e => driftStepProb d ε ξ (fun j => X j ω) t e)
    (fun e => f (X t ω + e)) (sum_driftStepProb hd ε ξ _ t) (f (X t ω))
  simp only [driftNextMean]
  rw [hvar]
  linarith [sq_nonneg (∑ j ∈ unitSteps d,
    driftStepProb d ε ξ (fun j => X j ω) t j * f (X t ω + j) - f (X t ω))]

end Law

end CERW.Support.Drift
