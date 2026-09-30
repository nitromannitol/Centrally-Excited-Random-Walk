import CERW.Support.Law.CondStep
import CERW.Support.Occupation.Facts
import Mathlib.Probability.Martingale.Basic

/-!
# The Dynkin martingale of the walk

For `f : ℤ^d → ℝ`, the process
`f(X_t) - f(X_0) - Σ_{j<t} (Σ_e p_j(e) f(X_j + e) - f(X_j))`
is a martingale for the natural filtration (`eq:dynkin`, and the decompositions behind
`eq:radialmart`, `eq:vector` and `eq:quadratic`). No growth condition on `f` is needed: almost
surely `|X_j| ≤ j`, so up to any fixed time only finitely many values of `f` enter. An increment
is at most twice the largest one-step oscillation of `f` at the current position. The conditional
variance of an increment is at most the mean square oscillation
`Σ_e p_t(e) (f(X_t + e) - f(X_t))²`.
-/

namespace CERW.Support.Law

open MeasureTheory ProbabilityTheory LatticeProb Finset

variable {d : ℕ} {Ω : Type*}

/-- The mean of `f` after the next step of the path `x` at time `j`. -/
noncomputable def nextMean (ε : ℝ) (f : Site d → ℝ) (x : ℕ → Site d) (j : ℕ) : ℝ :=
  ∑ e ∈ unitSteps d, stepProb d ε x j e * f (x j + e)

/-- The Dynkin martingale `f(X_t) - f(X_0) - Σ_{j<t} (Σ_e p_j(e) f(X_j + e) - f(X_j))`. -/
noncomputable def dynkin (ε : ℝ) (f : Site d → ℝ) (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) : ℝ :=
  f (X t ω) - f (X 0 ω) -
    ∑ j ∈ range t, (nextMean ε f (fun i => X i ω) j - f (X j ω))

/-- The increment of the Dynkin martingale is the new value of `f` minus its predicted mean. -/
theorem dynkin_succ_sub (ε : ℝ) (f : Site d → ℝ) (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) :
    dynkin ε f X (t + 1) ω - dynkin ε f X t ω =
      f (X (t + 1) ω) - nextMean ε f (fun i => X i ω) t := by
  simp only [dynkin, sum_range_succ]
  ring

/-- The Dynkin martingale starts at `0`. -/
@[simp]
theorem dynkin_zero (ε : ℝ) (f : Site d → ℝ) (X : ℕ → Ω → Site d) (ω : Ω) :
    dynkin ε f X 0 ω = 0 := by
  simp [dynkin]

/-- With weights summing to one and mean `m = Σ p a`, the spread about `m` is the spread about
any `c` minus `(m - c)²`. -/
theorem sum_mul_sub_mean_sq {ι : Type*} (s : Finset ι) (p a : ι → ℝ)
    (hp : ∑ i ∈ s, p i = 1) (c : ℝ) :
    ∑ i ∈ s, p i * (a i - ∑ j ∈ s, p j * a j) ^ 2 =
      ∑ i ∈ s, p i * (a i - c) ^ 2 - (∑ j ∈ s, p j * a j - c) ^ 2 := by
  set m := ∑ j ∈ s, p j * a j with hm
  have hterm : ∀ i ∈ s, p i * (a i - m) ^ 2 =
      p i * (a i - c) ^ 2 - 2 * (m - c) * (p i * a i) + (m ^ 2 - c ^ 2) * p i :=
    fun i _ => by ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hp, ← hm]
  ring

/-- The next-step mean depends on the path only up to the current time. -/
theorem nextMean_congr (ε : ℝ) (f : Site d → ℝ) {x y : ℕ → Site d} {j : ℕ}
    (h : ∀ i ≤ j, x i = y i) : nextMean ε f x j = nextMean ε f y j := by
  simp only [nextMean, stepProb_congr h, h j le_rfl]

/-- The extension of the past path at time `t` returns the walk up to time `t`. -/
theorem extendPath_pastPath (X : ℕ → Ω → Site d) {t j : ℕ} (hj : j ≤ t) (ω : Ω) :
    extendPath (pastPath X t ω) j = X j ω := by
  rw [extendPath_of_le _ hj]
  rfl

/-- A function of a site is bounded on each lattice ball. -/
theorem exists_abs_le_of_euclidNorm_le (g : Site d → ℝ) (r : ℝ) :
    ∃ C, ∀ x, euclidNorm x ≤ r → |g x| ≤ C :=
  ⟨∑ y ∈ ballFinset d r, |g y|, fun _ hx =>
    single_le_sum (f := fun y => |g y|) (fun _ _ => abs_nonneg _) (mem_ballFinset_iff.mpr hx)⟩

/-- The Dynkin martingale at time `t` as a function of the path `x_0, …, x_t`. -/
noncomputable def dynkinPath (ε : ℝ) (f : Site d → ℝ) (t : ℕ) (p : (i : Iic t) → Site d) : ℝ :=
  f (extendPath p t) - f (extendPath p 0) -
    ∑ j ∈ range t, (nextMean ε f (extendPath p) j - f (extendPath p j))

/-- The next-step mean along the walk, as a function of the past path. -/
theorem nextMean_pastPath (ε : ℝ) (f : Site d → ℝ) (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) :
    nextMean ε f (fun j => X j ω) t = nextMean ε f (extendPath (pastPath X t ω)) t :=
  nextMean_congr ε f fun _ hi => (extendPath_pastPath X hi ω).symm

/-- The Dynkin martingale at time `t` is a function of the past path. -/
theorem dynkin_eq_pastPath (ε : ℝ) (f : Site d → ℝ) (X : ℕ → Ω → Site d) (t : ℕ) :
    dynkin ε f X t = fun ω => dynkinPath ε f t (pastPath X t ω) := by
  funext ω
  simp only [dynkin, dynkinPath]
  rw [extendPath_pastPath X le_rfl, extendPath_pastPath X (Nat.zero_le t)]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hjt : j ≤ t := (mem_range.mp hj).le
  rw [extendPath_pastPath X hjt,
    nextMean_congr ε f fun _ hi => (extendPath_pastPath X (hi.trans hjt) ω).symm]

variable [MeasurableSpace Ω]

/-- A function of the past path is measurable for the natural filtration. -/
theorem stronglyMeasurable_comp_pastPath {X : ℕ → Ω → Site d}
    (hX : ∀ n, Measurable (X n)) (t : ℕ) (G : ((i : Iic t) → Site d) → ℝ) :
    StronglyMeasurable[pathFiltration hX t] (fun ω => G (pastPath X t ω)) :=
  ((measurable_of_countable G).comp (comap_measurable _)).stronglyMeasurable

section Law

variable {ε : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d}

/-- The conditional expectation of a function of the past path and the next position is its
mean over the next step: `E[h(X_{0..n}, X_{n+1}) | ℱ_n] = Σ_e p_n(e) h(X_{0..n}, X_n + e)`. -/
theorem condExp_path_next (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) (n : ℕ) (h : ((i : Iic n) → Site d) → Site d → ℝ)
    (hint : Integrable (fun ω => h (pastPath X n ω) (X (n + 1) ω)) μ) :
    μ[fun ω => h (pastPath X n ω) (X (n + 1) ω) | pathFiltration hX.measurable n] =ᵐ[μ]
      fun ω => ∑ e ∈ unitSteps d,
        stepProb d ε (fun j => X j ω) n e * h (pastPath X n ω) (X n ω + e) := by
  haveI : IsMarkovKernel (stepKernel (d := d) ε n) := isMarkovKernel_stepKernel hd hε hεd n
  have hmeasY := measurable_pastPath hX.measurable n
  have hfm : StronglyMeasurable (Function.uncurry h) :=
    (measurable_of_countable _).stronglyMeasurable
  have hcond := condExp_prod_ae_eq_integral_condDistrib hmeasY
    (hX.measurable (n + 1)).aemeasurable hfm hint
  have hker := condDistrib_ae_eq_of_measure_eq_compProd (μ := μ) (Y := X (n + 1))
    (pastPath X n) (hX.measurable (n + 1)).aemeasurable (map_pastPath_prod hX n)
  have hker' : ∀ᵐ ω ∂μ, condDistrib (X (n + 1)) (pastPath X n) μ (pastPath X n ω) =
      stepKernel ε n (pastPath X n ω) := ae_of_ae_map hmeasY.aemeasurable hker
  refine hcond.trans ?_
  filter_upwards [hker'] with ω hω
  rw [hω]
  change ∫ y, h (pastPath X n ω) y ∂(nextLaw ε n (pastPath X n ω)) = _
  have hdirac : ∀ e ∈ unitSteps d, Integrable (h (pastPath X n ω))
      (ENNReal.ofReal (stepProb d ε (extendPath (pastPath X n ω)) n e) •
        Measure.dirac (extendPath (pastPath X n ω) n + e)) :=
    fun e _ => (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  rw [nextLaw, integral_finsetSum_measure hdirac]
  refine sum_congr rfl fun e _ => ?_
  have hext : ∀ j ≤ n, extendPath (pastPath X n ω) j = X j ω :=
    fun j hj => extendPath_pastPath X hj ω
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (stepProb_nonneg hε hεd _ n e),
    smul_eq_mul, stepProb_congr hext, hext n le_rfl]

/-- Almost surely every step of the walk is a unit step. -/
theorem ae_sub_mem_unitSteps (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) (n : ℕ) : ∀ᵐ ω ∂μ, X (n + 1) ω - X n ω ∈ unitSteps d := by
  classical
  haveI : IsMarkovKernel (stepKernel (d := d) ε n) := isMarkovKernel_stepKernel hd hε hεd n
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
  have hzero : ∀ p, stepKernel ε n p (Prod.mk p ⁻¹' S) = 0 := by
    intro p
    change nextLaw ε n p _ = 0
    simp only [nextLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine sum_eq_zero fun e he => ?_
    rw [Measure.dirac_apply, Set.indicator_of_notMem, mul_zero]
    simp [hS, he]
  rw [ae_iff, hpre, ← Measure.map_apply hmeas hSm, map_pastPath_prod hX n,
    Measure.compProd_apply hSm]
  simp [hzero]

/-- Almost surely the walk is within distance `n` of the origin at every time `n`. -/
theorem ae_euclidNorm_le (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) : ∀ᵐ ω ∂μ, ∀ n, euclidNorm (X n ω) ≤ n := by
  have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  have hs : ∀ᵐ ω ∂μ, ∀ n, X (n + 1) ω - X n ω ∈ unitSteps d :=
    ae_all_iff.mpr (ae_sub_mem_unitSteps hd hε hεd hX)
  filter_upwards [h0, hs] with ω h0 hs n
  exact CERW.Support.Occupation.euclidNorm_le_of_steps (fun j => X j ω) h0 hs n

/-- Every function of the past path and the next position is integrable: almost surely both
range over finite sets, because `|X_j| ≤ j`. -/
theorem integrable_path_next (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) (n : ℕ) (G : ((i : Iic n) → Site d) → Site d → ℝ) :
    Integrable (fun ω => G (pastPath X n ω) (X (n + 1) ω)) μ := by
  classical
  set T := Fintype.piFinset (fun _ : Iic n => ballFinset d n) ×ˢ ballFinset d ((n : ℝ) + 1)
  refine Integrable.of_bound (C := ∑ q ∈ T, |G q.1 q.2|)
    ((measurable_of_countable (Function.uncurry G)).comp
      ((measurable_pastPath hX.measurable n).prodMk
        (hX.measurable (n + 1)))).aestronglyMeasurable ?_
  filter_upwards [ae_euclidNorm_le hd hε hεd hX] with ω hω
  have hmem : (pastPath X n ω, X (n + 1) ω) ∈ T := by
    refine mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
    · rw [mem_ballFinset_iff]
      exact (hω i).trans (by exact_mod_cast mem_Iic.mp i.2)
    · rw [mem_ballFinset_iff]
      exact_mod_cast hω (n + 1)
  rw [Real.norm_eq_abs]
  exact single_le_sum (f := fun q => |G q.1 q.2|) (fun _ _ => abs_nonneg _) hmem

/-- For every `f : ℤ^d → ℝ`, the Dynkin process is a martingale for the natural filtration. -/
theorem martingale_dynkin (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) (f : Site d → ℝ) :
    Martingale (dynkin ε f X) (pathFiltration hX.measurable) μ := by
  have hint : ∀ t, Integrable (dynkin ε f X t) μ := fun t => by
    rw [dynkin_eq_pastPath]
    exact integrable_path_next hd hε hεd hX t fun p _ => dynkinPath ε f t p
  refine martingale_of_condExp_sub_eq_zero_nat (fun t => ?_) hint fun t => ?_
  · rw [dynkin_eq_pastPath]
    exact stronglyMeasurable_comp_pastPath hX.measurable t (dynkinPath ε f t)
  · have hinc : dynkin ε f X (t + 1) - dynkin ε f X t = fun ω =>
        f (X (t + 1) ω) - nextMean ε f (extendPath (pastPath X t ω)) t := by
      funext ω
      rw [Pi.sub_apply, dynkin_succ_sub, nextMean_pastPath]
    have hint1 : Integrable (fun ω => f (X (t + 1) ω)) μ :=
      integrable_path_next hd hε hεd hX t fun _ z => f z
    have hint2 : Integrable (fun ω => nextMean ε f (extendPath (pastPath X t ω)) t) μ :=
      integrable_path_next hd hε hεd hX t fun p _ => nextMean ε f (extendPath p) t
    have hnext := condExp_path_next hd hε hεd hX t (fun _ z => f z) hint1
    have hmeas := condExp_of_stronglyMeasurable ((pathFiltration hX.measurable).le t)
      (stronglyMeasurable_comp_pastPath hX.measurable t
        fun p => nextMean ε f (extendPath p) t) hint2
    rw [hinc]
    refine (condExp_sub hint1 hint2 _).trans ?_
    rw [hmeas]
    filter_upwards [hnext] with ω hω
    rw [Pi.sub_apply, hω, Pi.zero_apply, ← nextMean_pastPath]
    simp only [nextMean, sub_self]

/-- Almost surely, an increment of the Dynkin martingale at time `t` is at most twice any bound
on the one-step oscillation of `f` at `X_t`. -/
theorem ae_abs_dynkin_succ_sub_le (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) (f : Site d → ℝ) :
    ∀ᵐ ω ∂μ, ∀ t (B : ℝ), (∀ e ∈ unitSteps d, |f (X t ω + e) - f (X t ω)| ≤ B) →
      |dynkin ε f X (t + 1) ω - dynkin ε f X t ω| ≤ 2 * B := by
  filter_upwards [ae_all_iff.mpr (ae_sub_mem_unitSteps hd hε hεd hX)] with ω hs t B hB
  have hp1 : ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e = 1 := sum_stepProb hd ε _ t
  have hsplit : dynkin ε f X (t + 1) ω - dynkin ε f X t ω =
      (f (X t ω + (X (t + 1) ω - X t ω)) - f (X t ω)) -
        ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω)) := by
    rw [dynkin_succ_sub, add_sub_cancel]
    simp only [nextMean, mul_sub, sum_sub_distrib, ← sum_mul, hp1]
    ring
  rw [hsplit]
  have hsum : |∑ e ∈ unitSteps d,
      stepProb d ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))| ≤ B := by
    calc |∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))|
        ≤ ∑ e ∈ unitSteps d,
            |stepProb d ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e * B := by
          refine sum_le_sum fun e he => ?_
          rw [abs_mul, abs_of_nonneg (stepProb_nonneg hε hεd _ t e)]
          exact mul_le_mul_of_nonneg_left (hB e he) (stepProb_nonneg hε hεd _ t e)
      _ = B := by rw [← sum_mul, hp1, one_mul]
  calc |(f (X t ω + (X (t + 1) ω - X t ω)) - f (X t ω)) -
        ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))|
      ≤ |f (X t ω + (X (t + 1) ω - X t ω)) - f (X t ω)| +
        |∑ e ∈ unitSteps d,
          stepProb d ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω))| :=
        abs_sub _ _
    _ ≤ B + B := add_le_add (hB _ (hs t)) hsum
    _ = 2 * B := by ring

/-- The conditional variance of an increment of the Dynkin martingale is at most the one-step
mean square oscillation `Σ_e p_t(e) (f(X_t + e) - f(X_t))²`. -/
theorem condExp_sq_dynkin_succ_sub_le (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) (f : Site d → ℝ) (t : ℕ) :
    μ[fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2 |
        pathFiltration hX.measurable t] ≤ᵐ[μ]
      fun ω => ∑ e ∈ unitSteps d,
        stepProb d ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω)) ^ 2 := by
  set h : ((i : Iic t) → Site d) → Site d → ℝ :=
    fun p z => (f z - nextMean ε f (extendPath p) t) ^ 2 with hh
  have hsq : (fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2) =
      fun ω => h (pastPath X t ω) (X (t + 1) ω) := by
    funext ω
    rw [dynkin_succ_sub, nextMean_pastPath]
  have hint := integrable_path_next hd hε hεd hX t h
  rw [hsq]
  filter_upwards [condExp_path_next hd hε hεd hX t h hint] with ω hω
  rw [hω]
  simp only [hh, ← nextMean_pastPath]
  have hvar := sum_mul_sub_mean_sq (unitSteps d) (fun e => stepProb d ε (fun j => X j ω) t e)
    (fun e => f (X t ω + e)) (sum_stepProb hd ε _ t) (f (X t ω))
  simp only [nextMean]
  rw [hvar]
  linarith [sq_nonneg (∑ j ∈ unitSteps d, stepProb d ε (fun j => X j ω) t j * f (X t ω + j) -
    f (X t ω))]

end Law

end CERW.Support.Law
