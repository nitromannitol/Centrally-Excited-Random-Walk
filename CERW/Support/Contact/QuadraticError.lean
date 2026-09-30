import CERW.Support.Contact.Quadratic
import CERW.Generic.Martingale.Dyadic
import CERW.Generic.Martingale.Clamp

/-!
# Concentration of the quadratic martingale

`eq:quadraticerror`: on the event that the path stays in `B̄(0, KN)` up to time `n`,
`|𝒬_n| ≤ C (N √(nL) + N L)`, except on an event of probability at most `C n^{-p}`. Here `𝒬` is the
Dynkin martingale of `|x|²`. Instead of stopping at the exit time, multiply each increment by the
predictable indicator `1{|X_j| ≤ KN}`. The truncated process is a martingale with increments
`O(N)` and bracket `O(nN²)`, and it agrees with `𝒬` on the event. Freedman's inequality at dyadic
brackets then applies.
-/

namespace CERW.Support.Contact

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law

variable {d : ℕ}

/-- The squared norm changes by at most `2 |x| + 1` under a unit step. -/
private theorem abs_sq_euclidNorm_add_le (x e : Site d) (he : e ∈ unitSteps d) :
    |euclidNorm (x + e) ^ 2 - euclidNorm x ^ 2| ≤ 2 * euclidNorm x + 1 := by
  have hto : toSpace (x + e) = toSpace x + toSpace e := by
    apply PiLp.ext
    intro i
    simp [toSpace_apply, Pi.add_apply, Int.cast_add]
  have he1 : euclidNorm e = 1 := CERW.Support.Law.euclidNorm_of_mem_unitSteps he
  have hnorm : ‖toSpace e‖ = 1 := by rw [norm_toSpace, he1]
  have hdecomp : euclidNorm (x + e) ^ 2 - euclidNorm x ^ 2 =
      2 * inner ℝ (toSpace x) (toSpace e) + 1 := by
    rw [← norm_toSpace (x + e), ← norm_toSpace x, hto, norm_add_sq_real, hnorm]
    ring
  rw [hdecomp]
  have hinner : |inner ℝ (toSpace x) (toSpace e)| ≤ euclidNorm x := by
    calc |inner ℝ (toSpace x) (toSpace e)| ≤ ‖toSpace x‖ * ‖toSpace e‖ :=
          abs_real_inner_le_norm _ _
      _ = euclidNorm x := by rw [norm_toSpace, hnorm, mul_one]
  rw [abs_le] at hinner ⊢
  constructor <;> linarith [hinner.1, hinner.2]

/-- The indicator that the walk at time `j` is still inside the ball of radius `K N`. -/
private noncomputable def ballIndicator (K N : ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : ℝ :=
  if euclidNorm (X j ω) ≤ K * N then 1 else 0

/-- The Dynkin martingale of `|x|²` with its increments kept only while the walk is inside the
ball of radius `K N`. -/
private noncomputable def truncatedQuadratic (ε K N : ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range t, ballIndicator K N X j ω *
    (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
      dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω)

/-- The ball indicator is nonnegative. -/
private theorem ballIndicator_nonneg (K N : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : 0 ≤ ballIndicator K N X j ω := by
  rw [ballIndicator]
  split_ifs <;> norm_num

/-- The ball indicator is at most one. -/
private theorem ballIndicator_le_one (K N : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : ballIndicator K N X j ω ≤ 1 := by
  rw [ballIndicator]
  split_ifs <;> norm_num

/-- The ball indicator is a function of the past path. -/
private theorem stronglyMeasurable_ballIndicator {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (K N : ℝ) (j : ℕ) :
    StronglyMeasurable[pathFiltration hX j] (ballIndicator K N X j) := by
  have h := stronglyMeasurable_comp_pastPath hX j
    (fun q : ((i : Iic j) → Site d) =>
      if euclidNorm (q ⟨j, Finset.mem_Iic.mpr le_rfl⟩) ≤ K * N then (1 : ℝ) else 0)
  exact h

/-- The truncated quadratic martingale vanishes at time zero. -/
private theorem truncatedQuadratic_zero (ε K N : ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) :
    truncatedQuadratic ε K N X 0 ω = 0 := by
  simp only [truncatedQuadratic, Finset.range_zero, Finset.sum_empty]

/-- One step of the truncated quadratic martingale keeps the indicator times the Dynkin
increment. -/
private theorem truncatedQuadratic_succ_sub (ε K N : ℝ) {Ω : Type*} (X : ℕ → Ω → Site d)
    (t : ℕ) (ω : Ω) :
    truncatedQuadratic ε K N X (t + 1) ω - truncatedQuadratic ε K N X t ω =
      ballIndicator K N X t ω *
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X t ω) := by
  simp only [truncatedQuadratic, Finset.sum_range_succ]
  ring

/-- The truncated Dynkin martingale of `|x|²`, clamped so that its increments are surely
bounded, has increments at most `2 (2 K N + 1)`, conditional variances at most
`(2 K N + 1)²`, starts at `0` and agrees almost surely with `𝒬` on the event that the walk
stays in the ball of radius `K N` up to time `n`. -/
private theorem exists_clamped_quadratic (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) {K N : ℝ} (hK : 0 < K) (hN : 1 ≤ N) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2 * (2 * K * N + 1)) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun _ => (2 * K * N + 1) ^ 2) ∧
      (∀ ω, M 0 ω = 0) ∧
      ∀ᵐ ω ∂μ, (∀ j ≤ n, euclidNorm (X j ω) ≤ K * N) →
        M n ω = dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω := by
  have hd1 : 1 ≤ d := by omega
  have hQmart : Martingale (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X)
      (pathFiltration hX.measurable) μ :=
    martingale_dynkin hd1 hε hεd hX (fun z : Site d => euclidNorm z ^ 2)
  have hI_sm : ∀ j, StronglyMeasurable[pathFiltration hX.measurable j]
      (ballIndicator K N X j) := fun j => stronglyMeasurable_ballIndicator hX.measurable K N j
  have hQ'adp : StronglyAdapted (pathFiltration hX.measurable)
      (truncatedQuadratic ε K N X) := by
    intro t
    show StronglyMeasurable[pathFiltration hX.measurable t]
      (fun ω => ∑ j ∈ Finset.range t, ballIndicator K N X j ω *
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω))
    refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
    have hjt : j + 1 ≤ t := Finset.mem_range.mp hj
    have hjt' : j ≤ t := le_of_lt hjt
    exact ((hI_sm j).mono ((pathFiltration hX.measurable).mono hjt')).mul
      (((hQmart.stronglyMeasurable (j + 1)).mono ((pathFiltration hX.measurable).mono hjt)).sub
        ((hQmart.stronglyMeasurable j).mono ((pathFiltration hX.measurable).mono hjt')))
  have hQ'int : ∀ t, Integrable (truncatedQuadratic ε K N X t) μ := by
    intro t
    have hterm : ∀ j ∈ Finset.range t, Integrable (fun ω => ballIndicator K N X j ω *
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω)) μ := by
      intro j _
      refine Integrable.bdd_mul ((hQmart.integrable (j + 1)).sub (hQmart.integrable j))
        (((hI_sm j).mono ((pathFiltration hX.measurable).le j))).aestronglyMeasurable
        (c := 1) (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (ballIndicator_nonneg K N X j ω)]
      exact ballIndicator_le_one K N X j ω
    change Integrable (fun ω => ∑ j ∈ Finset.range t, ballIndicator K N X j ω *
      (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
        dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω)) μ
    exact integrable_finsetSum (Finset.range t) hterm
  have hQ'cond : ∀ k, μ[truncatedQuadratic ε K N X (k + 1) - truncatedQuadratic ε K N X k
      | pathFiltration hX.measurable k] =ᵐ[μ] 0 := by
    intro k
    have hfun : truncatedQuadratic ε K N X (k + 1) - truncatedQuadratic ε K N X k =
        ballIndicator K N X k * (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (k + 1) -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X k) := by
      funext ω
      exact truncatedQuadratic_succ_sub ε K N X k ω
    rw [hfun]
    have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ)
      ((pathFiltration hX.measurable).le k) (hI_sm k)
      ((hQmart.integrable (k + 1)).sub (hQmart.integrable k)) 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (ballIndicator_nonneg K N X k ω)]
        exact ballIndicator_le_one K N X k ω)
    have hcent : μ[dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (k + 1) -
        dynkin ε (fun z : Site d => euclidNorm z ^ 2) X k | pathFiltration hX.measurable k]
        =ᵐ[μ] 0 := by
      have h3 := condExp_sub (hQmart.integrable (k + 1)) (hQmart.integrable k)
        (pathFiltration hX.measurable k)
      have h1 := hQmart.condExp_ae_eq (Nat.le_succ k)
      have h2 : μ[dynkin ε (fun z : Site d => euclidNorm z ^ 2) X k
          | pathFiltration hX.measurable k] =
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X k :=
        condExp_of_stronglyMeasurable ((pathFiltration hX.measurable).le k)
          (hQmart.stronglyMeasurable k) (hQmart.integrable k)
      filter_upwards [h3, h1] with ω e3 e1
      rw [e3, Pi.sub_apply, e1, h2, sub_self]
      rfl
    filter_upwards [hpull, hcent] with ω e1 e2
    rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]
  have hmartQ' : Martingale (truncatedQuadratic ε K N X) (pathFiltration hX.measurable) μ :=
    martingale_of_condExp_sub_eq_zero_nat hQ'adp hQ'int hQ'cond
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |truncatedQuadratic ε K N X (i + 1) ω -
      truncatedQuadratic ε K N X i ω| ≤ 2 * (2 * K * N + 1) := by
    intro i
    filter_upwards [ae_abs_dynkin_succ_sub_le hd1 hε hεd hX
      (fun z : Site d => euclidNorm z ^ 2)] with ω hω
    rw [truncatedQuadratic_succ_sub]
    by_cases hb : euclidNorm (X i ω) ≤ K * N
    · have hI1 : ballIndicator K N X i ω = 1 := by rw [ballIndicator, if_pos hb]
      rw [hI1, one_mul]
      exact hω i (2 * K * N + 1) fun e he => by
        have h1 := abs_sq_euclidNorm_add_le (X i ω) e he
        linarith
    · have hI0 : ballIndicator K N X i ω = 0 := by rw [ballIndicator, if_neg hb]
      rw [hI0, zero_mul, abs_zero]
      positivity
  have hvarQ' : ∀ j, μ[fun ω => (truncatedQuadratic ε K N X (j + 1) ω -
      truncatedQuadratic ε K N X j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
      fun _ => (2 * K * N + 1) ^ 2 := by
    intro j
    have hsquare : (fun ω => (truncatedQuadratic ε K N X (j + 1) ω -
        truncatedQuadratic ε K N X j ω) ^ 2) =ᵐ[μ]
        ballIndicator K N X j * fun ω =>
          (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
            dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω) ^ 2 := by
      filter_upwards with ω
      rw [truncatedQuadratic_succ_sub, Pi.mul_apply, mul_pow, ballIndicator]
      split_ifs <;> ring
    refine (condExp_congr_ae hsquare).trans_le ?_
    have hIntDelta2 : Integrable (fun ω =>
        (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω) ^ 2) μ := by
      have hpath := integrable_path_next hd1 hε hεd hX j
        (fun p z => (euclidNorm z ^ 2 - nextMean ε (fun z : Site d => euclidNorm z ^ 2)
          (extendPath p) j) ^ 2)
      simpa only [dynkin_succ_sub, nextMean_pastPath] using hpath
    have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ)
      ((pathFiltration hX.measurable).le j) (hI_sm j) hIntDelta2 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (ballIndicator_nonneg K N X j ω)]
        exact ballIndicator_le_one K N X j ω)
    filter_upwards [hpull, condExp_sq_dynkin_succ_sub_le hd1 hε hεd hX
      (fun z : Site d => euclidNorm z ^ 2) j] with ω e1 e2
    rw [e1, Pi.mul_apply]
    by_cases hb : euclidNorm (X j ω) ≤ K * N
    · have hI1 : ballIndicator K N X j ω = 1 := by rw [ballIndicator, if_pos hb]
      rw [hI1, one_mul]
      refine e2.trans ?_
      calc ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e *
            (euclidNorm (X j ω + e) ^ 2 - euclidNorm (X j ω) ^ 2) ^ 2
          ≤ ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e * (2 * K * N + 1) ^ 2 := by
            refine sum_le_sum fun e he => mul_le_mul_of_nonneg_left ?_
              (stepProb_nonneg hε hεd _ j e)
            have h1 := abs_sq_euclidNorm_add_le (X j ω) e he
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
        _ = (2 * K * N + 1) ^ 2 := by
            rw [← sum_mul, sum_stepProb hd1 ε _ j, one_mul]
    · have hI0 : ballIndicator K N X j ω = 0 := by rw [ballIndicator, if_neg hb]
      rw [hI0, zero_mul]
      positivity
  obtain ⟨M, hMmart, hMinc, hM0, hMae⟩ :=
    CERW.Generic.Martingale.exists_martingale_clamp hmartQ'
      (b := 2 * (2 * K * N + 1)) (by positivity) hinc
  refine ⟨M, hMmart, hMinc, ?_, ?_, ?_⟩
  · intro j
    have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
        fun ω => (truncatedQuadratic ε K N X (j + 1) ω -
          truncatedQuadratic ε K N X j ω) ^ 2 := by
      filter_upwards [hMae] with ω hω
      rw [hω (j + 1), hω j]
    exact (condExp_congr_ae hsq).trans_le (hvarQ' j)
  · intro ω
    rw [hM0 ω, truncatedQuadratic_zero]
  · have hQ'eq : ∀ ω, (∀ j ≤ n, euclidNorm (X j ω) ≤ K * N) →
        truncatedQuadratic ε K N X n ω =
          dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω := by
      intro ω hball
      have hsum : truncatedQuadratic ε K N X n ω =
          ∑ j ∈ Finset.range n,
            (dynkin ε (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
              dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω) := by
        simp only [truncatedQuadratic]
        refine sum_congr rfl fun j hj => ?_
        have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
        have hI1 : ballIndicator K N X j ω = 1 := by rw [ballIndicator, if_pos (hball j hjn)]
        rw [hI1, one_mul]
      rw [hsum, Finset.sum_range_sub
        (fun j => dynkin ε (fun z : Site d => euclidNorm z ^ 2) X j ω) n,
        dynkin_zero, sub_zero]
    filter_upwards [hMae] with ω hω hball
    rw [hω n, hQ'eq ω hball]

/-- `eq:quadraticerror`: for `K > 0` and `p > 0` there is `C` with, for every `n ≥ 2`,
`μ(|X_j| ≤ KN for all j ≤ n, and C (N √(nL) + NL) < |𝒬_n|) ≤ C n^{-p}`. -/
theorem exists_quadratic_error (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {K : ℝ} (hK : 0 < K) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ K * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ∧
          C * ((n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.sqrt (n * Real.log (n + 2)) +
              (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2)) <
            |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound (K := p + 3) (by linarith)
  set Cdet : ℝ := 2 * c * (2 * K + 1) with hCdet
  set Cp : ℝ := 16 * ((2 * K + 1) ^ 2 + 2) with hCp
  have hCdetpos : 0 < Cdet := by
    rw [hCdet]
    have hcpos : 0 < c := by linarith
    have hKpos : 0 < 2 * K + 1 := by linarith
    exact mul_pos (mul_pos (by norm_num) hcpos) hKpos
  have hCp0 : 0 ≤ Cp := by
    rw [hCp]
    positivity
  refine ⟨Cdet + Cp, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hn1 : 1 ≤ n := by omega
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact Real.one_le_rpow hn1R (by positivity)
  have hNle : N ≤ (n : ℝ) := by
    rw [hN]
    calc (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1R (by
            rw [div_le_iff₀ (by positivity), one_mul]
            exact_mod_cast (by omega : 1 ≤ d + 1))
      _ = (n : ℝ) := Real.rpow_one _
  obtain ⟨M, hMmart, hMinc, hMvar, hM0, hMae⟩ :=
    exists_clamped_quadratic hd hε hεd hK hN1 n hX
  set b : ℝ := 2 * (2 * K * N + 1) with hb
  set W : ℝ := (n : ℝ) * (2 * K * N + 1) ^ 2 with hW
  set V : ℕ → Ω → ℝ := fun t _ => (t : ℝ) * (2 * K * N + 1) ^ 2 with hV
  have hKN : 0 < K * N := mul_pos hK (by linarith)
  have hbpos : 0 < b := by
    rw [hb]
    nlinarith
  have hLpos : 0 < L := by
    rw [hL]
    exact Real.log_pos (by linarith)
  have hW1 : 1 ≤ W := by
    rw [hW]
    have hsq1 : (1 : ℝ) ≤ (2 * K * N + 1) ^ 2 := by
      have h1 : (1 : ℝ) ≤ 2 * K * N + 1 := by nlinarith
      nlinarith
    have h := mul_le_mul hn1R hsq1 (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (0 : ℝ) ≤ (n : ℝ))
    simpa using h
  have hVpred : ∀ j, StronglyMeasurable[pathFiltration hX.measurable j] (V (j + 1)) :=
    fun _ => stronglyMeasurable_const
  have hV0 : ∀ ω, V 0 ω = 0 := by
    intro ω
    simp only [hV]
    ring
  have hVmono : ∀ j ω, V j ω ≤ V (j + 1) ω := by
    intro j ω
    simp only [hV]
    have hnn : 0 ≤ (2 * K * N + 1) ^ 2 := sq_nonneg _
    push_cast
    nlinarith
  have hVdom : ∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j]
      ≤ᵐ[μ] fun ω => V (j + 1) ω - V j ω := by
    intro j
    refine (hMvar j).trans ?_
    filter_upwards with ω
    have h : V (j + 1) ω - V j ω = (2 * K * N + 1) ^ 2 := by
      simp only [hV]
      push_cast
      ring
    rw [h]
  have hVW : ∀ ω, V (0 + n) ω - V 0 ω ≤ W := by
    intro ω
    rw [zero_add]
    have h : V n ω - V 0 ω = W := by
      simp only [hV, hW]
      push_cast
      ring
    rw [h]
  have hdy := hc hMmart hVpred hV0 hVmono hVdom (b := b) hbpos 0 n
    (fun i _ _ ω => hMinc i ω) (W := W) (L := L) hW1 hLpos (fun ω => hVW ω)
  have hdet : ∀ ω, c * (Real.sqrt (max (V (0 + n) ω - V 0 ω) 1 * L) + b * L) ≤
      Cdet * (N * Real.sqrt ((n : ℝ) * L) + N * L) := by
    intro ω
    have hVval : V (0 + n) ω - V 0 ω = (n : ℝ) * (2 * K * N + 1) ^ 2 := by
      rw [zero_add]
      simp only [hV]
      ring
    have hge1 : (1 : ℝ) ≤ (n : ℝ) * (2 * K * N + 1) ^ 2 := by
      have hsq1 : (1 : ℝ) ≤ (2 * K * N + 1) ^ 2 := by
        have h1 : (1 : ℝ) ≤ 2 * K * N + 1 := by nlinarith
        nlinarith
      nlinarith
    rw [hVval, max_eq_left hge1]
    have hsqrt : Real.sqrt ((n : ℝ) * (2 * K * N + 1) ^ 2 * L) =
        (2 * K * N + 1) * Real.sqrt ((n : ℝ) * L) := by
      rw [show (n : ℝ) * (2 * K * N + 1) ^ 2 * L =
          (2 * K * N + 1) ^ 2 * ((n : ℝ) * L) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rw [hsqrt, hb, hCdet]
    have hbound1 : 2 * K * N + 1 ≤ (2 * K + 1) * N := by nlinarith [hN1]
    have hnn : 0 ≤ Real.sqrt ((n : ℝ) * L) + 2 * L := by
      refine add_nonneg (Real.sqrt_nonneg _) ?_
      positivity
    have hstep : (2 * K * N + 1) * (Real.sqrt ((n : ℝ) * L) + 2 * L) ≤
        2 * (2 * K + 1) * (N * Real.sqrt ((n : ℝ) * L) + N * L) := by
      calc (2 * K * N + 1) * (Real.sqrt ((n : ℝ) * L) + 2 * L)
          ≤ ((2 * K + 1) * N) * (Real.sqrt ((n : ℝ) * L) + 2 * L) :=
            mul_le_mul_of_nonneg_right hbound1 hnn
        _ = (2 * K + 1) * (N * Real.sqrt ((n : ℝ) * L) + 2 * (N * L)) := by ring
        _ ≤ (2 * K + 1) * (2 * (N * Real.sqrt ((n : ℝ) * L) + N * L)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith [Real.sqrt_nonneg ((n : ℝ) * L),
              mul_nonneg (by linarith : 0 ≤ N) hLpos.le]
        _ = 2 * (2 * K + 1) * (N * Real.sqrt ((n : ℝ) * L) + N * L) := by ring
    calc c * ((2 * K * N + 1) * Real.sqrt ((n : ℝ) * L) + 2 * (2 * K * N + 1) * L)
        = c * ((2 * K * N + 1) * (Real.sqrt ((n : ℝ) * L) + 2 * L)) := by ring
      _ ≤ c * (2 * (2 * K + 1) * (N * Real.sqrt ((n : ℝ) * L) + N * L)) :=
          mul_le_mul_of_nonneg_left hstep (by linarith)
      _ = 2 * c * (2 * K + 1) * (N * Real.sqrt ((n : ℝ) * L) + N * L) := by ring
  have hTsub : {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ K * N) ∧
        (Cdet + Cp) * (N * Real.sqrt ((n : ℝ) * L) + N * L) <
          |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|} ≤ᵐ[μ]
      {ω | c * (Real.sqrt (max (V (0 + n) ω - V 0 ω) 1 * L) + b * L) <
          |M (0 + n) ω - M 0 ω|} := by
    filter_upwards [hMae] with ω hMaeω hT
    rcases hT with ⟨hball, hgt⟩
    by_contra hnot
    have hle : |M (0 + n) ω - M 0 ω| ≤
        c * (Real.sqrt (max (V (0 + n) ω - V 0 ω) 1 * L) + b * L) := not_lt.mp hnot
    have hMeq : M (0 + n) ω = dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω := by
      rw [zero_add]
      exact hMaeω hball
    have hchain : |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω| ≤
        (Cdet + Cp) * (N * Real.sqrt ((n : ℝ) * L) + N * L) := by
      calc |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω| = |M (0 + n) ω - M 0 ω| := by
            rw [hMeq, hM0 ω, sub_zero]
        _ ≤ c * (Real.sqrt (max (V (0 + n) ω - V 0 ω) 1 * L) + b * L) := hle
        _ ≤ Cdet * (N * Real.sqrt ((n : ℝ) * L) + N * L) := hdet ω
        _ ≤ (Cdet + Cp) * (N * Real.sqrt ((n : ℝ) * L) + N * L) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · linarith [hCp0]
            · exact add_nonneg (mul_nonneg (by linarith : 0 ≤ N) (Real.sqrt_nonneg _))
                (mul_nonneg (by linarith : 0 ≤ N) hLpos.le)
    linarith
  have hprob : (((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) + 1) *
        (2 * Real.exp (-((p + 3) * L))) ≤ (Cdet + Cp) * (n : ℝ) ^ (-p) := by
    have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1R
    have hn13 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith)
    have hWle : W ≤ (2 * K + 1) ^ 2 * (n : ℝ) ^ 3 := by
      rw [hW]
      have hbnd : 2 * K * N + 1 ≤ (2 * K + 1) * (n : ℝ) := by
        have h1 : 2 * K * N + 1 ≤ (2 * K + 1) * N := by nlinarith [hN1]
        have h2 : (2 * K + 1) * N ≤ (2 * K + 1) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hNle (by linarith)
        linarith
      have hsq : (2 * K * N + 1) ^ 2 ≤ ((2 * K + 1) * (n : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hbnd 2
      calc (n : ℝ) * (2 * K * N + 1) ^ 2
          ≤ (n : ℝ) * ((2 * K + 1) * (n : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (2 * K + 1) ^ 2 * (n : ℝ) ^ 3 := by ring
    have hceil : (⌈W⌉₊ : ℝ) ≤ ((2 * K + 1) ^ 2 + 1) * ((n : ℝ) + 1) ^ 3 := by
      have h1 : (⌈W⌉₊ : ℝ) < W + 1 := Nat.ceil_lt_add_one (by linarith)
      have h2 : W + 1 ≤ ((2 * K + 1) ^ 2 + 1) * ((n : ℝ) + 1) ^ 3 := by
        have h3 : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 3
        calc W + 1 ≤ (2 * K + 1) ^ 2 * (n : ℝ) ^ 3 + 1 := by linarith [hWle]
          _ ≤ (2 * K + 1) ^ 2 * ((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 3 :=
              add_le_add (mul_le_mul_of_nonneg_left h3 (by positivity)) hn13
          _ = ((2 * K + 1) ^ 2 + 1) * ((n : ℝ) + 1) ^ 3 := by ring
      linarith
    have hclog : ((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) ≤ (⌈W⌉₊ : ℝ) := by
      exact_mod_cast Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    have hclog1 : ((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) + 1 ≤
        ((2 * K + 1) ^ 2 + 2) * ((n : ℝ) + 1) ^ 3 := by
      have h4 : ((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) ≤
          ((2 * K + 1) ^ 2 + 1) * ((n : ℝ) + 1) ^ 3 := le_trans hclog hceil
      calc ((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) + 1
          ≤ ((2 * K + 1) ^ 2 + 1) * ((n : ℝ) + 1) ^ 3 + 1 := by linarith
        _ ≤ ((2 * K + 1) ^ 2 + 1) * ((n : ℝ) + 1) ^ 3 + ((n : ℝ) + 1) ^ 3 :=
              add_le_add le_rfl hn13
        _ = ((2 * K + 1) ^ 2 + 2) * ((n : ℝ) + 1) ^ 3 := by ring
    have hexp : 2 * Real.exp (-((p + 3) * L)) ≤ 2 * (n : ℝ) ^ (-(p + 3)) := by
      rw [hL]
      exact CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le (K := p + 3) (by linarith)
        (n := n) hn1
    have hpow := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn1 3 p
    calc (((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) + 1) * (2 * Real.exp (-((p + 3) * L)))
        ≤ (((2 * K + 1) ^ 2 + 2) * ((n : ℝ) + 1) ^ 3) *
            (2 * (n : ℝ) ^ (-(p + 3))) := by
          refine mul_le_mul hclog1 hexp ?_ (by positivity)
          positivity
      _ = 2 * ((2 * K + 1) ^ 2 + 2) *
            (((n : ℝ) + 1) ^ 3 * (n : ℝ) ^ (-(p + 3))) := by ring
      _ ≤ 2 * ((2 * K + 1) ^ 2 + 2) * (2 ^ 3 * (n : ℝ) ^ (-p)) := by
          refine mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 16 * ((2 * K + 1) ^ 2 + 2) * (n : ℝ) ^ (-p) := by ring
      _ ≤ (Cdet + Cp) * (n : ℝ) ^ (-p) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
          rw [hCp]
          linarith [hCdetpos]
  calc μ {ω | (∀ j ≤ n, euclidNorm (X j ω) ≤ K * N) ∧
        (Cdet + Cp) * (N * Real.sqrt ((n : ℝ) * L) + N * L) <
          |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|}
      ≤ μ {ω | c * (Real.sqrt (max (V (0 + n) ω - V 0 ω) 1 * L) + b * L) <
          |M (0 + n) ω - M 0 ω|} := measure_mono_ae hTsub
    _ ≤ ENNReal.ofReal ((((Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) + 1) *
          (2 * Real.exp (-((p + 3) * L)))) := hdy
    _ ≤ ENNReal.ofReal ((Cdet + Cp) * (n : ℝ) ^ (-p)) := ENNReal.ofReal_le_ofReal hprob

end CERW.Support.Contact
