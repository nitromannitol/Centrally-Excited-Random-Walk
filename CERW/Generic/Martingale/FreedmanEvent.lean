import LatticeProb.Prob.Freedman

/-!
# Freedman's inequality on the event of a small bracket

The consequence of Freedman's inequality used by the paper (`eq:freedman`). Let `M` be a
martingale from `0` with increments at most `b`, and let `V` be a predictable nondecreasing
process from `0` that dominates the conditional variances of the increments. Then
`P(|M_n| ≥ t, V_n ≤ v) ≤ 2 exp(-t²/(2(v + bt/3)))`. The paper's statement is the case where `V`
is the predictable quadratic variation. Every use in the paper bounds that variation by a
pathwise sum over the local times, which is the `V` here. The proof stops the martingale
predictably once `V` would exceed `v`, and applies `LatticeProb.freedman_upper` and
`LatticeProb.freedman` to the stopped martingale.
-/

namespace CERW.Generic.Martingale

open MeasureTheory ProbabilityTheory

section Stopping

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- The indicator that the bracket `V` at time `k + 1` is still at most `v`. -/
noncomputable def bracketIndicator (V : ℕ → Ω → ℝ) (v : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if V (k + 1) ω ≤ v then 1 else 0

/-- The martingale `M` stopped predictably: the increment from `j` to `j + 1` is kept exactly
when `V (j + 1) ≤ v`. -/
noncomputable def predictableStop (M V : ℕ → Ω → ℝ) (v : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range k, bracketIndicator V v j ω * (M (j + 1) ω - M j ω)

/-- The bracket indicator is nonnegative. -/
theorem bracketIndicator_nonneg (V : ℕ → Ω → ℝ) (v : ℝ) (k : ℕ) (ω : Ω) :
    0 ≤ bracketIndicator V v k ω := by
  unfold bracketIndicator
  split_ifs <;> norm_num

/-- The bracket indicator is at most `1`. -/
theorem bracketIndicator_le_one (V : ℕ → Ω → ℝ) (v : ℝ) (k : ℕ) (ω : Ω) :
    bracketIndicator V v k ω ≤ 1 := by
  unfold bracketIndicator
  split_ifs <;> norm_num

/-- The bracket indicator is idempotent. -/
theorem bracketIndicator_mul_self (V : ℕ → Ω → ℝ) (v : ℝ) (k : ℕ) (ω : Ω) :
    bracketIndicator V v k ω * bracketIndicator V v k ω = bracketIndicator V v k ω := by
  unfold bracketIndicator
  split_ifs <;> norm_num

/-- The bracket indicator is `1` when the bracket at time `k + 1` is at most `v`. -/
theorem bracketIndicator_of_le {V : ℕ → Ω → ℝ} {v : ℝ} {k : ℕ} {ω : Ω}
    (h : V (k + 1) ω ≤ v) : bracketIndicator V v k ω = 1 := by
  unfold bracketIndicator
  rw [if_pos h]

/-- The bracket indicator is `0` when the bracket at time `k + 1` exceeds `v`. -/
theorem bracketIndicator_of_lt {V : ℕ → Ω → ℝ} {v : ℝ} {k : ℕ} {ω : Ω}
    (h : v < V (k + 1) ω) : bracketIndicator V v k ω = 0 := by
  unfold bracketIndicator
  rw [if_neg (not_le.mpr h)]

/-- The bracket indicator at time `k` is `ℱ k`-measurable when `V (k + 1)` is. -/
theorem stronglyMeasurable_bracketIndicator {ℱ : Filtration ℕ m0} {V : ℕ → Ω → ℝ} {v : ℝ}
    (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) (k : ℕ) :
    StronglyMeasurable[ℱ k] (bracketIndicator V v k) := by
  refine Measurable.stronglyMeasurable ?_
  exact Measurable.ite (measurableSet_le (hVpred k).measurable measurable_const)
    measurable_const measurable_const

/-- The stopped martingale vanishes at time `0`. -/
theorem predictableStop_zero (M V : ℕ → Ω → ℝ) (v : ℝ) (ω : Ω) :
    predictableStop M V v 0 ω = 0 := by
  simp only [predictableStop, Finset.range_zero, Finset.sum_empty]

/-- One step of the stopped martingale. -/
theorem predictableStop_succ_sub (M V : ℕ → Ω → ℝ) (v : ℝ) (k : ℕ) (ω : Ω) :
    predictableStop M V v (k + 1) ω - predictableStop M V v k ω
      = bracketIndicator V v k ω * (M (k + 1) ω - M k ω) := by
  simp only [predictableStop, Finset.sum_range_succ, add_sub_cancel_left]

/-- Where the bracket at time `n` is at most `v`, the stopped martingale agrees with `M`. -/
theorem predictableStop_eq_of_le {M V : ℕ → Ω → ℝ} {v : ℝ} (hM0 : ∀ ω, M 0 ω = 0)
    (hVmono : ∀ k ω, V k ω ≤ V (k + 1) ω) {n : ℕ} {ω : Ω} (h : V n ω ≤ v) :
    predictableStop M V v n ω = M n ω := by
  have hmono : Monotone fun k => V k ω := monotone_nat_of_le_succ fun k => hVmono k ω
  have hone : ∀ j ∈ Finset.range n, bracketIndicator V v j ω = 1 := by
    intro j hj
    exact bracketIndicator_of_le
      (le_trans (hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hj))) h)
  calc predictableStop M V v n ω
      = ∑ j ∈ Finset.range n, (M (j + 1) ω - M j ω) := by
        simp only [predictableStop]
        exact Finset.sum_congr rfl fun j hj => by rw [hone j hj, one_mul]
    _ = M n ω - M 0 ω := Finset.sum_range_sub (fun j => M j ω) n
    _ = M n ω := by rw [hM0 ω, sub_zero]

/-- The pathwise telescoping bound: the increments of a nondecreasing `V` from `0`, kept only
while `V ≤ v`, sum to at most `v` and at most the current value of `V`. -/
theorem sum_bracketIndicator_mul_le {V : ℕ → Ω → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (hV0 : ∀ ω, V 0 ω = 0) (hVmono : ∀ k ω, V k ω ≤ V (k + 1) ω) (ω : Ω) (n : ℕ) :
    ∑ j ∈ Finset.range n, bracketIndicator V v j ω * (V (j + 1) ω - V j ω) ≤ v
      ∧ ∑ j ∈ Finset.range n, bracketIndicator V v j ω * (V (j + 1) ω - V j ω) ≤ V n ω := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, hV0 ω]
      exact ⟨hv, le_rfl⟩
  | succ n ih =>
      rw [Finset.sum_range_succ]
      obtain ⟨ih1, ih2⟩ := ih
      rcases le_or_gt (V (n + 1) ω) v with h | h
      · rw [bracketIndicator_of_le h, one_mul]
        constructor <;> linarith
      · rw [bracketIndicator_of_lt h, zero_mul, add_zero]
        exact ⟨ih1, le_trans ih2 (hVmono n ω)⟩

variable {ℱ : Filtration ℕ m0}

/-- A martingale has centred increments given the past. -/
theorem condExp_increment_eq_zero [IsFiniteMeasure P] {M : ℕ → Ω → ℝ}
    (hmart : Martingale M ℱ P) (k : ℕ) :
    P[fun ω => M (k + 1) ω - M k ω | ℱ k] =ᵐ[P] 0 := by
  have h3 := condExp_sub (μ := P) (hmart.integrable (k + 1)) (hmart.integrable k) (ℱ k)
  have h1 : P[M (k + 1) | ℱ k] =ᵐ[P] M k := hmart.condExp_ae_eq (Nat.le_succ k)
  have h2 : P[M k | ℱ k] = M k :=
    condExp_of_stronglyMeasurable (ℱ.le k) (hmart.stronglyMeasurable k) (hmart.integrable k)
  filter_upwards [h3, h1] with ω e3 e1
  show P[M (k + 1) - M k | ℱ k] ω = 0
  rw [e3]
  simp only [Pi.sub_apply]
  rw [e1, h2, sub_self]

/-- The stopped martingale is integrable at every time. -/
theorem integrable_predictableStop [IsFiniteMeasure P] {M V : ℕ → Ω → ℝ} {v : ℝ}
    (hmart : Martingale M ℱ P) (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) (k : ℕ) :
    Integrable (predictableStop M V v k) P := by
  induction k with
  | zero =>
      have hzero : predictableStop M V v 0 = fun _ => 0 := funext (predictableStop_zero M V v)
      rw [hzero]
      exact integrable_zero Ω ℝ P
  | succ k ih =>
      have hinc : Integrable (fun ω => bracketIndicator V v k ω * (M (k + 1) ω - M k ω)) P := by
        refine Integrable.bdd_mul ((hmart.integrable (k + 1)).sub (hmart.integrable k))
          ((stronglyMeasurable_bracketIndicator hVpred k).mono (ℱ.le k)).aestronglyMeasurable
          (c := 1) (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (bracketIndicator_nonneg V v k ω)]
        exact bracketIndicator_le_one V v k ω
      have hsum : predictableStop M V v (k + 1) = fun ω =>
          predictableStop M V v k ω + bracketIndicator V v k ω * (M (k + 1) ω - M k ω) := by
        funext ω
        have h := predictableStop_succ_sub M V v k ω
        linarith
      rw [hsum]
      exact ih.add hinc

/-- The stopped martingale is adapted. -/
theorem stronglyAdapted_predictableStop {M V : ℕ → Ω → ℝ} {v : ℝ}
    (hmart : Martingale M ℱ P) (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) :
    StronglyAdapted ℱ (predictableStop M V v) := by
  intro k
  show StronglyMeasurable[ℱ k] fun ω => ∑ j ∈ Finset.range k,
    bracketIndicator V v j ω * (M (j + 1) ω - M j ω)
  refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
  have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
  have hind := (stronglyMeasurable_bracketIndicator (v := v) hVpred j).mono
    (ℱ.mono (le_of_lt hjk))
  have hM1 := (hmart.stronglyMeasurable (j + 1)).mono (ℱ.mono hjk)
  have hM0 := (hmart.stronglyMeasurable j).mono (ℱ.mono (le_of_lt hjk))
  exact hind.mul (hM1.sub hM0)

/-- The stopped martingale is a martingale. -/
theorem martingale_predictableStop [IsFiniteMeasure P] {M V : ℕ → Ω → ℝ} {v : ℝ}
    (hmart : Martingale M ℱ P) (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) :
    Martingale (predictableStop M V v) ℱ P := by
  refine martingale_of_condExp_sub_eq_zero_nat (stronglyAdapted_predictableStop hmart hVpred)
    (integrable_predictableStop hmart hVpred) fun k => ?_
  have hfun : predictableStop M V v (k + 1) - predictableStop M V v k
      = bracketIndicator V v k * fun ω => M (k + 1) ω - M k ω :=
    funext fun ω => predictableStop_succ_sub M V v k ω
  rw [hfun]
  have hpull : P[bracketIndicator V v k * fun ω => M (k + 1) ω - M k ω | ℱ k]
      =ᵐ[P] bracketIndicator V v k * P[fun ω => M (k + 1) ω - M k ω | ℱ k] :=
    condExp_stronglyMeasurable_mul_of_bound (μ := P) (ℱ.le k)
      (stronglyMeasurable_bracketIndicator (v := v) hVpred k)
      ((hmart.integrable (k + 1)).sub (hmart.integrable k)) 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (bracketIndicator_nonneg V v k ω)]
        exact bracketIndicator_le_one V v k ω)
  filter_upwards [hpull, condExp_increment_eq_zero hmart k] with ω e1 e2
  rw [e1]
  simp only [Pi.mul_apply, Pi.zero_apply] at e2 ⊢
  rw [e2, mul_zero]

/-- The increments of the stopped martingale are bounded by those of `M`. -/
theorem abs_predictableStop_succ_sub_le {M V : ℕ → Ω → ℝ} {v b : ℝ} {n : ℕ}
    (hinc : ∀ i < n, ∀ ω, |M (i + 1) ω - M i ω| ≤ b) :
    ∀ i < n, ∀ ω, |predictableStop M V v (i + 1) ω - predictableStop M V v i ω| ≤ b := by
  intro i hi ω
  rw [predictableStop_succ_sub, abs_mul, abs_of_nonneg (bracketIndicator_nonneg V v i ω)]
  have h1 := bracketIndicator_le_one V v i ω
  have h2 := hinc i hi ω
  have h3 : 0 ≤ |M (i + 1) ω - M i ω| := abs_nonneg _
  nlinarith [bracketIndicator_nonneg V v i ω]

/-- The conditional quadratic variation of the stopped martingale is at most `v` a.e. -/
theorem condQvar_predictableStop_le [IsProbabilityMeasure P] {M V : ℕ → Ω → ℝ} {v b : ℝ}
    {n : ℕ} (hmart : Martingale M ℱ P) (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1)))
    (hV0 : ∀ ω, V 0 ω = 0) (hVmono : ∀ k ω, V k ω ≤ V (k + 1) ω)
    (hVdom : ∀ k, P[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ≤ᵐ[P]
      fun ω => V (k + 1) ω - V k ω)
    (hinc : ∀ i < n, ∀ ω, |M (i + 1) ω - M i ω| ≤ b) (hv : 0 ≤ v) :
    ∀ᵐ ω ∂P, LatticeProb.condQvar P ℱ (predictableStop M V v) n ω ≤ v := by
  have hstep : ∀ j ∈ Finset.range n, ∀ᵐ ω ∂P,
      (P[fun ω' => (predictableStop M V v (j + 1) ω' - predictableStop M V v j ω') ^ 2
        | ℱ j]) ω ≤ bracketIndicator V v j ω * (V (j + 1) ω - V j ω) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hX2int : Integrable (fun ω => (M (j + 1) ω - M j ω) ^ 2) P := by
      have hmeas : StronglyMeasurable fun ω => (M (j + 1) ω - M j ω) ^ 2 :=
        (((hmart.stronglyMeasurable (j + 1)).mono (ℱ.le (j + 1))).sub
          ((hmart.stronglyMeasurable j).mono (ℱ.le j))).pow 2
      refine Integrable.mono' (integrable_const (b ^ 2)) hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have h := hinc j hjn ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hfun : (fun ω' => (predictableStop M V v (j + 1) ω' - predictableStop M V v j ω') ^ 2)
        = bracketIndicator V v j * fun ω => (M (j + 1) ω - M j ω) ^ 2 := by
      funext ω'
      rw [predictableStop_succ_sub, mul_pow, sq (bracketIndicator V v j ω'),
        bracketIndicator_mul_self]
      rfl
    rw [hfun]
    have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := P) (ℱ.le j)
      (stronglyMeasurable_bracketIndicator (v := v) hVpred j) hX2int 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (bracketIndicator_nonneg V v j ω)]
        exact bracketIndicator_le_one V v j ω)
    filter_upwards [hpull, hVdom j] with ω e1 e2
    rw [e1]
    exact mul_le_mul_of_nonneg_left e2 (bracketIndicator_nonneg V v j ω)
  have hall := (Filter.eventually_all_finset (Finset.range n)).mpr hstep
  filter_upwards [hall] with ω hω
  calc LatticeProb.condQvar P ℱ (predictableStop M V v) n ω
      = ∑ j ∈ Finset.range n, (P[fun ω' => (predictableStop M V v (j + 1) ω'
          - predictableStop M V v j ω') ^ 2 | ℱ j]) ω := rfl
    _ ≤ ∑ j ∈ Finset.range n, bracketIndicator V v j ω * (V (j + 1) ω - V j ω) :=
        Finset.sum_le_sum hω
    _ ≤ v := (sum_bracketIndicator_mul_le hv hV0 hVmono ω n).1

end Stopping

/-- Freedman's inequality on the event `V_n ≤ v`, for a predictable nondecreasing `V` from `0`
dominating the conditional variances of a martingale from `0` with increments at most `b`. -/
theorem measure_le_abs_and_le {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0} {M V : ℕ → Ω → ℝ}
    (hmart : Martingale M ℱ P) (hM0 : ∀ ω, M 0 ω = 0)
    (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) (hV0 : ∀ ω, V 0 ω = 0)
    (hVmono : ∀ k ω, V k ω ≤ V (k + 1) ω)
    (hVdom : ∀ k, P[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ≤ᵐ[P]
      fun ω => V (k + 1) ω - V k ω)
    {b : ℝ} (hb : 0 < b) (n : ℕ) (hinc : ∀ i < n, ∀ ω, |M (i + 1) ω - M i ω| ≤ b)
    {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    P {ω | t ≤ |M n ω| ∧ V n ω ≤ v} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / (2 * (v + b * t / 3))))) := by
  have hmart' : Martingale (predictableStop M V v) ℱ P := martingale_predictableStop hmart hVpred
  have hM0' : ∀ ω, predictableStop M V v 0 ω = 0 := predictableStop_zero M V v
  have hinc' := abs_predictableStop_succ_sub_le (V := V) (v := v) hinc
  have hqv := condQvar_predictableStop_le hmart hVpred hV0 hVmono hVdom hinc hv
  have hup := LatticeProb.freedman_upper hmart' hM0' hb hv hinc' hqv ht
  have hlow := LatticeProb.freedman hmart' (funext hM0') hb hv hinc' hqv t ht
  set e : ℝ := Real.exp (-(t ^ 2 / (2 * (v + b * t / 3)))) with hedef
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hsub : {ω | t ≤ |M n ω| ∧ V n ω ≤ v}
      ⊆ {ω | t ≤ predictableStop M V v n ω} ∪ {ω | predictableStop M V v n ω ≤ -t} := by
    rintro ω ⟨h1, h2⟩
    have hs := predictableStop_eq_of_le hM0 hVmono h2
    simp only [Set.mem_union, Set.mem_setOf_eq, hs]
    rcases le_abs'.mp h1 with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hPup : P {ω | t ≤ predictableStop M V v n ω} ≤ ENNReal.ofReal e :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) he).mpr hup
  have hPlow : P {ω | predictableStop M V v n ω ≤ -t} ≤ ENNReal.ofReal e :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) he).mpr hlow
  calc P {ω | t ≤ |M n ω| ∧ V n ω ≤ v}
      ≤ P ({ω | t ≤ predictableStop M V v n ω} ∪ {ω | predictableStop M V v n ω ≤ -t}) :=
        measure_mono hsub
    _ ≤ P {ω | t ≤ predictableStop M V v n ω} + P {ω | predictableStop M V v n ω ≤ -t} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal e + ENNReal.ofReal e := add_le_add hPup hPlow
    _ = ENNReal.ofReal (2 * e) := by rw [two_mul, ENNReal.ofReal_add he he]

end CERW.Generic.Martingale
