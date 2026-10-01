import CERW.Generic.Martingale.FreedmanEvent
import CERW.Model.Bracket
import CERW.Generic.Martingale.CLT.Interfaces

/-!
# The path bracket and the predictable truncation of a martingale

For a process `M` adapted to a filtration `ℱ`, the path bracket `pathBracket μ ℱ M` is the sum of
the nonnegative parts of the conditional variances of the increments. It is a version of the
predictable bracket that is nondecreasing and predictable at every point, not just almost surely.
Truncating the increments by `bracketIndicator (pathBracket μ ℱ M) c` keeps the martingale
property, multiplies the conditional variances by the indicator, keeps their sum below `c`, and
does not increase the conditional Lindeberg terms. Only square integrability of `M` is used, never a
bound on the increments. The conditional Lindeberg sum is `lind`.
-/

namespace CERW.Generic.Martingale.CLT

open MeasureTheory ProbabilityTheory

section Definitions

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

end Definitions

section PathBracket

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- One step of the path bracket adds the nonnegative part of the conditional variance. -/
private theorem pathBracket_succ (μ : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ)
    (ω : Ω) :
    pathBracket μ ℱ M (k + 1) ω = pathBracket μ ℱ M k ω
      + max (μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω) 0 := by
  unfold pathBracket
  rw [Finset.sum_range_succ]

/-- The path bracket vanishes at time `0`. -/
private theorem pathBracket_zero_aux (μ : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ)
    (ω : Ω) : pathBracket μ ℱ M 0 ω = 0 := by
  simp only [pathBracket, Finset.range_zero, Finset.sum_empty]

/-- The path bracket is nondecreasing in time at every point. -/
private theorem pathBracket_le_succ (μ : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ)
    (k : ℕ) (ω : Ω) : pathBracket μ ℱ M k ω ≤ pathBracket μ ℱ M (k + 1) ω := by
  rw [pathBracket_succ]
  exact le_add_of_nonneg_right (le_max_right _ _)

/-- The path bracket at time `k + 1` is `ℱ k`-measurable. -/
private theorem stronglyMeasurable_pathBracket_succ (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (M : ℕ → Ω → ℝ) (k : ℕ) : StronglyMeasurable[ℱ k] (pathBracket μ ℱ M (k + 1)) := by
  show StronglyMeasurable[ℱ k] fun ω => ∑ j ∈ Finset.range (k + 1),
    max (μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | ℱ j] ω) 0
  refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h := (stronglyMeasurable_condExp (μ := μ) (m := ℱ j)
    (f := fun ω => (M (j + 1) ω - M j ω) ^ 2)).mono (ℱ.mono hjk)
  exact (h.measurable.max measurable_const).stronglyMeasurable

/-- The conditional variance of an increment is almost surely nonnegative. -/
private theorem condExp_sq_increment_nonneg (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (M : ℕ → Ω → ℝ) (k : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ μ[fun ω' => (M (k + 1) ω' - M k ω') ^ 2 | ℱ k] ω :=
  condExp_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- The path bracket is zero at time `0`, nondecreasing, predictable, and almost surely equal to
the predictable bracket at all times. -/
theorem pathBracket_predictable_nondecreasing_ae_eq_predBracket (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) :
    (∀ ω, pathBracket μ ℱ M 0 ω = 0) ∧
      (∀ k ω, pathBracket μ ℱ M k ω ≤ pathBracket μ ℱ M (k + 1) ω) ∧
      (∀ k, StronglyMeasurable[ℱ k] (pathBracket μ ℱ M (k + 1))) ∧
      (∀ᵐ ω ∂μ, ∀ k, pathBracket μ ℱ M k ω = CERW.predBracket μ ℱ M M k ω) := by
  refine ⟨pathBracket_zero_aux μ ℱ M, pathBracket_le_succ μ ℱ M,
    stronglyMeasurable_pathBracket_succ μ ℱ M, ?_⟩
  filter_upwards [ae_all_iff.mpr (condExp_sq_increment_nonneg μ ℱ M)] with ω hω k
  unfold pathBracket CERW.predBracket
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [max_eq_left (hω j)]
  have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2)
      = fun ω => (M (j + 1) ω - M j ω) * (M (j + 1) ω - M j ω) := funext fun ω => sq _
  rw [hsq]

end PathBracket

section Truncation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {M : ℕ → Ω → ℝ}

/-- A predictable `{0, 1}`-valued weight pulls out of a conditional expectation. -/
private theorem condExp_bracketIndicator_mul [IsFiniteMeasure μ] {V : ℕ → Ω → ℝ} {v : ℝ}
    (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) {f : Ω → ℝ} (hf : Integrable f μ)
    (k : ℕ) :
    μ[fun ω => bracketIndicator V v k ω * f ω | ℱ k]
      =ᵐ[μ] fun ω => bracketIndicator V v k ω * μ[f | ℱ k] ω :=
  condExp_stronglyMeasurable_mul_of_bound (μ := μ) (ℱ.le k)
    (stronglyMeasurable_bracketIndicator (v := v) hVpred k) hf 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (bracketIndicator_nonneg V v k ω)]
      exact bracketIndicator_le_one V v k ω)

/-- The square of an increment of a square-integrable process is integrable. -/
private theorem integrable_sq_increment (hL2 : ∀ k, MemLp (M k) 2 μ) (k : ℕ) :
    Integrable (fun ω => (M (k + 1) ω - M k ω) ^ 2) μ :=
  ((hL2 (k + 1)).sub (hL2 k)).integrable_sq

/-- The increments of a martingale are integrable. -/
private theorem integrable_increment (hmart : Martingale M ℱ μ) (k : ℕ) :
    Integrable (fun ω => M (k + 1) ω - M k ω) μ :=
  (hmart.integrable (k + 1)).sub (hmart.integrable k)

/-- The bracket indicator is `0` or `1`. -/
private theorem bracketIndicator_eq_zero_or_one (V : ℕ → Ω → ℝ) (v : ℝ) (k : ℕ) (ω : Ω) :
    bracketIndicator V v k ω = 0 ∨ bracketIndicator V v k ω = 1 := by
  unfold bracketIndicator
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The truncation of a square-integrable martingale by the path bracket keeps the centred
increments, and multiplies their conditional variance by the bracket indicator. -/
theorem condExp_truncated_increment_eq_zero_and_condExp_sq_eq [IsProbabilityMeasure μ]
    (hmart : Martingale M ℱ μ) (hL2 : ∀ k, MemLp (M k) 2 μ) (c : ℝ) (k : ℕ) :
    μ[fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω) | ℱ k]
        =ᵐ[μ] 0 ∧
      μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2
          | ℱ k]
        =ᵐ[μ] fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω
          * μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω := by
  have hVpred := stronglyMeasurable_pathBracket_succ μ ℱ M
  refine ⟨?_, ?_⟩
  · have h1 := condExp_bracketIndicator_mul (v := c) hVpred (integrable_increment hmart k) k
    filter_upwards [h1, condExp_increment_eq_zero hmart k] with ω e1 e2
    rw [e1]
    simp only [Pi.zero_apply] at e2 ⊢
    rw [e2, mul_zero]
  · have hfun : (fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω
          * (M (k + 1) ω - M k ω)) ^ 2)
        = fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω
          * (M (k + 1) ω - M k ω) ^ 2 := by
      funext ω
      rw [mul_pow, sq (bracketIndicator (pathBracket μ ℱ M) c k ω),
        bracketIndicator_mul_self]
    rw [hfun]
    exact condExp_bracketIndicator_mul (v := c) hVpred (integrable_sq_increment hL2 k) k

/-- The squared truncated increment restricted to the event `δ < |·|` is measurable. -/
private theorem measurable_sq_mul_ite {X : Ω → ℝ} (hX : Measurable X) (δ : ℝ) :
    Measurable fun ω => X ω ^ 2 * (if δ < |X ω| then 1 else 0) :=
  (hX.pow_const 2).mul
    (Measurable.ite (measurableSet_lt measurable_const hX.abs) measurable_const measurable_const)

/-- A squared random variable restricted to the event `δ < |·|` is at most the square. -/
private theorem sq_mul_ite_le (x δ : ℝ) :
    x ^ 2 * (if δ < |x| then 1 else 0) ≤ x ^ 2 := by
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]
    exact sq_nonneg x

/-- A squared random variable restricted to the event `δ < |·|` is nonnegative. -/
private theorem sq_mul_ite_nonneg (x δ : ℝ) :
    0 ≤ x ^ 2 * (if δ < |x| then 1 else 0) := by
  split_ifs
  · rw [mul_one]
    exact sq_nonneg x
  · rw [mul_zero]

/-- The truncation by the path bracket keeps the sum of the conditional variances below `c`, and
does not increase the conditional Lindeberg terms. -/
theorem sum_condExp_sq_truncated_le_and_lindeberg_term_le [IsProbabilityMeasure μ]
    (hmart : Martingale M ℱ μ) (hL2 : ∀ k, MemLp (M k) 2 μ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ)
    (δ : ℝ) :
    (∀ᵐ ω ∂μ, ∑ k ∈ Finset.range n,
        μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2
          | ℱ k] ω ≤ c) ∧
      ∀ k, μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2
          * (if δ < |bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)|
            then 1 else 0) | ℱ k]
        ≤ᵐ[μ] μ[fun ω => (M (k + 1) ω - M k ω) ^ 2
          * (if δ < |M (k + 1) ω - M k ω| then 1 else 0) | ℱ k] := by
  refine ⟨?_, fun k => ?_⟩
  · have hV0 := pathBracket_zero_aux μ ℱ M
    have hVmono := pathBracket_le_succ μ ℱ M
    have hstep : ∀ j ∈ Finset.range n, ∀ᵐ ω ∂μ,
        μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c j ω * (M (j + 1) ω - M j ω)) ^ 2
          | ℱ j] ω
        ≤ bracketIndicator (pathBracket μ ℱ M) c j ω
          * (pathBracket μ ℱ M (j + 1) ω - pathBracket μ ℱ M j ω) := by
      intro j _
      filter_upwards [(condExp_truncated_increment_eq_zero_and_condExp_sq_eq hmart hL2 c j).2,
        condExp_sq_increment_nonneg μ ℱ M j] with ω e1 e2
      rw [e1, pathBracket_succ, add_sub_cancel_left, max_eq_left e2]
    have hall := (Filter.eventually_all_finset (Finset.range n)).mpr hstep
    filter_upwards [hall] with ω hω
    exact le_trans (Finset.sum_le_sum hω) (sum_bracketIndicator_mul_le hc hV0 hVmono ω n).1
  · have hVpred := stronglyMeasurable_pathBracket_succ μ ℱ M
    have hg : Measurable (bracketIndicator (pathBracket μ ℱ M) c k) :=
      ((stronglyMeasurable_bracketIndicator (v := c) hVpred k).mono (ℱ.le k)).measurable
    have hΔ : Measurable fun ω => M (k + 1) ω - M k ω :=
      (((hmart.stronglyMeasurable (k + 1)).mono (ℱ.le (k + 1))).sub
        ((hmart.stronglyMeasurable k).mono (ℱ.le k))).measurable
    have hX : Measurable fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω
        * (M (k + 1) ω - M k ω) := hg.mul hΔ
    have hbound : ∀ ω, (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2
        * (if δ < |bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)|
          then 1 else 0)
        ≤ (M (k + 1) ω - M k ω) ^ 2 * (if δ < |M (k + 1) ω - M k ω| then 1 else 0) := by
      intro ω
      rcases bracketIndicator_eq_zero_or_one (pathBracket μ ℱ M) c k ω with h | h
      · rw [h, zero_mul]
        simpa using sq_mul_ite_nonneg (M (k + 1) ω - M k ω) δ
      · rw [h, one_mul]
    have hfint : Integrable (fun ω => (M (k + 1) ω - M k ω) ^ 2
        * (if δ < |M (k + 1) ω - M k ω| then 1 else 0)) μ := by
      refine Integrable.mono' (integrable_sq_increment hL2 k)
        (measurable_sq_mul_ite hΔ δ).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_mul_ite_nonneg _ δ)]
      exact sq_mul_ite_le _ δ
    have hgint : Integrable (fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω
        * (M (k + 1) ω - M k ω)) ^ 2
        * (if δ < |bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)|
          then 1 else 0)) μ := by
      refine Integrable.mono' hfint (measurable_sq_mul_ite hX δ).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_mul_ite_nonneg _ δ)]
      exact hbound ω
    exact condExp_mono hgint hfint (Filter.Eventually.of_forall hbound)

end Truncation

end CERW.Generic.Martingale.CLT
