import CERW.Generic.Martingale.FreedmanEvent
import CERW.Model.Bracket
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import CERW.Generic.Martingale.CLT.Interfaces

/-!
# The compensated exponential and the characteristic-function bound

The telescoping exponential compensator of a square-integrable martingale, truncated predictably
at the level where its pathwise bracket exceeds `c`, and the resulting bound on the difference of
the characteristic function of the terminal value from that of the centered Gaussian. The
increment step bound and the properties of the path bracket and its truncation enter as explicit
hypotheses.
-/

universe u

namespace CERW.Generic.Martingale.CLT

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal

section Helpers

/-- One step of the path bracket adds the nonnegative part of the conditional variance. -/
private theorem pathBracket_succ {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    pathBracket μ ℱ M (k + 1) ω = pathBracket μ ℱ M k ω
      + max (μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω) 0 := by
  unfold pathBracket
  rw [Finset.sum_range_succ]

/-- The conditional variance of an increment is almost surely nonnegative. -/
private theorem condExp_sq_increment_nonneg {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (k : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ μ[fun ω' => (M (k + 1) ω' - M k ω') ^ 2 | ℱ k] ω :=
  condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg (M (k + 1) ω - M k ω))

/-- A bracket indicator is `0` or `1`. -/
private theorem bracketIndicator_eq_zero_or_one {Ω : Type*} {V : ℕ → Ω → ℝ} (v : ℝ)
    (k : ℕ) (ω : Ω) : bracketIndicator V v k ω = 0 ∨ bracketIndicator V v k ω = 1 := by
  unfold bracketIndicator
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- A squared value restricted to the event `δ < |·|` is at most the square. -/
private theorem sq_mul_ite_le (x δ : ℝ) :
    x ^ 2 * (if δ < |x| then 1 else 0) ≤ x ^ 2 := by
  split_ifs with h
  · rw [mul_one]
  · rw [mul_zero]
    exact sq_nonneg x

/-- A squared value restricted to the event `δ < |·|` is nonnegative. -/
private theorem sq_mul_ite_nonneg (x δ : ℝ) :
    0 ≤ x ^ 2 * (if δ < |x| then 1 else 0) := by
  split_ifs with h
  · rw [mul_one]
    exact sq_nonneg x
  · rw [mul_zero]

/-- The conditional expectation of a square is almost surely at least the square of the
conditional expectation: here only the nonnegativity of the second moment is needed. -/
private theorem condExp_sq_nonneg {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (X : Ω → ℝ) (k : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ μ[fun ω' => X ω' ^ 2 | ℱ k] ω :=
  condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω))

/-- Telescoping bound for a `ℂ`-valued process whose increments are `Y k (F k - 1)`. -/
private theorem norm_integral_sub_one_le_sum
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℂ) (F : ℕ → Ω → ℂ) (B : ℕ → ℝ) (n : ℕ)
    (hY0 : Y 0 = fun _ => 1)
    (hYstep : ∀ k, Y (k + 1) - Y k = fun ω => Y k ω * (F k ω - 1))
    (hYint : ∀ k, k ≤ n → Integrable (Y k) μ)
    (hstep : ∀ k, k < n → ‖∫ ω, Y k ω * (F k ω - 1) ∂μ‖ ≤ B k) :
    ‖∫ ω, Y n ω ∂μ - 1‖ ≤ ∑ k ∈ Finset.range n, B k := by
  have hYsum : Y n - Y 0 = ∑ k ∈ Finset.range n, (Y (k + 1) - Y k) :=
    (Finset.sum_range_sub Y n).symm
  have hY0int : ∫ ω, Y 0 ω ∂μ = 1 := by
    rw [hY0]
    simp
  have hfun : ∫ ω, (Y n - Y 0) ω ∂μ
      = ∑ k ∈ Finset.range n, ∫ ω, Y k ω * (F k ω - 1) ∂μ := by
    rw [hYsum]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [hYstep k]
    · intro k hk
      exact (hYint (k + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hk))).sub
        (hYint k (le_of_lt (Finset.mem_range.mp hk)))
  calc ‖∫ ω, Y n ω ∂μ - 1‖
      = ‖∫ ω, (Y n ω - Y 0 ω) ∂μ‖ := by
        rw [integral_sub (hYint n le_rfl) (hYint 0 (Nat.zero_le n)), hY0int]
    _ = ‖∑ k ∈ Finset.range n, ∫ ω, Y k ω * (F k ω - 1) ∂μ‖ := by
        rw [show (∫ ω, (Y n ω - Y 0 ω) ∂μ) = ∫ ω, (Y n - Y 0) ω ∂μ from rfl, hfun]
    _ ≤ ∑ k ∈ Finset.range n, ‖∫ ω, Y k ω * (F k ω - 1) ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, B k :=
        Finset.sum_le_sum fun k hk => hstep k (Finset.mem_range.mp hk)

/-- One telescoping step of the compensated exponential: the increment of
`exp (i t M'_k + t² Q_k / 2)` is the previous value times the centred exponential factor. -/
private lemma cexp_compensator_step {Ω : Type*} (t : ℝ) (Mp : ℕ → Ω → ℝ)
    (q : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    Complex.exp ((t : ℂ) * (Mp (k + 1) ω : ℂ) * Complex.I +
        (((t ^ 2 / 2 * ∑ j ∈ Finset.range (k + 1), q j ω) : ℝ) : ℂ))
      - Complex.exp ((t : ℂ) * (Mp k ω : ℂ) * Complex.I +
        (((t ^ 2 / 2 * ∑ j ∈ Finset.range k, q j ω) : ℝ) : ℂ))
      = Complex.exp ((t : ℂ) * (Mp k ω : ℂ) * Complex.I +
          (((t ^ 2 / 2 * ∑ j ∈ Finset.range k, q j ω) : ℝ) : ℂ))
        * (Complex.exp ((t : ℂ) * (((Mp (k + 1) ω - Mp k ω : ℝ)) : ℂ) * Complex.I) *
            Complex.exp (((t ^ 2 * q k ω / 2 : ℝ) : ℂ)) - 1) := by
  have hsum : (∑ j ∈ Finset.range (k + 1), q j ω)
      = (∑ j ∈ Finset.range k, q j ω) + q k ω := Finset.sum_range_succ ..
  have harg : ((t : ℂ) * (Mp (k + 1) ω : ℂ) * Complex.I +
        (((t ^ 2 / 2 * ∑ j ∈ Finset.range (k + 1), q j ω) : ℝ) : ℂ))
      = ((t : ℂ) * (Mp k ω : ℂ) * Complex.I +
          (((t ^ 2 / 2 * ∑ j ∈ Finset.range k, q j ω) : ℝ) : ℂ))
        + ((t : ℂ) * (((Mp (k + 1) ω - Mp k ω : ℝ)) : ℂ) * Complex.I +
            (((t ^ 2 * q k ω / 2 : ℝ) : ℂ))) := by
    rw [hsum]
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_add]
  ring

end Helpers

/-- A squared value restricted to the complement of `δ < |·|` is at most the square. -/
private theorem sq_mul_ite_le' (x δ : ℝ) :
    x ^ 2 * (if δ < |x| then 0 else 1) ≤ x ^ 2 := by
  split_ifs <;> simp [sq_nonneg]

/-- A squared value restricted to the complement of `δ < |·|` is nonnegative. -/
private theorem sq_mul_ite_nonneg' (x δ : ℝ) :
    0 ≤ x ^ 2 * (if δ < |x| then 0 else 1) := by
  split_ifs <;> simp [sq_nonneg]

/-- A squared value restricted to the complement of `δ < |·|` is at most `δ ^ 2`. -/
private theorem sq_mul_ite_le_sq (x δ : ℝ) :
    x ^ 2 * (if δ < |x| then 0 else 1) ≤ δ ^ 2 := by
  by_cases h : δ < |x|
  · simp [h, sq_nonneg]
  · have hx : |x| ≤ δ := not_lt.mp h
    simp only [h, ↓reduceIte, mul_one]
    nlinarith [sq_abs x, abs_nonneg x]

/-- The truncated-square map is Borel measurable. -/
private theorem measurable_sq_mul_ite_fn (δ : ℝ) :
    Measurable fun x : ℝ => x ^ 2 * (if δ < |x| then 1 else 0) :=
  (measurable_id.pow_const 2).mul
    (Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
      measurable_const measurable_const)

/-- The complementary truncated-square map is Borel measurable. -/
private theorem measurable_sq_mul_ite_fn' (δ : ℝ) :
    Measurable fun x : ℝ => x ^ 2 * (if δ < |x| then 0 else 1) :=
  (measurable_id.pow_const 2).mul
    (Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
      measurable_const measurable_const)

/-- A truncated square is integrable. -/
private theorem integrable_sq_mul_ite {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (δ : ℝ) :
    Integrable (fun ω => X ω ^ 2 * (if δ < |X ω| then 1 else 0)) μ := by
  refine (hX.integrable_sq).mono'
    ((measurable_sq_mul_ite_fn δ).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_mul_ite_nonneg _ _)]
  exact sq_mul_ite_le _ _

/-- The complementary truncated square is integrable. -/
private theorem integrable_sq_mul_ite' {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (δ : ℝ) :
    Integrable (fun ω => X ω ^ 2 * (if δ < |X ω| then 0 else 1)) μ := by
  refine (hX.integrable_sq).mono'
    ((measurable_sq_mul_ite_fn' δ).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_mul_ite_nonneg' _ _)]
  exact sq_mul_ite_le' _ _

/-- For a square-integrable martingale, the expectation of the exponential
`e^{itM'_n + t² Q_n / 2}` built from the predictably truncated martingale `M'` and the sum `Q_n`
of its conditional variances differs from `1` by at most an explicit bound in `E[min (lind, c)]`. -/
theorem compensated_cexp_bound
    (hE4 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {m : MeasurableSpace Ω} (X : Ω → ℝ) (W : Ω → ℂ) (K c : ℝ),
      m ≤ m0 → MemLp X 2 μ → μ[X | m] =ᵐ[μ] 0 → StronglyMeasurable[m] W →
      (∀ᵐ ω ∂μ, ‖W ω‖ ≤ K) →
      (∀ᵐ ω ∂μ, μ[fun ω => X ω ^ 2 | m] ω ≤ c) →
      ∀ t δ : ℝ, 0 ≤ δ →
      ‖∫ ω, W ω * (Complex.exp (t * X ω * Complex.I) *
          Complex.exp ((t ^ 2 * μ[fun ω => X ω ^ 2 | m] ω / 2 : ℝ)) - 1) ∂μ‖ ≤
        K * Real.exp (t ^ 2 * c / 2) *
          (t ^ 4 / 8 * ∫ ω, μ[fun ω => X ω ^ 2 | m] ω ^ 2 ∂μ +
            4 * (δ * |t| ^ 3 * ∫ ω, X ω ^ 2 ∂μ +
              t ^ 2 * ∫ ω, X ω ^ 2 * (if δ < |X ω| then 1 else 0) ∂μ)))
    (hF1 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ),
      (∀ ω, pathBracket μ ℱ M 0 ω = 0) ∧
      (∀ k ω, pathBracket μ ℱ M k ω ≤ pathBracket μ ℱ M (k + 1) ω) ∧
      (∀ k, StronglyMeasurable[ℱ k] (pathBracket μ ℱ M (k + 1))) ∧
      (∀ᵐ ω ∂μ, ∀ k, pathBracket μ ℱ M k ω = CERW.predBracket μ ℱ M M k ω))
    (hF2 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c : ℝ), 0 ≤ c →
      Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → ∀ k,
      μ[fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω) | ℱ k]
          =ᵐ[μ] 0 ∧
      μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω *
          (M (k + 1) ω - M k ω)) ^ 2 | ℱ k]
          =ᵐ[μ] fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω *
            μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω)
    (hF3 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c : ℝ), 0 ≤ c →
      Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → (∀ ω, M 0 ω = 0) →
      ∀ (n : ℕ) (δ : ℝ),
      (∀ᵐ ω ∂μ, ∑ k ∈ Finset.range n,
          μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω *
            (M (k + 1) ω - M k ω)) ^ 2
            | ℱ k] ω ≤ c) ∧
      ∀ k, μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω *
            (M (k + 1) ω - M k ω)) ^ 2 *
            (if δ < |bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)|
              then 1 else 0) | ℱ k]
          ≤ᵐ[μ] μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 *
            (if δ < |M (k + 1) ω - M k ω| then 1 else 0) | ℱ k]) :
    ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c : ℝ), 0 ≤ c →
      Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → (∀ ω, M 0 ω = 0) →
      ∀ (n : ℕ) (t δ : ℝ), 0 ≤ δ →
      ‖∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) c n ω * Complex.I +
          (t ^ 2 / 2 * ∑ k ∈ Finset.range n,
            μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω -
              predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω : ℝ)) ∂μ
          - 1‖ ≤
        Real.exp (t ^ 2 * c) *
          (t ^ 4 / 8 * (c * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ)) +
            4 * (δ * |t| ^ 3 * c + t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ)) := by
  intro Ω m0 μ _ ℱ M c hc hmart hL2 hM0 n t δ hδ
  obtain ⟨hV0, hVmono, hVpred, hVpredBr⟩ := hF1 μ ℱ M
  let Mp : ℕ → Ω → ℝ := predictableStop M (pathBracket μ ℱ M) c
  let X : ℕ → Ω → ℝ := fun k ω => Mp (k + 1) ω - Mp k ω
  let q : ℕ → Ω → ℝ := fun k ω => μ[fun ω' => X k ω' ^ 2 | ℱ k] ω
  let Q : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range k, q j ω
  let Y : ℕ → Ω → ℂ := fun k ω => Complex.exp ((t : ℂ) * (Mp k ω : ℂ) * Complex.I +
      (((t ^ 2 / 2 * Q k ω : ℝ)) : ℂ))
  change ‖∫ ω, Y n ω ∂μ - 1‖ ≤ Real.exp (t ^ 2 * c) *
    (t ^ 4 / 8 * (c * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ)) +
      4 * (δ * |t| ^ 3 * c + t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ))
  -- the increment of the truncated martingale
  have hXeq : ∀ k, X k = fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω *
      (M (k + 1) ω - M k ω) := by
    intro k
    funext ω
    simp only [X, Mp]
    exact predictableStop_succ_sub M (pathBracket μ ℱ M) c k ω
  -- the truncated increments are centred
  have hX0 : ∀ k, μ[X k | ℱ k] =ᵐ[μ] 0 := by
    intro k
    have h := (hF2 μ ℱ M c hc hmart hL2 k).1
    rwa [← hXeq k] at h
  -- nonnegativity of the conditional variances
  have hq_nonneg : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ q k ω := by
    rw [ae_all_iff]
    intro k
    exact condExp_nonneg (ae_of_all _ fun ω => sq_nonneg (X k ω))
  -- the sum of the conditional variances is at most c
  have hQn : ∀ᵐ ω ∂μ, Q n ω ≤ c := by
    have h := (hF3 μ ℱ M c hc hmart hL2 hM0 n δ).1
    filter_upwards [h] with ω hω
    have hsum : Q n ω = ∑ k ∈ Finset.range n, μ[fun ω' =>
        (bracketIndicator (pathBracket μ ℱ M) c k ω' * (M (k + 1) ω' - M k ω')) ^ 2
          | ℱ k] ω := by
      simp only [Q, q]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      funext ω'
      rw [hXeq k]
    rw [hsum]
    exact hω
  -- every partial sum is at most c
  have hQ_le : ∀ᵐ ω ∂μ, ∀ k, k ≤ n → Q k ω ≤ c := by
    filter_upwards [hQn, hq_nonneg] with ω hQnω hnn
    intro k hk
    have hmono : Q k ω ≤ Q n ω := by
      simp only [Q]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun j hj => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hj) hk))
        (fun j _ _ => hnn j)
    linarith
  -- the individual conditional variances are at most c
  have hq_le : ∀ᵐ ω ∂μ, ∀ k, k < n → q k ω ≤ c := by
    filter_upwards [hq_nonneg, hQn] with ω hnn hQnω
    intro k hk
    have hle : q k ω ≤ Q n ω := by
      simp only [Q]
      exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_range.mpr hk)
    linarith
  -- strong measurability of the compensator
  have hYsm : ∀ k, StronglyMeasurable[ℱ k] (Y k) := by
    intro k
    have hMp : StronglyMeasurable[ℱ k] (Mp k) :=
      stronglyAdapted_predictableStop hmart hVpred k
    have hQ : StronglyMeasurable[ℱ k] (Q k) := by
      simp only [Q]
      refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
      exact (stronglyMeasurable_condExp (μ := μ) (m := ℱ j)).mono
        (ℱ.mono (le_of_lt (Finset.mem_range.mp hj)))
    simp only [Y]
    fun_prop
  -- the norm of the compensator
  have hYnorm : ∀ᵐ ω ∂μ, ∀ k, k ≤ n → ‖Y k ω‖ ≤ Real.exp (t ^ 2 * c / 2) := by
    filter_upwards [hQ_le] with ω hQ
    intro k hk
    rw [Complex.norm_exp]
    have hre : (((t : ℂ) * (Mp k ω : ℂ) * Complex.I +
        (((t ^ 2 / 2 * Q k ω : ℝ)) : ℂ))).re = t ^ 2 / 2 * Q k ω := by
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hre]
    refine Real.exp_le_exp.mpr ?_
    have h := mul_le_mul_of_nonneg_left (hQ k hk) (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
    linarith
  -- integrability of the compensator
  have hYint : ∀ k, k ≤ n → Integrable (Y k) μ := by
    intro k hk
    refine Integrable.of_bound ((hYsm k).mono (ℱ.le k)).aestronglyMeasurable
      (Real.exp (t ^ 2 * c / 2)) ?_
    filter_upwards [hYnorm] with ω h
    exact h k hk
  -- the one-step exponential factor
  let F : ℕ → Ω → ℂ := fun k ω => Complex.exp ((t : ℂ) * (X k ω : ℂ) * Complex.I) *
      Complex.exp ((t ^ 2 * q k ω / 2 : ℝ))
  let D : ℕ → Ω → ℝ := fun k ω => M (k + 1) ω - M k ω
  let L : ℕ → Ω → ℝ := fun k ω => μ[fun ω' => D k ω' ^ 2 *
      (if δ < |D k ω'| then 1 else 0) | ℱ k] ω
  let L' : ℕ → Ω → ℝ := fun k ω => μ[fun ω' => X k ω' ^ 2 *
      (if δ < |X k ω'| then 1 else 0) | ℱ k] ω
  let iota : ℝ := ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ
  -- the compensator starts at one
  have hY0 : Y 0 = fun _ => 1 := by
    funext ω
    simp only [Y, Q, Finset.range_zero, Finset.sum_empty, Mp, predictableStop_zero,
      mul_zero, Complex.ofReal_zero, zero_mul, add_zero, Complex.exp_zero]
  -- one telescoping step
  have hYstep : ∀ k, Y (k + 1) - Y k = fun ω => Y k ω * (F k ω - 1) := by
    intro k
    funext ω
    simp only [Pi.sub_apply, Y, Q, F, X]
    exact cexp_compensator_step t Mp q k ω
  -- the truncated increments are square-integrable
  have hXmem : ∀ k, MemLp (X k) 2 μ := by
    intro k
    have hD : MemLp (fun ω => M (k + 1) ω - M k ω) 2 μ := (hL2 (k + 1)).sub (hL2 k)
    refine MemLp.of_le hD ?_ ?_
    · exact (((stronglyAdapted_predictableStop hmart hVpred (k + 1)).sub
          ((stronglyAdapted_predictableStop hmart hVpred k).mono
            (ℱ.mono (Nat.le_succ k)))).mono (ℱ.le (k + 1))).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, Real.norm_eq_abs, hXeq k]
      simp only [abs_mul]      
      refine mul_le_of_le_one_left (abs_nonneg _) ?_
      rw [abs_of_nonneg (bracketIndicator_nonneg (pathBracket μ ℱ M) c k ω)]
      exact bracketIndicator_le_one (pathBracket μ ℱ M) c k ω
  -- the one-step bound
  have hFstep : ∀ k, k < n → ‖∫ ω, Y k ω * (F k ω - 1) ∂μ‖ ≤
      Real.exp (t ^ 2 * c) * (t ^ 4 / 8 * ∫ ω, q k ω ^ 2 ∂μ +
        4 * (δ * |t| ^ 3 * ∫ ω, X k ω ^ 2 ∂μ +
          t ^ 2 * ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ)) := by
    intro k hk
    have hYnorm_k : ∀ᵐ ω ∂μ, ‖Y k ω‖ ≤ Real.exp (t ^ 2 * c / 2) :=
      hYnorm.mono fun ω h => h k (le_of_lt hk)
    have hqk_le : ∀ᵐ ω ∂μ, μ[fun ω' => X k ω' ^ 2 | ℱ k] ω ≤ c :=
      hq_le.mono fun ω h => h k hk
    have hE4k := hE4 μ (X k) (Y k) (Real.exp (t ^ 2 * c / 2)) c (ℱ.le k) (hXmem k)
      (hX0 k) (hYsm k) hYnorm_k hqk_le t δ hδ
    have hexp : Real.exp (t ^ 2 * c / 2) * Real.exp (t ^ 2 * c / 2) = Real.exp (t ^ 2 * c) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc ‖∫ ω, Y k ω * (F k ω - 1) ∂μ‖
        ≤ Real.exp (t ^ 2 * c / 2) * Real.exp (t ^ 2 * c / 2) *
            (t ^ 4 / 8 * ∫ ω, q k ω ^ 2 ∂μ + 4 * (δ * |t| ^ 3 * ∫ ω, X k ω ^ 2 ∂μ +
              t ^ 2 * ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ)) := hE4k
      _ = Real.exp (t ^ 2 * c) * (t ^ 4 / 8 * ∫ ω, q k ω ^ 2 ∂μ +
            4 * (δ * |t| ^ 3 * ∫ ω, X k ω ^ 2 ∂μ +
              t ^ 2 * ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ)) := by
          rw [hexp]
  -- the conditional variance is dominated by `δ ^ 2` plus its Lindeberg tail
  have hL'_le_q : ∀ k, L' k ≤ᵐ[μ] q k := by
    intro k
    refine condExp_mono (m := ℱ k) (integrable_sq_mul_ite (hXmem k) δ)
      ((hXmem k).integrable_sq) (ae_of_all _ fun ω => sq_mul_ite_le (X k ω) δ)
  have hq_le_delta : ∀ k, q k ≤ᵐ[μ] fun ω => δ ^ 2 + L' k ω := by
    intro k
    have hi1 := integrable_sq_mul_ite (hXmem k) δ
    have hi2 := integrable_sq_mul_ite' (hXmem k) δ
    have hsplit : q k =ᵐ[μ] L' k + fun ω => μ[fun ω' =>
        X k ω' ^ 2 * (if δ < |X k ω'| then 0 else 1) | ℱ k] ω := by
      have hcongr : μ[fun ω' => X k ω' ^ 2 | ℱ k] =ᵐ[μ]
          μ[fun ω' => X k ω' ^ 2 * (if δ < |X k ω'| then 1 else 0) +
            X k ω' ^ 2 * (if δ < |X k ω'| then 0 else 1) | ℱ k] :=
        condExp_congr_ae (ae_of_all _ fun ω => by
          by_cases h : δ < |X k ω| <;> simp [h])
      exact hcongr.trans (condExp_add hi1 hi2 (ℱ k))
    have hR : (fun ω => μ[fun ω' => X k ω' ^ 2 *
        (if δ < |X k ω'| then 0 else 1) | ℱ k] ω) ≤ᵐ[μ] fun _ => δ ^ 2 := by
      have h := condExp_mono (m := ℱ k) hi2 (integrable_const (δ ^ 2))
        (ae_of_all _ fun ω => sq_mul_ite_le_sq (X k ω) δ)
      simpa only [condExp_const (ℱ.le k) (δ ^ 2)] using h
    filter_upwards [hsplit, hR] with ω h1 h2
    simp only [Pi.add_apply] at h1
    rw [h1]
    linarith
  -- the truncated Lindeberg term is at most the original one
  have hL'_le_L : ∀ k, L' k ≤ᵐ[μ] L k := by
    intro k
    have h := (hF3 μ ℱ M c hc hmart hL2 hM0 n δ).2 k
    have hL' : L' k = fun ω => μ[fun ω' =>
        (bracketIndicator (pathBracket μ ℱ M) c k ω' * (M (k + 1) ω' - M k ω')) ^ 2 *
          (if δ < |bracketIndicator (pathBracket μ ℱ M) c k ω' *
            (M (k + 1) ω' - M k ω')| then 1 else 0) | ℱ k] ω := by
      funext ω
      simp only [L']
      congr 1
      funext ω'
      rw [hXeq k]
    have hL : L k = fun ω => μ[fun ω' => (M (k + 1) ω' - M k ω') ^ 2 *
        (if δ < |M (k + 1) ω' - M k ω'| then 1 else 0) | ℱ k] ω := by
      funext ω
      simp only [L, D]
    rw [hL', hL]
    exact h
  -- nonnegativity of the Lindeberg sum
  have hlind_nonneg : 0 ≤ᵐ[μ] lind μ ℱ M δ n := by
    filter_upwards [(Filter.eventually_all_finset (Finset.range n)).mpr
      (fun i _ => condExp_nonneg (μ := μ) (m := ℱ i)
        (f := fun ω => (M (i + 1) ω - M i ω) ^ 2 *
          (if δ < |M (i + 1) ω - M i ω| then 1 else 0))
        (Eventually.of_forall fun ω => by positivity))] with ω hω
    rw [lind]
    exact Finset.sum_nonneg fun i hi => hω i hi
  -- measurability of the Lindeberg sum
  have hlind_aesm : AEStronglyMeasurable (lind μ ℱ M δ n) μ := by
    have h : AEStronglyMeasurable (∑ i ∈ Finset.range n, (fun ω =>
        μ[fun ω => (M (i + 1) ω - M i ω) ^ 2 *
          (if δ < |M (i + 1) ω - M i ω| then 1 else 0) | ℱ i] ω) : Ω → ℝ) μ :=
      Finset.aestronglyMeasurable_sum (M := ℝ) (Finset.range n) (fun i _ =>
        ((stronglyMeasurable_condExp (μ := μ) (m := ℱ i)
          (f := fun ω => (M (i + 1) ω - M i ω) ^ 2 *
            (if δ < |M (i + 1) ω - M i ω| then 1 else 0))).mono
          (ℱ.le i)).aestronglyMeasurable)
    convert h using 1
    ext ω
    simp only [lind, Finset.sum_apply]
  have hmin_int : Integrable (fun ω => min (lind μ ℱ M δ n ω) c) μ := by
    refine Integrable.of_bound
      ((hlind_aesm.aemeasurable.min aemeasurable_const).aestronglyMeasurable) (max c 0) ?_
    filter_upwards [hlind_nonneg] with ω h0
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min h0 hc)]
    exact (min_le_right _ _).trans (le_max_left _ _)
  -- nonnegativity of the truncated Lindeberg term
  have hL'_nonneg : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ L' k ω := by
    rw [ae_all_iff]
    intro k
    exact condExp_nonneg (ae_of_all _ fun ω => sq_mul_ite_nonneg (X k ω) δ)
  -- the tail sum
  have hsumTail : ∑ k ∈ Finset.range n,
      ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ ≤ iota := by
    have hint : ∀ k, ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ =
        ∫ ω, L' k ω ∂μ := fun k => (integral_condExp (ℱ.le k)).symm
    have hle : (fun ω => ∑ k ∈ Finset.range n, L' k ω) ≤ᵐ[μ]
        fun ω => min (lind μ ℱ M δ n ω) c := by
      have h1 : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range n, L' k ω ≤ lind μ ℱ M δ n ω := by
        have h := (Filter.eventually_all_finset (Finset.range n)).mpr
          (fun k _ => hL'_le_L k)
        filter_upwards [h] with ω hω
        simp only [lind]
        exact Finset.sum_le_sum fun k hk => hω k hk
      have h2 : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range n, L' k ω ≤ c := by
        have h := (Filter.eventually_all_finset (Finset.range n)).mpr
          (fun k _ => hL'_le_q k)
        filter_upwards [h, hQn] with ω hω hQ
        refine (Finset.sum_le_sum fun k hk => hω k hk).trans ?_
        simpa only [Q] using hQ
      filter_upwards [h1, h2] with ω e1 e2
      exact le_min e1 e2
    calc ∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ
        = ∑ k ∈ Finset.range n, ∫ ω, L' k ω ∂μ :=
          Finset.sum_congr rfl fun k _ => hint k
      _ = ∫ ω, ∑ k ∈ Finset.range n, L' k ω ∂μ := by
          rw [integral_finsetSum]
          intro k _
          exact integrable_condExp
      _ ≤ ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ :=
          integral_mono_ae (integrable_finsetSum _ fun k _ => integrable_condExp) hmin_int hle
      _ = iota := rfl
  -- the square sum
  have hsumX2 : ∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ ≤ c := by
    have hint : ∀ k, ∫ ω, X k ω ^ 2 ∂μ = ∫ ω, q k ω ∂μ :=
      fun k => (integral_condExp (ℱ.le k)).symm
    have hQint : Integrable (Q n) μ := by
      simp only [Q]
      exact integrable_finsetSum _ fun k _ => integrable_condExp
    calc ∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ
        = ∑ k ∈ Finset.range n, ∫ ω, q k ω ∂μ := Finset.sum_congr rfl fun k _ => hint k
      _ = ∫ ω, ∑ k ∈ Finset.range n, q k ω ∂μ := by
          rw [integral_finsetSum]
          intro k _
          exact integrable_condExp
      _ = ∫ ω, Q n ω ∂μ := rfl
      _ ≤ ∫ ω, c ∂μ := integral_mono_ae hQint (integrable_const c) hQn
      _ = c := by rw [integral_const, probReal_univ, one_smul]
  -- the quadratic sum
  have hsumQ2 : ∑ k ∈ Finset.range n, ∫ ω, q k ω ^ 2 ∂μ ≤ c * (δ ^ 2 + iota) := by
    have hq2 : ∀ k, k < n → ∫ ω, q k ω ^ 2 ∂μ ≤
        δ ^ 2 * ∫ ω, q k ω ∂μ + c * ∫ ω, L' k ω ∂μ := by
      intro k hk
      have hq2int : Integrable (fun ω => q k ω ^ 2) μ := by
        refine Integrable.mono'
          ((integrable_condExp (f := fun ω => X k ω ^ 2) (m := ℱ k)).const_mul c)
          (((stronglyMeasurable_condExp (μ := μ) (m := ℱ k)
            (f := fun ω => X k ω ^ 2)).mono (ℱ.le k)).aestronglyMeasurable.pow 2) ?_
        filter_upwards [hq_nonneg, hq_le] with ω h0 h1
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
        exact mul_le_mul_of_nonneg_right (h1 k hk) (h0 k)
      have hpt : q k ^ 2 ≤ᵐ[μ] fun ω => δ ^ 2 * q k ω + c * L' k ω := by
        filter_upwards [hq_nonneg, hq_le, hq_le_delta k, hL'_nonneg] with ω h0 h1 h2 h3
        calc q k ω ^ 2 = q k ω * q k ω := by ring
          _ ≤ q k ω * (δ ^ 2 + L' k ω) := mul_le_mul_of_nonneg_left h2 (h0 k)
          _ = δ ^ 2 * q k ω + q k ω * L' k ω := by ring
          _ ≤ δ ^ 2 * q k ω + c * L' k ω := by
              have := mul_le_mul_of_nonneg_right (h1 k hk) (h3 k)
              linarith
      have hintdom : Integrable (fun ω => δ ^ 2 * q k ω + c * L' k ω) μ :=
        ((integrable_condExp (f := fun ω => X k ω ^ 2) (m := ℱ k)).const_mul (δ ^ 2)).add
          ((integrable_condExp (f := fun ω => X k ω ^ 2 * (if δ < |X k ω| then 1 else 0))
            (m := ℱ k)).const_mul c)
      calc ∫ ω, q k ω ^ 2 ∂μ
          ≤ ∫ ω, δ ^ 2 * q k ω + c * L' k ω ∂μ := integral_mono_ae hq2int hintdom hpt
        _ = δ ^ 2 * ∫ ω, q k ω ∂μ + c * ∫ ω, L' k ω ∂μ := by
            rw [integral_add, integral_const_mul, integral_const_mul]
            · exact
                (integrable_condExp (f := fun ω => X k ω ^ 2) (m := ℱ k)).const_mul (δ ^ 2)
            · exact
                (integrable_condExp (f := fun ω => X k ω ^ 2 *
                  (if δ < |X k ω| then 1 else 0)) (m := ℱ k)).const_mul c
    have hsumQ : ∑ k ∈ Finset.range n, ∫ ω, q k ω ∂μ ≤ c := by
      calc ∑ k ∈ Finset.range n, ∫ ω, q k ω ∂μ
          = ∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ :=
            Finset.sum_congr rfl fun k _ => integral_condExp (ℱ.le k)
        _ ≤ c := hsumX2
    have hsumL' : ∑ k ∈ Finset.range n, ∫ ω, L' k ω ∂μ ≤ iota := by
      calc ∑ k ∈ Finset.range n, ∫ ω, L' k ω ∂μ
          = ∑ k ∈ Finset.range n,
              ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ :=
            Finset.sum_congr rfl fun k _ => integral_condExp (ℱ.le k)
        _ ≤ iota := hsumTail
    calc ∑ k ∈ Finset.range n, ∫ ω, q k ω ^ 2 ∂μ
        ≤ ∑ k ∈ Finset.range n,
            (δ ^ 2 * ∫ ω, q k ω ∂μ + c * ∫ ω, L' k ω ∂μ) :=
          Finset.sum_le_sum fun k hk => hq2 k (Finset.mem_range.mp hk)
      _ = δ ^ 2 * ∑ k ∈ Finset.range n, ∫ ω, q k ω ∂μ +
            c * ∑ k ∈ Finset.range n, ∫ ω, L' k ω ∂μ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ δ ^ 2 * c + c * iota := by
          gcongr
      _ = c * (δ ^ 2 + iota) := by ring
  -- the telescoping sum
  have hB : ∀ k, k < n → ‖∫ ω, Y k ω * (F k ω - 1) ∂μ‖ ≤
      Real.exp (t ^ 2 * c) * (t ^ 4 / 8 * ∫ ω, q k ω ^ 2 ∂μ +
        4 * (δ * |t| ^ 3 * ∫ ω, X k ω ^ 2 ∂μ +
          t ^ 2 * ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ)) := hFstep
  have htele := norm_integral_sub_one_le_sum Y F (fun k => Real.exp (t ^ 2 * c) *
      (t ^ 4 / 8 * ∫ ω, q k ω ^ 2 ∂μ +
        4 * (δ * |t| ^ 3 * ∫ ω, X k ω ^ 2 ∂μ +
          t ^ 2 * ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ)))
      n hY0 hYstep hYint hB
  have hsumB : ∑ k ∈ Finset.range n, (Real.exp (t ^ 2 * c) *
      (t ^ 4 / 8 * ∫ ω, q k ω ^ 2 ∂μ +
        4 * (δ * |t| ^ 3 * ∫ ω, X k ω ^ 2 ∂μ +
          t ^ 2 * ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ)))
      ≤ Real.exp (t ^ 2 * c) *
        (t ^ 4 / 8 * (c * (δ ^ 2 + iota)) + 4 * (δ * |t| ^ 3 * c + t ^ 2 * iota)) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have h4 : ∑ k ∈ Finset.range n, (t ^ 4 / 8 * ∫ ω, q k ω ^ 2 ∂μ +
        4 * (δ * |t| ^ 3 * ∫ ω, X k ω ^ 2 ∂μ +
          t ^ 2 * ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ))
        = t ^ 4 / 8 * ∑ k ∈ Finset.range n, ∫ ω, q k ω ^ 2 ∂μ +
          4 * (δ * |t| ^ 3 * ∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ +
            t ^ 2 * ∑ k ∈ Finset.range n,
              ∫ ω, X k ω ^ 2 * (if δ < |X k ω| then 1 else 0) ∂μ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h4]
    gcongr
  exact htele.trans hsumB

end CERW.Generic.Martingale.CLT
