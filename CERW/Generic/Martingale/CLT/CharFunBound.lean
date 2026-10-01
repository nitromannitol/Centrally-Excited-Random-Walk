import CERW.Generic.Martingale.FreedmanEvent
import CERW.Model.Bracket
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Measure.Real
import CERW.Generic.Martingale.CLT.Interfaces

/-!
# The characteristic-function bound for one martingale

The conditional Lindeberg sum and the pathwise predictable bracket of a process, the
`e^A`-Lipschitz bound for the real exponential below `A`, and the `G2` estimate, split into small
private lemmas so that each stays within the heartbeat budget. The bound of the compensated
exponential (`G1`), the centred conditional increments (`F2`) and the truncated bracket and
Lindeberg bounds (`F3`) enter as explicit hypotheses.
-/

universe u

namespace CERW.Generic.Martingale.CLT

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal

section PathBracket

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)
  (M : ℕ → Ω → ℝ)

/-- The pathwise bracket vanishes at time `0`. -/
private theorem pathBracket_zero_aux (ω : Ω) : pathBracket μ ℱ M 0 ω = 0 := by
  simp only [pathBracket, Finset.range_zero, Finset.sum_empty]

/-- The pathwise bracket is nondecreasing. -/
private theorem pathBracket_mono_aux (k : ℕ) (ω : Ω) :
    pathBracket μ ℱ M k ω ≤ pathBracket μ ℱ M (k + 1) ω := by
  simp only [pathBracket, Finset.sum_range_succ]
  exact le_add_of_nonneg_right (le_max_right _ _)

/-- The pathwise bracket is nonnegative. -/
private theorem pathBracket_nonneg_aux (k : ℕ) (ω : Ω) : 0 ≤ pathBracket μ ℱ M k ω := by
  simp only [pathBracket]
  exact Finset.sum_nonneg fun j _ => le_max_right _ _

/-- The pathwise bracket agrees with the predictable bracket almost surely. -/
private theorem pathBracket_ae_eq_predBracket_aux (k : ℕ) :
    pathBracket μ ℱ M k =ᵐ[μ] CERW.predBracket μ ℱ M M k := by
  filter_upwards [(eventually_all_finset (Finset.range k)).mpr
    (fun j _ => condExp_nonneg (μ := μ) (m := ℱ j)
      (f := fun ω => (M (j + 1) ω - M j ω) ^ 2)
      (Eventually.of_forall fun ω => sq_nonneg _))] with ω hω
  simp only [pow_two] at hω
  simp only [pathBracket, CERW.predBracket, Finset.sum_apply, pow_two]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [max_eq_left (by simpa only [Pi.zero_apply] using hω j hj)]

/-- The pathwise bracket is measurable. -/
private theorem measurable_pathBracket (k : ℕ) : Measurable (pathBracket μ ℱ M k) := by
  unfold pathBracket
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (((stronglyMeasurable_condExp (μ := μ) (m := ℱ j)
    (f := fun ω => (M (j + 1) ω - M j ω) ^ 2)).mono (ℱ.le j)).measurable).max measurable_const

/-- One step of the path bracket. -/
private theorem pathBracket_succ (k : ℕ) (ω : Ω) :
    pathBracket μ ℱ M (k + 1) ω = pathBracket μ ℱ M k ω
      + max (μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω) 0 := by
  simp only [pathBracket, Finset.sum_range_succ]

/-- The predictably stopped martingale is measurable. -/
private theorem measurable_predictableStop (c : ℝ) (hM : ∀ k, Measurable (M k)) (k : ℕ) :
    Measurable (predictableStop M (pathBracket μ ℱ M) c k) := by
  unfold predictableStop
  refine Finset.measurable_sum _ fun j _ => ?_
  refine (Measurable.ite
    (measurableSet_le (measurable_pathBracket μ ℱ M (j + 1)) measurable_const)
    measurable_const measurable_const).mul ((hM (j + 1)).sub (hM j))

end PathBracket


/-- The real exponential is `e^A`-Lipschitz below `A`. -/
private theorem abs_exp_sub_exp_le {x y A : ℝ} (hx : x ≤ A) (hy : y ≤ A) :
    |Real.exp y - Real.exp x| ≤ Real.exp A * |y - x| := by
  have h1 : Real.exp y - Real.exp x ≤ (y - x) * Real.exp y := by
    have h := Real.add_one_le_exp (x - y)
    have hpos := Real.exp_pos y
    have e : Real.exp x = Real.exp (x - y) * Real.exp y := by rw [← Real.exp_add]; ring_nf
    nlinarith
  have h2 : Real.exp x - Real.exp y ≤ (x - y) * Real.exp x := by
    have h := Real.add_one_le_exp (y - x)
    have hpos := Real.exp_pos x
    have e : Real.exp y = Real.exp (y - x) * Real.exp x := by rw [← Real.exp_add]; ring_nf
    nlinarith
  have hxA := Real.exp_le_exp.mpr hx
  have hyA := Real.exp_le_exp.mpr hy
  rw [abs_le]
  constructor
  · rcases le_total y x with h | h
    · rw [abs_of_nonpos (by linarith : y - x ≤ 0)]
      nlinarith [Real.exp_pos A, Real.exp_pos x, Real.exp_pos y]
    · rw [abs_of_nonneg (by linarith : 0 ≤ y - x)]
      nlinarith [Real.exp_pos A, Real.exp_pos x, Real.exp_pos y, Real.exp_le_exp.mpr h]
  · rcases le_total y x with h | h
    · rw [abs_of_nonpos (by linarith : y - x ≤ 0)]
      nlinarith [Real.exp_pos A, Real.exp_pos x, Real.exp_pos y]
    · rw [abs_of_nonneg (by linarith : 0 ≤ y - x)]
      nlinarith [Real.exp_pos A, Real.exp_pos x, Real.exp_pos y]

/-- A pure imaginary exponential has norm one. -/
private theorem norm_cexp_mul_I {t x : ℝ} :
    ‖Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
  rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]

section Main

variable {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}

/-- On the event where the path bracket at time `n` is at most `c`, the sum of the conditional
variances of the truncated increments equals the path bracket. -/
private theorem condVarSum_eq_pathBracket_of_le (c : ℝ) (n : ℕ)
    (hqeq : ∀ k, μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
        - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] =ᵐ[μ]
        fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω *
          μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω) :
    ∀ᵐ ω ∂μ, pathBracket μ ℱ M n ω ≤ c →
      (∑ k ∈ Finset.range n, μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
        - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω)
      = pathBracket μ ℱ M n ω := by
  have hσnn : ∀ᵐ ω ∂μ, ∀ k,
      0 ≤ μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω := by
    rw [ae_all_iff]
    intro k
    exact condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
  have hstep : ∀ᵐ ω ∂μ, ∀ k ∈ Finset.range n,
      μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
        - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω
      = bracketIndicator (pathBracket μ ℱ M) c k ω *
          μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω := by
    rw [eventually_all_finset]
    intro k _
    filter_upwards [hqeq k] with ω hω
    exact hω
  filter_upwards [hstep, hσnn] with ω hstepω hσnnω hVc
  have hmono : Monotone fun k => pathBracket μ ℱ M k ω :=
    monotone_nat_of_le_succ fun k => pathBracket_mono_aux μ ℱ M k ω
  have hVk : ∀ j ∈ Finset.range n, pathBracket μ ℱ M (j + 1) ω ≤ c := fun j hj =>
    le_trans (hmono (Nat.succ_le_of_lt (Finset.mem_range.mp hj))) hVc
  have hsum1 : (∑ k ∈ Finset.range n,
        μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
          - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω)
      = ∑ k ∈ Finset.range n, μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hstepω k hk, bracketIndicator_of_le (hVk k hk), one_mul]
  have hVeq : pathBracket μ ℱ M n ω
      = ∑ k ∈ Finset.range n, μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω := by
    have htel := Finset.sum_range_sub (fun j => pathBracket μ ℱ M j ω) n
    rw [pathBracket_zero_aux μ ℱ M ω, sub_zero] at htel
    rw [← htel]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pathBracket_succ, add_sub_cancel_left, max_eq_left (hσnnω j)]
  rw [hsum1, hVeq]

/-- The difference of the characteristic functions of `M n` and its predictable stop is bounded
by twice the mass of the event where the bracket exceeds `c`. -/
private theorem norm_integral_sub_stopped_le [IsProbabilityMeasure μ]
    (c t : ℝ) (n : ℕ) (hzero : ∀ ω, M 0 ω = 0) (hM : ∀ k, Measurable (M k)) :
    ‖(∫ ω, Complex.exp (t * M n ω * Complex.I) ∂μ)
      - (∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) c n ω
          * Complex.I) ∂μ)‖
      ≤ 2 * μ.real {ω | c < pathBracket μ ℱ M n ω} := by
  have hMA : Measurable (fun ω => Complex.exp (t * M n ω * Complex.I)) :=
    Complex.continuous_exp.measurable.comp
      (((measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hM n))).mul
        measurable_const))
  have hMB : Measurable (fun ω => Complex.exp
      (t * predictableStop M (pathBracket μ ℱ M) c n ω * Complex.I)) :=
    Complex.continuous_exp.measurable.comp
      (((measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (measurable_predictableStop μ ℱ M c hM n))).mul measurable_const))
  have hIntA : Integrable (fun ω => Complex.exp (t * M n ω * Complex.I)) μ :=
    Integrable.of_bound hMA.aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by simp [norm_cexp_mul_I])
  have hIntB : Integrable (fun ω => Complex.exp
      (t * predictableStop M (pathBracket μ ℱ M) c n ω * Complex.I)) μ :=
    Integrable.of_bound hMB.aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by simp [norm_cexp_mul_I])
  rw [← integral_sub hIntA hIntB]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ᵐ ω ∂μ, ‖Complex.exp (t * M n ω * Complex.I)
      - Complex.exp (t * predictableStop M (pathBracket μ ℱ M) c n ω * Complex.I)‖
      ≤ 2 * Set.indicator {ω | c < pathBracket μ ℱ M n ω} (fun _ => (1 : ℝ)) ω := by
    filter_upwards with ω
    by_cases h : pathBracket μ ℱ M n ω ≤ c
    · have heq : predictableStop M (pathBracket μ ℱ M) c n ω = M n ω :=
        predictableStop_eq_of_le hzero
          (fun k ω => pathBracket_mono_aux μ ℱ M k ω) h
      rw [heq, sub_self, norm_zero,
        Set.indicator_of_notMem (by simp [not_lt.mpr h]), mul_zero]
    · have hlt : c < pathBracket μ ℱ M n ω := lt_of_not_ge h
      rw [Set.indicator_of_mem (by exact hlt), mul_one]
      calc ‖Complex.exp (t * M n ω * Complex.I)
            - Complex.exp (t * predictableStop M (pathBracket μ ℱ M) c n ω * Complex.I)‖
          ≤ ‖Complex.exp (t * M n ω * Complex.I)‖
            + ‖Complex.exp (t * predictableStop M (pathBracket μ ℱ M) c n ω
              * Complex.I)‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [norm_cexp_mul_I, norm_cexp_mul_I]
        _ = 2 := by norm_num
  have hIntInd : Integrable (fun ω => 2 * Set.indicator {ω | c < pathBracket μ ℱ M n ω}
      (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator
      (measurableSet_lt measurable_const (measurable_pathBracket μ ℱ M n))).const_mul 2
  refine (integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) hIntInd
    hpt).trans ?_
  rw [integral_const_mul,
    integral_indicator (measurableSet_lt measurable_const (measurable_pathBracket μ ℱ M n)),
    setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  exact le_rfl

/-- The deviation of the compensated exponential from the Gaussian factor is bounded by the
conditional-variance budget, split by the event where the bracket is `η`-close to `v`. -/
private theorem compensator_deviation_integral_le [IsProbabilityMeasure μ]
    (c v t η : ℝ) (hv : 0 ≤ v) (hvc1 : v + 1 ≤ c) (hη : 0 < η) (hη1 : η ≤ 1)
    (n : ℕ)
    (hQle : ∀ᵐ ω ∂μ, (∑ k ∈ Finset.range n,
        μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
          - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω) ≤ c)
    (hQnn : ∀ᵐ ω ∂μ, 0 ≤ (∑ k ∈ Finset.range n,
        μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
          - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω))
    (hQeq : ∀ᵐ ω ∂μ, pathBracket μ ℱ M n ω ≤ c →
        (∑ k ∈ Finset.range n,
          μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
            - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω)
          = pathBracket μ ℱ M n ω) :
    (∫ ω, ‖(Real.exp (t ^ 2 * v / 2) : ℂ)
        * Complex.exp (t * predictableStop M (pathBracket μ ℱ M) c n ω
            * Complex.I)
        - Complex.exp (t * predictableStop M (pathBracket μ ℱ M) c n ω
            * Complex.I
            + (t ^ 2 / 2 * (∑ k ∈ Finset.range n,
                μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
                  - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2
                  | ℱ k] ω) : ℝ))‖ ∂μ)
      ≤ Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) *
          (η + c * μ.real {ω | η < |pathBracket μ ℱ M n ω - v|}) := by
  let Mc : ℕ → Ω → ℝ := predictableStop M (pathBracket μ ℱ M) c
  let Q : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n,
      μ[fun ω => (Mc (k + 1) ω - Mc k ω) ^ 2 | ℱ k] ω
  let B : Set Ω := {ω | η < |pathBracket μ ℱ M n ω - v|}
  let Z : Ω → ℂ := fun ω =>
    (Real.exp (t ^ 2 * v / 2) : ℂ) * Complex.exp (t * Mc n ω * Complex.I)
      - Complex.exp (t * Mc n ω * Complex.I + (t ^ 2 / 2 * Q ω : ℝ))
  change ∫ ω, ‖Z ω‖ ∂μ ≤ Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) * (η + c * μ.real B)
  have hBmeas : MeasurableSet B := by
    change MeasurableSet {ω | η < |pathBracket μ ℱ M n ω - v|}
    exact measurableSet_lt measurable_const
      ((measurable_pathBracket μ ℱ M n).sub measurable_const).abs
  have hvc : v ≤ c := by linarith
  have hQle' : ∀ᵐ ω ∂μ, Q ω ≤ c := hQle
  have hQnn' : ∀ᵐ ω ∂μ, 0 ≤ Q ω := hQnn
  have hQeq' : ∀ᵐ ω ∂μ,
      pathBracket μ ℱ M n ω ≤ c → Q ω = pathBracket μ ℱ M n ω :=
    hQeq
  have hZnorm : ∀ ω, ‖Z ω‖ = |Real.exp (t ^ 2 * v / 2) - Real.exp (t ^ 2 / 2 * Q ω)| := by
    intro ω
    have h : Z ω = Complex.exp (t * Mc n ω * Complex.I) *
        ((Real.exp (t ^ 2 * v / 2) : ℂ) - (Real.exp (t ^ 2 / 2 * Q ω) : ℂ)) := by
      simp only [Z, Complex.ofReal_exp]
      rw [Complex.exp_add]
      ring
    rw [h, Complex.norm_mul, norm_cexp_mul_I, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  have hZbd : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) *
      (Set.indicator Bᶜ (fun _ => η) ω + Set.indicator B (fun _ => c) ω) := by
    filter_upwards [hQle', hQnn', hQeq'] with ω hQleω hQnnω hQeqω
    rw [hZnorm, show t ^ 2 * v / 2 = t ^ 2 / 2 * v by ring]
    have hA : t ^ 2 / 2 * v ≤ t ^ 2 * c / 2 := by nlinarith [sq_nonneg t, hvc]
    have hA' : t ^ 2 / 2 * Q ω ≤ t ^ 2 * c / 2 := by nlinarith [sq_nonneg t, hQleω]
    have hb := abs_exp_sub_exp_le hA' hA
    refine hb.trans ?_
    have hdiff : |t ^ 2 / 2 * v - t ^ 2 / 2 * Q ω| = t ^ 2 / 2 * |v - Q ω| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    rw [hdiff]
    have hQbd : |v - Q ω| ≤ Set.indicator Bᶜ (fun _ => η) ω
        + Set.indicator B (fun _ => c) ω := by
      by_cases hB : ω ∈ B
      · rw [Set.indicator_of_mem hB,
          Set.indicator_of_notMem (by simpa [B] using hB), zero_add]
        rw [abs_le]
        exact ⟨by linarith [hQleω, hQnnω, hv], by linarith [hQleω, hQnnω]⟩
      · rw [Set.indicator_of_notMem hB,
          Set.indicator_of_mem (by simpa [B] using hB), add_zero]
        have hgood : |pathBracket μ ℱ M n ω - v| ≤ η := le_of_not_gt (by simpa [B] using hB)
        have hVc : pathBracket μ ℱ M n ω ≤ c := by
          have := (abs_le.mp hgood).2
          linarith [this, hη1, hvc1]
        rw [hQeqω hVc, abs_sub_comm]
        exact hgood
    calc Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2 * |v - Q ω|)
        = Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) * |v - Q ω| := by ring
      _ ≤ Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2)
            * (Set.indicator Bᶜ (fun _ => η) ω + Set.indicator B (fun _ => c) ω) :=
          mul_le_mul_of_nonneg_left hQbd (by positivity)
  have hRhsInt : Integrable (fun ω => Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) *
      (Set.indicator Bᶜ (fun _ => η) ω + Set.indicator B (fun _ => c) ω)) μ :=
    (((integrable_const η).indicator hBmeas.compl).add
      ((integrable_const c).indicator hBmeas)).const_mul _
  have hstep := integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) hRhsInt hZbd
  refine hstep.trans ?_
  rw [integral_const_mul,
    integral_add ((integrable_const η).indicator hBmeas.compl)
      ((integrable_const c).indicator hBmeas),
    integral_indicator hBmeas.compl, integral_indicator hBmeas, setIntegral_const,
    setIntegral_const]
  simp only [smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcompl : μ.real Bᶜ ≤ 1 := measureReal_le_one
  have hnn : 0 ≤ μ.real B := measureReal_nonneg
  nlinarith [hcompl, hη, hnn]

/-- The characteristic function of the stopped martingale differs from the Gaussian factor by the
`G1` bound plus the compensated deviation. -/
private theorem norm_integral_stopped_sub_gaussian_le [IsProbabilityMeasure μ]
    (hG1 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
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
            4 * (δ * |t| ^ 3 * c + t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ)))
    (c v t δ η : ℝ) (hv : 0 ≤ v) (hvc1 : v + 1 ≤ c) (hδ : 0 ≤ δ)
    (hη : 0 < η) (hη1 : η ≤ 1) (n : ℕ)
    (hMart : Martingale M ℱ μ) (hLp : ∀ k, MemLp (M k) 2 μ) (hzero : ∀ ω, M 0 ω = 0)
    (hM : ∀ k, Measurable (M k))
    (hQle : ∀ᵐ ω ∂μ, (∑ k ∈ Finset.range n,
        μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
          - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω) ≤ c)
    (hQnn : ∀ᵐ ω ∂μ, 0 ≤ (∑ k ∈ Finset.range n,
        μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
          - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω))
    (hQeq : ∀ᵐ ω ∂μ, pathBracket μ ℱ M n ω ≤ c →
        (∑ k ∈ Finset.range n,
          μ[fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
            - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2 | ℱ k] ω)
          = pathBracket μ ℱ M n ω) :
    ‖(∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) c n ω * Complex.I) ∂μ)
      - Complex.exp (-(t ^ 2 * v / 2 : ℝ))‖
      ≤ Real.exp (t ^ 2 * c) *
          (t ^ 4 / 8 * (c * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ))
            + 4 * (δ * |t| ^ 3 * c + t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ))
        + Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) *
            (η + c * μ.real {ω | η < |pathBracket μ ℱ M n ω - v|}) := by
  let Mc : ℕ → Ω → ℝ := predictableStop M (pathBracket μ ℱ M) c
  let Q : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n,
      μ[fun ω => (Mc (k + 1) ω - Mc k ω) ^ 2 | ℱ k] ω
  let Y : Ω → ℂ := fun ω =>
    Complex.exp (t * Mc n ω * Complex.I + (t ^ 2 / 2 * Q ω : ℝ))
  let g0 : ℂ := Complex.exp (-(t ^ 2 * v / 2 : ℝ))
  let Z : Ω → ℂ := fun ω =>
    (Real.exp (t ^ 2 * v / 2) : ℂ) * Complex.exp (t * Mc n ω * Complex.I) - Y ω
  let G1b : ℝ := Real.exp (t ^ 2 * c) *
    (t ^ 4 / 8 * (c * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ))
      + 4 * (δ * |t| ^ 3 * c + t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ))
  change ‖(∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0‖
    ≤ G1b + Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) *
        (η + c * μ.real {ω | η < |pathBracket μ ℱ M n ω - v|})
  have hc : 0 ≤ c := by linarith
  have hG1' : ‖∫ ω, Y ω ∂μ - 1‖ ≤ G1b := by
    simp only [Y, Q, Mc, G1b]
    exact hG1 (Ω := Ω) (m0 := m0) μ ℱ M c hc hMart hLp hzero n t δ hδ
  have hMcmeas : Measurable (Mc n) := measurable_predictableStop μ ℱ M c hM n
  have hQmeas : Measurable Q := by
    simp only [Q, Mc]
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((stronglyMeasurable_condExp (μ := μ) (m := ℱ k)
      (f := fun ω => (predictableStop M (pathBracket μ ℱ M) c (k + 1) ω
        - predictableStop M (pathBracket μ ℱ M) c k ω) ^ 2)).mono (ℱ.le k)).measurable
  have hYmeas : Measurable Y :=
    Complex.continuous_exp.measurable.comp
      (((measurable_const.mul (Complex.continuous_ofReal.measurable.comp hMcmeas)).mul
        measurable_const).add
        (Complex.continuous_ofReal.measurable.comp (measurable_const.mul hQmeas)))
  have hQle' : ∀ᵐ ω ∂μ, Q ω ≤ c := hQle
  have hQnn' : ∀ᵐ ω ∂μ, 0 ≤ Q ω := hQnn
  have hQeq' : ∀ᵐ ω ∂μ,
      pathBracket μ ℱ M n ω ≤ c → Q ω = pathBracket μ ℱ M n ω :=
    hQeq
  have hYint : Integrable Y μ := by
    refine Integrable.of_bound hYmeas.aestronglyMeasurable (Real.exp (t ^ 2 * c / 2)) ?_
    filter_upwards [hQle'] with ω hQleω
    have hre : (t * Mc n ω * Complex.I + (t ^ 2 / 2 * Q ω : ℝ)).re = t ^ 2 / 2 * Q ω := by
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    simp only [Y, Complex.norm_exp, hre]
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hQleω (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
    nlinarith [this]
  have hBint : Integrable (fun ω => Complex.exp (t * Mc n ω * Complex.I)) μ :=
    Integrable.of_bound
      (Complex.continuous_exp.measurable.comp
        ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp hMcmeas)).mul
          measurable_const)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by simp [norm_cexp_mul_I])
  have hZint : Integrable Z μ := by
    refine Integrable.of_bound ?_ (2 * Real.exp (t ^ 2 * c / 2)) ?_
    · exact ((measurable_const.mul (Complex.continuous_exp.measurable.comp
          ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp hMcmeas)).mul
            measurable_const))).sub hYmeas).aestronglyMeasurable
    · filter_upwards [hQle', hQnn'] with ω hQleω hQnnω
      have h : ‖Z ω‖ = |Real.exp (t ^ 2 * v / 2) - Real.exp (t ^ 2 / 2 * Q ω)| := by
        have hfac : Z ω = Complex.exp (t * Mc n ω * Complex.I) *
            ((Real.exp (t ^ 2 * v / 2) : ℂ) - (Real.exp (t ^ 2 / 2 * Q ω) : ℂ)) := by
          simp only [Z, Y, Complex.ofReal_exp]
          rw [Complex.exp_add]
          ring
        rw [hfac, Complex.norm_mul, norm_cexp_mul_I, one_mul, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      rw [h, show t ^ 2 * v / 2 = t ^ 2 / 2 * v by ring]
      have hA : t ^ 2 / 2 * v ≤ t ^ 2 * c / 2 := by nlinarith [hvc1, sq_nonneg t]
      have hA' : t ^ 2 / 2 * Q ω ≤ t ^ 2 * c / 2 := by nlinarith [hQleω, sq_nonneg t]
      rw [abs_le]
      constructor
      · have h1 := Real.exp_le_exp.mpr hA
        have h2 := Real.exp_le_exp.mpr hA'
        have pa := Real.exp_pos (t ^ 2 / 2 * v)
        have pb := Real.exp_pos (t ^ 2 / 2 * Q ω)
        have pA := Real.exp_pos (t ^ 2 * c / 2)
        linarith
      · have h1 := Real.exp_le_exp.mpr hA
        have h2 := Real.exp_le_exp.mpr hA'
        have pa := Real.exp_pos (t ^ 2 / 2 * v)
        have pb := Real.exp_pos (t ^ 2 / 2 * Q ω)
        have pA := Real.exp_pos (t ^ 2 * c / 2)
        linarith
  have hEint : Integrable (fun ω => (Real.exp (t ^ 2 * v / 2) : ℂ)
      * Complex.exp (t * Mc n ω * Complex.I)) μ :=
    hBint.const_mul _
  have hsplit : (Real.exp (t ^ 2 * v / 2) : ℂ)
        * ((∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0)
      = ∫ ω, Z ω ∂μ + (∫ ω, Y ω ∂μ - 1) := by
    have hg : (Real.exp (t ^ 2 * v / 2) : ℂ) * g0 = 1 := by
      simp only [g0, Complex.ofReal_exp]
      rw [← Complex.exp_add]
      simp
    have hZY : (fun ω => Z ω + Y ω) = fun ω => (Real.exp (t ^ 2 * v / 2) : ℂ)
        * Complex.exp (t * Mc n ω * Complex.I) := by
      funext ω
      simp only [Z]
      ring
    have hE : (∫ ω, (Real.exp (t ^ 2 * v / 2) : ℂ)
        * Complex.exp (t * Mc n ω * Complex.I) ∂μ)
        = (Real.exp (t ^ 2 * v / 2) : ℂ)
          * (∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) := by
      rw [integral_const_mul]
    rw [mul_sub, hg, ← hE, ← hZY, integral_add hZint hYint]
    ring
  have hmain : Real.exp (t ^ 2 * v / 2)
        * ‖(∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0‖
      ≤ (∫ ω, ‖Z ω‖ ∂μ) + G1b := by
    have h1 : ‖(Real.exp (t ^ 2 * v / 2) : ℂ)
        * ((∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0)‖
        = Real.exp (t ^ 2 * v / 2)
          * ‖(∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0‖ := by
      rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_pos _).le]
    rw [← h1, hsplit]
    refine (norm_add_le _ _).trans (add_le_add (norm_integral_le_integral_norm _) hG1')
  have hZbd := compensator_deviation_integral_le c v t η hv hvc1 hη hη1 n hQle hQnn hQeq
  have hZc : (∫ ω, ‖Z ω‖ ∂μ)
      ≤ Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) *
          (η + c * μ.real {ω | η < |pathBracket μ ℱ M n ω - v|}) := by
    simp only [Z, Mc] at hZbd ⊢
    exact hZbd
  have hfin : ‖(∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0‖
      ≤ G1b + Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) *
          (η + c * μ.real {ω | η < |pathBracket μ ℱ M n ω - v|}) := by
    have hdiv : ‖(∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0‖
        ≤ ((∫ ω, ‖Z ω‖ ∂μ) + G1b) * Real.exp (-(t ^ 2 * v / 2)) := by
      have hmul : ‖(∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0‖
          * Real.exp (t ^ 2 * v / 2) ≤ (∫ ω, ‖Z ω‖ ∂μ) + G1b := by
        rw [mul_comm]; exact hmain
      have hd := (le_div_iff₀ (Real.exp_pos (t ^ 2 * v / 2))).mpr hmul
      rw [div_eq_mul_inv, ← Real.exp_neg] at hd
      exact hd
    have h1 : Real.exp (-(t ^ 2 * v / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg t, hv]
    have hR : 0 ≤ (∫ ω, ‖Z ω‖ ∂μ) + G1b := by
      have hpos := Real.exp_pos (-(t ^ 2 * v / 2))
      nlinarith [hdiv, norm_nonneg ((∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0),
        hpos]
    calc ‖(∫ ω, Complex.exp (t * Mc n ω * Complex.I) ∂μ) - g0‖
        ≤ ((∫ ω, ‖Z ω‖ ∂μ) + G1b) * Real.exp (-(t ^ 2 * v / 2)) := hdiv
      _ ≤ ((∫ ω, ‖Z ω‖ ∂μ) + G1b) * 1 := mul_le_mul_of_nonneg_left h1 hR
      _ = G1b + (∫ ω, ‖Z ω‖ ∂μ) := by ring
      _ ≤ G1b + Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) *
            (η + c * μ.real {ω | η < |pathBracket μ ℱ M n ω - v|}) :=
          add_le_add le_rfl hZc
  exact hfin

end Main

/-- For a square-integrable martingale started at `0`, the characteristic function of `M_n` is
within an explicit error of that of the centered Gaussian of variance `v`, in terms of the
probability that the bracket deviates from `v` by more than `η` and the Lindeberg quantity
`E[min (lind, v + 1)]`. -/
theorem charFun_martingale_bound
    (hG1 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
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
            4 * (δ * |t| ^ 3 * c + t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) c ∂μ)))
    (hF2 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c : ℝ), 0 ≤ c →
      Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → ∀ k,
      μ[fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω) | ℱ k]
          =ᵐ[μ] 0 ∧
      μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2 | ℱ k]
          =ᵐ[μ] fun ω => bracketIndicator (pathBracket μ ℱ M) c k ω *
            μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω)
    (hF3 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c : ℝ), 0 ≤ c →
      Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → (∀ ω, M 0 ω = 0) →
      ∀ (n : ℕ) (δ : ℝ),
      (∀ᵐ ω ∂μ, ∑ k ∈ Finset.range n,
          μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2
            | ℱ k] ω ≤ c) ∧
      ∀ k, μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)) ^ 2 *
            (if δ < |bracketIndicator (pathBracket μ ℱ M) c k ω * (M (k + 1) ω - M k ω)|
              then 1 else 0) | ℱ k]
          ≤ᵐ[μ] μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 *
            (if δ < |M (k + 1) ω - M k ω| then 1 else 0) | ℱ k]) :
    ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ),
      Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → (∀ ω, M 0 ω = 0) →
      ∀ v : ℝ, 0 ≤ v → ∀ (n : ℕ) (t δ η : ℝ), 0 < δ → 0 < η → η ≤ 1 →
      ‖∫ ω, Complex.exp (t * M n ω * Complex.I) ∂μ - Complex.exp (-(t ^ 2 * v / 2 : ℝ))‖ ≤
        2 * μ.real {ω | η < |CERW.predBracket μ ℱ M M n ω - v|} +
        Real.exp (t ^ 2 * (v + 1)) *
          (t ^ 4 / 8 * ((v + 1) * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
            4 * (δ * |t| ^ 3 * (v + 1) + t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
        Real.exp (t ^ 2 * (v + 1) / 2) *
          (t ^ 2 / 2 * (η + (v + 1) * μ.real {ω | η < |CERW.predBracket μ ℱ M M n ω - v|})) := by
  intro Ω m0 μ hprob ℱ M hMart hLp hzero v hv n t δ η hδ hη hη1
  have hc : 0 ≤ v + 1 := by positivity
  have hvc1 : v + 1 ≤ v + 1 := le_rfl
  have hM : ∀ k, Measurable (M k) :=
    fun k => ((hMart.stronglyMeasurable k).mono (ℱ.le k)).measurable
  set p : ℝ := μ.real {ω | η < |CERW.predBracket μ ℱ M M n ω - v|} with hpdef
  have hqeq : ∀ k, μ[fun ω => (predictableStop M (pathBracket μ ℱ M) (v + 1) (k + 1) ω
      - predictableStop M (pathBracket μ ℱ M) (v + 1) k ω) ^ 2 | ℱ k] =ᵐ[μ]
      fun ω => bracketIndicator (pathBracket μ ℱ M) (v + 1) k ω *
        μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ω := by
    intro k
    have h1 : μ[fun ω => (predictableStop M (pathBracket μ ℱ M) (v + 1) (k + 1) ω
        - predictableStop M (pathBracket μ ℱ M) (v + 1) k ω) ^ 2 | ℱ k] =ᵐ[μ]
        μ[fun ω => (bracketIndicator (pathBracket μ ℱ M) (v + 1) k ω
          * (M (k + 1) ω - M k ω)) ^ 2 | ℱ k] :=
      condExp_congr_ae (Eventually.of_forall fun ω => by
        beta_reduce
        rw [predictableStop_succ_sub])
    exact h1.trans (by simpa only [] using (hF2 μ ℱ M (v + 1) hc hMart hLp k).2)
  have hQle : ∀ᵐ ω ∂μ, (∑ k ∈ Finset.range n,
      μ[fun ω => (predictableStop M (pathBracket μ ℱ M) (v + 1) (k + 1) ω
        - predictableStop M (pathBracket μ ℱ M) (v + 1) k ω) ^ 2 | ℱ k] ω) ≤ v + 1 := by
    have h := (hF3 μ ℱ M (v + 1) hc hMart hLp hzero n δ).1
    simpa only [predictableStop_succ_sub] using h
  have hQnn : ∀ᵐ ω ∂μ, 0 ≤ (∑ k ∈ Finset.range n,
      μ[fun ω => (predictableStop M (pathBracket μ ℱ M) (v + 1) (k + 1) ω
        - predictableStop M (pathBracket μ ℱ M) (v + 1) k ω) ^ 2 | ℱ k] ω) := by
    filter_upwards [(Filter.eventually_all_finset (Finset.range n)).mpr
      (fun k _ => condExp_nonneg (μ := μ) (m := ℱ k)
        (f := fun ω => (predictableStop M (pathBracket μ ℱ M) (v + 1) (k + 1) ω
          - predictableStop M (pathBracket μ ℱ M) (v + 1) k ω) ^ 2)
        (Eventually.of_forall fun ω => sq_nonneg _))] with ω hω
    exact Finset.sum_nonneg fun k hk => hω k hk
  have hQeq := condVarSum_eq_pathBracket_of_le (μ := μ) (ℱ := ℱ) (M := M) (v + 1) n hqeq
  have hAB := norm_integral_sub_stopped_le (μ := μ) (ℱ := ℱ) (M := M) (v + 1) t n hzero hM
  have hpconv : μ.real {ω | η < |pathBracket μ ℱ M n ω - v|}
      = p := by
    rw [hpdef]
    refine measureReal_congr ?_
    filter_upwards [pathBracket_ae_eq_predBracket_aux μ ℱ M n] with ω hω
    exact congrArg (fun z => η < |z - v|) hω
  have hsub : {ω | v + 1 < pathBracket μ ℱ M n ω}
      ⊆ {ω | η < |pathBracket μ ℱ M n ω - v|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h1 : |pathBracket μ ℱ M n ω - v| = pathBracket μ ℱ M n ω - v :=
      abs_of_pos (by linarith)
    rw [h1]
    linarith [hη1]
  have hAB' : ‖(∫ ω, Complex.exp (t * M n ω * Complex.I) ∂μ)
      - (∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) (v + 1) n ω
          * Complex.I) ∂μ)‖ ≤ 2 * p := by
    refine hAB.trans ?_
    rw [← hpconv]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine measureReal_mono hsub
  have hBd := norm_integral_stopped_sub_gaussian_le
    (μ := μ) (ℱ := ℱ) (M := M) hG1 (v + 1) v t δ η hv hvc1 hδ.le hη hη1 n
      hMart hLp hzero hM hQle hQnn hQeq
  have hBd' : ‖(∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) (v + 1) n ω
        * Complex.I) ∂μ) - Complex.exp (-(t ^ 2 * v / 2 : ℝ))‖
      ≤ Real.exp (t ^ 2 * (v + 1)) *
          (t ^ 4 / 8 * ((v + 1) * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
            4 * (δ * |t| ^ 3 * (v + 1) + t ^ 2 *
              ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ))
        + Real.exp (t ^ 2 * (v + 1) / 2) * (t ^ 2 / 2) * (η + (v + 1) * p) := by
    simpa only [hpconv] using hBd
  calc ‖∫ ω, Complex.exp (t * M n ω * Complex.I) ∂μ
          - Complex.exp (-(t ^ 2 * v / 2 : ℝ))‖
      ≤ ‖(∫ ω, Complex.exp (t * M n ω * Complex.I) ∂μ)
          - (∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) (v + 1) n ω
              * Complex.I) ∂μ)‖
        + ‖(∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) (v + 1) n ω
              * Complex.I) ∂μ) - Complex.exp (-(t ^ 2 * v / 2 : ℝ))‖ := by
          have h := norm_add_le
            ((∫ ω, Complex.exp (t * M n ω * Complex.I) ∂μ)
              - (∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) (v + 1) n ω
                  * Complex.I) ∂μ))
            ((∫ ω, Complex.exp (t * predictableStop M (pathBracket μ ℱ M) (v + 1) n ω
                * Complex.I) ∂μ) - Complex.exp (-(t ^ 2 * v / 2 : ℝ)))
          rwa [sub_add_sub_cancel] at h
    _ ≤ 2 * p + (Real.exp (t ^ 2 * (v + 1)) *
          (t ^ 4 / 8 * ((v + 1) * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
            4 * (δ * |t| ^ 3 * (v + 1) + t ^ 2 *
              ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ))
        + Real.exp (t ^ 2 * (v + 1) / 2) * (t ^ 2 / 2) * (η + (v + 1) * p)) :=
          add_le_add hAB' hBd'
    _ = 2 * p + Real.exp (t ^ 2 * (v + 1)) *
          (t ^ 4 / 8 * ((v + 1) * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
            4 * (δ * |t| ^ 3 * (v + 1) + t ^ 2 *
              ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ))
        + Real.exp (t ^ 2 * (v + 1) / 2) * (t ^ 2 / 2 * (η + (v + 1) * p)) := by ring
    _ = 2 * μ.real {ω | η < |CERW.predBracket μ ℱ M M n ω - v|} +
          Real.exp (t ^ 2 * (v + 1)) *
            (t ^ 4 / 8 * ((v + 1) * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
              4 * (δ * |t| ^ 3 * (v + 1) + t ^ 2 *
                ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
          Real.exp (t ^ 2 * (v + 1) / 2) *
            (t ^ 2 / 2 * (η + (v + 1) * μ.real {ω | η < |CERW.predBracket μ ℱ M M n ω - v|})) := by
          rw [hpdef]

end CERW.Generic.Martingale.CLT
