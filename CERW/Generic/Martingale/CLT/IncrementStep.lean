import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set
import CERW.Generic.Martingale.CLT.Interfaces

/-!
# The increment step bound for the martingale central limit theorem

For a square-integrable real `X` with `E[X | m] = 0` and `E[X² | m] ≤ c`, a bounded
`m`-measurable complex weight `W`, and reals `t`, `δ ≥ 0`, the expectation of
`W (e^{itX} e^{t² E[X²|m]/2} - 1)` is bounded by the second moment of the conditional
variance and a Lindeberg truncation at level `δ`.
-/

universe u

namespace CERW.Generic.Martingale.CLT

open MeasureTheory Filter

open scoped Topology

/-! ### Elementary exponential bounds -/

/-- For `|y| ≤ 1`, the Taylor remainder of `exp (i y)` at order two is at most `4 |y|³`. -/
private lemma norm_cexp_I_sub_taylor_le_of_abs_le_one {y : ℝ} (hy : |y| ≤ 1) :
    ‖Complex.exp (y * Complex.I) - (1 + y * Complex.I - (y : ℂ) ^ 2 / 2)‖ ≤
      4 * min (|y| ^ 3) (y ^ 2) := by
  have hx : ‖(y : ℂ) * Complex.I‖ ≤ 1 := by simpa using hy
  have hb := Complex.exp_bound hx (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, ((y : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = 1 + y * Complex.I - (y : ℂ) ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [hsum] at hb
  have hnorm : ‖(y : ℂ) * Complex.I‖ = |y| := by simp
  rw [hnorm] at hb
  have hmin : min (|y| ^ 3) (y ^ 2) = |y| ^ 3 := by
    refine min_eq_left ?_
    rw [← sq_abs y]
    have h2 : 0 ≤ |y| ^ 2 := sq_nonneg _
    calc |y| ^ 3 = |y| ^ 2 * |y| := by ring
      _ ≤ |y| ^ 2 * 1 := mul_le_mul_of_nonneg_left hy h2
      _ = |y| ^ 2 := mul_one _
  rw [hmin]
  refine hb.trans ?_
  have h3 : 0 ≤ |y| ^ 3 := pow_nonneg (abs_nonneg y) 3
  norm_num [Nat.factorial]
  linarith

/-- For `1 < |y|`, the Taylor remainder of `exp (i y)` at order two is at most `4 y²`. -/
private lemma norm_cexp_I_sub_taylor_le_of_one_lt_abs {y : ℝ} (hy : 1 < |y|) :
    ‖Complex.exp (y * Complex.I) - (1 + y * Complex.I - (y : ℂ) ^ 2 / 2)‖ ≤
      4 * min (|y| ^ 3) (y ^ 2) := by
  have hmin : min (|y| ^ 3) (y ^ 2) = y ^ 2 := by
    refine min_eq_right ?_
    rw [← sq_abs y]
    have h2 : 0 ≤ |y| ^ 2 := sq_nonneg _
    calc |y| ^ 2 = |y| ^ 2 * 1 := (mul_one _).symm
      _ ≤ |y| ^ 2 * |y| := mul_le_mul_of_nonneg_left hy.le h2
      _ = |y| ^ 3 := by ring
  rw [hmin]
  have h1 : ‖Complex.exp (y * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I y
  have h2 : ‖(1 : ℂ) + y * Complex.I - (y : ℂ) ^ 2 / 2‖ ≤ 1 + |y| + y ^ 2 / 2 := by
    calc ‖(1 : ℂ) + y * Complex.I - (y : ℂ) ^ 2 / 2‖
        ≤ ‖(1 : ℂ) + y * Complex.I‖ + ‖(y : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖(y : ℂ) * Complex.I‖) + ‖(y : ℂ) ^ 2 / 2‖ := by
          gcongr
          exact norm_add_le _ _
      _ = 1 + |y| + y ^ 2 / 2 := by
          rw [norm_div, norm_mul, norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
            norm_one, mul_one, sq_abs]
          norm_num
  have h3 : ‖Complex.exp (y * Complex.I) - (1 + y * Complex.I - (y : ℂ) ^ 2 / 2)‖
      ≤ 1 + (1 + |y| + y ^ 2 / 2) := by
    calc ‖Complex.exp (y * Complex.I) - (1 + y * Complex.I - (y : ℂ) ^ 2 / 2)‖
        ≤ ‖Complex.exp (y * Complex.I)‖ +
            ‖(1 : ℂ) + y * Complex.I - (y : ℂ) ^ 2 / 2‖ :=
          norm_sub_le _ _
      _ ≤ 1 + (1 + |y| + y ^ 2 / 2) := by rw [h1]; gcongr
  have hsq : |y| ≤ y ^ 2 := by
    rw [← sq_abs y]
    calc |y| = |y| * 1 := (mul_one _).symm
      _ ≤ |y| * |y| := mul_le_mul_of_nonneg_left hy.le (abs_nonneg y)
      _ = |y| ^ 2 := (sq _).symm
  have hone : 1 ≤ y ^ 2 := le_trans hy.le hsq
  linarith

/-- The third-order Taylor remainder of `exp (i y)` is at most `4 min (|y|³, y²)` for all real
`y`. -/
private lemma norm_cexp_I_sub_taylor_le (y : ℝ) :
    ‖Complex.exp (y * Complex.I) - (1 + y * Complex.I - (y : ℂ) ^ 2 / 2)‖ ≤
      4 * min (|y| ^ 3) (y ^ 2) := by
  rcases le_or_gt |y| 1 with hy | hy
  · exact norm_cexp_I_sub_taylor_le_of_abs_le_one hy
  · exact norm_cexp_I_sub_taylor_le_of_one_lt_abs hy

/-- For `a ≥ 0`, `|e^a (1 - a) - 1| ≤ (a² / 2) e^a`. -/
private lemma abs_exp_mul_one_sub_sub_one_le (a : ℝ) (ha : 0 ≤ a) :
    |Real.exp a * (1 - a) - 1| ≤ a ^ 2 / 2 * Real.exp a := by
  have hup : Real.exp a * (1 - a) - 1 ≤ 0 := by
    have h := Real.one_sub_le_exp_neg a
    have hpos := Real.exp_pos a
    have hexp : Real.exp a * Real.exp (-a) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp a * (1 - a) - 1 ≤ Real.exp a * Real.exp (-a) - 1 := by gcongr
      _ = 0 := by rw [hexp]; ring
  have hq : 0 < 1 - a + a ^ 2 / 2 := by nlinarith [sq_nonneg (a - 1)]
  have hlow : 1 ≤ Real.exp a * (1 - a + a ^ 2 / 2) := by
    have hcube : 1 + a + a ^ 2 / 2 + a ^ 3 / 6 ≤ Real.exp a := by
      have h := Real.sum_le_exp_of_nonneg ha 4
      simpa [Finset.sum_range_succ, Nat.factorial] using h
    have hP : 1 ≤ (1 + a + a ^ 2 / 2 + a ^ 3 / 6) * (1 - a + a ^ 2 / 2) := by
      have e : (1 + a + a ^ 2 / 2 + a ^ 3 / 6) * (1 - a + a ^ 2 / 2)
          = 1 + a ^ 3 / 6 + a ^ 4 / 12 + a ^ 5 / 12 := by ring
      rw [e]
      have h3 : 0 ≤ a ^ 3 := pow_nonneg ha 3
      have h4 : 0 ≤ a ^ 4 := pow_nonneg ha 4
      have h5 : 0 ≤ a ^ 5 := pow_nonneg ha 5
      linarith
    exact hP.trans (mul_le_mul_of_nonneg_right hcube hq.le)
  rw [abs_of_nonpos hup]
  linarith

/-! ### Norm identities for the complex expressions -/

/-- `‖e^a (1 - a) - 1‖` is the absolute value of the corresponding real quantity. -/
private lemma norm_cexp_mul_one_sub_sub_one (a : ℝ) :
    ‖Complex.exp (a : ℂ) * (1 - (a : ℂ)) - 1‖ = |Real.exp a * (1 - a) - 1| := by
  rw [show Complex.exp (a : ℂ) * (1 - (a : ℂ)) - 1
      = ((Real.exp a * (1 - a) - 1 : ℝ) : ℂ) by
        rw [← Complex.ofReal_exp]; push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `‖z (i x)‖ = ‖z‖ |x|` for a real `x`. -/
private lemma norm_mul_I_ofReal (z : ℂ) (x : ℝ) :
    ‖z * (Complex.I * (x : ℂ))‖ = ‖z‖ * |x| := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- `‖a - y²/2‖ = |a - y²/2|` for real `a`, `y`. -/
private lemma norm_sub_sq_div_two (a y : ℝ) :
    ‖(a : ℂ) - (y : ℂ) ^ 2 / 2‖ = |a - y ^ 2 / 2| := by
  rw [show (a : ℂ) - (y : ℂ) ^ 2 / 2 = ((a - y ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `‖y²/2‖ = y²/2` for a real `y`. -/
private lemma norm_sq_div_two (y : ℝ) : ‖(y : ℂ) ^ 2 / 2‖ = y ^ 2 / 2 := by
  rw [show (y : ℂ) ^ 2 / 2 = ((y ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-! ### Pull-out of a complex weight -/

section PullOut

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} {f : Ω → ℝ} {W : Ω → ℂ} {K : ℝ}

/-- The integral of a bounded `m`-measurable complex weight times a real integrable function
equals the integral of the weight times the conditional expectation of the function given `m`. -/
private lemma integral_mul_ofReal_eq_integral_mul_condExp (hm : m ≤ m0) (hf : Integrable f μ)
    (hW : StronglyMeasurable[m] W) (hK : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ K) :
    ∫ ω, W ω * (f ω : ℂ) ∂μ = ∫ ω, W ω * (μ[f | m] ω : ℂ) ∂μ := by
  let B : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip
  have hB : ∀ (w : ℂ) (x : ℝ), B w x = w * (x : ℂ) := by
    intro w x
    simp [B, mul_comm]
  have h1 := condExp_stronglyMeasurable_bilin_of_bound (m := m) (mΩ := m0) (μ := μ)
    B hm hW hf K hK
  calc ∫ ω, W ω * (f ω : ℂ) ∂μ = ∫ ω, B (W ω) (f ω) ∂μ := by simp_rw [hB]
    _ = ∫ ω, (μ[fun ω => B (W ω) (f ω) | m]) ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, B (W ω) (μ[f | m] ω) ∂μ := integral_congr_ae h1
    _ = ∫ ω, W ω * (μ[f | m] ω : ℂ) ∂μ := by simp_rw [hB]

end PullOut

/-! ### Pointwise inequalities -/

/-- The Lindeberg truncation dominates the cubic-quadratic minimum:
`min (|t x|³, (t x)²) ≤ δ |t|³ x² + t² x² 1{δ < |x|}` for `δ ≥ 0`. -/
private lemma min_cube_sq_le (t δ x : ℝ) (hδ : 0 ≤ δ) :
    min (|t * x| ^ 3) ((t * x) ^ 2) ≤
      δ * |t| ^ 3 * x ^ 2 + t ^ 2 * x ^ 2 * (if δ < |x| then 1 else 0) := by
  rcases le_or_gt |x| δ with hx | hx
  · have hx3 : |x| ^ 3 ≤ δ * x ^ 2 := by
      have h3 : |x| ^ 3 = x ^ 2 * |x| := by rw [← sq_abs x]; ring
      rw [h3]
      calc x ^ 2 * |x| ≤ x ^ 2 * δ := mul_le_mul_of_nonneg_left hx (sq_nonneg x)
        _ = δ * x ^ 2 := by ring
    have ht3 : 0 ≤ |t| ^ 3 := pow_nonneg (abs_nonneg t) 3
    have hleft : |t * x| ^ 3 ≤ δ * |t| ^ 3 * x ^ 2 := by
      rw [abs_mul]
      calc (|t| * |x|) ^ 3 = |t| ^ 3 * |x| ^ 3 := by ring
        _ ≤ |t| ^ 3 * (δ * x ^ 2) := mul_le_mul_of_nonneg_left hx3 ht3
        _ = δ * |t| ^ 3 * x ^ 2 := by ring
    calc min (|t * x| ^ 3) ((t * x) ^ 2) ≤ |t * x| ^ 3 := min_le_left _ _
      _ ≤ δ * |t| ^ 3 * x ^ 2 := hleft
      _ ≤ δ * |t| ^ 3 * x ^ 2 + t ^ 2 * x ^ 2 * (if δ < |x| then 1 else 0) := by
          have : 0 ≤ t ^ 2 * x ^ 2 * (if δ < |x| then 1 else 0) := by positivity
          linarith
  · rw [if_pos hx, mul_one]
    have htx : (t * x) ^ 2 = t ^ 2 * x ^ 2 := by ring
    calc min (|t * x| ^ 3) ((t * x) ^ 2) ≤ (t * x) ^ 2 := min_le_right _ _
      _ = t ^ 2 * x ^ 2 := htx
      _ ≤ δ * |t| ^ 3 * x ^ 2 + t ^ 2 * x ^ 2 := by
          have h1 : 0 ≤ δ * |t| ^ 3 * x ^ 2 := by positivity
          linarith

/-- The exponential compensator identity: the increment `e^{i y} e^a - 1` splits into the
compensated `e^a (1 - a) - 1`, the two conditional-expectation terms `i y e^a` and
`(a - y²/2) e^a`, and the Taylor remainder. -/
private lemma mul_cexp_sub_one_decomp (W : ℂ) (y a : ℝ) :
    W * (Complex.exp (y * Complex.I) * Complex.exp (a : ℂ) - 1)
      = W * (Complex.exp (a : ℂ) * (1 - (a : ℂ)) - 1)
        + (W * Complex.exp (a : ℂ)) * (Complex.I * (y : ℂ))
        + (W * Complex.exp (a : ℂ)) * ((a : ℂ) - (y : ℂ) ^ 2 / 2)
        + (W * Complex.exp (a : ℂ)) *
            (Complex.exp (y * Complex.I) - (1 + (y : ℂ) * Complex.I - (y : ℂ) ^ 2 / 2)) := by
  ring

/-- The increment step bound for the martingale central limit theorem: for a square-integrable
real `X` with `E[X | m] = 0` and `E[X² | m] ≤ c`, a bounded `m`-measurable complex weight `W`,
and `t`, `δ ≥ 0`, the expectation of `W (e^{itX} e^{t² E[X²|m]/2} - 1)` is at most
the second moment of the conditional variance and a Lindeberg truncation at level `δ`. -/
theorem cexp_increment_step_bound :
    ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {m : MeasurableSpace Ω} (X : Ω → ℝ) (W : Ω → ℂ) (K c : ℝ),
      m ≤ m0 → MemLp X 2 μ → μ[X | m] =ᵐ[μ] 0 → StronglyMeasurable[m] W →
      (∀ᵐ ω ∂μ, ‖W ω‖ ≤ K) → (∀ᵐ ω ∂μ, μ[fun ω => X ω ^ 2 | m] ω ≤ c) →
      ∀ t δ : ℝ, 0 ≤ δ →
      ‖∫ ω, W ω * (Complex.exp (t * X ω * Complex.I) *
          Complex.exp ((t ^ 2 * μ[fun ω => X ω ^ 2 | m] ω / 2 : ℝ)) - 1) ∂μ‖ ≤
        K * Real.exp (t ^ 2 * c / 2) * (t ^ 4 / 8 * ∫ ω, μ[fun ω => X ω ^ 2 | m] ω ^ 2 ∂μ +
          4 * (δ * |t| ^ 3 * ∫ ω, X ω ^ 2 ∂μ +
            t ^ 2 * ∫ ω, X ω ^ 2 * (if δ < |X ω| then 1 else 0) ∂μ)) := by
  intro Ω m0 μ _ m X W K c hm hXmem hX0 hW hWK hqle t δ hδ
  have hK : 0 ≤ K := by
    obtain ⟨ω, hω⟩ := hWK.exists
    exact (norm_nonneg _).trans hω
  have hX2_int : Integrable (fun ω => X ω ^ 2) μ := hXmem.integrable_sq
  have hX_int : Integrable X μ := hXmem.integrable (by norm_num)
  set q : Ω → ℝ := fun ω => μ[fun ω => X ω ^ 2 | m] ω with hq
  set a : Ω → ℝ := fun ω => t ^ 2 * q ω / 2 with ha
  set y : Ω → ℝ := fun ω => t * X ω with hy
  set W' : Ω → ℂ := fun ω => W ω * Complex.exp (a ω) with hW'
  set r : Ω → ℂ := fun ω => Complex.exp (y ω * Complex.I) -
      (1 + (y ω : ℂ) * Complex.I - (y ω : ℂ) ^ 2 / 2) with hr
  have hq_nonneg : ∀ᵐ ω ∂μ, 0 ≤ q ω := by
    rw [hq]
    exact condExp_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
  have hq_le : ∀ᵐ ω ∂μ, q ω ≤ c := by
    rw [hq]; exact hqle
  have hc : 0 ≤ c := by
    obtain ⟨ω, h1, h2⟩ := (hq_nonneg.and hq_le).exists
    exact h1.trans h2
  have hq_sm : StronglyMeasurable[m] q := by
    rw [hq]; exact stronglyMeasurable_condExp
  have ha_sm : StronglyMeasurable[m] a := by
    rw [ha]; fun_prop
  have hW'_sm : StronglyMeasurable[m] W' := by
    rw [hW']; fun_prop
  have ha_nonneg : ∀ᵐ ω ∂μ, 0 ≤ a ω := by
    filter_upwards [hq_nonneg] with ω h
    rw [ha]; positivity
  have ha_le : ∀ᵐ ω ∂μ, a ω ≤ t ^ 2 * c / 2 := by
    filter_upwards [hq_le] with ω h
    rw [ha]; nlinarith [sq_nonneg t]
  have h_exp_le : ∀ᵐ ω ∂μ, Real.exp (a ω) ≤ Real.exp (t ^ 2 * c / 2) :=
    ha_le.mono fun _ h => Real.exp_le_exp.mpr h
  have h_norm_exp : ∀ ω, ‖Complex.exp (a ω)‖ = Real.exp (a ω) := by
    intro ω
    rw [← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hK' : 0 ≤ K * Real.exp (t ^ 2 * c / 2) := by positivity
  have hW'_bound : ∀ᵐ ω ∂μ, ‖W' ω‖ ≤ K * Real.exp (t ^ 2 * c / 2) := by
    filter_upwards [hWK, h_exp_le] with ω hWω hE
    rw [hW', norm_mul, h_norm_exp]
    exact mul_le_mul hWω hE (Real.exp_pos _).le hK
  -- Abbreviations for the four pieces of the decomposition.
  set f1 : Ω → ℂ := fun ω => W ω * (Complex.exp (a ω) * (1 - (a ω : ℂ)) - 1) with hf1
  set f2 : Ω → ℂ := fun ω => W' ω * (Complex.I * (y ω : ℂ)) with hf2
  set f3 : Ω → ℂ := fun ω => W' ω * ((a ω : ℂ) - (y ω : ℂ) ^ 2 / 2) with hf3
  set f4 : Ω → ℂ := fun ω => W' ω * r ω with hf4
  have hf1_sm : StronglyMeasurable[m] f1 := by rw [hf1]; fun_prop
  have ha_aes : AEStronglyMeasurable[m0] a μ := (ha_sm.mono hm).aestronglyMeasurable
  have hW'_aes : AEStronglyMeasurable[m0] W' μ := (hW'_sm.mono hm).aestronglyMeasurable
  have haC_aes : AEStronglyMeasurable[m0] (fun ω => (a ω : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable ha_aes
  have hy_aes : AEStronglyMeasurable[m0] y μ := by
    rw [hy]; exact hXmem.aestronglyMeasurable.const_mul t
  have hyC_aes : AEStronglyMeasurable[m0] (fun ω => (y ω : ℂ)) μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hy_aes
  have hyI_aes : AEStronglyMeasurable[m0] (fun ω => (y ω : ℂ) * Complex.I) μ :=
    hyC_aes.mul_const _
  have hy2_aes : AEStronglyMeasurable[m0] (fun ω => (y ω : ℂ) ^ 2 / 2) μ := by
    have h := (hyC_aes.pow 2).const_mul ((1 / 2 : ℂ))
    convert h using 1
    funext ω
    simp only [Pi.pow_apply]
    ring
  have hr_aes : AEStronglyMeasurable[m0] r μ := by
    rw [hr]
    exact (Complex.continuous_exp.comp_aestronglyMeasurable hyI_aes).sub
      ((aestronglyMeasurable_const.add hyI_aes).sub hy2_aes)
  have hf2_aes : AEStronglyMeasurable[m0] f2 μ := by
    rw [hf2]; exact hW'_aes.mul (hyC_aes.const_mul Complex.I)
  have hf3_aes : AEStronglyMeasurable[m0] f3 μ := by
    rw [hf3]; exact hW'_aes.mul (haC_aes.sub hy2_aes)
  have hf4_aes : AEStronglyMeasurable[m0] f4 μ := by
    rw [hf4]; exact hW'_aes.mul hr_aes
  -- Integrability of the four pieces.
  have hf1_int : Integrable f1 μ := by
    refine Integrable.of_bound (hf1_sm.mono hm).aestronglyMeasurable
      (K * Real.exp (t ^ 2 * c / 2) * ((t ^ 2 * c / 2) ^ 2 / 2)) ?_
    filter_upwards [hWK, ha_nonneg, ha_le, h_exp_le] with ω hWω ha0 ha1 hE
    rw [hf1, norm_mul, norm_cexp_mul_one_sub_sub_one]
    have hE2 := abs_exp_mul_one_sub_sub_one_le (a ω) ha0
    have hb : |Real.exp (a ω) * (1 - a ω) - 1| ≤ (a ω) ^ 2 / 2 * Real.exp (t ^ 2 * c / 2) :=
      hE2.trans (mul_le_mul_of_nonneg_left hE (by positivity))
    have h3 : (a ω) ^ 2 / 2 ≤ (t ^ 2 * c / 2) ^ 2 / 2 := by
      have h0 : 0 ≤ t ^ 2 * c / 2 := le_trans ha0 ha1
      nlinarith
    calc ‖W ω‖ * |Real.exp (a ω) * (1 - a ω) - 1|
        ≤ K * ((a ω) ^ 2 / 2 * Real.exp (t ^ 2 * c / 2)) :=
          mul_le_mul hWω hb (abs_nonneg _) hK
      _ ≤ K * (((t ^ 2 * c / 2) ^ 2 / 2) * Real.exp (t ^ 2 * c / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le) hK
      _ = K * Real.exp (t ^ 2 * c / 2) * ((t ^ 2 * c / 2) ^ 2 / 2) := by ring
  have hf2_int : Integrable f2 μ := by
    have hg : Integrable (fun ω => K * Real.exp (t ^ 2 * c / 2) * |t| * ‖X ω‖) μ :=
      (hX_int.norm.const_mul (K * Real.exp (t ^ 2 * c / 2) * |t|))
    refine Integrable.mono' hg hf2_aes ?_
    filter_upwards [hW'_bound] with ω hWω
    rw [hf2, norm_mul_I_ofReal, hy, abs_mul, Real.norm_eq_abs]
    calc ‖W' ω‖ * (|t| * |X ω|) ≤ (K * Real.exp (t ^ 2 * c / 2)) * (|t| * |X ω|) :=
          mul_le_mul_of_nonneg_right hWω (by positivity)
      _ = K * Real.exp (t ^ 2 * c / 2) * |t| * |X ω| := by ring
  have hf3_int : Integrable f3 μ := by
    have hg : Integrable (fun ω => K * Real.exp (t ^ 2 * c / 2) *
        (t ^ 2 * c / 2 + t ^ 2 / 2 * X ω ^ 2)) μ :=
      ((integrable_const _).add (hX2_int.const_mul (t ^ 2 / 2))).const_mul _
    refine Integrable.mono' hg hf3_aes ?_
    filter_upwards [hW'_bound, ha_nonneg, ha_le] with ω hWω ha0 ha1
    rw [hf3, norm_mul, norm_sub_sq_div_two]
    have hsum : |a ω - y ω ^ 2 / 2| ≤ t ^ 2 * c / 2 + t ^ 2 / 2 * X ω ^ 2 := by
      have h1 := abs_sub (a ω) (y ω ^ 2 / 2)
      have h2 : |a ω| ≤ t ^ 2 * c / 2 := abs_le.mpr ⟨by linarith, ha1⟩
      have h3 : |y ω ^ 2 / 2| = t ^ 2 / 2 * X ω ^ 2 := by
        rw [hy]; rw [abs_of_nonneg (by positivity)]; ring
      linarith
    calc ‖W' ω‖ * |a ω - y ω ^ 2 / 2|
        ≤ (K * Real.exp (t ^ 2 * c / 2)) * (t ^ 2 * c / 2 + t ^ 2 / 2 * X ω ^ 2) :=
          mul_le_mul hWω hsum (abs_nonneg _) hK'
      _ = K * Real.exp (t ^ 2 * c / 2) * (t ^ 2 * c / 2 + t ^ 2 / 2 * X ω ^ 2) := by ring
  have hX_aem : AEMeasurable X μ := hXmem.aestronglyMeasurable.aemeasurable
  have hS := hX_aem.nullMeasurableSet_preimage (s := {x : ℝ | δ < |x|})
    (measurableSet_lt measurable_const continuous_abs.measurable)
  have h_ind : Integrable (fun ω => X ω ^ 2 * (if δ < |X ω| then 1 else 0)) μ := by
    have h := hX2_int.indicator₀ hS
    have hcongr : (X ⁻¹' {x : ℝ | δ < |x|}).indicator (fun ω => X ω ^ 2)
        = fun ω => X ω ^ 2 * (if δ < |X ω| then 1 else 0) := by
      funext ω
      by_cases h : δ < |X ω|
      · rw [Set.indicator_of_mem (by simpa [Set.mem_preimage] using h), if_pos h, mul_one]
      · rw [Set.indicator_of_notMem (by simpa [Set.mem_preimage] using h), if_neg h, mul_zero]
    rwa [hcongr] at h
  have hBfun : Integrable (fun ω => K * Real.exp (t ^ 2 * c / 2) *
      (4 * (δ * |t| ^ 3 * X ω ^ 2 +
        t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0))))) μ := by
    have h1 : Integrable (fun ω => δ * |t| ^ 3 * X ω ^ 2) μ := hX2_int.const_mul _
    have h2 : Integrable (fun ω => t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0))) μ :=
      h_ind.const_mul _
    exact ((h1.add h2).const_mul 4).const_mul _
  have hf4_int : Integrable f4 μ := by
    refine Integrable.mono' hBfun hf4_aes ?_
    filter_upwards [hW'_bound] with ω hWω
    rw [hf4, norm_mul]
    have hr_le := norm_cexp_I_sub_taylor_le (y ω)
    have hmin := min_cube_sq_le t δ (X ω) hδ
    have hb : ‖r ω‖ ≤ 4 * (δ * |t| ^ 3 * X ω ^ 2 +
        t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0))) := by
      have hr' : ‖r ω‖ ≤ 4 * min (|t * X ω| ^ 3) ((t * X ω) ^ 2) :=
        by simpa only [hr, hy] using hr_le
      have h4 : 4 * min (|t * X ω| ^ 3) ((t * X ω) ^ 2) ≤
          4 * (δ * |t| ^ 3 * X ω ^ 2 + t ^ 2 * X ω ^ 2 * (if δ < |X ω| then 1 else 0)) :=
        mul_le_mul_of_nonneg_left hmin (by norm_num)
      have heq : t ^ 2 * X ω ^ 2 * (if δ < |X ω| then 1 else 0)
          = t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0)) := by ring
      rw [heq] at h4
      exact hr'.trans h4
    calc ‖W' ω‖ * ‖r ω‖ ≤ (K * Real.exp (t ^ 2 * c / 2)) * ‖r ω‖ :=
          mul_le_mul_of_nonneg_right hWω (norm_nonneg _)
      _ ≤ (K * Real.exp (t ^ 2 * c / 2)) *
            (4 * (δ * |t| ^ 3 * X ω ^ 2 +
              t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0)))) :=
          mul_le_mul_of_nonneg_left hb hK'
      _ = K * Real.exp (t ^ 2 * c / 2) *
            (4 * (δ * |t| ^ 3 * X ω ^ 2 +
              t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0)))) := by ring
  -- The linear term integrates to zero.
  have hy_mean : μ[y | m] =ᵐ[μ] 0 := by
    rw [hy]
    have h := condExp_smul (μ := μ) (m := m) t X
    filter_upwards [h, hX0] with ω h1 h2
    change μ[t • X | m] ω = 0
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    simp only [Pi.zero_apply] at h2
    rw [h1, h2, mul_zero]
  have h_lin : ∫ ω, f2 ω ∂μ = 0 := by
    have hy_int : Integrable y μ := by rw [hy]; exact hX_int.const_mul t
    have hzero : ∫ ω, W' ω * (μ[y | m] ω : ℂ) ∂μ = 0 := by
      have h0 : (fun ω => W' ω * (μ[y | m] ω : ℂ)) =ᵐ[μ] (fun _ => (0 : ℂ)) :=
        hy_mean.mono fun ω h => by
          simp only [Pi.zero_apply] at h
          simp [h]
      rw [integral_congr_ae h0, integral_zero]
    have hbase : ∫ ω, W' ω * (y ω : ℂ) ∂μ = 0 := by
      rw [integral_mul_ofReal_eq_integral_mul_condExp (m0 := m0) (m := m) hm hy_int
        hW'_sm hW'_bound, hzero]
    have hsplit : ∫ ω, W' ω * (Complex.I * (y ω : ℂ)) ∂μ
        = Complex.I * ∫ ω, W' ω * (y ω : ℂ) ∂μ := by
      have h0 : (fun ω => W' ω * (Complex.I * (y ω : ℂ)))
          = fun ω => Complex.I * (W' ω * (y ω : ℂ)) := by
        funext ω; ring
      rw [h0, integral_const_mul]
    rw [hf2, hsplit, hbase, mul_zero]
  -- The quadratic term integrates to zero.
  have h_x2 : ∫ ω, W' ω * ((X ω ^ 2 : ℝ) : ℂ) ∂μ =
      ∫ ω, W' ω * (q ω : ℂ) ∂μ := by
    have h := integral_mul_ofReal_eq_integral_mul_condExp (m0 := m0) (m := m) hm hX2_int
      hW'_sm hW'_bound
    have hcongr : (fun ω => W' ω * (μ[fun ω => X ω ^ 2 | m] ω : ℂ))
        = fun ω => W' ω * (q ω : ℂ) := by
      funext ω; rw [hq]
    rw [hcongr] at h
    exact h
  have h_quad : ∫ ω, f3 ω ∂μ = 0 := by
    have hf3a : Integrable (fun ω => W' ω * (a ω : ℂ)) μ := by
      refine Integrable.of_bound (hW'_aes.mul haC_aes)
        (K * Real.exp (t ^ 2 * c / 2) * (t ^ 2 * c / 2)) ?_
      filter_upwards [hW'_bound, ha_nonneg, ha_le] with ω hWω ha0 ha1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h2 : |a ω| ≤ t ^ 2 * c / 2 := abs_le.mpr ⟨by linarith, ha1⟩
      calc ‖W' ω‖ * |a ω| ≤ (K * Real.exp (t ^ 2 * c / 2)) * (t ^ 2 * c / 2) :=
            mul_le_mul hWω h2 (abs_nonneg _) hK'
        _ = K * Real.exp (t ^ 2 * c / 2) * (t ^ 2 * c / 2) := by ring
    have hf3b : Integrable (fun ω => W' ω * ((y ω : ℂ) ^ 2 / 2)) μ := by
      have hg : Integrable (fun ω => K * Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) * X ω ^ 2) μ :=
        hX2_int.const_mul _
      refine Integrable.mono' hg (hW'_aes.mul hy2_aes) ?_
      filter_upwards [hW'_bound] with ω hWω
      rw [norm_mul, norm_sq_div_two, hy]
      rw [show (t * X ω) ^ 2 / 2 = t ^ 2 * X ω ^ 2 / 2 by ring]
      calc ‖W' ω‖ * (t ^ 2 * X ω ^ 2 / 2)
          ≤ (K * Real.exp (t ^ 2 * c / 2)) * (t ^ 2 * X ω ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right hWω (by positivity)
        _ = K * Real.exp (t ^ 2 * c / 2) * (t ^ 2 / 2) * X ω ^ 2 := by ring
    have hdist : f3 =ᵐ[μ] (fun ω => W' ω * (a ω : ℂ) - W' ω * ((y ω : ℂ) ^ 2 / 2)) :=
      Eventually.of_forall fun ω => by rw [hf3]; ring
    rw [integral_congr_ae hdist, integral_sub hf3a hf3b]
    have ha_eq : ∫ ω, W' ω * (a ω : ℂ) ∂μ
        = ((t ^ 2 / 2 : ℝ) : ℂ) * ∫ ω, W' ω * (q ω : ℂ) ∂μ := by
      have h0 : (fun ω => W' ω * (a ω : ℂ))
          = fun ω => ((t ^ 2 / 2 : ℝ) : ℂ) * (W' ω * (q ω : ℂ)) := by
        funext ω; rw [ha]; push_cast; ring
      rw [h0, integral_const_mul]
    have hy2_eq : ∫ ω, W' ω * ((y ω : ℂ) ^ 2 / 2) ∂μ
        = ((t ^ 2 / 2 : ℝ) : ℂ) * ∫ ω, W' ω * ((X ω ^ 2 : ℝ) : ℂ) ∂μ := by
      have h0 : (fun ω => W' ω * ((y ω : ℂ) ^ 2 / 2))
          = fun ω => ((t ^ 2 / 2 : ℝ) : ℂ) * (W' ω * ((X ω ^ 2 : ℝ) : ℂ)) := by
        funext ω; rw [hy]; push_cast; ring
      rw [h0, integral_const_mul]
    rw [ha_eq, hy2_eq, h_x2]
    ring
  have h_mid : ∫ ω, (f2 + f3) ω ∂μ = 0 := by
    rw [show ∫ ω, (f2 + f3) ω ∂μ = ∫ ω, f2 ω ∂μ + ∫ ω, f3 ω ∂μ from
      integral_add hf2_int hf3_int, h_lin, h_quad, zero_add]
  -- The decomposition of the full integrand.
  have hpoint : ∀ ω, W ω * (Complex.exp (t * X ω * Complex.I) *
        Complex.exp ((t ^ 2 * q ω / 2 : ℝ)) - 1) = f1 ω + (f2 ω + f3 ω) + f4 ω := by
    intro ω
    have h := mul_cexp_sub_one_decomp (W ω) (t * X ω) (t ^ 2 * q ω / 2)
    simp only [hf1, hf2, hf3, hf4, hW', hr, hy, ha] at h ⊢
    push_cast at h ⊢
    rw [h]
    ring
  have hI0 : ∫ ω, W ω * (Complex.exp (t * X ω * Complex.I) *
        Complex.exp ((t ^ 2 * q ω / 2 : ℝ)) - 1) ∂μ
      = ∫ ω, f1 ω ∂μ + ∫ ω, f4 ω ∂μ := by
    have hcongr : (fun ω => W ω * (Complex.exp (t * X ω * Complex.I) *
          Complex.exp ((t ^ 2 * q ω / 2 : ℝ)) - 1))
        =ᵐ[μ] (fun ω => f1 ω + (f2 ω + f3 ω) + f4 ω) :=
      Eventually.of_forall hpoint
    rw [integral_congr_ae hcongr]
    calc ∫ ω, f1 ω + (f2 ω + f3 ω) + f4 ω ∂μ
        = ∫ ω, (f1 + (f2 + f3)) ω + f4 ω ∂μ := rfl
      _ = ∫ ω, (f1 + (f2 + f3)) ω ∂μ + ∫ ω, f4 ω ∂μ :=
            integral_add (hf1_int.add (hf2_int.add hf3_int)) hf4_int
      _ = (∫ ω, f1 ω ∂μ + ∫ ω, (f2 + f3) ω ∂μ) + ∫ ω, f4 ω ∂μ := by
            rw [show ∫ ω, (f1 + (f2 + f3)) ω ∂μ
                = ∫ ω, f1 ω ∂μ + ∫ ω, (f2 + f3) ω ∂μ from
              integral_add hf1_int (hf2_int.add hf3_int)]
      _ = (∫ ω, f1 ω ∂μ + 0) + ∫ ω, f4 ω ∂μ := by rw [h_mid]
      _ = ∫ ω, f1 ω ∂μ + ∫ ω, f4 ω ∂μ := by rw [add_zero]
  -- Bound the first piece.
  have hI1_bound : ‖∫ ω, f1 ω ∂μ‖ ≤
      K * Real.exp (t ^ 2 * c / 2) * (t ^ 4 / 8 * ∫ ω, q ω ^ 2 ∂μ) := by
    have hg : Integrable (fun ω => K * Real.exp (t ^ 2 * c / 2) * (a ω ^ 2 / 2)) μ := by
      have hg_aes : AEStronglyMeasurable[m0]
          (fun ω => K * Real.exp (t ^ 2 * c / 2) * (a ω ^ 2 / 2)) μ := by
        have h := (ha_aes.pow 2).const_mul (K * Real.exp (t ^ 2 * c / 2) / 2)
        convert h using 1
        funext ω
        simp only [Pi.pow_apply]
        ring
      refine Integrable.of_bound hg_aes
        (K * Real.exp (t ^ 2 * c / 2) * ((t ^ 2 * c / 2) ^ 2 / 2)) ?_
      filter_upwards [ha_nonneg, ha_le] with ω ha0 ha1
      have h0 : 0 ≤ t ^ 2 * c / 2 := le_trans ha0 ha1
      have h3 : (a ω) ^ 2 / 2 ≤ (t ^ 2 * c / 2) ^ 2 / 2 := by nlinarith
      calc ‖K * Real.exp (t ^ 2 * c / 2) * (a ω ^ 2 / 2)‖
          = K * Real.exp (t ^ 2 * c / 2) * (a ω ^ 2 / 2) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ K * Real.exp (t ^ 2 * c / 2) * ((t ^ 2 * c / 2) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    have hpt : ∀ᵐ ω ∂μ, ‖f1 ω‖ ≤ K * Real.exp (t ^ 2 * c / 2) * (a ω ^ 2 / 2) := by
      filter_upwards [hWK, ha_nonneg, ha_le, h_exp_le] with ω hWω ha0 ha1 hE
      rw [hf1, norm_mul, norm_cexp_mul_one_sub_sub_one]
      have hE2 := abs_exp_mul_one_sub_sub_one_le (a ω) ha0
      have hb : |Real.exp (a ω) * (1 - a ω) - 1| ≤ (a ω) ^ 2 / 2 * Real.exp (t ^ 2 * c / 2) :=
        hE2.trans (mul_le_mul_of_nonneg_left hE (by positivity))
      calc ‖W ω‖ * |Real.exp (a ω) * (1 - a ω) - 1|
          ≤ K * ((a ω) ^ 2 / 2 * Real.exp (t ^ 2 * c / 2)) :=
            mul_le_mul hWω hb (abs_nonneg _) hK
        _ = K * Real.exp (t ^ 2 * c / 2) * (a ω ^ 2 / 2) := by ring
    have h_int_norm : Integrable (fun ω => ‖f1 ω‖) μ :=
      Integrable.mono' hg (hf1_int.aestronglyMeasurable.norm)
        (hpt.mono fun ω h => by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h)
    have hint_eq : ∫ ω, K * Real.exp (t ^ 2 * c / 2) * (a ω ^ 2 / 2) ∂μ
        = K * Real.exp (t ^ 2 * c / 2) * (t ^ 4 / 8 * ∫ ω, q ω ^ 2 ∂μ) := by
      rw [integral_const_mul]
      have hsq : (fun ω => a ω ^ 2 / 2) = fun ω => (t ^ 4 / 8) * q ω ^ 2 := by
        funext ω; rw [ha]; ring
      rw [hsq, integral_const_mul]
    calc ‖∫ ω, f1 ω ∂μ‖ ≤ ∫ ω, ‖f1 ω‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, K * Real.exp (t ^ 2 * c / 2) * (a ω ^ 2 / 2) ∂μ :=
          integral_mono_ae h_int_norm hg hpt
      _ = K * Real.exp (t ^ 2 * c / 2) * (t ^ 4 / 8 * ∫ ω, q ω ^ 2 ∂μ) := hint_eq
  -- Bound the second piece.
  have hI2_bound : ‖∫ ω, f4 ω ∂μ‖ ≤
      K * Real.exp (t ^ 2 * c / 2) * (4 * (δ * |t| ^ 3 * ∫ ω, X ω ^ 2 ∂μ +
        t ^ 2 * ∫ ω, X ω ^ 2 * (if δ < |X ω| then 1 else 0) ∂μ)) := by
    have hpt : ∀ᵐ ω ∂μ, ‖f4 ω‖ ≤ K * Real.exp (t ^ 2 * c / 2) *
        (4 * (δ * |t| ^ 3 * X ω ^ 2 +
          t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0)))) := by
      filter_upwards [hW'_bound] with ω hWω
      rw [hf4, norm_mul]
      have hr_le := norm_cexp_I_sub_taylor_le (y ω)
      have hmin := min_cube_sq_le t δ (X ω) hδ
      have hb : ‖r ω‖ ≤ 4 * (δ * |t| ^ 3 * X ω ^ 2 +
          t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0))) := by
        have hr' : ‖r ω‖ ≤ 4 * min (|t * X ω| ^ 3) ((t * X ω) ^ 2) :=
          by simpa only [hr, hy] using hr_le
        have h4 : 4 * min (|t * X ω| ^ 3) ((t * X ω) ^ 2) ≤
            4 * (δ * |t| ^ 3 * X ω ^ 2 +
              t ^ 2 * X ω ^ 2 * (if δ < |X ω| then 1 else 0)) :=
          mul_le_mul_of_nonneg_left hmin (by norm_num)
        have heq : t ^ 2 * X ω ^ 2 * (if δ < |X ω| then 1 else 0)
            = t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0)) := by ring
        rw [heq] at h4
        exact hr'.trans h4
      calc ‖W' ω‖ * ‖r ω‖ ≤ (K * Real.exp (t ^ 2 * c / 2)) * ‖r ω‖ :=
            mul_le_mul_of_nonneg_right hWω (norm_nonneg _)
        _ ≤ (K * Real.exp (t ^ 2 * c / 2)) *
              (4 * (δ * |t| ^ 3 * X ω ^ 2 +
                t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0)))) :=
            mul_le_mul_of_nonneg_left hb hK'
        _ = K * Real.exp (t ^ 2 * c / 2) *
              (4 * (δ * |t| ^ 3 * X ω ^ 2 +
                t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0)))) := by ring
    have h_int_norm : Integrable (fun ω => ‖f4 ω‖) μ :=
      Integrable.mono' hBfun (hf4_int.aestronglyMeasurable.norm)
        (hpt.mono fun ω h => by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h)
    have hint_eq : ∫ ω, K * Real.exp (t ^ 2 * c / 2) *
          (4 * (δ * |t| ^ 3 * X ω ^ 2 +
            t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0)))) ∂μ
        = K * Real.exp (t ^ 2 * c / 2) * (4 * (δ * |t| ^ 3 * ∫ ω, X ω ^ 2 ∂μ +
            t ^ 2 * ∫ ω, X ω ^ 2 * (if δ < |X ω| then 1 else 0) ∂μ)) := by
      rw [integral_const_mul]
      congr 1
      rw [integral_const_mul]
      congr 1
      rw [integral_add (hX2_int.const_mul _) (h_ind.const_mul _),
        integral_const_mul, integral_const_mul]
    calc ‖∫ ω, f4 ω ∂μ‖ ≤ ∫ ω, ‖f4 ω‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, K * Real.exp (t ^ 2 * c / 2) *
            (4 * (δ * |t| ^ 3 * X ω ^ 2 +
              t ^ 2 * (X ω ^ 2 * (if δ < |X ω| then 1 else 0)))) ∂μ :=
          integral_mono_ae h_int_norm hBfun hpt
      _ = K * Real.exp (t ^ 2 * c / 2) * (4 * (δ * |t| ^ 3 * ∫ ω, X ω ^ 2 ∂μ +
            t ^ 2 * ∫ ω, X ω ^ 2 * (if δ < |X ω| then 1 else 0) ∂μ)) := hint_eq
  -- Assemble.
  have hmain : ‖∫ ω, W ω * (Complex.exp (t * X ω * Complex.I) *
        Complex.exp ((t ^ 2 * q ω / 2 : ℝ)) - 1) ∂μ‖ ≤
      K * Real.exp (t ^ 2 * c / 2) * (t ^ 4 / 8 * ∫ ω, q ω ^ 2 ∂μ) +
        K * Real.exp (t ^ 2 * c / 2) * (4 * (δ * |t| ^ 3 * ∫ ω, X ω ^ 2 ∂μ +
          t ^ 2 * ∫ ω, X ω ^ 2 * (if δ < |X ω| then 1 else 0) ∂μ)) :=
    calc ‖∫ ω, W ω * (Complex.exp (t * X ω * Complex.I) *
            Complex.exp ((t ^ 2 * q ω / 2 : ℝ)) - 1) ∂μ‖
        = ‖∫ ω, f1 ω ∂μ + ∫ ω, f4 ω ∂μ‖ := by rw [hI0]
      _ ≤ ‖∫ ω, f1 ω ∂μ‖ + ‖∫ ω, f4 ω ∂μ‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hI1_bound hI2_bound
  have hgoal : K * Real.exp (t ^ 2 * c / 2) * (t ^ 4 / 8 * ∫ ω, q ω ^ 2 ∂μ) +
        K * Real.exp (t ^ 2 * c / 2) * (4 * (δ * |t| ^ 3 * ∫ ω, X ω ^ 2 ∂μ +
          t ^ 2 * ∫ ω, X ω ^ 2 * (if δ < |X ω| then 1 else 0) ∂μ))
      = K * Real.exp (t ^ 2 * c / 2) * (t ^ 4 / 8 * ∫ ω, q ω ^ 2 ∂μ +
          4 * (δ * |t| ^ 3 * ∫ ω, X ω ^ 2 ∂μ +
            t ^ 2 * ∫ ω, X ω ^ 2 * (if δ < |X ω| then 1 else 0) ∂μ)) := by ring
  rw [hgoal] at hmain
  exact hmain

end CERW.Generic.Martingale.CLT
