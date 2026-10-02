import CERW.Model
import CERW.Generic.Kernel.ScalarTaylor
import CERW.Generic.Martingale.FreedmanEvent
import LatticeProb.Prob.PaleyZygmund

/-!
# The exponential martingale of a martingale with bounded increments

For increments `Y t` that are bounded by `b` and conditionally centred, the cumulant
`K(s) = ∑_t log E(e^{s Y_t} | ℱ t)` and the exponential martingale `exp (s ∑_t Y_t - K(s))` of
the sum. The exponential martingale has mean one (`Increments.integral_expMart`) and second
moment at most `exp (6 s² v)` when the total conditional variance is at most `v`
(`Increments.integral_expMart_sq_le`). The cumulant differs from `s² v / 2` by at most
`2 |s|³ b v` (`Increments.abs_cumulant_sub_le`).
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Generic.Martingale.ExpMart

/-- Second-order Taylor bound for the exponential. -/
lemma abs_exp_sub_quad_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - 1 - x - x ^ 2 / 2| ≤ |x| ^ 3 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have h3 : (0 : ℝ) ≤ |x| ^ 3 := by positivity
  have : |Real.exp x - 1 - x - x ^ 2 / 2|
      ≤ |x| ^ 3 * (((3 : ℕ).succ : ℝ) / (((3 : ℕ).factorial : ℝ) * (3 : ℕ))) := by
    convert h using 2; ring_nf
  refine this.trans ?_
  have hc : (((3 : ℕ).succ : ℝ) / (((3 : ℕ).factorial : ℝ) * (3 : ℕ))) ≤ 1 := by
    norm_num [Nat.factorial]
  exact mul_le_of_le_one_right h3 hc

section ExpMart

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)

/-- The increments `Y t`, `t < n`, are `ℱ (t + 1)`-measurable, bounded by `b` and conditionally
centred given `ℱ t`. -/
structure Increments (Y : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ) : Prop where
  nonneg : 0 ≤ b
  stronglyMeasurable : ∀ t < n, StronglyMeasurable[ℱ (t + 1)] (Y t)
  abs_le : ∀ t < n, ∀ ω, |Y t ω| ≤ b
  condExp_eq_zero : ∀ t < n, μ[Y t | ℱ t] =ᵐ[μ] 0

/-- The conditional moment generating function `E(e^{s Y_t} | ℱ t)`. -/
noncomputable def condMgf (Y : ℕ → Ω → ℝ) (s : ℝ) (t : ℕ) : Ω → ℝ :=
  μ[fun ω => Real.exp (s * Y t ω) | ℱ t]

/-- The conditional variance `E(Y_t² | ℱ t)`. -/
noncomputable def condVar (Y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  μ[fun ω => Y t ω ^ 2 | ℱ t]

/-- The cumulant `K(s) = Σ_{t<n} log E(e^{s Y_t} | ℱ t)`. -/
noncomputable def cumulant (Y : ℕ → Ω → ℝ) (s : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ t ∈ Finset.range n, Real.log (condMgf μ ℱ Y s t ω)

/-- The total conditional variance `Σ_{t<n} E(Y_t² | ℱ t)`. -/
noncomputable def varSum (Y : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ t ∈ Finset.range n, condVar μ ℱ Y t ω

/-- The exponential martingale `exp (s Σ_{t<n} Y_t - K(s))`. -/
noncomputable def expMart (Y : ℕ → Ω → ℝ) (s : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => Real.exp (s * ∑ t ∈ Finset.range n, Y t ω - cumulant μ ℱ Y s n ω)

variable {μ ℱ} {Y : ℕ → Ω → ℝ} {b : ℝ} {n : ℕ}

/-- Each increment `Y t`, `t < n`, is measurable. -/
lemma Increments.measurable (h : Increments μ ℱ Y b n) {t : ℕ} (ht : t < n) :
    Measurable (Y t) :=
  ((h.stronglyMeasurable t ht).mono (ℱ.le (t + 1))).measurable

/-- The exponential of a bounded increment is integrable. -/
lemma Increments.integrable_exp [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
    {t : ℕ} (ht : t < n) : Integrable (fun ω => Real.exp (s * Y t ω)) μ := by
  refine Integrable.of_bound (C := Real.exp (|s| * b)) ?_ ?_
  · exact (Real.measurable_exp.comp ((h.measurable ht).const_mul s)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc s * Y t ω ≤ |s * Y t ω| := le_abs_self _
      _ = |s| * |Y t ω| := abs_mul _ _
      _ ≤ |s| * b := mul_le_mul_of_nonneg_left (h.abs_le t ht ω) (abs_nonneg _)

/-- The square of a bounded increment is integrable. -/
lemma Increments.integrable_sq [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    {t : ℕ} (ht : t < n) : Integrable (fun ω => Y t ω ^ 2) μ := by
  refine Integrable.of_bound (C := b ^ 2) ?_ ?_
  · exact ((h.measurable ht).pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h.abs_le t ht ω) 2

/-- A bounded increment is integrable. -/
lemma Increments.integrable [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    {t : ℕ} (ht : t < n) : Integrable (Y t) μ := by
  refine Integrable.of_bound (C := b) (h.measurable ht).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact h.abs_le t ht ω

/-- A conditional expectation of a function bounded below is bounded below a.e. -/
lemma ae_le_condExp_of_le [IsFiniteMeasure μ] {f : Ω → ℝ} {t : ℕ}
    (hf : Integrable f μ) {a : ℝ} (ha : ∀ ω, a ≤ f ω) : ∀ᵐ ω ∂μ, a ≤ μ[f | ℱ t] ω := by
  have h := condExp_mono (m := ℱ t) (integrable_const a) hf (Filter.Eventually.of_forall ha)
  filter_upwards [h] with ω hω
  rwa [condExp_const (ℱ.le t)] at hω

/-- A conditional expectation of a function bounded above is bounded above a.e. -/
lemma ae_condExp_le_of_le [IsFiniteMeasure μ] {f : Ω → ℝ} {t : ℕ}
    (hf : Integrable f μ) {a : ℝ} (ha : ∀ ω, f ω ≤ a) : ∀ᵐ ω ∂μ, μ[f | ℱ t] ω ≤ a := by
  have h := condExp_mono (m := ℱ t) hf (integrable_const a) (Filter.Eventually.of_forall ha)
  filter_upwards [h] with ω hω
  rwa [condExp_const (ℱ.le t)] at hω


/-- The conditional moment generating function is bounded below by `exp (-(|s| b))` a.e. -/
lemma Increments.condMgf_ge [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
    {t : ℕ} (ht : t < n) : ∀ᵐ ω ∂μ, Real.exp (-(|s| * b)) ≤ condMgf μ ℱ Y s t ω := by
  refine ae_le_condExp_of_le (h.integrable_exp s ht) fun ω => Real.exp_le_exp.mpr ?_
  have h1 : |s * Y t ω| ≤ |s| * b := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h.abs_le t ht ω) (abs_nonneg _)
  linarith [neg_abs_le (s * Y t ω)]

/-- The conditional moment generating function is bounded above by `exp (|s| b)` a.e. -/
lemma Increments.condMgf_le [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
    {t : ℕ} (ht : t < n) : ∀ᵐ ω ∂μ, condMgf μ ℱ Y s t ω ≤ Real.exp (|s| * b) := by
  refine ae_condExp_le_of_le (h.integrable_exp s ht) fun ω => Real.exp_le_exp.mpr ?_
  have h1 : |s * Y t ω| ≤ |s| * b := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h.abs_le t ht ω) (abs_nonneg _)
  linarith [le_abs_self (s * Y t ω)]

/-- The conditional variance is nonnegative a.e. -/
lemma Increments.condVar_nonneg [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    {t : ℕ} (ht : t < n) : ∀ᵐ ω ∂μ, 0 ≤ condVar μ ℱ Y t ω :=
  ae_le_condExp_of_le (h.integrable_sq ht) fun _ => sq_nonneg _

/-- The conditional variance is at most `b ^ 2` a.e. -/
lemma Increments.condVar_le [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    {t : ℕ} (ht : t < n) : ∀ᵐ ω ∂μ, condVar μ ℱ Y t ω ≤ b ^ 2 := by
  refine ae_condExp_le_of_le (h.integrable_sq ht) fun ω => ?_
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h.abs_le t ht ω) 2

/-- Conditional expectation of a quadratic polynomial in a bounded variable. -/
lemma condExp_quad [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    {Y : Ω → ℝ} (hY : Integrable Y μ) (hY2 : Integrable (fun ω => Y ω ^ 2) μ) (a₀ a₁ a₂ : ℝ) :
    μ[fun ω => a₀ + a₁ * Y ω + a₂ * Y ω ^ 2 | m]
      =ᵐ[μ] fun ω => a₀ + a₁ * μ[Y | m] ω + a₂ * μ[fun ω => Y ω ^ 2 | m] ω := by
  have h01 : Integrable (fun ω => a₀ + a₁ * Y ω) μ := (integrable_const a₀).add (hY.const_mul a₁)
  have h2 : Integrable (fun ω => a₂ * Y ω ^ 2) μ := hY2.const_mul a₂
  have e1 : μ[fun ω => a₀ + a₁ * Y ω + a₂ * Y ω ^ 2 | m]
      =ᵐ[μ] μ[fun ω => a₀ + a₁ * Y ω | m] + μ[fun ω => a₂ * Y ω ^ 2 | m] :=
    condExp_add h01 h2 m
  have e2 : μ[fun ω => a₀ + a₁ * Y ω | m]
      =ᵐ[μ] μ[fun _ => a₀ | m] + μ[fun ω => a₁ * Y ω | m] :=
    condExp_add (integrable_const a₀) (hY.const_mul a₁) m
  have e3 : μ[fun ω => a₁ * Y ω | m] =ᵐ[μ] fun ω => a₁ * μ[Y | m] ω :=
    condExp_smul (μ := μ) a₁ Y m
  have e4 : μ[fun ω => a₂ * Y ω ^ 2 | m] =ᵐ[μ] fun ω => a₂ * μ[fun ω => Y ω ^ 2 | m] ω :=
    condExp_smul (μ := μ) a₂ (fun ω => Y ω ^ 2) m
  have e5 : μ[fun _ => a₀ | m] = fun _ => a₀ := condExp_const hm a₀
  filter_upwards [e1, e2, e3, e4] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.add_apply, e5, h3, h4]


/-- Pointwise second-order bound for the exponential of a bounded increment. -/
lemma abs_exp_mul_sub_quad_le {s y b : ℝ} (hy : |y| ≤ b) (hsb : |s| * b ≤ 1) :
    |Real.exp (s * y) - (1 + s * y + s ^ 2 / 2 * y ^ 2)| ≤ |s| ^ 3 * b * y ^ 2 := by
  have hx : |s * y| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hy (abs_nonneg _)).trans hsb
  have h := abs_exp_sub_quad_le hx
  have e1 : Real.exp (s * y) - (1 + s * y + s ^ 2 / 2 * y ^ 2)
      = Real.exp (s * y) - 1 - s * y - (s * y) ^ 2 / 2 := by ring
  rw [e1]
  refine h.trans ?_
  rw [abs_mul, mul_pow]
  have h3 : |y| ^ 3 = |y| * y ^ 2 := by rw [← sq_abs y]; ring
  rw [h3]
  have h4 : |y| * y ^ 2 ≤ b * y ^ 2 :=
    mul_le_mul_of_nonneg_right hy (sq_nonneg _)
  have h5 : 0 ≤ |s| ^ 3 := by positivity
  calc |s| ^ 3 * (|y| * y ^ 2) ≤ |s| ^ 3 * (b * y ^ 2) := mul_le_mul_of_nonneg_left h4 h5
    _ = |s| ^ 3 * b * y ^ 2 := by ring

/-- One-step Taylor bound for the conditional moment generating function of a centred bounded
increment. -/
lemma Increments.abs_condMgf_sub_le [IsProbabilityMeasure μ] (h : Increments μ ℱ Y b n)
    (s : ℝ) (hsb : |s| * b ≤ 1) {t : ℕ} (ht : t < n) :
    ∀ᵐ ω ∂μ, |condMgf μ ℱ Y s t ω - 1 - s ^ 2 / 2 * condVar μ ℱ Y t ω|
      ≤ |s| ^ 3 * b * condVar μ ℱ Y t ω := by
  have hpt := fun ω => abs_exp_mul_sub_quad_le (s := s) (h.abs_le t ht ω) hsb
  have hint : Integrable (fun ω => Real.exp (s * Y t ω)) μ := h.integrable_exp s ht
  have hY := h.integrable ht
  have hY2 := h.integrable_sq ht
  have hup : (fun ω => Real.exp (s * Y t ω)) ≤ᵐ[μ]
      fun ω => 1 + s * Y t ω + (s ^ 2 / 2 + |s| ^ 3 * b) * Y t ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => by
      have := (_root_.abs_le.mp (hpt ω)).2
      simp only
      linarith
  have hlo : (fun ω => 1 + s * Y t ω + (s ^ 2 / 2 - |s| ^ 3 * b) * Y t ω ^ 2) ≤ᵐ[μ]
      fun ω => Real.exp (s * Y t ω) :=
    Filter.Eventually.of_forall fun ω => by
      have := (_root_.abs_le.mp (hpt ω)).1
      simp only
      linarith
  have hg1 : Integrable
      (fun ω => 1 + s * Y t ω + (s ^ 2 / 2 + |s| ^ 3 * b) * Y t ω ^ 2) μ :=
    ((integrable_const (1 : ℝ)).add (hY.const_mul s)).add (hY2.const_mul _)
  have hg2 : Integrable
      (fun ω => 1 + s * Y t ω + (s ^ 2 / 2 - |s| ^ 3 * b) * Y t ω ^ 2) μ :=
    ((integrable_const (1 : ℝ)).add (hY.const_mul s)).add (hY2.const_mul _)
  have hup' := condExp_mono (m := ℱ t) hint hg1 hup
  have hlo' := condExp_mono (m := ℱ t) hg2 hint hlo
  have hq1 := condExp_quad (ℱ.le t) hY hY2 1 s (s ^ 2 / 2 + |s| ^ 3 * b)
  have hq2 := condExp_quad (ℱ.le t) hY hY2 1 s (s ^ 2 / 2 - |s| ^ 3 * b)
  filter_upwards [hup', hlo', hq1, hq2, h.condExp_eq_zero t ht] with ω h1 h2 h3 h4 h5
  simp only [Pi.zero_apply] at h5
  rw [h3, h5] at h1
  rw [h4, h5] at h2
  unfold condMgf condVar
  rw [_root_.abs_le]
  constructor <;> linarith

/-- One-step bound for the logarithm of the conditional moment generating function of a centred
bounded increment, when `|s| b ≤ 1 / 2`. -/
lemma Increments.abs_log_condMgf_sub_le [IsProbabilityMeasure μ]
    (h : Increments μ ℱ Y b n) (s : ℝ) (hsb : |s| * b ≤ 1 / 2) {t : ℕ} (ht : t < n) :
    ∀ᵐ ω ∂μ, |Real.log (condMgf μ ℱ Y s t ω) - s ^ 2 / 2 * condVar μ ℱ Y t ω|
      ≤ 2 * |s| ^ 3 * b * condVar μ ℱ Y t ω := by
  filter_upwards [h.abs_condMgf_sub_le s (by linarith) ht, h.condVar_nonneg ht,
    h.condVar_le ht] with ω hT hq0 hq1
  set q := condVar μ ℱ Y t ω with hq
  set φ := condMgf μ ℱ Y s t ω with hφ
  set x := |s| * b with hx
  have hx0 : 0 ≤ x := mul_nonneg (abs_nonneg _) h.nonneg
  have hs2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  set P := s ^ 2 * q with hP
  have hP0 : 0 ≤ P := mul_nonneg (sq_nonneg _) hq0
  have hPx : |s| ^ 3 * b * q = P * x := by rw [hP, hs2, hx]; ring
  have hPle : P ≤ x ^ 2 := by
    calc P = s ^ 2 * q := rfl
      _ ≤ s ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_left hq1 (sq_nonneg _)
      _ = x ^ 2 := by rw [hx, mul_pow, sq_abs]
  rw [hPx] at hT
  set u := φ - 1 with hu
  have hT' : |u - s ^ 2 / 2 * q| ≤ P * x := by
    simpa only [hu, sub_sub] using hT
  have hPx2 : P * x ≤ P * (1 / 2) := mul_le_mul_of_nonneg_left hsb hP0
  have hxx : x ^ 2 ≤ x / 2 := by
    have := mul_le_mul_of_nonneg_left hsb hx0
    rw [sq]; linarith
  have hu1 : |u| ≤ P := by
    have h2 : |u| ≤ |s ^ 2 / 2 * q| + |u - s ^ 2 / 2 * q| := by
      have := abs_add_le (s ^ 2 / 2 * q) (u - s ^ 2 / 2 * q)
      rw [add_sub_cancel] at this
      exact this
    have h3 : |s ^ 2 / 2 * q| = P / 2 := by
      rw [abs_of_nonneg (by positivity)]; rw [hP]; ring
    linarith
  have hu2 : |u| ≤ 1 / 2 := by linarith
  have hlog := CERW.Generic.Kernel.abs_log_one_add_sub_le hu2
  have hφu : 1 + u = φ := by rw [hu]; ring
  rw [hφu] at hlog
  have hu3 : u ^ 2 ≤ P ^ 2 := by
    rw [← sq_abs u]; exact pow_le_pow_left₀ (abs_nonneg _) hu1 2
  have hfin : |Real.log φ - s ^ 2 / 2 * q| ≤ 2 * u ^ 2 + P * x := by
    have := abs_add_le (Real.log φ - u) (u - s ^ 2 / 2 * q)
    rw [sub_add_sub_cancel] at this
    linarith
  rw [show 2 * |s| ^ 3 * b * q = 2 * (P * x) by rw [← hPx]; ring]
  have hPP : P ^ 2 ≤ P * x ^ 2 := by
    rw [sq P]; exact mul_le_mul_of_nonneg_left hPle hP0
  have h5 : P * x ^ 2 ≤ P * (x / 2) := mul_le_mul_of_nonneg_left hxx hP0
  have h6 : P * (x / 2) = P * x / 2 := by ring
  linarith

/-- The cumulant differs from `s² / 2` times the total conditional variance by at most
`2 |s|³ b` times the total conditional variance. -/
lemma Increments.abs_cumulant_sub_le [IsProbabilityMeasure μ]
    (h : Increments μ ℱ Y b n) (s : ℝ) (hsb : |s| * b ≤ 1 / 2) :
    ∀ᵐ ω ∂μ, |cumulant μ ℱ Y s n ω - s ^ 2 / 2 * varSum μ ℱ Y n ω|
      ≤ 2 * |s| ^ 3 * b * varSum μ ℱ Y n ω := by
  have hall : ∀ᵐ ω ∂μ, ∀ t ∈ Finset.range n,
      |Real.log (condMgf μ ℱ Y s t ω) - s ^ 2 / 2 * condVar μ ℱ Y t ω|
        ≤ 2 * |s| ^ 3 * b * condVar μ ℱ Y t ω :=
    (Filter.eventually_all_finset _).2 fun t ht =>
      h.abs_log_condMgf_sub_le s hsb (Finset.mem_range.1 ht)
  filter_upwards [hall] with ω hω
  have e : cumulant μ ℱ Y s n ω - s ^ 2 / 2 * varSum μ ℱ Y n ω
      = ∑ t ∈ Finset.range n,
        (Real.log (condMgf μ ℱ Y s t ω) - s ^ 2 / 2 * condVar μ ℱ Y t ω) := by
    unfold cumulant varSum
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold varSum
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hω

/-- For `|s| b ≤ 1 / 2`, the cumulant satisfies `K(2s) - 2 K(s) ≤ 6 s² Σ_t E(Y_t² | ℱ t)`. -/
lemma Increments.cumulant_two_mul_sub_le [IsProbabilityMeasure μ]
    (h : Increments μ ℱ Y b n) (s : ℝ) (hsb : |s| * b ≤ 1 / 2) :
    ∀ᵐ ω ∂μ, cumulant μ ℱ Y (2 * s) n ω - 2 * cumulant μ ℱ Y s n ω
      ≤ 6 * s ^ 2 * varSum μ ℱ Y n ω := by
  have hs2b : |2 * s| * b ≤ 1 := by
    rw [abs_mul, abs_two]; linarith
  have hall : ∀ᵐ ω ∂μ, ∀ t ∈ Finset.range n,
      Real.log (condMgf μ ℱ Y (2 * s) t ω) - 2 * Real.log (condMgf μ ℱ Y s t ω)
        ≤ 6 * s ^ 2 * condVar μ ℱ Y t ω := by
    refine (Filter.eventually_all_finset _).2 fun t ht => ?_
    have htn : t < n := Finset.mem_range.1 ht
    filter_upwards [h.abs_condMgf_sub_le s (by linarith) htn, h.abs_condMgf_sub_le (2 * s) hs2b htn,
      h.condVar_nonneg htn, h.condMgf_ge (2 * s) htn] with ω hT1 hT2 hq0 hge
    set q := condVar μ ℱ Y t ω with hq
    set x := |s| * b with hx
    have hx0 : 0 ≤ x := mul_nonneg (abs_nonneg _) h.nonneg
    have hs2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    have hP0 : 0 ≤ s ^ 2 * q := mul_nonneg (sq_nonneg _) hq0
    have hPx : |s| ^ 3 * b * q = s ^ 2 * q * x := by rw [hs2, hx]; ring
    have hPx2 : |2 * s| ^ 3 * b * q = 8 * (s ^ 2 * q * x) := by
      rw [abs_mul, abs_two, hs2, hx]; ring
    rw [hPx] at hT1
    rw [hPx2] at hT2
    have hxle : s ^ 2 * q * x ≤ s ^ 2 * q * (1 / 2) := mul_le_mul_of_nonneg_left hsb hP0
    have h1 : 1 ≤ condMgf μ ℱ Y s t ω := by
      have := (_root_.abs_le.mp hT1).1
      linarith
    have h2 : condMgf μ ℱ Y (2 * s) t ω ≤ 1 + 6 * (s ^ 2 * q) := by
      have := (_root_.abs_le.mp hT2).2
      have e : (2 * s) ^ 2 / 2 * q = 2 * (s ^ 2 * q) := by ring
      rw [e] at this
      linarith
    have hpos : 0 < condMgf μ ℱ Y (2 * s) t ω :=
      lt_of_lt_of_le (Real.exp_pos _) hge
    have h3 : Real.log (condMgf μ ℱ Y (2 * s) t ω) ≤ 6 * (s ^ 2 * q) := by
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    have h4 : 0 ≤ Real.log (condMgf μ ℱ Y s t ω) := Real.log_nonneg h1
    linarith
  filter_upwards [hall] with ω hω
  have e : cumulant μ ℱ Y (2 * s) n ω - 2 * cumulant μ ℱ Y s n ω
      = ∑ t ∈ Finset.range n,
        (Real.log (condMgf μ ℱ Y (2 * s) t ω) - 2 * Real.log (condMgf μ ℱ Y s t ω)) := by
    unfold cumulant
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [e]
  unfold varSum
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hω

variable (μ ℱ Y) in
/-- The exponential martingale is positive. -/
lemma expMart_pos (s : ℝ) (k : ℕ) (ω : Ω) : 0 < expMart μ ℱ Y s k ω :=
  Real.exp_pos _

/-- The exponential martingale at time `k ≤ n` is `ℱ k`-measurable. -/
lemma Increments.measurable_expMart (h : Increments μ ℱ Y b n) (s : ℝ) {k : ℕ}
    (hk : k ≤ n) : Measurable[ℱ k] (expMart μ ℱ Y s k) := by
  have hS : Measurable[ℱ k] (fun ω => ∑ t ∈ Finset.range k, Y t ω) := by
    refine Finset.measurable_sum _ fun t ht => ?_
    have htk : t < k := Finset.mem_range.1 ht
    exact ((h.stronglyMeasurable t (lt_of_lt_of_le htk hk)).mono (ℱ.mono htk)).measurable
  have hK : Measurable[ℱ k] (cumulant μ ℱ Y s k) := by
    refine Finset.measurable_sum _ fun t ht => ?_
    have htk : t < k := Finset.mem_range.1 ht
    exact (Real.measurable_log.comp
      ((stronglyMeasurable_condExp.mono (ℱ.mono htk.le)).measurable))
  exact Real.measurable_exp.comp ((hS.const_mul s).sub hK)

/-- The exponential martingale at time `k ≤ n` is a.e. bounded by `exp (2 |s| b k)`. -/
lemma Increments.expMart_le [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
    {k : ℕ} (hk : k ≤ n) : ∀ᵐ ω ∂μ, expMart μ ℱ Y s k ω ≤ Real.exp (2 * (|s| * b) * k) := by
  have hall : ∀ᵐ ω ∂μ, ∀ t ∈ Finset.range k, -(|s| * b) ≤ Real.log (condMgf μ ℱ Y s t ω) := by
    refine (Filter.eventually_all_finset _).2 fun t ht => ?_
    have htn : t < n := lt_of_lt_of_le (Finset.mem_range.1 ht) hk
    filter_upwards [h.condMgf_ge s htn] with ω hω
    exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hω)).2 hω
  filter_upwards [hall] with ω hω
  unfold expMart
  refine Real.exp_le_exp.2 ?_
  have h1 : s * ∑ t ∈ Finset.range k, Y t ω ≤ k * (|s| * b) := by
    calc s * ∑ t ∈ Finset.range k, Y t ω = ∑ t ∈ Finset.range k, s * Y t ω := by
          rw [Finset.mul_sum]
      _ ≤ ∑ t ∈ Finset.range k, |s| * b := by
          refine Finset.sum_le_sum fun t ht => ?_
          have htn : t < n := lt_of_lt_of_le (Finset.mem_range.1 ht) hk
          calc s * Y t ω ≤ |s * Y t ω| := le_abs_self _
            _ = |s| * |Y t ω| := abs_mul _ _
            _ ≤ |s| * b := mul_le_mul_of_nonneg_left (h.abs_le t htn ω) (abs_nonneg _)
      _ = k * (|s| * b) := by simp
  have h2 : -(k * (|s| * b)) ≤ cumulant μ ℱ Y s k ω := by
    calc -(k * (|s| * b)) = ∑ t ∈ Finset.range k, -(|s| * b) := by simp
      _ ≤ cumulant μ ℱ Y s k ω := Finset.sum_le_sum hω
  linarith

/-- The exponential martingale at time `k ≤ n` is integrable. -/
lemma Increments.integrable_expMart [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    (s : ℝ) {k : ℕ} (hk : k ≤ n) : Integrable (expMart μ ℱ Y s k) μ := by
  refine Integrable.of_bound (C := Real.exp (2 * (|s| * b) * k)) ?_ ?_
  · exact ((h.measurable_expMart s hk).mono (ℱ.le k) le_rfl).aestronglyMeasurable
  · filter_upwards [h.expMart_le s hk] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (expMart_pos μ ℱ Y s k ω)]
    exact hω

/-- One step of the exponential martingale, as a multiplicative update. -/
lemma Increments.expMart_succ_ae [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
    {k : ℕ} (hk : k < n) : ∀ᵐ ω ∂μ, expMart μ ℱ Y s (k + 1) ω
      = expMart μ ℱ Y s k ω * (condMgf μ ℱ Y s k ω)⁻¹ * Real.exp (s * Y k ω) := by
  filter_upwards [h.condMgf_ge s hk] with ω hω
  have hpos : 0 < condMgf μ ℱ Y s k ω := lt_of_lt_of_le (Real.exp_pos _) hω
  unfold expMart cumulant
  rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
  simp only [sub_eq_add_neg, neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hpos]
  ring

/-- The exponential martingale has expectation one at every time `k ≤ n`. -/
lemma Increments.integral_expMart [IsProbabilityMeasure μ] (h : Increments μ ℱ Y b n)
    (s : ℝ) {k : ℕ} (hk : k ≤ n) : ∫ ω, expMart μ ℱ Y s k ω ∂μ = 1 := by
  induction k with
  | zero =>
      simp [expMart, cumulant]
  | succ k ih =>
      have hkn : k < n := hk
      have hf : StronglyMeasurable[ℱ k]
          (fun ω => expMart μ ℱ Y s k ω * (condMgf μ ℱ Y s k ω)⁻¹) := by
        refine StronglyMeasurable.mul ?_ ?_
        · exact (h.measurable_expMart s hkn.le).stronglyMeasurable
        · exact (stronglyMeasurable_condExp (m := ℱ k)).measurable.inv.stronglyMeasurable
      have hbound : ∀ᵐ ω ∂μ,
          ‖expMart μ ℱ Y s k ω * (condMgf μ ℱ Y s k ω)⁻¹‖
            ≤ Real.exp (2 * (|s| * b) * k) * Real.exp (|s| * b) := by
        filter_upwards [h.expMart_le s hkn.le, h.condMgf_ge s hkn] with ω h1 h2
        have hpos : 0 < condMgf μ ℱ Y s k ω := lt_of_lt_of_le (Real.exp_pos _) h2
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (expMart_pos μ ℱ Y s k ω).le
          (inv_nonneg.2 hpos.le))]
        refine mul_le_mul h1 ?_ (inv_nonneg.2 hpos.le) (Real.exp_pos _).le
        calc (condMgf μ ℱ Y s k ω)⁻¹ ≤ (Real.exp (-(|s| * b)))⁻¹ :=
              inv_anti₀ (Real.exp_pos _) h2
          _ = Real.exp (|s| * b) := by rw [← Real.exp_neg, neg_neg]
      have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ) (ℱ.le k) hf
        (h.integrable_exp s hkn) _ hbound
      have hstep : ∀ᵐ ω ∂μ, (μ[(fun ω => expMart μ ℱ Y s k ω * (condMgf μ ℱ Y s k ω)⁻¹) *
          fun ω => Real.exp (s * Y k ω) | ℱ k]) ω = expMart μ ℱ Y s k ω := by
        filter_upwards [hpull, h.condMgf_ge s hkn] with ω h1 h2
        have hpos : 0 < condMgf μ ℱ Y s k ω := lt_of_lt_of_le (Real.exp_pos _) h2
        rw [h1, Pi.mul_apply]
        show expMart μ ℱ Y s k ω * (condMgf μ ℱ Y s k ω)⁻¹ * condMgf μ ℱ Y s k ω = _
        rw [mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
      calc ∫ ω, expMart μ ℱ Y s (k + 1) ω ∂μ
          = ∫ ω, ((fun ω => expMart μ ℱ Y s k ω * (condMgf μ ℱ Y s k ω)⁻¹) *
              fun ω => Real.exp (s * Y k ω)) ω ∂μ :=
            integral_congr_ae (h.expMart_succ_ae s hkn)
        _ = ∫ ω, (μ[(fun ω => expMart μ ℱ Y s k ω * (condMgf μ ℱ Y s k ω)⁻¹) *
              fun ω => Real.exp (s * Y k ω) | ℱ k]) ω ∂μ :=
            (integral_condExp (ℱ.le k)).symm
        _ = ∫ ω, expMart μ ℱ Y s k ω ∂μ := integral_congr_ae hstep
        _ = 1 := ih hkn.le

variable (μ ℱ Y) in
/-- The square of the exponential martingale at `s` is the exponential martingale at `2 s` times
`exp (K(2s) - 2 K(s))`. -/
lemma expMart_sq (s : ℝ) (n : ℕ) (ω : Ω) :
    expMart μ ℱ Y s n ω ^ 2
      = expMart μ ℱ Y (2 * s) n ω
        * Real.exp (cumulant μ ℱ Y (2 * s) n ω - 2 * cumulant μ ℱ Y s n ω) := by
  unfold expMart
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The square of the exponential martingale is integrable. -/
lemma Increments.integrable_expMart_sq [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    (s : ℝ) : Integrable (fun ω => expMart μ ℱ Y s n ω ^ 2) μ := by
  refine Integrable.of_bound (C := Real.exp (2 * (|s| * b) * n) ^ 2) ?_ ?_
  · exact ((h.measurable_expMart s le_rfl).mono (ℱ.le n) le_rfl).pow_const 2 |>.aestronglyMeasurable
  · filter_upwards [h.expMart_le s le_rfl] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (expMart_pos μ ℱ Y s n ω).le hω 2

/-- Second-moment bound for the exponential martingale: if the total conditional variance is at
most `v` then `E Z(s)² ≤ exp (6 s² v)`, for `|s| b ≤ 1 / 2`. -/
lemma Increments.integral_expMart_sq_le [IsProbabilityMeasure μ]
    (h : Increments μ ℱ Y b n) (s : ℝ) (hsb : |s| * b ≤ 1 / 2) {v : ℝ}
    (hv : ∀ᵐ ω ∂μ, varSum μ ℱ Y n ω ≤ v) :
    ∫ ω, expMart μ ℱ Y s n ω ^ 2 ∂μ ≤ Real.exp (6 * s ^ 2 * v) := by
  have hint : Integrable (fun ω => Real.exp (6 * s ^ 2 * v) * expMart μ ℱ Y (2 * s) n ω) μ :=
    (h.integrable_expMart (2 * s) le_rfl).const_mul _
  calc ∫ ω, expMart μ ℱ Y s n ω ^ 2 ∂μ
      ≤ ∫ ω, Real.exp (6 * s ^ 2 * v) * expMart μ ℱ Y (2 * s) n ω ∂μ := by
        refine integral_mono_ae (h.integrable_expMart_sq s) hint ?_
        filter_upwards [h.cumulant_two_mul_sub_le s hsb, hv] with ω h1 h2
        rw [expMart_sq, mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (expMart_pos μ ℱ Y (2 * s) n ω).le
        refine Real.exp_le_exp.2 (h1.trans ?_)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp (6 * s ^ 2 * v) := by
        rw [integral_const_mul, h.integral_expMart (2 * s) le_rfl, mul_one]

/-- The conditional expectation of a linear combination of three integrable functions. -/
lemma condExp_lin3 [IsFiniteMeasure μ] {m : MeasurableSpace Ω} {f₁ f₂ f₃ : Ω → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (a₁ a₂ a₃ : ℝ) :
    μ[fun ω => a₁ * f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω | m]
      =ᵐ[μ] fun ω => a₁ * μ[f₁ | m] ω + a₂ * μ[f₂ | m] ω + a₃ * μ[f₃ | m] ω := by
  have e1 : μ[fun ω => a₁ * f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω | m]
      =ᵐ[μ] μ[fun ω => a₁ * f₁ ω + a₂ * f₂ ω | m] + μ[fun ω => a₃ * f₃ ω | m] :=
    condExp_add ((h₁.const_mul a₁).add (h₂.const_mul a₂)) (h₃.const_mul a₃) m
  have e2 : μ[fun ω => a₁ * f₁ ω + a₂ * f₂ ω | m]
      =ᵐ[μ] μ[fun ω => a₁ * f₁ ω | m] + μ[fun ω => a₂ * f₂ ω | m] :=
    condExp_add (h₁.const_mul a₁) (h₂.const_mul a₂) m
  have e3 : μ[fun ω => a₁ * f₁ ω | m] =ᵐ[μ] fun ω => a₁ * μ[f₁ | m] ω :=
    condExp_smul (μ := μ) a₁ f₁ m
  have e4 : μ[fun ω => a₂ * f₂ ω | m] =ᵐ[μ] fun ω => a₂ * μ[f₂ | m] ω :=
    condExp_smul (μ := μ) a₂ f₂ m
  have e5 : μ[fun ω => a₃ * f₃ ω | m] =ᵐ[μ] fun ω => a₃ * μ[f₃ | m] ω :=
    condExp_smul (μ := μ) a₃ f₃ m
  filter_upwards [e1, e2, e3, e4, e5] with ω h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5]

variable (μ ℱ) in
/-- The conditional covariance `E(Y_t Y'_t | ℱ t)` of two increments. -/
noncomputable def condCov (Y Y' : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  μ[fun ω => Y t ω * Y' t ω | ℱ t]

variable (μ ℱ) in
/-- The total conditional covariance `Σ_{t<n} E(Y_t Y'_t | ℱ t)`. -/
noncomputable def covSum (Y Y' : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ t ∈ Finset.range n, condCov μ ℱ Y Y' t ω

/-- The sum of two families of increments is again a family of centred bounded increments, with
twice the bound. -/
lemma Increments.add [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ} (h : Increments μ ℱ Y b n)
    (h' : Increments μ ℱ Y' b n) : Increments μ ℱ (Y + Y') (2 * b) n where
  nonneg := by have := h.nonneg; linarith
  stronglyMeasurable t ht := (h.stronglyMeasurable t ht).add (h'.stronglyMeasurable t ht)
  abs_le t ht ω := by
    have := abs_add_le (Y t ω) (Y' t ω)
    have h1 := h.abs_le t ht ω
    have h2 := h'.abs_le t ht ω
    show |Y t ω + Y' t ω| ≤ 2 * b
    linarith
  condExp_eq_zero t ht := by
    have e := condExp_add (μ := μ) (h.integrable ht) (h'.integrable ht) (ℱ t)
    filter_upwards [e, h.condExp_eq_zero t ht, h'.condExp_eq_zero t ht] with ω h1 h2 h3
    simp only [Pi.zero_apply] at h2 h3 ⊢
    show μ[Y t + Y' t | ℱ t] ω = 0
    rw [h1, Pi.add_apply, h2, h3, add_zero]

/-- The product of two bounded increments is integrable. -/
lemma Increments.integrable_mul [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
    (h : Increments μ ℱ Y b n) (h' : Increments μ ℱ Y' b n) {t : ℕ} (ht : t < n) :
    Integrable (fun ω => Y t ω * Y' t ω) μ := by
  refine Integrable.of_bound (C := b * b) ?_ ?_
  · exact ((h.measurable ht).mul (h'.measurable ht)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (h.abs_le t ht ω) (h'.abs_le t ht ω) (abs_nonneg _) h.nonneg

/-- The conditional variance of a sum is the sum of the variances plus twice the covariance. -/
lemma Increments.condVar_add_ae [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
    (h : Increments μ ℱ Y b n) (h' : Increments μ ℱ Y' b n) {t : ℕ} (ht : t < n) :
    ∀ᵐ ω ∂μ, condVar μ ℱ (Y + Y') t ω
      = condVar μ ℱ Y t ω + condVar μ ℱ Y' t ω + 2 * condCov μ ℱ Y Y' t ω := by
  have e := condExp_lin3 (μ := μ) (m := ℱ t) (h.integrable_sq ht) (h'.integrable_sq ht)
    (h.integrable_mul h' ht) 1 1 2
  have hfun : (fun ω => (Y + Y') t ω ^ 2)
      = fun ω => 1 * Y t ω ^ 2 + 1 * Y' t ω ^ 2 + 2 * (Y t ω * Y' t ω) := by
    funext ω
    show (Y t ω + Y' t ω) ^ 2 = _
    ring
  filter_upwards [e] with ω hω
  unfold condVar condCov
  rw [hfun, hω]
  ring

/-- The conditional variance of a sum is at most twice the sum of the conditional variances. -/
lemma Increments.condVar_add_le [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
    (h : Increments μ ℱ Y b n) (h' : Increments μ ℱ Y' b n) {t : ℕ} (ht : t < n) :
    ∀ᵐ ω ∂μ, condVar μ ℱ (Y + Y') t ω
      ≤ 2 * condVar μ ℱ Y t ω + 2 * condVar μ ℱ Y' t ω := by
  have e := condExp_lin3 (μ := μ) (m := ℱ t) (h.integrable_sq ht) (h'.integrable_sq ht)
    (h.integrable_mul h' ht) 2 2 0
  have hg : Integrable (fun ω => 2 * Y t ω ^ 2 + 2 * Y' t ω ^ 2 + 0 * (Y t ω * Y' t ω)) μ :=
    (((h.integrable_sq ht).const_mul 2).add ((h'.integrable_sq ht).const_mul 2)).add
      ((h.integrable_mul h' ht).const_mul 0)
  have hmono := condExp_mono (m := ℱ t) ((h.add h').integrable_sq ht) hg
    (Filter.Eventually.of_forall fun ω => by
      show (Y t ω + Y' t ω) ^ 2 ≤ 2 * Y t ω ^ 2 + 2 * Y' t ω ^ 2 + 0 * (Y t ω * Y' t ω)
      linarith [sq_nonneg (Y t ω - Y' t ω)])
  filter_upwards [e, hmono] with ω h1 h2
  unfold condVar
  rw [h1] at h2
  simpa using h2

/-- The total conditional variance of a sum splits into the variances and the covariance. -/
lemma Increments.varSum_add_ae [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
    (h : Increments μ ℱ Y b n) (h' : Increments μ ℱ Y' b n) :
    ∀ᵐ ω ∂μ, varSum μ ℱ (Y + Y') n ω
      = varSum μ ℱ Y n ω + varSum μ ℱ Y' n ω + 2 * covSum μ ℱ Y Y' n ω := by
  have hall := (Filter.eventually_all_finset (Finset.range n)).2 fun t ht =>
    h.condVar_add_ae h' (Finset.mem_range.1 ht)
  filter_upwards [hall] with ω hω
  unfold varSum covSum
  rw [Finset.sum_congr rfl hω, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The total conditional variance of a sum is at most twice the sum of the variances. -/
lemma Increments.varSum_add_le [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
    (h : Increments μ ℱ Y b n) (h' : Increments μ ℱ Y' b n) :
    ∀ᵐ ω ∂μ, varSum μ ℱ (Y + Y') n ω
      ≤ 2 * varSum μ ℱ Y n ω + 2 * varSum μ ℱ Y' n ω := by
  have hall := (Filter.eventually_all_finset (Finset.range n)).2 fun t ht =>
    h.condVar_add_le h' (Finset.mem_range.1 ht)
  filter_upwards [hall] with ω hω
  unfold varSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hω

/-- For two families of increments with total conditional variances at most `v`, the cumulant of
the sum exceeds the sum of the cumulants by at most `s²` times the total conditional covariance
plus an error `20 v |s|³ b`, when `|s| b ≤ 1 / 4`. -/
lemma Increments.cumulant_add_sub_le [IsProbabilityMeasure μ] {Y' : ℕ → Ω → ℝ}
    (h : Increments μ ℱ Y b n) (h' : Increments μ ℱ Y' b n) (s : ℝ) (hsb : |s| * b ≤ 1 / 4)
    {v : ℝ} (hv : ∀ᵐ ω ∂μ, varSum μ ℱ Y n ω ≤ v) (hv' : ∀ᵐ ω ∂μ, varSum μ ℱ Y' n ω ≤ v) :
    ∀ᵐ ω ∂μ, cumulant μ ℱ (Y + Y') s n ω - cumulant μ ℱ Y s n ω - cumulant μ ℱ Y' s n ω
      ≤ s ^ 2 * covSum μ ℱ Y Y' n ω + 20 * v * (|s| ^ 3 * b) := by
  have h2 := h.add h'
  have hsb2 : |s| * (2 * b) ≤ 1 / 2 := by linarith
  filter_upwards [h2.abs_cumulant_sub_le s hsb2, h.abs_cumulant_sub_le s (by linarith),
    h'.abs_cumulant_sub_le s (by linarith), h.varSum_add_ae h', h.varSum_add_le h', hv, hv']
    with ω c2 c1 c1' e le2 hv hv'
  have hA : 0 ≤ |s| ^ 3 * b := mul_nonneg (by positivity) h.nonneg
  have c2' := (_root_.abs_le.mp c2).2
  have c1l := (_root_.abs_le.mp c1).1
  have c1l' := (_root_.abs_le.mp c1').1
  set V'' := varSum μ ℱ (Y + Y') n ω
  set V := varSum μ ℱ Y n ω
  set V' := varSum μ ℱ Y' n ω
  have m1 : |s| ^ 3 * b * V'' ≤ |s| ^ 3 * b * (4 * v) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have m2 : |s| ^ 3 * b * V ≤ |s| ^ 3 * b * v := mul_le_mul_of_nonneg_left hv hA
  have m3 : |s| ^ 3 * b * V' ≤ |s| ^ 3 * b * v := mul_le_mul_of_nonneg_left hv' hA
  have q1 : 2 * |s| ^ 3 * (2 * b) * V'' = 4 * (|s| ^ 3 * b * V'') := by ring
  have q2 : 2 * |s| ^ 3 * b * V = 2 * (|s| ^ 3 * b * V) := by ring
  have q3 : 2 * |s| ^ 3 * b * V' = 2 * (|s| ^ 3 * b * V') := by ring
  rw [q1] at c2'
  rw [q2] at c1l
  rw [q3] at c1l'
  have q4 : s ^ 2 / 2 * V'' = s ^ 2 / 2 * V + s ^ 2 / 2 * V' + s ^ 2 * covSum μ ℱ Y Y' n ω := by
    rw [e]; ring
  have q5 : |s| ^ 3 * b * (4 * v) = 4 * (|s| ^ 3 * b * v) := by ring
  have q6 : 20 * v * (|s| ^ 3 * b) = 20 * (|s| ^ 3 * b * v) := by ring
  rw [q5] at m1
  rw [q6]
  linarith

end ExpMart

end CERW.Generic.Martingale.ExpMart
