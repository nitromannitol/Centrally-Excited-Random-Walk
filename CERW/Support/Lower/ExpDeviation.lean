import CERW.Model
import CERW.Generic.Kernel.ScalarTaylor
import CERW.Generic.Martingale.FreedmanEvent
import LatticeProb.Prob.PaleyZygmund

/-!
# Exponential deviations of martingales

Lemma 9.1 (`lem:exp-deviation`) of the paper. Let `S⁰, …, S^{m-1}` be martingales started at `0`
with increments at most `b`, whose brackets at time `n` lie in `[c₀, C₀]` on an event `E` of
probability at least `1 - α`. For `C ≤ β` with `β b ≤ c`, part (i) bounds each of the tails
`P(± Sⁱ_n ≥ c β)` from below by `e^{-C β²} / 4 - α`, and part (ii) bounds the probability that
every `Sⁱ_n` stays below `c β`, when the cross brackets are at most `δ` on `E`.

The proof follows the paper. Each martingale is stopped predictably when its bracket exceeds
`2 C₀` (`stopInc`). For the stopped increments `Y_t`, the exponential martingale is
`Z(s) = exp (s Σ_t Y_t - K(s))`, where `K(s) = Σ_t log E(e^{s Y_t} | ℱ t)` is the cumulant. It
has mean one (`Increments.integral_expMart`), and second moment at most `exp (6 s² v)` when the
total conditional variance is at most `v` (`Increments.integral_expMart_sq_le`). Part (i) is the
Paley-Zygmund inequality for `Z` (`tail_lower`). Part (ii) bounds `E(Z_i Z_j)` by
`1 + O(β² δ + β³ b) + e^{C β²} √α` (`integral_expMart_mul_le`) and applies Chebyshev's
inequality to the average of the `Z_i` (`measureReal_sum_le_half`, `prob_max_lt_le`).
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower

/-- Second-order Taylor bound for the exponential. -/
private lemma abs_exp_sub_quad_le {x : ℝ} (hx : |x| ≤ 1) :
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
private structure Increments (Y : ℕ → Ω → ℝ) (b : ℝ) (n : ℕ) : Prop where
  nonneg : 0 ≤ b
  stronglyMeasurable : ∀ t < n, StronglyMeasurable[ℱ (t + 1)] (Y t)
  abs_le : ∀ t < n, ∀ ω, |Y t ω| ≤ b
  condExp_eq_zero : ∀ t < n, μ[Y t | ℱ t] =ᵐ[μ] 0

/-- The conditional moment generating function `E(e^{s Y_t} | ℱ t)`. -/
private noncomputable def condMgf (Y : ℕ → Ω → ℝ) (s : ℝ) (t : ℕ) : Ω → ℝ :=
  μ[fun ω => Real.exp (s * Y t ω) | ℱ t]

/-- The conditional variance `E(Y_t² | ℱ t)`. -/
private noncomputable def condVar (Y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  μ[fun ω => Y t ω ^ 2 | ℱ t]

/-- The cumulant `K(s) = Σ_{t<n} log E(e^{s Y_t} | ℱ t)`. -/
private noncomputable def cumulant (Y : ℕ → Ω → ℝ) (s : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ t ∈ Finset.range n, Real.log (condMgf μ ℱ Y s t ω)

/-- The total conditional variance `Σ_{t<n} E(Y_t² | ℱ t)`. -/
private noncomputable def varSum (Y : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ t ∈ Finset.range n, condVar μ ℱ Y t ω

/-- The exponential martingale `exp (s Σ_{t<n} Y_t - K(s))`. -/
private noncomputable def expMart (Y : ℕ → Ω → ℝ) (s : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => Real.exp (s * ∑ t ∈ Finset.range n, Y t ω - cumulant μ ℱ Y s n ω)

variable {μ ℱ} {Y : ℕ → Ω → ℝ} {b : ℝ} {n : ℕ}

/-- Each increment `Y t`, `t < n`, is measurable. -/
private lemma Increments.measurable (h : Increments μ ℱ Y b n) {t : ℕ} (ht : t < n) :
    Measurable (Y t) :=
  ((h.stronglyMeasurable t ht).mono (ℱ.le (t + 1))).measurable

/-- The exponential of a bounded increment is integrable. -/
private lemma Increments.integrable_exp [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
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
private lemma Increments.integrable_sq [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    {t : ℕ} (ht : t < n) : Integrable (fun ω => Y t ω ^ 2) μ := by
  refine Integrable.of_bound (C := b ^ 2) ?_ ?_
  · exact ((h.measurable ht).pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h.abs_le t ht ω) 2

/-- A bounded increment is integrable. -/
private lemma Increments.integrable [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    {t : ℕ} (ht : t < n) : Integrable (Y t) μ := by
  refine Integrable.of_bound (C := b) (h.measurable ht).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact h.abs_le t ht ω

/-- A conditional expectation of a function bounded below is bounded below a.e. -/
private lemma ae_le_condExp_of_le [IsFiniteMeasure μ] {f : Ω → ℝ} {t : ℕ}
    (hf : Integrable f μ) {a : ℝ} (ha : ∀ ω, a ≤ f ω) : ∀ᵐ ω ∂μ, a ≤ μ[f | ℱ t] ω := by
  have h := condExp_mono (m := ℱ t) (integrable_const a) hf (Filter.Eventually.of_forall ha)
  filter_upwards [h] with ω hω
  rwa [condExp_const (ℱ.le t)] at hω

/-- A conditional expectation of a function bounded above is bounded above a.e. -/
private lemma ae_condExp_le_of_le [IsFiniteMeasure μ] {f : Ω → ℝ} {t : ℕ}
    (hf : Integrable f μ) {a : ℝ} (ha : ∀ ω, f ω ≤ a) : ∀ᵐ ω ∂μ, μ[f | ℱ t] ω ≤ a := by
  have h := condExp_mono (m := ℱ t) hf (integrable_const a) (Filter.Eventually.of_forall ha)
  filter_upwards [h] with ω hω
  rwa [condExp_const (ℱ.le t)] at hω


/-- The conditional moment generating function is bounded below by `exp (-(|s| b))` a.e. -/
private lemma Increments.condMgf_ge [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
    {t : ℕ} (ht : t < n) : ∀ᵐ ω ∂μ, Real.exp (-(|s| * b)) ≤ condMgf μ ℱ Y s t ω := by
  refine ae_le_condExp_of_le (h.integrable_exp s ht) fun ω => Real.exp_le_exp.mpr ?_
  have h1 : |s * Y t ω| ≤ |s| * b := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h.abs_le t ht ω) (abs_nonneg _)
  linarith [neg_abs_le (s * Y t ω)]

/-- The conditional moment generating function is bounded above by `exp (|s| b)` a.e. -/
private lemma Increments.condMgf_le [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
    {t : ℕ} (ht : t < n) : ∀ᵐ ω ∂μ, condMgf μ ℱ Y s t ω ≤ Real.exp (|s| * b) := by
  refine ae_condExp_le_of_le (h.integrable_exp s ht) fun ω => Real.exp_le_exp.mpr ?_
  have h1 : |s * Y t ω| ≤ |s| * b := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h.abs_le t ht ω) (abs_nonneg _)
  linarith [le_abs_self (s * Y t ω)]

/-- The conditional variance is nonnegative a.e. -/
private lemma Increments.condVar_nonneg [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    {t : ℕ} (ht : t < n) : ∀ᵐ ω ∂μ, 0 ≤ condVar μ ℱ Y t ω :=
  ae_le_condExp_of_le (h.integrable_sq ht) fun _ => sq_nonneg _

/-- The conditional variance is at most `b ^ 2` a.e. -/
private lemma Increments.condVar_le [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    {t : ℕ} (ht : t < n) : ∀ᵐ ω ∂μ, condVar μ ℱ Y t ω ≤ b ^ 2 := by
  refine ae_condExp_le_of_le (h.integrable_sq ht) fun ω => ?_
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h.abs_le t ht ω) 2

/-- Conditional expectation of a quadratic polynomial in a bounded variable. -/
private lemma condExp_quad [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
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
private lemma abs_exp_mul_sub_quad_le {s y b : ℝ} (hy : |y| ≤ b) (hsb : |s| * b ≤ 1) :
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
private lemma Increments.abs_condMgf_sub_le [IsProbabilityMeasure μ] (h : Increments μ ℱ Y b n)
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
private lemma Increments.abs_log_condMgf_sub_le [IsProbabilityMeasure μ]
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
private lemma Increments.abs_cumulant_sub_le [IsProbabilityMeasure μ]
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
private lemma Increments.cumulant_two_mul_sub_le [IsProbabilityMeasure μ]
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
private lemma expMart_pos (s : ℝ) (k : ℕ) (ω : Ω) : 0 < expMart μ ℱ Y s k ω :=
  Real.exp_pos _

/-- The exponential martingale at time `k ≤ n` is `ℱ k`-measurable. -/
private lemma Increments.measurable_expMart (h : Increments μ ℱ Y b n) (s : ℝ) {k : ℕ}
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
private lemma Increments.expMart_le [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
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
private lemma Increments.integrable_expMart [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    (s : ℝ) {k : ℕ} (hk : k ≤ n) : Integrable (expMart μ ℱ Y s k) μ := by
  refine Integrable.of_bound (C := Real.exp (2 * (|s| * b) * k)) ?_ ?_
  · exact ((h.measurable_expMart s hk).mono (ℱ.le k) le_rfl).aestronglyMeasurable
  · filter_upwards [h.expMart_le s hk] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (expMart_pos μ ℱ Y s k ω)]
    exact hω

/-- One step of the exponential martingale, as a multiplicative update. -/
private lemma Increments.expMart_succ_ae [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n) (s : ℝ)
    {k : ℕ} (hk : k < n) : ∀ᵐ ω ∂μ, expMart μ ℱ Y s (k + 1) ω
      = expMart μ ℱ Y s k ω * (condMgf μ ℱ Y s k ω)⁻¹ * Real.exp (s * Y k ω) := by
  filter_upwards [h.condMgf_ge s hk] with ω hω
  have hpos : 0 < condMgf μ ℱ Y s k ω := lt_of_lt_of_le (Real.exp_pos _) hω
  unfold expMart cumulant
  rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
  simp only [sub_eq_add_neg, neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hpos]
  ring

/-- The exponential martingale has expectation one at every time `k ≤ n`. -/
private lemma Increments.integral_expMart [IsProbabilityMeasure μ] (h : Increments μ ℱ Y b n)
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
private lemma expMart_sq (s : ℝ) (n : ℕ) (ω : Ω) :
    expMart μ ℱ Y s n ω ^ 2
      = expMart μ ℱ Y (2 * s) n ω
        * Real.exp (cumulant μ ℱ Y (2 * s) n ω - 2 * cumulant μ ℱ Y s n ω) := by
  unfold expMart
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The square of the exponential martingale is integrable. -/
private lemma Increments.integrable_expMart_sq [IsFiniteMeasure μ] (h : Increments μ ℱ Y b n)
    (s : ℝ) : Integrable (fun ω => expMart μ ℱ Y s n ω ^ 2) μ := by
  refine Integrable.of_bound (C := Real.exp (2 * (|s| * b) * n) ^ 2) ?_ ?_
  · exact ((h.measurable_expMart s le_rfl).mono (ℱ.le n) le_rfl).pow_const 2 |>.aestronglyMeasurable
  · filter_upwards [h.expMart_le s le_rfl] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (expMart_pos μ ℱ Y s n ω).le hω 2

/-- Second-moment bound for the exponential martingale: if the total conditional variance is at
most `v` then `E Z(s)² ≤ exp (6 s² v)`, for `|s| b ≤ 1 / 2`. -/
private lemma Increments.integral_expMart_sq_le [IsProbabilityMeasure μ]
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
private lemma condExp_lin3 [IsFiniteMeasure μ] {m : MeasurableSpace Ω} {f₁ f₂ f₃ : Ω → ℝ}
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
private noncomputable def condCov (Y Y' : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  μ[fun ω => Y t ω * Y' t ω | ℱ t]

variable (μ ℱ) in
/-- The total conditional covariance `Σ_{t<n} E(Y_t Y'_t | ℱ t)`. -/
private noncomputable def covSum (Y Y' : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ t ∈ Finset.range n, condCov μ ℱ Y Y' t ω

/-- The sum of two families of increments is again a family of centred bounded increments, with
twice the bound. -/
private lemma Increments.add [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ} (h : Increments μ ℱ Y b n)
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
private lemma Increments.integrable_mul [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
    (h : Increments μ ℱ Y b n) (h' : Increments μ ℱ Y' b n) {t : ℕ} (ht : t < n) :
    Integrable (fun ω => Y t ω * Y' t ω) μ := by
  refine Integrable.of_bound (C := b * b) ?_ ?_
  · exact ((h.measurable ht).mul (h'.measurable ht)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (h.abs_le t ht ω) (h'.abs_le t ht ω) (abs_nonneg _) h.nonneg

/-- The conditional variance of a sum is the sum of the variances plus twice the covariance. -/
private lemma Increments.condVar_add_ae [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
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
private lemma Increments.condVar_add_le [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
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
private lemma Increments.varSum_add_ae [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
    (h : Increments μ ℱ Y b n) (h' : Increments μ ℱ Y' b n) :
    ∀ᵐ ω ∂μ, varSum μ ℱ (Y + Y') n ω
      = varSum μ ℱ Y n ω + varSum μ ℱ Y' n ω + 2 * covSum μ ℱ Y Y' n ω := by
  have hall := (Filter.eventually_all_finset (Finset.range n)).2 fun t ht =>
    h.condVar_add_ae h' (Finset.mem_range.1 ht)
  filter_upwards [hall] with ω hω
  unfold varSum covSum
  rw [Finset.sum_congr rfl hω, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- The total conditional variance of a sum is at most twice the sum of the variances. -/
private lemma Increments.varSum_add_le [IsFiniteMeasure μ] {Y' : ℕ → Ω → ℝ}
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
private lemma Increments.cumulant_add_sub_le [IsProbabilityMeasure μ] {Y' : ℕ → Ω → ℝ}
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

section Stopping

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)

/-- The covariance `E((S_{t+1} - S_t)(T_{t+1} - T_t) | ℱ t)` of the increments at time `t`. -/
private noncomputable def incCov (S T : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  μ[fun ω => (S (t + 1) ω - S t ω) * (T (t + 1) ω - T t ω) | ℱ t]

/-- The bracket is the sum of the increment covariances. -/
private lemma predBracket_apply (S T : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    CERW.predBracket μ ℱ S T n ω = ∑ t ∈ Finset.range n, incCov μ ℱ S T t ω := by
  simp only [CERW.predBracket, incCov, Finset.sum_apply]

/-- The predictable gate: one while the bracket at the next time is at most `L`, then zero. -/
private noncomputable def gate (S : ℕ → Ω → ℝ) (L : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if CERW.predBracket μ ℱ S S (t + 1) ω ≤ L then 1 else 0

/-- The increments of `S`, stopped predictably when its bracket exceeds `L`. -/
private noncomputable def stopInc (S : ℕ → Ω → ℝ) (L : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  gate μ ℱ S L t ω * (S (t + 1) ω - S t ω)

variable {μ ℱ}

/-- The gate is nonnegative. -/
private lemma gate_nonneg (S : ℕ → Ω → ℝ) (L : ℝ) (t : ℕ) (ω : Ω) : 0 ≤ gate μ ℱ S L t ω := by
  unfold gate; split_ifs <;> norm_num

/-- The gate is at most `1`. -/
private lemma gate_le_one (S : ℕ → Ω → ℝ) (L : ℝ) (t : ℕ) (ω : Ω) : gate μ ℱ S L t ω ≤ 1 := by
  unfold gate; split_ifs <;> norm_num

/-- The gate is idempotent. -/
private lemma gate_mul_self (S : ℕ → Ω → ℝ) (L : ℝ) (t : ℕ) (ω : Ω) :
    gate μ ℱ S L t ω * gate μ ℱ S L t ω = gate μ ℱ S L t ω := by
  unfold gate; split_ifs <;> norm_num

/-- The gate is `1` when the bracket at the next time is at most `L`. -/
private lemma gate_eq_one {S : ℕ → Ω → ℝ} {L : ℝ} {t : ℕ} {ω : Ω}
    (h : CERW.predBracket μ ℱ S S (t + 1) ω ≤ L) : gate μ ℱ S L t ω = 1 := by
  unfold gate; rw [if_pos h]

/-- The bracket at time `t + 1` is `ℱ t`-measurable. -/
private lemma stronglyMeasurable_predBracket_succ (S T : ℕ → Ω → ℝ) (t : ℕ) :
    StronglyMeasurable[ℱ t] (CERW.predBracket μ ℱ S T (t + 1)) := by
  have h : CERW.predBracket μ ℱ S T (t + 1)
      = fun ω => ∑ s ∈ Finset.range (t + 1), incCov μ ℱ S T s ω := by
    funext ω; exact predBracket_apply μ ℱ S T (t + 1) ω
  rw [h]
  refine Finset.stronglyMeasurable_fun_sum _ fun s hs => ?_
  have hst : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
  exact (stronglyMeasurable_condExp (m := ℱ s)).mono (ℱ.mono hst)

/-- The gate at time `t` is `ℱ t`-measurable. -/
private lemma stronglyMeasurable_gate (S : ℕ → Ω → ℝ) (L : ℝ) (t : ℕ) :
    StronglyMeasurable[ℱ t] (gate μ ℱ S L t) := by
  refine Measurable.stronglyMeasurable ?_
  exact Measurable.ite
    (measurableSet_le (stronglyMeasurable_predBracket_succ S S t).measurable measurable_const)
    measurable_const measurable_const

/-- Summing the increment covariances of a predictably stopped process gives at most `L`. -/
private lemma sum_gate_mul_incCov_le (S : ℕ → Ω → ℝ) {L : ℝ} (hL : 0 ≤ L) (ω : Ω) :
    ∀ k : ℕ, (∀ t < k, 0 ≤ incCov μ ℱ S S t ω) →
      ∑ t ∈ Finset.range k, gate μ ℱ S L t ω * incCov μ ℱ S S t ω ≤ L := by
  intro k
  induction k with
  | zero => intro _; simpa using hL
  | succ k ih =>
    intro hp
    have ih' := ih fun t ht => hp t (Nat.lt_succ_of_lt ht)
    rw [Finset.sum_range_succ]
    by_cases hk : CERW.predBracket μ ℱ S S (k + 1) ω ≤ L
    · rw [gate_eq_one hk, one_mul]
      calc ∑ t ∈ Finset.range k, gate μ ℱ S L t ω * incCov μ ℱ S S t ω + incCov μ ℱ S S k ω
          ≤ ∑ t ∈ Finset.range k, incCov μ ℱ S S t ω + incCov μ ℱ S S k ω := by
            refine add_le_add (Finset.sum_le_sum fun t ht => ?_) le_rfl
            have := hp t (lt_trans (Finset.mem_range.1 ht) (Nat.lt_succ_self k))
            calc gate μ ℱ S L t ω * incCov μ ℱ S S t ω ≤ 1 * incCov μ ℱ S S t ω :=
                  mul_le_mul_of_nonneg_right (gate_le_one S L t ω) this
              _ = incCov μ ℱ S S t ω := one_mul _
        _ = CERW.predBracket μ ℱ S S (k + 1) ω := by
            rw [predBracket_apply, Finset.sum_range_succ]
        _ ≤ L := hk
    · have h0 : gate μ ℱ S L k ω = 0 := by unfold gate; rw [if_neg hk]
      rw [h0, zero_mul, add_zero]
      exact ih'

variable {S T : ℕ → Ω → ℝ}

/-- The stopped increments of a martingale with bounded increments are centred, bounded and
measurable. -/
private lemma increments_stopInc [IsFiniteMeasure μ] (hS : Martingale S ℱ μ) (L : ℝ) {b : ℝ}
    (hb : 0 ≤ b) {n : ℕ} (hinc : ∀ t < n, ∀ ω, |S (t + 1) ω - S t ω| ≤ b) :
    Increments μ ℱ (stopInc μ ℱ S L) b n where
  nonneg := hb
  stronglyMeasurable t _ := by
    have hg := (stronglyMeasurable_gate (μ := μ) (ℱ := ℱ) S L t).mono (ℱ.mono (Nat.le_succ t))
    have h1 := hS.stronglyMeasurable (t + 1)
    have h0 := (hS.stronglyMeasurable t).mono (ℱ.mono (Nat.le_succ t))
    exact hg.mul (h1.sub h0)
  abs_le t ht ω := by
    unfold stopInc
    rw [abs_mul, abs_of_nonneg (gate_nonneg S L t ω)]
    calc gate μ ℱ S L t ω * |S (t + 1) ω - S t ω| ≤ 1 * b :=
          mul_le_mul (gate_le_one S L t ω) (hinc t ht ω) (abs_nonneg _) zero_le_one
      _ = b := one_mul b
  condExp_eq_zero t ht := by
    have hint : Integrable (fun ω => S (t + 1) ω - S t ω) μ :=
      (hS.integrable (t + 1)).sub (hS.integrable t)
    have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ) (ℱ.le t)
      (stronglyMeasurable_gate (μ := μ) (ℱ := ℱ) S L t) hint 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gate_nonneg S L t ω)]
        exact gate_le_one S L t ω)
    filter_upwards [hpull, CERW.Generic.Martingale.condExp_increment_eq_zero hS t] with ω h1 h2
    simp only [Pi.zero_apply] at h2 ⊢
    show μ[fun ω => gate μ ℱ S L t ω * (S (t + 1) ω - S t ω) | ℱ t] ω = 0
    have h3 : μ[(gate μ ℱ S L t) * fun ω => S (t + 1) ω - S t ω | ℱ t] ω = 0 := by
      rw [h1, Pi.mul_apply, h2, mul_zero]
    exact h3

/-- The product of the increments of two martingales with bounded increments is integrable. -/
private lemma integrable_incr_mul [IsFiniteMeasure μ] (hS : Martingale S ℱ μ)
    (hT : Martingale T ℱ μ) {b b' : ℝ} (hb : 0 ≤ b) {n t : ℕ} (ht : t < n)
    (hincS : ∀ t < n, ∀ ω, |S (t + 1) ω - S t ω| ≤ b)
    (hincT : ∀ t < n, ∀ ω, |T (t + 1) ω - T t ω| ≤ b') :
    Integrable (fun ω => (S (t + 1) ω - S t ω) * (T (t + 1) ω - T t ω)) μ := by
  refine Integrable.of_bound (C := b * b') ?_ ?_
  · exact ((((hS.stronglyMeasurable (t + 1)).mono (ℱ.le (t + 1))).sub
      ((hS.stronglyMeasurable t).mono (ℱ.le t))).mul
      (((hT.stronglyMeasurable (t + 1)).mono (ℱ.le (t + 1))).sub
      ((hT.stronglyMeasurable t).mono (ℱ.le t)))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hincS t ht ω) (hincT t ht ω) (abs_nonneg _) hb

/-- The conditional variance of the increments of a process is nonnegative a.e. -/
private lemma incCov_self_nonneg (S : ℕ → Ω → ℝ) (t : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ incCov μ ℱ S S t ω :=
  condExp_nonneg (f := fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω))
    (Filter.Eventually.of_forall fun _ => mul_self_nonneg _)

/-- The conditional covariance of two predictably stopped increments. -/
private lemma condCov_stopInc_ae [IsFiniteMeasure μ] (hS : Martingale S ℱ μ)
    (hT : Martingale T ℱ μ) (L : ℝ) {b b' : ℝ} (hb : 0 ≤ b) {n t : ℕ} (ht : t < n)
    (hincS : ∀ t < n, ∀ ω, |S (t + 1) ω - S t ω| ≤ b)
    (hincT : ∀ t < n, ∀ ω, |T (t + 1) ω - T t ω| ≤ b') :
    ∀ᵐ ω ∂μ, condCov μ ℱ (stopInc μ ℱ S L) (stopInc μ ℱ T L) t ω
      = gate μ ℱ S L t ω * gate μ ℱ T L t ω * incCov μ ℱ S T t ω := by
  have hint := integrable_incr_mul hS hT hb ht hincS hincT
  have hg : StronglyMeasurable[ℱ t]
      (fun ω => gate μ ℱ S L t ω * gate μ ℱ T L t ω) :=
    (stronglyMeasurable_gate (μ := μ) (ℱ := ℱ) S L t).mul
      (stronglyMeasurable_gate (μ := μ) (ℱ := ℱ) T L t)
  have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ) (ℱ.le t) hg hint 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gate_nonneg S L t ω)
        (gate_nonneg T L t ω))]
      calc gate μ ℱ S L t ω * gate μ ℱ T L t ω ≤ 1 * 1 :=
            mul_le_mul (gate_le_one S L t ω) (gate_le_one T L t ω) (gate_nonneg T L t ω)
              zero_le_one
        _ = 1 := one_mul 1)
  have hfun : (fun ω => stopInc μ ℱ S L t ω * stopInc μ ℱ T L t ω)
      = (fun ω => gate μ ℱ S L t ω * gate μ ℱ T L t ω) *
        fun ω => (S (t + 1) ω - S t ω) * (T (t + 1) ω - T t ω) := by
    funext ω; simp only [stopInc, Pi.mul_apply]; ring
  filter_upwards [hpull] with ω h1
  unfold condCov
  rw [hfun, h1, Pi.mul_apply]
  rfl

variable (μ ℱ) in
/-- The total conditional variance is the total conditional covariance of a family with itself. -/
private lemma varSum_eq_covSum (Y : ℕ → Ω → ℝ) (n : ℕ) :
    varSum μ ℱ Y n = covSum μ ℱ Y Y n := by
  funext ω
  unfold varSum covSum condVar condCov
  simp only [sq]

/-- The total conditional variance of a stopped martingale is at most the stopping level. -/
private lemma varSum_stopInc_le [IsFiniteMeasure μ] (hS : Martingale S ℱ μ) {L b : ℝ}
    (hL : 0 ≤ L) (hb : 0 ≤ b) {n : ℕ} (hinc : ∀ t < n, ∀ ω, |S (t + 1) ω - S t ω| ≤ b) :
    ∀ᵐ ω ∂μ, varSum μ ℱ (stopInc μ ℱ S L) n ω ≤ L := by
  have hall := (Filter.eventually_all_finset (Finset.range n)).2 fun t ht =>
    (condCov_stopInc_ae hS hS L hb (Finset.mem_range.1 ht) hinc hinc).and
      (incCov_self_nonneg (μ := μ) (ℱ := ℱ) S t)
  filter_upwards [hall] with ω hω
  rw [varSum_eq_covSum]
  have hp : ∀ t < n, 0 ≤ incCov μ ℱ S S t ω := fun t ht => (hω t (Finset.mem_range.2 ht)).2
  calc covSum μ ℱ (stopInc μ ℱ S L) (stopInc μ ℱ S L) n ω
      = ∑ t ∈ Finset.range n, gate μ ℱ S L t ω * incCov μ ℱ S S t ω := by
        unfold covSum
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [(hω t ht).1, gate_mul_self]
    _ ≤ L := sum_gate_mul_incCov_le S hL ω n hp

/-- On an event where the bracket at time `n` is at most `L`, the gate stays open up to time
`n`. -/
private lemma ae_gate_eq_one [IsFiniteMeasure μ] (S : ℕ → Ω → ℝ) {L : ℝ} {n : ℕ} {E : Set Ω}
    (hE : ∀ᵐ ω ∂μ, ω ∈ E → CERW.predBracket μ ℱ S S n ω ≤ L) :
    ∀ᵐ ω ∂μ, ω ∈ E → ∀ t < n, gate μ ℱ S L t ω = 1 := by
  have hall := (Filter.eventually_all_finset (Finset.range n)).2 fun t _ =>
    incCov_self_nonneg (μ := μ) (ℱ := ℱ) S t
  filter_upwards [hall, hE] with ω h1 h2 hωE t ht
  refine gate_eq_one ?_
  rw [predBracket_apply]
  refine le_trans ?_ (predBracket_apply μ ℱ S S n ω ▸ h2 hωE)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun s hs _ => h1 s hs
  intro s hs
  exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hs) ht)

/-- Where the gate stays open, the stopped increments add up to the martingale. -/
private lemma sum_stopInc_eq {L : ℝ} (hS0 : ∀ ω, S 0 ω = 0) {n : ℕ} {ω : Ω}
    (hg : ∀ t < n, gate μ ℱ S L t ω = 1) :
    ∑ t ∈ Finset.range n, stopInc μ ℱ S L t ω = S n ω := by
  have h : ∑ t ∈ Finset.range n, stopInc μ ℱ S L t ω
      = ∑ t ∈ Finset.range n, (S (t + 1) ω - S t ω) :=
    Finset.sum_congr rfl fun t ht => by
      unfold stopInc; rw [hg t (Finset.mem_range.1 ht), one_mul]
  rw [h, Finset.sum_range_sub (fun t => S t ω) n, hS0, sub_zero]

/-- Where the gates of both martingales stay open, the total conditional covariance of the
stopped increments is the bracket. -/
private lemma covSum_stopInc_eq [IsFiniteMeasure μ] (hS : Martingale S ℱ μ)
    (hT : Martingale T ℱ μ) (L : ℝ) {b b' : ℝ} (hb : 0 ≤ b) {n : ℕ}
    (hincS : ∀ t < n, ∀ ω, |S (t + 1) ω - S t ω| ≤ b)
    (hincT : ∀ t < n, ∀ ω, |T (t + 1) ω - T t ω| ≤ b') :
    ∀ᵐ ω ∂μ, (∀ t < n, gate μ ℱ S L t ω = 1) → (∀ t < n, gate μ ℱ T L t ω = 1) →
      covSum μ ℱ (stopInc μ ℱ S L) (stopInc μ ℱ T L) n ω = CERW.predBracket μ ℱ S T n ω := by
  have hall := (Filter.eventually_all_finset (Finset.range n)).2 fun t ht =>
    condCov_stopInc_ae hS hT L hb (Finset.mem_range.1 ht) hincS hincT
  filter_upwards [hall] with ω hω hgS hgT
  rw [predBracket_apply]
  unfold covSum
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [hω t ht, hgS t (Finset.mem_range.1 ht), hgT t (Finset.mem_range.1 ht), one_mul, one_mul]

/-- Monotonicity of the real-valued measure for sets included up to a null set. -/
private lemma measureReal_le_of_ae_imp [IsFiniteMeasure μ] {A B : Set Ω}
    (h : ∀ᵐ ω ∂μ, ω ∈ A → ω ∈ B) : μ.real A ≤ μ.real B :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h)

/-- Where the exponential martingale of the stopped increments exceeds `1 / 2`, the martingale
has deviated by `c β`, on an event where its bracket is at least `c₀`. -/
private lemma ae_deviation [IsProbabilityMeasure μ] {c₀ C₀ c b β : ℝ} {n : ℕ}
    (hc₀ : 0 < c₀) (hcC : c₀ ≤ C₀) (hc1 : c ≤ 1 / 8) (hc2 : c ≤ c₀ / 8) (hb : 0 < b)
    (hS : Martingale S ℱ μ) (hS0 : ∀ ω, S 0 ω = 0)
    (hinc : ∀ t < n, ∀ ω, |S (t + 1) ω - S t ω| ≤ b) {E : Set Ω}
    (hbr : ∀ᵐ ω ∂μ, ω ∈ E →
      c₀ ≤ CERW.predBracket μ ℱ S S n ω ∧ CERW.predBracket μ ℱ S S n ω ≤ C₀)
    (hβ : 8 * Real.log 2 / c₀ ≤ β) (hβ1 : 1 ≤ β) (hβb : β * b ≤ c) :
    ∀ᵐ ω ∂μ, ω ∈ E → 1 / 2 < expMart μ ℱ (stopInc μ ℱ S (2 * C₀)) β n ω → c * β ≤ S n ω := by
  have hL : 0 ≤ 2 * C₀ := by linarith
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ1
  have hsb : |β| * b ≤ 1 / 8 := by rw [abs_of_pos hβ0]; linarith
  have hY := increments_stopInc (μ := μ) hS (2 * C₀) hb.le hinc
  set Y := stopInc μ ℱ S (2 * C₀) with hYdef
  have hgate := ae_gate_eq_one (ℱ := ℱ) S (L := 2 * C₀) (n := n) (E := E)
    (by filter_upwards [hbr] with ω hω hωE; exact (hω hωE).2.trans (by linarith))
  have hcov := covSum_stopInc_eq hS hS (2 * C₀) hb.le hinc hinc
  have hcum := hY.abs_cumulant_sub_le β (by linarith)
  filter_upwards [hbr, hgate, hcov, hcum] with ω h1 h2 h3 h4 hωE hZω
  have hg := h2 hωE
  have hsum := sum_stopInc_eq (μ := μ) (ℱ := ℱ) (L := 2 * C₀) hS0 hg
  have hV : varSum μ ℱ Y n ω = CERW.predBracket μ ℱ S S n ω := by
    rw [varSum_eq_covSum]; exact h3 hg hg
  obtain ⟨hV1, _⟩ := h1 hωE
  have hK := (_root_.abs_le.mp h4).1
  rw [hV] at hK
  set V := CERW.predBracket μ ℱ S S n ω with hVdef
  have hβ2 : 0 ≤ β ^ 2 * V := mul_nonneg (sq_nonneg _) (by linarith)
  have hcb : β * b ≤ 1 / 8 := by linarith
  have e1 : 2 * |β| ^ 3 * b * V = 2 * (β ^ 2 * V) * (β * b) := by
    rw [abs_of_pos hβ0]; ring
  have e2 : 2 * (β ^ 2 * V) * (β * b) ≤ 2 * (β ^ 2 * V) * (1 / 8) :=
    mul_le_mul_of_nonneg_left hcb (by linarith)
  have hKlow : β ^ 2 * c₀ / 4 ≤ cumulant μ ℱ Y β n ω := by
    have : β ^ 2 * c₀ ≤ β ^ 2 * V := mul_le_mul_of_nonneg_left hV1 (sq_nonneg _)
    rw [e1] at hK
    linarith
  have hZ' : -Real.log 2 < β * S n ω - cumulant μ ℱ Y β n ω := by
    have h5 : Real.log (1 / 2) < β * S n ω - cumulant μ ℱ Y β n ω := by
      refine (Real.log_lt_iff_lt_exp (by norm_num)).2 ?_
      have : 1 / 2 < Real.exp (β * ∑ t ∈ Finset.range n, Y t ω - cumulant μ ℱ Y β n ω) :=
        hZω
      rwa [hsum] at this
    rwa [one_div, Real.log_inv] at h5
  have hlog2 : Real.log 2 ≤ β * c₀ / 8 := by
    rw [div_le_iff₀ hc₀] at hβ
    linarith
  have hlog2' : Real.log 2 ≤ β ^ 2 * c₀ / 8 := by
    have : β * c₀ / 8 ≤ β ^ 2 * c₀ / 8 := by
      have := mul_le_mul_of_nonneg_right hβ1 (mul_nonneg hβ0.le hc₀.le)
      linarith
    linarith
  have hS1 : β * (β * c₀ / 8) < β * S n ω := by linarith
  have hS2 : β * c₀ / 8 < S n ω := (mul_lt_mul_iff_right₀ hβ0).1 hS1
  have hS3 : c * β ≤ β * c₀ / 8 := by
    have := mul_le_mul_of_nonneg_right hc2 hβ0.le
    linarith
  exact hS3.trans hS2.le

/-- **Lower deviation bound for one martingale.** The deviation of a martingale with bracket in
`[c₀, C₀]` on an event `E` of probability at least `1 - α` reaches `c β` with probability at
least `exp (-(12 C₀ β²)) / 4 - α`. -/
private lemma tail_lower [IsProbabilityMeasure μ] {c₀ C₀ c b α β : ℝ} {n : ℕ}
    (hc₀ : 0 < c₀) (hcC : c₀ ≤ C₀) (hc1 : c ≤ 1 / 8) (hc2 : c ≤ c₀ / 8) (hb : 0 < b)
    (hS : Martingale S ℱ μ) (hS0 : ∀ ω, S 0 ω = 0)
    (hinc : ∀ t < n, ∀ ω, |S (t + 1) ω - S t ω| ≤ b)
    {E : Set Ω} (hE : MeasurableSet E) (hEα : 1 - α ≤ (μ E).toReal)
    (hbr : ∀ᵐ ω ∂μ, ω ∈ E →
      c₀ ≤ CERW.predBracket μ ℱ S S n ω ∧ CERW.predBracket μ ℱ S S n ω ≤ C₀)
    (hβ : 8 * Real.log 2 / c₀ ≤ β) (hβ1 : 1 ≤ β) (hβb : β * b ≤ c) :
    Real.exp (-(12 * C₀ * β ^ 2)) / 4 - α ≤ (μ {ω | c * β ≤ S n ω}).toReal := by
  have hL : 0 ≤ 2 * C₀ := by linarith
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ1
  have hsb : |β| * b ≤ 1 / 8 := by rw [abs_of_pos hβ0]; linarith
  have hY := increments_stopInc (μ := μ) hS (2 * C₀) hb.le hinc
  set Y := stopInc μ ℱ S (2 * C₀) with hYdef
  have hvar : ∀ᵐ ω ∂μ, varSum μ ℱ Y n ω ≤ 2 * C₀ := varSum_stopInc_le hS hL hb.le hinc
  have hZ1 : ∫ ω, expMart μ ℱ Y β n ω ∂μ = 1 := hY.integral_expMart β le_rfl
  have hZ2 : ∫ ω, expMart μ ℱ Y β n ω ^ 2 ∂μ ≤ Real.exp (12 * C₀ * β ^ 2) := by
    have := hY.integral_expMart_sq_le β (by linarith) hvar
    rwa [show 6 * β ^ 2 * (2 * C₀) = 12 * C₀ * β ^ 2 by ring] at this
  have hPZ := LatticeProb.paley_zygmund μ
    (((hY.measurable_expMart β le_rfl).mono (ℱ.le n) le_rfl))
    (fun ω => (expMart_pos μ ℱ Y β n ω).le) (hY.integrable_expMart_sq β) (θ := 1 / 2)
    (by norm_num) (by norm_num)
  rw [hZ1] at hPZ
  set P := μ.real {ω | 1 / 2 * 1 < expMart μ ℱ Y β n ω} with hP
  have hP0 : 0 ≤ P := measureReal_nonneg
  have hPlow : Real.exp (-(12 * C₀ * β ^ 2)) / 4 ≤ P := by
    have h1 : 1 / 4 ≤ Real.exp (12 * C₀ * β ^ 2) * P := by
      have h2 := mul_le_mul_of_nonneg_right hZ2 hP0
      linarith [hPZ, h2]
    calc Real.exp (-(12 * C₀ * β ^ 2)) / 4
        = Real.exp (-(12 * C₀ * β ^ 2)) * (1 / 4) := by ring
      _ ≤ Real.exp (-(12 * C₀ * β ^ 2)) * (Real.exp (12 * C₀ * β ^ 2) * P) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = P := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hincl : ∀ᵐ ω ∂μ, ω ∈ {ω | 1 / 2 * 1 < expMart μ ℱ Y β n ω} →
      ω ∈ {ω | c * β ≤ S n ω} ∪ Eᶜ := by
    filter_upwards [ae_deviation hc₀ hcC hc1 hc2 hb hS hS0 hinc hbr hβ hβ1 hβb] with ω hω hZω
    by_cases hωE : ω ∈ E
    · exact Or.inl (hω hωE (by simpa using hZω))
    · exact Or.inr hωE
  have hEc : μ.real Eᶜ ≤ α := by
    rw [measureReal_compl hE, probReal_univ]
    have : μ.real E = (μ E).toReal := rfl
    linarith
  calc Real.exp (-(12 * C₀ * β ^ 2)) / 4 - α ≤ P - μ.real Eᶜ := by linarith
    _ ≤ μ.real {ω | c * β ≤ S n ω} := by
        have h1 := measureReal_le_of_ae_imp hincl
        have h2 := measureReal_union_le (μ := μ) {ω | c * β ≤ S n ω} Eᶜ
        linarith

end Stopping

section Averaging

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Chebyshev bound for a sum of second-moment variables.** If `m` measurable variables have
mean `1`, second moments at most `D`, and pairwise products with mean at most `1 + X`, then their
sum is at most `m / 2` with probability at most `4 (D / m + X)`. -/
private lemma measureReal_sum_le_half [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (Z : Fin m → Ω → ℝ) (hmeas : ∀ i, Measurable (Z i)) (hint : ∀ i, Integrable (Z i) μ)
    (hint2 : ∀ i, Integrable (fun ω => Z i ω ^ 2) μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 1)
    {D X : ℝ} (hD : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ D) (hX : 0 ≤ X)
    (hcross : ∀ i j, i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ ≤ 1 + X) :
    μ.real {ω | ∑ i, Z i ω ≤ (m : ℝ) / 2} ≤ 4 * (D / m + X) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hprod : ∀ i j, Integrable (fun ω => Z i ω * Z j ω) μ := by
    intro i j
    have hB : Integrable (fun ω => 1 / 2 * (Z i ω ^ 2 + Z j ω ^ 2)) μ :=
      ((hint2 i).add (hint2 j)).const_mul (1 / 2)
    refine Integrable.mono' hB ((hmeas i).mul (hmeas j)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, _root_.abs_le]
    constructor
    · linarith [sq_nonneg (Z i ω + Z j ω)]
    · linarith [sq_nonneg (Z i ω - Z j ω)]
  set U : Ω → ℝ := fun ω => ∑ i, Z i ω with hU
  have hUint : Integrable U μ := integrable_finsetSum _ fun i _ => hint i
  have hUmean : ∫ ω, U ω ∂μ = m := by
    rw [hU, integral_finsetSum _ fun i _ => hint i]
    simp [hmean]
  have hUsq : (fun ω => U ω ^ 2) = fun ω => ∑ i, ∑ j, Z i ω * Z j ω := by
    funext ω; rw [hU, sq, Finset.sum_mul_sum]
  have hUsq_int : Integrable (fun ω => U ω ^ 2) μ := by
    rw [hUsq]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hprod i j
  have hUsq_mean : ∫ ω, U ω ^ 2 ∂μ ≤ m ^ 2 * (1 + X) + m * D := by
    rw [hUsq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hprod i j]
    have hinner : ∀ i, ∫ ω, ∑ j, Z i ω * Z j ω ∂μ ≤ m * (1 + X) + D := by
      intro i
      rw [integral_finsetSum _ fun j _ => hprod i j]
      calc ∑ j, ∫ ω, Z i ω * Z j ω ∂μ
          ≤ ∑ j, ((1 + X) + if j = i then D else 0) := by
            refine Finset.sum_le_sum fun j _ => ?_
            by_cases hji : j = i
            · subst hji
              simp only [if_true]
              have : (fun ω => Z j ω * Z j ω) = fun ω => Z j ω ^ 2 := funext fun ω => (sq _).symm
              rw [this]
              linarith [hD j]
            · simp only [hji, if_false, add_zero]
              exact hcross i j (Ne.symm hji)
        _ = m * (1 + X) + D := by
            rw [Finset.sum_add_distrib]
            simp
            ring
    calc ∑ i, ∫ ω, ∑ j, Z i ω * Z j ω ∂μ ≤ ∑ _i : Fin m, (m * (1 + X) + D) :=
          Finset.sum_le_sum fun i _ => hinner i
      _ = m ^ 2 * (1 + X) + m * D := by simp; ring
  have h1 : Integrable (fun ω => U ω ^ 2 - 2 * m * U ω) μ :=
    hUsq_int.sub (hUint.const_mul _)
  have e : (fun ω => (U ω - m) ^ 2) = fun ω => U ω ^ 2 - 2 * m * U ω + m ^ 2 := by
    funext ω; ring
  have hvarint : Integrable (fun ω => (U ω - m) ^ 2) μ := by
    rw [e]; exact h1.add (integrable_const _)
  have hvar : ∫ ω, (U ω - m) ^ 2 ∂μ ≤ m ^ 2 * X + m * D := by
    rw [e, integral_add h1 (integrable_const _), integral_sub hUsq_int (hUint.const_mul _),
      integral_const_mul, hUmean]
    simp
    linarith [hUsq_mean]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun ω => (U ω - m) ^ 2)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _) hvarint ((m : ℝ) ^ 2 / 4)
  have hincl : {ω | U ω ≤ (m : ℝ) / 2} ⊆ {ω | (m : ℝ) ^ 2 / 4 ≤ (U ω - m) ^ 2} := by
    intro ω hω
    have hω' : U ω ≤ (m : ℝ) / 2 := hω
    show (m : ℝ) ^ 2 / 4 ≤ (U ω - m) ^ 2
    have h : (m : ℝ) / 2 ≤ m - U ω := by linarith
    calc (m : ℝ) ^ 2 / 4 = ((m : ℝ) / 2) ^ 2 := by ring
      _ ≤ (m - U ω) ^ 2 := pow_le_pow_left₀ (by positivity) h 2
      _ = (U ω - m) ^ 2 := by ring
  have hmono := measureReal_mono (μ := μ) hincl
  have hpos : (0 : ℝ) < (m : ℝ) ^ 2 / 4 := by positivity
  refine le_of_mul_le_mul_left ?_ hpos
  calc (m : ℝ) ^ 2 / 4 * μ.real {ω | ∑ i, Z i ω ≤ (m : ℝ) / 2}
      ≤ (m : ℝ) ^ 2 / 4 * μ.real {ω | (m : ℝ) ^ 2 / 4 ≤ (U ω - m) ^ 2} :=
        mul_le_mul_of_nonneg_left hmono hpos.le
    _ ≤ m ^ 2 * X + m * D := hmarkov.trans hvar
    _ = (m : ℝ) ^ 2 / 4 * (4 * (D / m + X)) := by
        field_simp
        ring

end Averaging

section Tails

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
  {S T : ℕ → Ω → ℝ}

/-- The product of the exponential martingales of two stopped martingales is the exponential
martingale of the sum, times the exponential of the excess of the cumulants. -/
private lemma expMart_mul_eq (Y Y' : ℕ → Ω → ℝ) (s : ℝ) (n : ℕ) (ω : Ω) :
    expMart μ ℱ Y s n ω * expMart μ ℱ Y' s n ω
      = expMart μ ℱ (Y + Y') s n ω
        * Real.exp (cumulant μ ℱ (Y + Y') s n ω - cumulant μ ℱ Y s n ω
          - cumulant μ ℱ Y' s n ω) := by
  unfold expMart
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have : ∑ t ∈ Finset.range n, (Y + Y') t ω
      = ∑ t ∈ Finset.range n, Y t ω + ∑ t ∈ Finset.range n, Y' t ω :=
    Finset.sum_add_distrib
  rw [this]
  ring

/-- The square root of `exp (2 y)` is `exp y`. -/
private lemma sqrt_exp_two_mul (y : ℝ) : Real.sqrt (Real.exp (2 * y)) = Real.exp y := by
  rw [show Real.exp (2 * y) = Real.exp y ^ 2 by rw [sq, ← Real.exp_add]; ring_nf]
  exact Real.sqrt_sq (Real.exp_pos y).le

/-- **Second moment of a product of two exponential martingales.** For two martingales with
bracket at most `C₀` on an event `E` of probability at least `1 - α`, and cross bracket at most
`δ` on `E`, the exponential martingales of the stopped increments satisfy
`E(Z_S Z_T) ≤ 1 + A e^A (β² δ + β³ b) + e^{31 C₀ β²} √α`, where `A = 1 + 40 C₀`. -/
private lemma integral_expMart_mul_le [IsProbabilityMeasure μ] {C₀ b δ α β : ℝ} {n : ℕ}
    (hC₀ : 0 < C₀) (hb : 0 < b) (hS : Martingale S ℱ μ) (hT : Martingale T ℱ μ)
    (hincS : ∀ t < n, ∀ ω, |S (t + 1) ω - S t ω| ≤ b)
    (hincT : ∀ t < n, ∀ ω, |T (t + 1) ω - T t ω| ≤ b) {E : Set Ω} (hE : MeasurableSet E)
    (hEα : 1 - α ≤ (μ E).toReal)
    (hbrS : ∀ᵐ ω ∂μ, ω ∈ E → CERW.predBracket μ ℱ S S n ω ≤ C₀)
    (hbrT : ∀ᵐ ω ∂μ, ω ∈ E → CERW.predBracket μ ℱ T T n ω ≤ C₀)
    (hcr : ∀ᵐ ω ∂μ, ω ∈ E → |CERW.predBracket μ ℱ S T n ω| ≤ δ)
    (hβ0 : 0 < β) (hβb : β * b ≤ 1 / 8) (hδ : 0 ≤ δ) (hsmall : β ^ 2 * δ + β ^ 3 * b ≤ 1) :
    ∫ ω, expMart μ ℱ (stopInc μ ℱ S (2 * C₀)) β n ω
        * expMart μ ℱ (stopInc μ ℱ T (2 * C₀)) β n ω ∂μ
      ≤ 1 + ((1 + 40 * C₀) * Real.exp (1 + 40 * C₀) * (β ^ 2 * δ + β ^ 3 * b)
        + Real.exp (31 * C₀ * β ^ 2) * Real.sqrt α) := by
  have hL : 0 ≤ 2 * C₀ := by linarith
  have hsb : |β| * b ≤ 1 / 8 := by rw [abs_of_pos hβ0]; exact hβb
  have hYS := increments_stopInc (μ := μ) hS (2 * C₀) hb.le hincS
  have hYT := increments_stopInc (μ := μ) hT (2 * C₀) hb.le hincT
  set YS := stopInc μ ℱ S (2 * C₀) with hYSdef
  set YT := stopInc μ ℱ T (2 * C₀) with hYTdef
  have hvS : ∀ᵐ ω ∂μ, varSum μ ℱ YS n ω ≤ 2 * C₀ := varSum_stopInc_le hS hL hb.le hincS
  have hvT : ∀ᵐ ω ∂μ, varSum μ ℱ YT n ω ≤ 2 * C₀ := varSum_stopInc_le hT hL hb.le hincT
  have h2 := hYS.add hYT
  have hsb2 : |β| * (2 * b) ≤ 1 / 2 := by linarith
  have hv2 : ∀ᵐ ω ∂μ, varSum μ ℱ (YS + YT) n ω ≤ 8 * C₀ := by
    filter_upwards [hYS.varSum_add_le hYT, hvS, hvT] with ω h1 h2 h3
    linarith
  have hZ2a : ∫ ω, expMart μ ℱ (YS + YT) β n ω ∂μ = 1 := h2.integral_expMart β le_rfl
  have hZ2b : ∫ ω, expMart μ ℱ (YS + YT) β n ω ^ 2 ∂μ ≤ Real.exp (2 * (24 * C₀ * β ^ 2)) := by
    have := h2.integral_expMart_sq_le β hsb2 hv2
    rwa [show 6 * β ^ 2 * (8 * C₀) = 2 * (24 * C₀ * β ^ 2) by ring] at this
  have hgS := ae_gate_eq_one (ℱ := ℱ) S (L := 2 * C₀) (n := n) (E := E)
    (by filter_upwards [hbrS] with ω hω hωE; exact (hω hωE).trans (by linarith))
  have hgT := ae_gate_eq_one (ℱ := ℱ) T (L := 2 * C₀) (n := n) (E := E)
    (by filter_upwards [hbrT] with ω hω hωE; exact (hω hωE).trans (by linarith))
  have hcov := covSum_stopInc_eq hS hT (2 * C₀) hb.le hincS hincT
  have hpair := hYS.cumulant_add_sub_le hYT β (by linarith) hvS hvT
  have hb3 : β ^ 3 * b ≤ β ^ 2 / 8 := by
    have := mul_le_mul_of_nonneg_left hβb (sq_nonneg β)
    calc β ^ 3 * b = β ^ 2 * (β * b) := by ring
      _ ≤ β ^ 2 * (1 / 8) := this
      _ = β ^ 2 / 8 := by ring
  have hb3' : 0 ≤ β ^ 3 * b := by positivity
  set x : ℝ := β ^ 2 * δ + 40 * C₀ * (β ^ 3 * b) with hx
  set ZS := expMart μ ℱ YS β n with hZS
  set ZT := expMart μ ℱ YT β n with hZT
  set Z2 := expMart μ ℱ (YS + YT) β n with hZ2
  set B : Ω → ℝ := Eᶜ.indicator (fun _ => (1 : ℝ)) with hB
  have hZ2pos : ∀ ω, 0 < Z2 ω := fun ω => expMart_pos μ ℱ (YS + YT) β n ω
  have hkey : ∀ᵐ ω ∂μ, ZS ω * ZT ω ≤ Real.exp x * Z2 ω
      + Real.exp (7 * C₀ * β ^ 2) * (Z2 ω * B ω) := by
    filter_upwards [hpair, hYS.varSum_add_ae hYT, hYS.varSum_add_le hYT, hvS, hvT, hgS, hgT, hcov,
      hcr] with ω hp e le hv1 hv2 hg1 hg2 hc hcrω
    have hprod : ZS ω * ZT ω = Z2 ω * Real.exp (cumulant μ ℱ (YS + YT) β n ω
        - cumulant μ ℱ YS β n ω - cumulant μ ℱ YT β n ω) := expMart_mul_eq YS YT β n ω
    rw [abs_of_pos hβ0] at hp
    have hW : covSum μ ℱ YS YT n ω ≤ 2 * C₀ := by linarith
    by_cases hωE : ω ∈ E
    · have hBω : B ω = 0 := by simp [hB, hωE]
      rw [hBω, mul_zero, mul_zero, add_zero, hprod, mul_comm]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hZ2pos ω).le
      have hWδ : covSum μ ℱ YS YT n ω ≤ δ := by
        rw [hc (hg1 hωE) (hg2 hωE)]
        exact (le_abs_self _).trans (hcrω hωE)
      have := mul_le_mul_of_nonneg_left hWδ (sq_nonneg β)
      rw [hx]
      linarith
    · have hBω : B ω = 1 := by simp [hB, hωE]
      rw [hBω, mul_one, hprod]
      have h1 : Z2 ω * Real.exp (cumulant μ ℱ (YS + YT) β n ω - cumulant μ ℱ YS β n ω
          - cumulant μ ℱ YT β n ω) ≤ Z2 ω * Real.exp (7 * C₀ * β ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hZ2pos ω).le
        have h3 := mul_le_mul_of_nonneg_left hW (sq_nonneg β)
        have h4 := mul_le_mul_of_nonneg_left hb3 hC₀.le
        linarith
      have h2 : 0 ≤ Real.exp x * Z2 ω := mul_nonneg (Real.exp_pos _).le (hZ2pos ω).le
      linarith
  have hZSm : Measurable ZS := (hYS.measurable_expMart β le_rfl).mono (ℱ.le n) le_rfl
  have hZTm : Measurable ZT := (hYT.measurable_expMart β le_rfl).mono (ℱ.le n) le_rfl
  have hZ2m : Measurable Z2 := (h2.measurable_expMart β le_rfl).mono (ℱ.le n) le_rfl
  have hBm : Measurable B := measurable_const.indicator hE.compl
  have hZ2int : Integrable Z2 μ := h2.integrable_expMart β le_rfl
  have hB01 : ∀ ω, 0 ≤ B ω ∧ B ω ≤ 1 := by
    intro ω
    by_cases hωE : ω ∈ E <;> simp [hB, hωE]
  have hZ2Bint : Integrable (fun ω => Z2 ω * B ω) μ := by
    refine Integrable.mono' hZ2int (hZ2m.mul hBm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hZ2pos ω).le (hB01 ω).1)]
    calc Z2 ω * B ω ≤ Z2 ω * 1 := mul_le_mul_of_nonneg_left (hB01 ω).2 (hZ2pos ω).le
      _ = Z2 ω := mul_one _
  have hFint : Integrable (fun ω => Real.exp x * Z2 ω
      + Real.exp (7 * C₀ * β ^ 2) * (Z2 ω * B ω)) μ :=
    (hZ2int.const_mul _).add (hZ2Bint.const_mul _)
  have hLint : Integrable (fun ω => ZS ω * ZT ω) μ := by
    refine Integrable.mono' hFint (hZSm.mul hZTm).aestronglyMeasurable ?_
    filter_upwards [hkey] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (expMart_pos μ ℱ YS β n ω).le
      (expMart_pos μ ℱ YT β n ω).le)]
    exact h
  have hmono := integral_mono_ae hLint hFint hkey
  have hFval : ∫ ω, (Real.exp x * Z2 ω + Real.exp (7 * C₀ * β ^ 2) * (Z2 ω * B ω)) ∂μ
      = Real.exp x * ∫ ω, Z2 ω ∂μ + Real.exp (7 * C₀ * β ^ 2) * ∫ ω, Z2 ω * B ω ∂μ := by
    rw [integral_add (hZ2int.const_mul _) (hZ2Bint.const_mul _), integral_const_mul,
      integral_const_mul]
  have hB2 : (fun ω => B ω ^ 2) = B := by
    funext ω
    by_cases hωE : ω ∈ E <;> simp [hB, hωE]
  have hB2int : Integrable (fun ω => B ω ^ 2) μ := by
    rw [hB2]; exact (integrable_const (1 : ℝ)).indicator hE.compl
  have hEc : μ.real Eᶜ ≤ α := by
    rw [measureReal_compl hE, probReal_univ]
    have : μ.real E = (μ E).toReal := rfl
    linarith
  have hCS := LatticeProb.abs_integral_mul_le (P := μ) hZ2m.aestronglyMeasurable
    hBm.aestronglyMeasurable (h2.integrable_expMart_sq β) hB2int
  have hB2val : ∫ ω, B ω ^ 2 ∂μ = μ.real Eᶜ := by
    rw [hB2]
    have := integral_indicator_const (μ := μ) (1 : ℝ) hE.compl
    simpa using this
  have hcross : ∫ ω, Z2 ω * B ω ∂μ ≤ Real.exp (24 * C₀ * β ^ 2) * Real.sqrt α := by
    calc ∫ ω, Z2 ω * B ω ∂μ ≤ |∫ ω, Z2 ω * B ω ∂μ| := le_abs_self _
      _ ≤ Real.sqrt (∫ ω, Z2 ω ^ 2 ∂μ) * Real.sqrt (∫ ω, B ω ^ 2 ∂μ) := hCS
      _ ≤ Real.exp (24 * C₀ * β ^ 2) * Real.sqrt α := by
          rw [hB2val]
          refine mul_le_mul ?_ (Real.sqrt_le_sqrt hEc) (Real.sqrt_nonneg _)
            (Real.exp_pos _).le
          rw [← sqrt_exp_two_mul (24 * C₀ * β ^ 2)]
          exact Real.sqrt_le_sqrt hZ2b
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxA : x ≤ (1 + 40 * C₀) * (β ^ 2 * δ + β ^ 3 * b) := by
    rw [hx]
    have h1 : 0 ≤ β ^ 2 * δ := by positivity
    have h2 := mul_nonneg hC₀.le h1
    linarith
  have hxA' : x ≤ 1 + 40 * C₀ := by
    have : (1 + 40 * C₀) * (β ^ 2 * δ + β ^ 3 * b) ≤ (1 + 40 * C₀) * 1 :=
      mul_le_mul_of_nonneg_left hsmall (by linarith)
    linarith
  have hexp : Real.exp x ≤ 1 + (1 + 40 * C₀) * Real.exp (1 + 40 * C₀)
      * (β ^ 2 * δ + β ^ 3 * b) := by
    have h1 : Real.exp x ≤ 1 + x * Real.exp x := by
      have := Real.add_one_le_exp (-x)
      have h2 := mul_le_mul_of_nonneg_right this (Real.exp_pos x).le
      rw [add_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
      linarith
    have h2 : x * Real.exp x ≤ x * Real.exp (1 + 40 * C₀) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hxA') hx0
    have h3 : x * Real.exp (1 + 40 * C₀)
        ≤ (1 + 40 * C₀) * (β ^ 2 * δ + β ^ 3 * b) * Real.exp (1 + 40 * C₀) :=
      mul_le_mul_of_nonneg_right hxA (Real.exp_pos _).le
    linarith
  have hexp2 : Real.exp (7 * C₀ * β ^ 2) * (Real.exp (24 * C₀ * β ^ 2) * Real.sqrt α)
      = Real.exp (31 * C₀ * β ^ 2) * Real.sqrt α := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  calc ∫ ω, ZS ω * ZT ω ∂μ
      ≤ ∫ ω, (Real.exp x * Z2 ω + Real.exp (7 * C₀ * β ^ 2) * (Z2 ω * B ω)) ∂μ := hmono
    _ = Real.exp x * 1 + Real.exp (7 * C₀ * β ^ 2) * ∫ ω, Z2 ω * B ω ∂μ := by
        rw [hFval, hZ2a]
    _ ≤ Real.exp x * 1 + Real.exp (7 * C₀ * β ^ 2) * (Real.exp (24 * C₀ * β ^ 2) * Real.sqrt α) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcross (Real.exp_pos _).le)
    _ ≤ _ := by rw [hexp2, mul_one]; linarith

/-- **Upper tail for the maximum of a family of martingales.** -/
private lemma prob_max_lt_le [IsProbabilityMeasure μ] {c₀ C₀ c b δ α β : ℝ} {m n : ℕ}
    (hm : 0 < m) (hc₀ : 0 < c₀) (hcC : c₀ ≤ C₀) (hc1 : c ≤ 1 / 8) (hc2 : c ≤ c₀ / 8)
    (hb : 0 < b) {S : Fin m → ℕ → Ω → ℝ} (hS : ∀ i, Martingale (S i) ℱ μ)
    (hS0 : ∀ i ω, S i 0 ω = 0) (hinc : ∀ i, ∀ t < n, ∀ ω, |S i (t + 1) ω - S i t ω| ≤ b)
    {E : Set Ω} (hE : MeasurableSet E) (hEα : 1 - α ≤ (μ E).toReal)
    (hbr : ∀ i, ∀ᵐ ω ∂μ, ω ∈ E → c₀ ≤ CERW.predBracket μ ℱ (S i) (S i) n ω ∧
      CERW.predBracket μ ℱ (S i) (S i) n ω ≤ C₀)
    (hcr : ∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E → |CERW.predBracket μ ℱ (S i) (S j) n ω| ≤ δ)
    (hβ : 8 * Real.log 2 / c₀ ≤ β) (hβ1 : 1 ≤ β) (hβb : β * b ≤ c) (hδ : 0 ≤ δ)
    (hsmall : β ^ 2 * δ + β ^ 3 * b ≤ 1) :
    (μ {ω | ∀ i, S i n ω < c * β}).toReal
      ≤ α + 4 * (Real.exp (12 * C₀ * β ^ 2) / m
        + ((1 + 40 * C₀) * Real.exp (1 + 40 * C₀) * (β ^ 2 * δ + β ^ 3 * b)
          + Real.exp (31 * C₀ * β ^ 2) * Real.sqrt α)) := by
  have hC₀ : 0 < C₀ := lt_of_lt_of_le hc₀ hcC
  have hL : 0 ≤ 2 * C₀ := by linarith
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ1
  have hsb : |β| * b ≤ 1 / 8 := by rw [abs_of_pos hβ0]; linarith
  have hY : ∀ i, Increments μ ℱ (stopInc μ ℱ (S i) (2 * C₀)) b n := fun i =>
    increments_stopInc (hS i) (2 * C₀) hb.le (hinc i)
  set Z : Fin m → Ω → ℝ := fun i => expMart μ ℱ (stopInc μ ℱ (S i) (2 * C₀)) β n with hZ
  have hZm : ∀ i, Measurable (Z i) := fun i =>
    ((hY i).measurable_expMart β le_rfl).mono (ℱ.le n) le_rfl
  have hZint : ∀ i, Integrable (Z i) μ := fun i => (hY i).integrable_expMart β le_rfl
  have hZint2 : ∀ i, Integrable (fun ω => Z i ω ^ 2) μ := fun i =>
    (hY i).integrable_expMart_sq β
  have hZmean : ∀ i, ∫ ω, Z i ω ∂μ = 1 := fun i => (hY i).integral_expMart β le_rfl
  have hZD : ∀ i, ∫ ω, Z i ω ^ 2 ∂μ ≤ Real.exp (12 * C₀ * β ^ 2) := by
    intro i
    have := (hY i).integral_expMart_sq_le β (by linarith)
      (varSum_stopInc_le (hS i) hL hb.le (hinc i))
    rwa [show 6 * β ^ 2 * (2 * C₀) = 12 * C₀ * β ^ 2 by ring] at this
  set X : ℝ := (1 + 40 * C₀) * Real.exp (1 + 40 * C₀) * (β ^ 2 * δ + β ^ 3 * b)
    + Real.exp (31 * C₀ * β ^ 2) * Real.sqrt α with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hZcross : ∀ i j, i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ ≤ 1 + X := by
    intro i j hij
    exact integral_expMart_mul_le hC₀ hb (hS i) (hS j) (hinc i) (hinc j) hE hEα
      (by filter_upwards [hbr i] with ω h hωE; exact (h hωE).2)
      (by filter_upwards [hbr j] with ω h hωE; exact (h hωE).2)
      (hcr i j hij) hβ0 (by linarith) hδ hsmall
  have hsum := measureReal_sum_le_half hm Z hZm hZint hZint2 hZmean hZD hX0 hZcross
  have hall : ∀ᵐ ω ∂μ, ∀ i, ω ∈ E → 1 / 2 < Z i ω → c * β ≤ S i n ω :=
    ae_all_iff.2 fun i => ae_deviation hc₀ hcC hc1 hc2 hb (hS i) (hS0 i) (hinc i) (hbr i)
      hβ hβ1 hβb
  have hincl : ∀ᵐ ω ∂μ, ω ∈ {ω | ∀ i, S i n ω < c * β} →
      ω ∈ Eᶜ ∪ {ω | ∑ i, Z i ω ≤ (m : ℝ) / 2} := by
    filter_upwards [hall] with ω hω hωS
    by_cases hωE : ω ∈ E
    · refine Or.inr ?_
      have hle : ∀ i, Z i ω ≤ 1 / 2 := by
        intro i
        by_contra hcon
        exact absurd (hω i hωE (not_le.1 hcon)) (not_le.2 (hωS i))
      show ∑ i, Z i ω ≤ (m : ℝ) / 2
      calc ∑ i, Z i ω ≤ ∑ _i : Fin m, (1 / 2 : ℝ) := Finset.sum_le_sum fun i _ => hle i
        _ = (m : ℝ) / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    · exact Or.inl hωE
  have hEc : μ.real Eᶜ ≤ α := by
    rw [measureReal_compl hE, probReal_univ]
    have : μ.real E = (μ E).toReal := rfl
    linarith
  have h1 := measureReal_le_of_ae_imp hincl
  have h2 := measureReal_union_le (μ := μ) Eᶜ {ω | ∑ i, Z i ω ≤ (m : ℝ) / 2}
  show μ.real {ω | ∀ i, S i n ω < c * β} ≤ _
  linarith

end Tails

/-- The bracket of the negative of a process with itself is unchanged. -/
private lemma predBracket_neg_neg {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (n : ℕ) :
    CERW.predBracket μ ℱ (-S) (-S) n = CERW.predBracket μ ℱ S S n := by
  unfold CERW.predBracket
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  funext ω
  simp only [Pi.neg_apply]
  ring

/-- A number in `[0, 1]` is at most its square root. -/
private lemma le_sqrt_of_le_one {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) : α ≤ Real.sqrt α := by
  refine Real.le_sqrt_of_sq_le ?_
  calc α ^ 2 = α * α := sq α
    _ ≤ α * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = α := mul_one α

theorem exp_deviation :
    ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (m n : ℕ), 0 < m → 0 < n →
      ∀ b δ α : ℝ, 0 < b → 0 ≤ δ → 0 ≤ α → α ≤ 1 →
      ∀ S : Fin m → ℕ → Ω → ℝ, (∀ i, Martingale (S i) ℱ μ) → (∀ i ω, S i 0 ω = 0) →
        (∀ i, ∀ t < n, ∀ ω, |S i (t + 1) ω - S i t ω| ≤ b) →
      ∀ E : Set Ω, MeasurableSet E → 1 - α ≤ (μ E).toReal →
        (∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
          c₀ ≤ CERW.predBracket μ ℱ (S i) (S i) n ω ∧
            CERW.predBracket μ ℱ (S i) (S i) n ω ≤ C₀) →
      ∀ β : ℝ, C ≤ β → β * b ≤ c →
        (∀ i, Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | c * β ≤ S i n ω}).toReal ∧
          Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | S i n ω ≤ -(c * β)}).toReal) ∧
        ((∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E → |CERW.predBracket μ ℱ (S i) (S j) n ω| ≤ δ) →
          β ^ 2 * δ + β ^ 3 * b ≤ 1 →
          (μ {ω | ∀ i, S i n ω < c * β}).toReal
            ≤ C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * δ + β ^ 3 * b
              + Real.exp (C * β ^ 2) * Real.sqrt α)) := by
  intro c₀ C₀ hc₀ hcC
  have hC₀ : 0 < C₀ := lt_of_lt_of_le hc₀ hcC
  set K : ℝ := (1 + 40 * C₀) * Real.exp (1 + 40 * C₀) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hlog : 0 ≤ 8 * Real.log 2 / c₀ :=
    div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg one_le_two)) hc₀.le
  refine ⟨min (1 / 8) (c₀ / 8), 5 + 4 * K + 31 * C₀ + 8 * Real.log 2 / c₀,
    lt_min (by norm_num) (by linarith), by linarith, ?_⟩
  intro Ω _ μ _ ℱ m n hm hn b δ α hb hδ hα hα1 S hS hS0 hinc E hE hEα hbr β hβC hβb
  set C : ℝ := 5 + 4 * K + 31 * C₀ + 8 * Real.log 2 / c₀ with hC
  set c : ℝ := min (1 / 8) (c₀ / 8) with hc
  have hc1 : c ≤ 1 / 8 := min_le_left _ _
  have hc2 : c ≤ c₀ / 8 := min_le_right _ _
  have hβ1 : 1 ≤ β := by linarith
  have hβ : 8 * Real.log 2 / c₀ ≤ β := by linarith
  have hβ0 : 0 < β := by linarith
  have hexp12 : Real.exp (-(C * β ^ 2)) ≤ Real.exp (-(12 * C₀ * β ^ 2)) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg β)
  refine ⟨fun i => ⟨?_, ?_⟩, fun hcr hsmall => ?_⟩
  · have := tail_lower hc₀ hcC hc1 hc2 hb (hS i) (hS0 i) (hinc i) hE hEα (hbr i) hβ hβ1 hβb
    linarith
  · have hneg : Martingale (-(S i)) ℱ μ := (hS i).neg
    have hbr' : ∀ᵐ ω ∂μ, ω ∈ E → c₀ ≤ CERW.predBracket μ ℱ (-(S i)) (-(S i)) n ω ∧
        CERW.predBracket μ ℱ (-(S i)) (-(S i)) n ω ≤ C₀ := by
      rw [predBracket_neg_neg]
      exact hbr i
    have hinc' : ∀ t < n, ∀ ω, |(-(S i)) (t + 1) ω - (-(S i)) t ω| ≤ b := by
      intro t ht ω
      have := hinc i t ht ω
      simp only [Pi.neg_apply, neg_sub_neg]
      rwa [abs_sub_comm]
    have := tail_lower hc₀ hcC hc1 hc2 hb hneg (fun ω => by simp [hS0 i ω]) hinc' hE hEα hbr'
      hβ hβ1 hβb
    have hset : {ω | c * β ≤ (-(S i)) n ω} = {ω | S i n ω ≤ -(c * β)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Pi.neg_apply]
      exact le_neg
    rw [hset] at this
    linarith
  · have hmax := prob_max_lt_le hm hc₀ hcC hc1 hc2 hb hS hS0 hinc hE hEα hbr hcr hβ hβ1 hβb hδ
      hsmall
    rw [← hK] at hmax
    have hC0 : 0 ≤ C := by linarith
    have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
    have hR1 : 1 ≤ Real.exp (C * β ^ 2) := Real.one_le_exp (mul_nonneg hC0 hβ2)
    have hs0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
    have h12 : Real.exp (12 * C₀ * β ^ 2) ≤ Real.exp (C * β ^ 2) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hβ2)
    have h31 : Real.exp (31 * C₀ * β ^ 2) ≤ Real.exp (C * β ^ 2) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hβ2)
    have hm0 : (0 : ℝ) ≤ (m : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg m)
    have hQ0 : 0 ≤ β ^ 2 * δ + β ^ 3 * b := by positivity
    have hu0 : 0 ≤ (m : ℝ)⁻¹ * Real.exp (C * β ^ 2) := mul_nonneg hm0 (Real.exp_pos _).le
    have hw0 : 0 ≤ Real.exp (C * β ^ 2) * Real.sqrt α := mul_nonneg (Real.exp_pos _).le hs0
    have hαs : α ≤ Real.exp (C * β ^ 2) * Real.sqrt α := by
      calc α ≤ Real.sqrt α := le_sqrt_of_le_one hα hα1
        _ = 1 * Real.sqrt α := (one_mul _).symm
        _ ≤ Real.exp (C * β ^ 2) * Real.sqrt α := mul_le_mul_of_nonneg_right hR1 hs0
    have h4 : Real.exp (12 * C₀ * β ^ 2) / m ≤ (m : ℝ)⁻¹ * Real.exp (C * β ^ 2) := by
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left h12 hm0
    have h5 : Real.exp (31 * C₀ * β ^ 2) * Real.sqrt α
        ≤ Real.exp (C * β ^ 2) * Real.sqrt α := mul_le_mul_of_nonneg_right h31 hs0
    have h6 : 4 * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2)) ≤ C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2)) :=
      mul_le_mul_of_nonneg_right (by linarith) hu0
    have h7 : 4 * K * (β ^ 2 * δ + β ^ 3 * b) ≤ C * (β ^ 2 * δ + β ^ 3 * b) :=
      mul_le_mul_of_nonneg_right (by linarith) hQ0
    have h8 : 5 * (Real.exp (C * β ^ 2) * Real.sqrt α)
        ≤ C * (Real.exp (C * β ^ 2) * Real.sqrt α) :=
      mul_le_mul_of_nonneg_right (by linarith) hw0
    calc (μ {ω | ∀ i, S i n ω < c * β}).toReal
        ≤ α + 4 * (Real.exp (12 * C₀ * β ^ 2) / m
          + (K * (β ^ 2 * δ + β ^ 3 * b) + Real.exp (31 * C₀ * β ^ 2) * Real.sqrt α)) := hmax
      _ ≤ C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * δ + β ^ 3 * b
          + Real.exp (C * β ^ 2) * Real.sqrt α) := by linarith

end CERW.Support.Lower
