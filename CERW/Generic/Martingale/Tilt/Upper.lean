import CERW.Generic.Martingale.Tilt.Statements

/-!
# The upper tail weighted by the exponential martingale

`Z(s) e^{l (N - c)} = Z(s + l) e^{K(s + l) - K(s) - l c}`, and the cumulant bound controls the
exponent; the mean of `Z(s + l)` is one.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

/-- The real inequality behind the upper tilt: a cumulant increment bound. -/
lemma tilt_upper_arith {K₁ K₀ V v s l b w : ℝ} (hs : 0 ≤ s) (hl : 0 ≤ l) (hb : 0 ≤ b)
    (h₁ : |K₁ - (s + l) ^ 2 / 2 * V| ≤ 2 * |s + l| ^ 3 * b * V)
    (h₀ : |K₀ - s ^ 2 / 2 * V| ≤ 2 * |s| ^ 3 * b * V) (hV : V ≤ v) :
    K₁ - K₀ - l * (s * v + w)
      ≤ l ^ 2 * v / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b * v - l * w := by
  rw [abs_of_nonneg (add_nonneg hs hl)] at h₁
  rw [abs_of_nonneg hs] at h₀
  have a₁ := (_root_.abs_le.mp h₁).2
  have a₀ := (_root_.abs_le.mp h₀).1
  have hC : 0 ≤ s * l + l ^ 2 / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b := by positivity
  have hCV := mul_le_mul_of_nonneg_left hV hC
  have e : K₁ - K₀ ≤ (s * l + l ^ 2 / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b) * V := by
    linarith
  have e2 : (s * l + l ^ 2 / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b) * v
      = l * (s * v) + (l ^ 2 * v / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b * v) := by ring
  linarith

theorem tilt_upper : TiltUpper.{u} := by
  intro Ω m0 μ _ ℱ Y b n h v s l w hs hl hsl hV
  have hb := h.nonneg
  have hsb : |s + l| * b ≤ 1 / 2 := by
    rw [abs_of_nonneg (add_nonneg hs hl)]; exact hsl
  have hsb0 : |s| * b ≤ 1 / 2 := by
    rw [abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hl) hb).trans hsl
  have hpt : ∀ᵐ ω ∂μ,
      cumulant μ ℱ Y (s + l) n ω - cumulant μ ℱ Y s n ω - l * (s * v + w)
      ≤ l ^ 2 * v / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b * v - l * w := by
    filter_upwards [h.abs_cumulant_sub_le (s + l) hsb, h.abs_cumulant_sub_le s hsb0, hV]
      with ω h₁ h₀ hv
    exact tilt_upper_arith hs hl hb h₁ h₀ hv
  have hN : Measurable (fun ω => ∑ t ∈ Finset.range n, Y t ω) :=
    Finset.measurable_sum _ fun t ht => h.measurable (Finset.mem_range.1 ht)
  have hZ : ∀ r : ℝ, Measurable (expMart μ ℱ Y r n) := fun r =>
    (h.measurable_expMart r le_rfl).mono (ℱ.le n) le_rfl
  have hF_eq : ∀ ω, expMart μ ℱ Y s n ω
      * Real.exp (l * (∑ t ∈ Finset.range n, Y t ω - (s * v + w)))
      = expMart μ ℱ Y (s + l) n ω
        * Real.exp
          (cumulant μ ℱ Y (s + l) n ω - cumulant μ ℱ Y s n ω - l * (s * v + w)) := by
    intro ω
    unfold expMart
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hFmeas : Measurable (fun ω => expMart μ ℱ Y s n ω
      * Real.exp (l * (∑ t ∈ Finset.range n, Y t ω - (s * v + w)))) :=
    (hZ s).mul (Real.measurable_exp.comp ((hN.sub_const _).const_mul l))
  have hFint : Integrable (fun ω => expMart μ ℱ Y s n ω
      * Real.exp (l * (∑ t ∈ Finset.range n, Y t ω - (s * v + w)))) μ := by
    refine Integrable.mono'
      ((h.integrable_expMart (s + l) le_rfl).mul_const
        (Real.exp (l ^ 2 * v / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b * v - l * w)))
      hFmeas.aestronglyMeasurable ?_
    filter_upwards [hpt] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (expMart_pos μ ℱ Y s n ω) (Real.exp_pos _)),
      hF_eq ω]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hω) (expMart_pos μ ℱ Y (s + l) n ω).le
  have hset : MeasurableSet {ω | s * v + w ≤ ∑ t ∈ Finset.range n, Y t ω} :=
    measurableSet_le measurable_const hN
  calc ∫ ω in {ω | s * v + w ≤ ∑ t ∈ Finset.range n, Y t ω},
        expMart μ ℱ Y s n ω ∂μ
      ≤ ∫ ω in {ω | s * v + w ≤ ∑ t ∈ Finset.range n, Y t ω}, expMart μ ℱ Y s n ω
          * Real.exp (l * (∑ t ∈ Finset.range n, Y t ω - (s * v + w))) ∂μ := by
        refine setIntegral_mono_on (h.integrable_expMart s le_rfl).integrableOn
          hFint.integrableOn hset fun ω hω => ?_
        have h1 : 1 ≤ Real.exp (l * (∑ t ∈ Finset.range n, Y t ω - (s * v + w))) :=
          Real.one_le_exp (mul_nonneg hl (sub_nonneg.2 hω))
        exact le_mul_of_one_le_right (expMart_pos μ ℱ Y s n ω).le h1
    _ ≤ ∫ ω, expMart μ ℱ Y s n ω
          * Real.exp (l * (∑ t ∈ Finset.range n, Y t ω - (s * v + w))) ∂μ :=
        setIntegral_le_integral hFint (Filter.Eventually.of_forall fun ω =>
          (mul_pos (expMart_pos μ ℱ Y s n ω) (Real.exp_pos _)).le)
    _ ≤ ∫ ω, expMart μ ℱ Y (s + l) n ω
          * Real.exp (l ^ 2 * v / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b * v - l * w) ∂μ := by
        refine integral_mono_ae hFint ((h.integrable_expMart (s + l) le_rfl).mul_const _) ?_
        filter_upwards [hpt] with ω hω
        rw [hF_eq ω]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hω)
          (expMart_pos μ ℱ Y (s + l) n ω).le
    _ = Real.exp (l ^ 2 * v / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b * v - l * w) := by
        rw [integral_mul_const, h.integral_expMart (s + l) le_rfl, one_mul]

end CERW.Generic.Martingale.Tilt
