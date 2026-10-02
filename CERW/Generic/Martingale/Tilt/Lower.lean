import CERW.Generic.Martingale.Tilt.Statements

/-!
# The lower tail weighted by the exponential martingale

`Z(s) e^{-l (N - c')} = Z(s - l) e^{K(s - l) - K(s) + l c'}`, and the cumulant bound together with
the lower bound on the bracket controls the exponent.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

/-- Real arithmetic of the lower tilt: the exponent after the change of tilt. -/
lemma tilt_lower_arith {Kl Ks V v ρ s l w b : ℝ} (hs : 0 ≤ s) (hl : 0 ≤ l)
    (hsl : 0 ≤ s - l) (hb : 0 ≤ b) (hV1 : v * (1 - ρ) ≤ V) (hV2 : V ≤ v)
    (hKl : Kl - (s - l) ^ 2 / 2 * V ≤ 2 * (s - l) ^ 3 * b * V)
    (hKs : s ^ 2 / 2 * V - Ks ≤ 2 * s ^ 3 * b * V) :
    Kl - Ks + l * (s * v * (1 - ρ) - w)
      ≤ l ^ 2 * v / 2 + 2 * ((s - l) ^ 3 + s ^ 3) * b * v - l * w := by
  have hA : 0 ≤ 2 * ((s - l) ^ 3 + s ^ 3) * b :=
    mul_nonneg (mul_nonneg two_pos.le (add_nonneg (pow_nonneg hsl 3) (pow_nonneg hs 3))) hb
  have h1 : 0 ≤ s * l * (V - v * (1 - ρ)) :=
    mul_nonneg (mul_nonneg hs hl) (sub_nonneg.2 hV1)
  have h2 : l ^ 2 / 2 * V ≤ l ^ 2 / 2 * v :=
    mul_le_mul_of_nonneg_left hV2 (by positivity)
  have h3 : 2 * ((s - l) ^ 3 + s ^ 3) * b * V ≤ 2 * ((s - l) ^ 3 + s ^ 3) * b * v :=
    mul_le_mul_of_nonneg_left hV2 hA
  linarith

/-- The pointwise change of tilt: `Z(s) e^{-l (N - c)} = Z(s - l) e^{K(s - l) - K(s) + l c}`. -/
lemma expMart_mul_exp_neg {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (n : ℕ) (s l c : ℝ) (ω : Ω) :
    expMart μ ℱ Y s n ω * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c))
      = expMart μ ℱ Y (s - l) n ω
        * Real.exp (cumulant μ ℱ Y (s - l) n ω - cumulant μ ℱ Y s n ω + l * c) := by
  unfold expMart
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem tilt_lower : TiltLower.{u} := by
  intro Ω m0 μ _ ℱ Y b n h v ρ s l w hl hls hsb hV
  have hs : 0 ≤ s := hl.trans hls
  have hsl : 0 ≤ s - l := sub_nonneg.2 hls
  have hb : 0 ≤ b := h.nonneg
  have hN : Measurable (fun ω => ∑ t ∈ Finset.range n, Y t ω) :=
    Finset.measurable_sum _ fun t ht => h.measurable (Finset.mem_range.1 ht)
  have hZm : Measurable (expMart μ ℱ Y s n) :=
    (h.measurable_expMart s le_rfl).mono (ℱ.le n) le_rfl
  have hZi : Integrable (expMart μ ℱ Y s n) μ := h.integrable_expMart s le_rfl
  have hZi' : Integrable (expMart μ ℱ Y (s - l) n) μ := h.integrable_expMart (s - l) le_rfl
  have hpos := expMart_pos μ ℱ Y s n
  have hpos' := expMart_pos μ ℱ Y (s - l) n
  set c : ℝ := s * v * (1 - ρ) - w with hc
  set E : ℝ := l ^ 2 * v / 2 + 2 * ((s - l) ^ 3 + s ^ 3) * b * v - l * w with hE
  have hmain : ∀ᵐ ω ∂μ, expMart μ ℱ Y s n ω
      * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c))
        ≤ Real.exp E * expMart μ ℱ Y (s - l) n ω := by
    have hsb1 : |s - l| * b ≤ 1 / 2 := by
      rw [abs_of_nonneg hsl]
      have := mul_le_mul_of_nonneg_right (show s - l ≤ s by linarith) hb
      linarith
    have hsb2 : |s| * b ≤ 1 / 2 := by rwa [abs_of_nonneg hs]
    filter_upwards [h.abs_cumulant_sub_le (s - l) hsb1, h.abs_cumulant_sub_le s hsb2, hV]
      with ω h1 h2 h3
    rw [abs_of_nonneg hsl] at h1
    rw [abs_of_nonneg hs] at h2
    have h5 := (_root_.abs_le.mp h2).1
    have h4 := tilt_lower_arith (w := w) (Ks := cumulant μ ℱ Y s n ω) hs hl hsl hb h3.1 h3.2
      (_root_.abs_le.mp h1).2 (by linarith)
    rw [expMart_mul_exp_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h4) (hpos' ω).le
  have hFm : Measurable (fun ω => expMart μ ℱ Y s n ω
      * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c))) :=
    hZm.mul (Real.measurable_exp.comp ((hN.sub_const c).const_mul (-l)))
  have hFi : Integrable (fun ω => expMart μ ℱ Y s n ω
      * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c))) μ := by
    refine Integrable.mono' (hZi'.const_mul (Real.exp E)) hFm.aestronglyMeasurable ?_
    filter_upwards [hmain] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos ω).le (Real.exp_pos _).le)]
    exact hω
  calc ∫ ω in {ω | ∑ t ∈ Finset.range n, Y t ω ≤ c}, expMart μ ℱ Y s n ω ∂μ
      ≤ ∫ ω in {ω | ∑ t ∈ Finset.range n, Y t ω ≤ c}, expMart μ ℱ Y s n ω
          * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c)) ∂μ := by
        refine setIntegral_mono_on hZi.integrableOn hFi.integrableOn
          (measurableSet_le hN measurable_const) fun ω hω => ?_
        refine le_mul_of_one_le_right (hpos ω).le (Real.one_le_exp ?_)
        exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hl) (sub_nonpos.2 hω)
    _ ≤ ∫ ω, expMart μ ℱ Y s n ω
          * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c)) ∂μ :=
        setIntegral_le_integral hFi (Filter.Eventually.of_forall fun ω =>
          mul_nonneg (hpos ω).le (Real.exp_pos _).le)
    _ ≤ ∫ ω, Real.exp E * expMart μ ℱ Y (s - l) n ω ∂μ :=
        integral_mono_ae hFi (hZi'.const_mul _) hmain
    _ = Real.exp E := by
        rw [integral_const_mul, h.integral_expMart (s - l) le_rfl, mul_one]

end CERW.Generic.Martingale.Tilt
