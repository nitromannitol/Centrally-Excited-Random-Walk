import CERW.Generic.Martingale.Tilt.LimitStatements
import CERW.Generic.Martingale.Tilt.SharpLowerTail

/-!
# The weighted lower tail on a set

`TiltLower` with the lower bound of the bracket assumed only on a measurable set `W`.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

/-- The lower tail weighted by the exponential martingale, on a set where the bracket is large. -/
theorem tilt_lower_on : TiltLowerOn.{u} := by
  intro Ω m0 μ _ ℱ Y b n h v ρ s l w W hW hl hls hsb hV hVW
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
  have hS : MeasurableSet ({ω | ∑ t ∈ Finset.range n, Y t ω ≤ c} ∩ W) :=
    (measurableSet_le hN measurable_const).inter hW
  have hmain : ∀ᵐ ω ∂μ, ω ∈ W → expMart μ ℱ Y s n ω
      * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c))
        ≤ Real.exp E * expMart μ ℱ Y (s - l) n ω := by
    have hsb1 : |s - l| * b ≤ 1 / 2 := by
      rw [abs_of_nonneg hsl]
      have := mul_le_mul_of_nonneg_right (show s - l ≤ s by linarith) hb
      linarith
    have hsb2 : |s| * b ≤ 1 / 2 := by rwa [abs_of_nonneg hs]
    filter_upwards [h.abs_cumulant_sub_le (s - l) hsb1, h.abs_cumulant_sub_le s hsb2, hV, hVW]
      with ω h1 h2 h3 h4 hωW
    rw [abs_of_nonneg hsl] at h1
    rw [abs_of_nonneg hs] at h2
    have h5 := (_root_.abs_le.mp h2).1
    have h6 := tilt_lower_arith (w := w) (Ks := cumulant μ ℱ Y s n ω) hs hl hsl hb (h4 hωW) h3
      (_root_.abs_le.mp h1).2 (by linarith)
    rw [expMart_mul_exp_neg, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h6) (hpos' ω).le
  have hFm : Measurable (fun ω => expMart μ ℱ Y s n ω
      * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c))) :=
    hZm.mul (Real.measurable_exp.comp ((hN.sub_const c).const_mul (-l)))
  have hFi : IntegrableOn (fun ω => expMart μ ℱ Y s n ω
      * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c)))
        ({ω | ∑ t ∈ Finset.range n, Y t ω ≤ c} ∩ W) μ := by
    refine Integrable.mono' (hZi'.const_mul (Real.exp E)).integrableOn
      hFm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).2 ?_
    filter_upwards [hmain] with ω hω hωS
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos ω).le (Real.exp_pos _).le)]
    exact hω hωS.2
  calc ∫ ω in {ω | ∑ t ∈ Finset.range n, Y t ω ≤ c} ∩ W, expMart μ ℱ Y s n ω ∂μ
      ≤ ∫ ω in {ω | ∑ t ∈ Finset.range n, Y t ω ≤ c} ∩ W, expMart μ ℱ Y s n ω
          * Real.exp (-l * (∑ t ∈ Finset.range n, Y t ω - c)) ∂μ := by
        refine setIntegral_mono_on hZi.integrableOn hFi hS fun ω hω => ?_
        refine le_mul_of_one_le_right (hpos ω).le (Real.one_le_exp ?_)
        exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hl) (sub_nonpos.2 hω.1)
    _ ≤ ∫ ω in {ω | ∑ t ∈ Finset.range n, Y t ω ≤ c} ∩ W,
          Real.exp E * expMart μ ℱ Y (s - l) n ω ∂μ :=
        setIntegral_mono_on_ae hFi (hZi'.const_mul _).integrableOn hS
          (by filter_upwards [hmain] with ω hω hωS using hω hωS.2)
    _ ≤ ∫ ω, Real.exp E * expMart μ ℱ Y (s - l) n ω ∂μ :=
        setIntegral_le_integral (hZi'.const_mul _) (Filter.Eventually.of_forall fun ω =>
          mul_nonneg (Real.exp_pos _).le (hpos' ω).le)
    _ = Real.exp E := by
        rw [integral_const_mul, h.integral_expMart (s - l) le_rfl, mul_one]

end CERW.Generic.Martingale.Tilt
