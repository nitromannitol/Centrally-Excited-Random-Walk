import CERW.Generic.Martingale.Tilt.LimitStatements
import CERW.Generic.Martingale.Tilt.SharpLowerTail

/-!
# The tail when the bracket is large only on a set

As in `Tail`, with the complement of `W` paid for by Cauchy–Schwarz and the second moment of the
exponential martingale: `∫_{Wᶜ} Z(s) ≤ e^{3 s² v} √μ(Wᶜ)`.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

/-- On the window `c' ≤ N ≤ c` inside `W`, the inverse of the exponential martingale is bounded
below, when the lower bound of the bracket is only known on `W`. -/
theorem tilt_window_on_bound {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Y : ℕ → Ω → ℝ} {b : ℝ} {n : ℕ}
    (h : Increments μ ℱ Y b n) {v ρ s w : ℝ} {W : Set Ω} (hs : 0 ≤ s) (hsb : s * b ≤ 1 / 2)
    (hV : ∀ᵐ ω ∂μ, varSum μ ℱ Y n ω ≤ v)
    (hVW : ∀ᵐ ω ∂μ, ω ∈ W → v * (1 - ρ) ≤ varSum μ ℱ Y n ω) :
    ∀ᵐ ω ∂μ, ω ∈ {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
        ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w} ∩ W →
      Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) *
        expMart μ ℱ Y s n ω ≤ 1 := by
  have hsb' : |s| * b ≤ 1 / 2 := by rwa [abs_of_nonneg hs]
  filter_upwards [h.abs_cumulant_sub_le s hsb', hV, hVW] with ω hK hVω hVWω hmem
  obtain ⟨hG, hW⟩ := hmem
  have hlo := hVWω hW
  have hK' := (_root_.abs_le.mp hK).1
  rw [abs_of_nonneg hs] at hK'
  have h1 : s * ∑ t ∈ Finset.range n, Y t ω ≤ s * (s * v + w) :=
    mul_le_mul_of_nonneg_left hG.2 hs
  have h2 : s ^ 2 * (v * (1 - ρ)) ≤ s ^ 2 * varSum μ ℱ Y n ω :=
    mul_le_mul_of_nonneg_left hlo (sq_nonneg s)
  have h3 : s ^ 3 * b * varSum μ ℱ Y n ω ≤ s ^ 3 * b * v :=
    mul_le_mul_of_nonneg_left hVω (mul_nonneg (pow_nonneg hs 3) h.nonneg)
  calc Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) * expMart μ ℱ Y s n ω
      = Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)
          + (s * ∑ t ∈ Finset.range n, Y t ω - cumulant μ ℱ Y s n ω)) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
    _ = 1 := Real.exp_zero

/-- A nonnegative integrable function of mean `m` has integral over the window `{c' ≤ N ≤ c} ∩ W`
at least `m` minus the three tail integrals. -/
theorem tilt_window_on_integral {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {Z N : Ω → ℝ} {W : Set Ω} (hZ : Integrable Z μ) (hZ0 : ∀ ω, 0 ≤ Z ω) (hN : Measurable N)
    (hW : MeasurableSet W) (c c' : ℝ) :
    ∫ ω, Z ω ∂μ - ∫ ω in {ω | c ≤ N ω}, Z ω ∂μ
        - ∫ ω in {ω | N ω ≤ c'} ∩ W, Z ω ∂μ - ∫ ω in Wᶜ, Z ω ∂μ
      ≤ ∫ ω in {ω | c' ≤ N ω ∧ N ω ≤ c} ∩ W, Z ω ∂μ := by
  have hA : MeasurableSet {ω | c ≤ N ω} := measurableSet_le measurable_const hN
  have hB : MeasurableSet ({ω | N ω ≤ c'} ∩ W) := (measurableSet_le hN measurable_const).inter hW
  have hG : MeasurableSet ({ω | c' ≤ N ω ∧ N ω ≤ c} ∩ W) :=
    ((measurableSet_le measurable_const hN).inter (measurableSet_le hN measurable_const)).inter hW
  have h1 := integral_add_compl hG hZ
  have hiA := hZ.indicator hA
  have hiB := hZ.indicator hB
  have hiC := hZ.indicator hW.compl
  have h2 : ∫ ω in ({ω | c' ≤ N ω ∧ N ω ≤ c} ∩ W)ᶜ, Z ω ∂μ
      ≤ ∫ ω, ({ω | c ≤ N ω}.indicator Z ω + ({ω | N ω ≤ c'} ∩ W).indicator Z ω
        + Wᶜ.indicator Z ω) ∂μ := by
    rw [← integral_indicator hG.compl]
    refine integral_mono (hZ.indicator hG.compl) ((hiA.add hiB).add hiC) fun ω => ?_
    have hn1 : 0 ≤ {ω | c ≤ N ω}.indicator Z ω := Set.indicator_nonneg (fun x _ => hZ0 x) ω
    have hn2 : 0 ≤ ({ω | N ω ≤ c'} ∩ W).indicator Z ω :=
      Set.indicator_nonneg (fun x _ => hZ0 x) ω
    have hn3 : 0 ≤ Wᶜ.indicator Z ω := Set.indicator_nonneg (fun x _ => hZ0 x) ω
    by_cases hω : ω ∈ ({ω | c' ≤ N ω ∧ N ω ≤ c} ∩ W)ᶜ
    · rw [Set.indicator_of_mem hω]
      by_cases hωW : ω ∈ W
      · by_cases hc : c ≤ N ω
        · rw [Set.indicator_of_mem (show ω ∈ {ω | c ≤ N ω} from hc)]
          linarith
        · have hc' : N ω ≤ c' := by
            by_contra hc'
            exact hω ⟨⟨(not_le.1 hc').le, (not_le.1 hc).le⟩, hωW⟩
          rw [Set.indicator_of_mem (show ω ∈ {ω | N ω ≤ c'} ∩ W from ⟨hc', hωW⟩)]
          linarith
      · rw [Set.indicator_of_mem (show ω ∈ Wᶜ from hωW)]
        linarith
    · rw [Set.indicator_of_notMem hω]
      linarith
  have h3 : ∫ ω, ({ω | c ≤ N ω}.indicator Z ω + ({ω | N ω ≤ c'} ∩ W).indicator Z ω
        + Wᶜ.indicator Z ω) ∂μ
      = ∫ ω in {ω | c ≤ N ω}, Z ω ∂μ + ∫ ω in {ω | N ω ≤ c'} ∩ W, Z ω ∂μ
        + ∫ ω in Wᶜ, Z ω ∂μ := by
    have e1 := integral_add (hiA.add hiB) hiC
    have e2 := integral_add hiA hiB
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2, integral_indicator hA, integral_indicator hB, integral_indicator hW.compl]
  linarith

/-- Cauchy–Schwarz for the exponential martingale: its integral over a measurable set `A` is at
most `e^{3 s² v}` times the square root of the measure of `A`. -/
theorem tilt_set_integral_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Y : ℕ → Ω → ℝ} {b : ℝ} {n : ℕ}
    (h : Increments μ ℱ Y b n) {v s : ℝ} (hsb : |s| * b ≤ 1 / 2)
    (hV : ∀ᵐ ω ∂μ, varSum μ ℱ Y n ω ≤ v) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in A, expMart μ ℱ Y s n ω ∂μ ≤ Real.exp (3 * s ^ 2 * v) * Real.sqrt (μ A).toReal := by
  have hZm : AEStronglyMeasurable (expMart μ ℱ Y s n) μ := (h.integrable_expMart s le_rfl).1
  have hZL : MemLp (expMart μ ℱ Y s n) (ENNReal.ofReal 2) μ := by
    refine MemLp.of_bound hZm (Real.exp (2 * (|s| * b) * n)) ?_
    filter_upwards [h.expMart_le s le_rfl] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (expMart_pos μ ℱ Y s n ω)]
    exact hω
  have hgL : MemLp (A.indicator (fun _ => (1 : ℝ))) (ENNReal.ofReal 2) μ :=
    (memLp_const (1 : ℝ)).indicator hA
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun ω => (expMart_pos μ ℱ Y s n ω).le)
    (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    hZL hgL
  have hlhs : ∫ ω, expMart μ ℱ Y s n ω * A.indicator (fun _ => (1 : ℝ)) ω ∂μ
      = ∫ ω in A, expMart μ ℱ Y s n ω ∂μ := by
    rw [← integral_indicator hA]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have hZ2 : ∫ ω, expMart μ ℱ Y s n ω ^ (2 : ℝ) ∂μ ≤ Real.exp (6 * s ^ 2 * v) := by
    have := h.integral_expMart_sq_le s hsb hV
    simpa only [Real.rpow_two] using this
  have hg2 : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ^ (2 : ℝ) ∂μ = (μ A).toReal := by
    have : ∀ ω, A.indicator (fun _ => (1 : ℝ)) ω ^ (2 : ℝ) = A.indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases hω : ω ∈ A
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    simp only [this]
    rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  rw [hlhs, hg2] at hCS
  refine hCS.trans ?_
  have hpos : 0 ≤ ∫ ω, expMart μ ℱ Y s n ω ^ (2 : ℝ) ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (expMart_pos μ ℱ Y s n ω).le _
  have h1 : (∫ ω, expMart μ ℱ Y s n ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      ≤ Real.exp (3 * s ^ 2 * v) := by
    calc (∫ ω, expMart μ ℱ Y s n ω ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
        ≤ Real.exp (6 * s ^ 2 * v) ^ (1 / (2 : ℝ)) :=
          Real.rpow_le_rpow hpos hZ2 (by norm_num)
      _ = Real.exp (3 * s ^ 2 * v) := by
          rw [← Real.exp_mul]
          congr 1
          ring
  rw [Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- The tail from the weighted tails, with the cost of the set where the bracket is small. -/
theorem tiltTailOn_of (hU : TiltUpper.{u}) (hL : TiltLowerOn.{u}) : TiltTailOn.{u} := by
  intro Ω m0 μ _ ℱ Y b n h v ρ s w l₁ l₂ W hW hs hl₁ hl₂ hl₂s hsl hV hVW
  have hsb : s * b ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right (show s ≤ s + l₁ by linarith) h.nonneg
    linarith
  have hsb' : |s| * b ≤ 1 / 2 := by rwa [abs_of_nonneg hs]
  have hN : Measurable (fun ω => ∑ t ∈ Finset.range n, Y t ω) :=
    Finset.measurable_sum _ fun t ht => h.measurable (Finset.mem_range.1 ht)
  have hZi := h.integrable_expMart s (le_refl n)
  have hUp := hU μ ℱ Y b n h (v := v) (s := s) (l := l₁) (w := w) hs hl₁ hsl hV
  have hLo := hL μ ℱ Y b n h (v := v) (ρ := ρ) (s := s) (l := l₂) (w := w) hW hl₂ hl₂s hsb
    hV hVW
  have hCS := tilt_set_integral_le h hsb' hV hW.compl
  have hint := tilt_window_on_integral hZi (fun ω => (expMart_pos μ ℱ Y s n ω).le) hN hW
    (s * v + w) (s * v * (1 - ρ) - w)
  rw [h.integral_expMart s le_rfl] at hint
  have hG : MeasurableSet ({ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
      ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w} ∩ W) :=
    ((measurableSet_le measurable_const hN).inter (measurableSet_le hN measurable_const)).inter hW
  have hmono : Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) *
      ∫ ω in {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
        ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w} ∩ W, expMart μ ℱ Y s n ω ∂μ ≤
      (μ ({ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
        ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w} ∩ W)).toReal := by
    rw [← integral_const_mul]
    calc _ ≤ ∫ _ in {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
            ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w} ∩ W, (1 : ℝ) ∂μ :=
          setIntegral_mono_on_ae (hZi.const_mul _).integrableOn (integrable_const _).integrableOn
            hG (tilt_window_on_bound h hs hsb hV hVW)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
  have hsub : {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
      ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w} ∩ W ⊆
      {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω} := fun ω hω => hω.1.1
  refine le_trans ?_ (hmono.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)))
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

end CERW.Generic.Martingale.Tilt
