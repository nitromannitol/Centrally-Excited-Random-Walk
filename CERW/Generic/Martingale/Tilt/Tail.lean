import CERW.Generic.Martingale.Tilt.Statements

/-!
# The tail from the two weighted tails

On the window between the two weighted tails, `Z(s)⁻¹` is at least `e^{-F}`. Since the mean of
`Z(s)` is one, the window has probability at least `e^{-F} (1 - e^{E₊} - e^{E₋})`.
-/

universe u

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

/-- On the window `c' ≤ N ≤ c`, the inverse of the exponential martingale is bounded below. -/
lemma tilt_window_bound {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Y : ℕ → Ω → ℝ} {b : ℝ} {n : ℕ}
    (h : Increments μ ℱ Y b n) {v ρ s w : ℝ} (hs : 0 ≤ s) (hsb : s * b ≤ 1 / 2)
    (hV : ∀ᵐ ω ∂μ, v * (1 - ρ) ≤ varSum μ ℱ Y n ω ∧ varSum μ ℱ Y n ω ≤ v) :
    ∀ᵐ ω ∂μ, (s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
        ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w) →
      Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) *
        expMart μ ℱ Y s n ω ≤ 1 := by
  have hsb' : |s| * b ≤ 1 / 2 := by rwa [abs_of_nonneg hs]
  filter_upwards [h.abs_cumulant_sub_le s hsb', hV] with ω hK hVω hG
  obtain ⟨hlo, hhi⟩ := hVω
  have hK' := (_root_.abs_le.mp hK).1
  rw [abs_of_nonneg hs] at hK'
  have h1 : s * ∑ t ∈ Finset.range n, Y t ω ≤ s * (s * v + w) :=
    mul_le_mul_of_nonneg_left hG.2 hs
  have h2 : s ^ 2 * (v * (1 - ρ)) ≤ s ^ 2 * varSum μ ℱ Y n ω :=
    mul_le_mul_of_nonneg_left hlo (sq_nonneg s)
  have h3 : s ^ 3 * b * varSum μ ℱ Y n ω ≤ s ^ 3 * b * v :=
    mul_le_mul_of_nonneg_left hhi (mul_nonneg (pow_nonneg hs 3) h.nonneg)
  calc Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) * expMart μ ℱ Y s n ω
      = Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)
          + (s * ∑ t ∈ Finset.range n, Y t ω - cumulant μ ℱ Y s n ω)) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
    _ = 1 := Real.exp_zero

/-- A nonnegative integrable function of mean `m` has window integral at least `m` minus the
two tail integrals. -/
lemma tilt_window_integral {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {Z N : Ω → ℝ} (hZ : Integrable Z μ) (hZ0 : ∀ ω, 0 ≤ Z ω) (hN : Measurable N)
    (c c' : ℝ) :
    ∫ ω, Z ω ∂μ - ∫ ω in {ω | c ≤ N ω}, Z ω ∂μ
        - ∫ ω in {ω | N ω ≤ c'}, Z ω ∂μ
      ≤ ∫ ω in {ω | c' ≤ N ω ∧ N ω ≤ c}, Z ω ∂μ := by
  have hA : MeasurableSet {ω | c ≤ N ω} := measurableSet_le measurable_const hN
  have hB : MeasurableSet {ω | N ω ≤ c'} := measurableSet_le hN measurable_const
  have hG : MeasurableSet {ω | c' ≤ N ω ∧ N ω ≤ c} :=
    (measurableSet_le measurable_const hN).inter (measurableSet_le hN measurable_const)
  have h1 := integral_add_compl hG hZ
  have h2 : ∫ ω in {ω | c' ≤ N ω ∧ N ω ≤ c}ᶜ, Z ω ∂μ
      ≤ ∫ ω in {ω | c ≤ N ω} ∪ {ω | N ω ≤ c'}, Z ω ∂μ := by
    refine setIntegral_mono_set hZ.integrableOn (Filter.Eventually.of_forall hZ0)
      (Filter.Eventually.of_forall fun ω hω => ?_)
    by_contra hc
    refine hω ⟨?_, ?_⟩
    · by_contra h3
      exact hc (Or.inr (not_le.1 h3).le)
    · by_contra h3
      exact hc (Or.inl (not_le.1 h3).le)
  have h3 : ∫ ω in {ω | c ≤ N ω} ∪ {ω | N ω ≤ c'}, Z ω ∂μ
      ≤ ∫ ω in {ω | c ≤ N ω}, Z ω ∂μ + ∫ ω in {ω | N ω ≤ c'}, Z ω ∂μ := by
    have h4 : ∫ ω in {ω | N ω ≤ c'} \ {ω | c ≤ N ω}, Z ω ∂μ
        ≤ ∫ ω in {ω | N ω ≤ c'}, Z ω ∂μ :=
      setIntegral_mono_set hZ.integrableOn (Filter.Eventually.of_forall hZ0)
        (Filter.Eventually.of_forall
          fun ω (hω : ω ∈ {ω | N ω ≤ c'} \ {ω | c ≤ N ω}) => hω.1)
    rw [← Set.union_sdiff_self, setIntegral_union Set.disjoint_sdiff_right (hB.diff hA)
      hZ.integrableOn hZ.integrableOn]
    exact add_le_add_right h4 _
  linarith

theorem tiltTail_of (hU : TiltUpper.{u}) (hL : TiltLower.{u}) : TiltTail.{u} := by
  intro Ω m0 μ _ ℱ Y b n h v ρ s w l₁ l₂ hs hl₁ hl₂ hl₂s hsl hV
  have hsb : s * b ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right (show s ≤ s + l₁ by linarith) h.nonneg
    linarith
  have hN : Measurable (fun ω => ∑ t ∈ Finset.range n, Y t ω) :=
    Finset.measurable_sum _ fun t ht => h.measurable (Finset.mem_range.1 ht)
  have hZi := h.integrable_expMart s (le_refl n)
  have hUp := hU μ ℱ Y b n h (v := v) (s := s) (l := l₁) (w := w) hs hl₁ hsl
    (hV.mono fun ω hω => hω.2)
  have hLo := hL μ ℱ Y b n h (v := v) (ρ := ρ) (s := s) (l := l₂) (w := w) hl₂ hl₂s hsb
    hV
  have hint := tilt_window_integral hZi (fun ω => (expMart_pos μ ℱ Y s n ω).le) hN
    (s * v + w) (s * v * (1 - ρ) - w)
  rw [h.integral_expMart s le_rfl] at hint
  have hG : MeasurableSet {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
      ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w} :=
    (measurableSet_le measurable_const hN).inter (measurableSet_le hN measurable_const)
  have hmono : Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) *
      ∫ ω in {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
        ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w}, expMart μ ℱ Y s n ω ∂μ ≤
      (μ {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
        ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w}).toReal := by
    rw [← integral_const_mul]
    calc _ ≤ ∫ _ in {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
            ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w}, (1 : ℝ) ∂μ :=
          setIntegral_mono_on_ae (hZi.const_mul _).integrableOn (integrable_const _).integrableOn
            hG (tilt_window_bound h hs hsb hV)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
  have hsub : {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω ∧
      ∑ t ∈ Finset.range n, Y t ω ≤ s * v + w} ⊆
      {ω | s * v * (1 - ρ) - w ≤ ∑ t ∈ Finset.range n, Y t ω} := fun ω hω => hω.1
  refine le_trans ?_ (hmono.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)))
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

end CERW.Generic.Martingale.Tilt
