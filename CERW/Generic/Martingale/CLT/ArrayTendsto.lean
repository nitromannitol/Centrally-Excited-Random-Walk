import CERW.Generic.Martingale.FreedmanEvent
import CERW.Model.Bracket
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import CERW.Generic.Martingale.CLT.Interfaces

/-!
# The characteristic function of the array rows

The conditional Lindeberg sum `lind`, and the passage to the limit in the characteristic
function of the last term of each row of a square-integrable martingale array. The one-row bound
is taken as an explicit hypothesis; the martingale hypotheses of a row are used only to apply
that bound.
-/

universe u

namespace CERW.Generic.Martingale.CLT

open MeasureTheory Filter Topology
open scoped NNReal

section BoundedConvergence

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f : ℕ → Ω → ℝ} {C : ℝ}

/-- A uniformly bounded sequence of nonnegative functions that tends to `0` in measure has
integrals tending to `0`. -/
private theorem tendsto_integral_of_tendstoInMeasure_of_bounded
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hb : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ f n ω ∧ f n ω ≤ C)
    (h : TendstoInMeasure μ f atTop (fun _ => 0)) :
    Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at h
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  have hev : ∀ᶠ n in atTop,
      (|C| + 1) * μ.real {ω | ε / 2 ≤ ‖f n ω - 0‖} < ε / 2 := by
    have := (h (ε / 2) hδ).const_mul (|C| + 1)
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [hev] with n hn
  set S : Set Ω := {ω | ε / 2 ≤ ‖f n ω - 0‖} with hS
  have hSm : NullMeasurableSet S μ :=
    aestronglyMeasurable_const.nullMeasurableSet_le (((hf n).sub aestronglyMeasurable_const).norm)
  have hpt : ∀ᵐ ω ∂μ, f n ω ≤ ε / 2 + |C| * S.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hb n] with ω hω
    by_cases hωS : ω ∈ S
    · rw [Set.indicator_of_mem hωS]
      linarith [hω.2, le_abs_self C]
    · rw [Set.indicator_of_notMem hωS]
      have : ‖f n ω - 0‖ < ε / 2 := not_le.mp hωS
      rw [sub_zero, Real.norm_of_nonneg hω.1] at this
      simp only [mul_zero, add_zero]
      exact this.le
  have hind : Integrable (S.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator₀ hSm
  have hint : Integrable (fun ω => ε / 2 + |C| * S.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const _).add (hind.const_mul _)
  have hle : ∫ ω, f n ω ∂μ ≤
      ∫ ω, (ε / 2 + |C| * S.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
    integral_mono_of_nonneg ((hb n).mono fun ω hω => hω.1) hint hpt
  have heq : ∫ ω, (ε / 2 + |C| * S.indicator (fun _ => (1 : ℝ)) ω) ∂μ
      = ε / 2 + |C| * μ.real S := by
    rw [integral_add (integrable_const _) (hind.const_mul _), integral_const_mul,
      integral_indicator₀ hSm, setIntegral_const]
    simp
  have hnn : 0 ≤ ∫ ω, f n ω ∂μ := integral_nonneg_of_ae ((hb n).mono fun ω hω => hω.1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hμS : 0 ≤ μ.real S := measureReal_nonneg
  have hC : |C| * μ.real S ≤ (|C| + 1) * μ.real S := by
    nlinarith
  linarith

end BoundedConvergence

section Lindeberg

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)
  (M : ℕ → Ω → ℝ) (δ : ℝ) (n : ℕ)

/-- The conditional Lindeberg sum is nonnegative almost surely. -/
private theorem lind_nonneg : 0 ≤ᵐ[μ] lind μ ℱ M δ n := by
  filter_upwards [(eventually_all_finset (Finset.range n)).mpr
    (fun i _ => condExp_nonneg (μ := μ) (m := ℱ i)
      (f := fun ω => (M (i + 1) ω - M i ω) ^ 2 *
        (if δ < |M (i + 1) ω - M i ω| then 1 else 0))
      (Eventually.of_forall fun ω => by positivity))] with ω hω
  rw [lind]
  exact Finset.sum_nonneg fun i hi => hω i hi

/-- The conditional Lindeberg sum is almost strongly measurable. -/
private theorem aestronglyMeasurable_lind : AEStronglyMeasurable (lind μ ℱ M δ n) μ := by
  have h : AEStronglyMeasurable (∑ i ∈ Finset.range n, (fun ω =>
      μ[fun ω => (M (i + 1) ω - M i ω) ^ 2 *
        (if δ < |M (i + 1) ω - M i ω| then 1 else 0) | ℱ i] ω) : Ω → ℝ) μ := by
    refine Finset.aestronglyMeasurable_sum (M := ℝ) (Finset.range n) (fun i _ => ?_)
    exact ((stronglyMeasurable_condExp (μ := μ) (m := ℱ i)
      (f := fun ω => (M (i + 1) ω - M i ω) ^ 2 *
        (if δ < |M (i + 1) ω - M i ω| then 1 else 0))).mono (ℱ.le i)).aestronglyMeasurable
  convert h using 1
  ext ω
  simp only [lind, Finset.sum_apply]

end Lindeberg

section Limit

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  (ℱ : Filtration ℕ m0)

/-- Composing a sequence converging to `0` in measure with `x ↦ min (max x 0) c` preserves
convergence to `0` in measure, and the result is nonnegative and bounded by `c`. -/
private theorem tendstoInMeasure_min_max_zero {L : ℕ → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : TendstoInMeasure μ L atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => min (max (L n ω) 0) c) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm] at h ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun n => measureReal_nonneg) (fun n => ?_)
  refine measureReal_mono fun ω hω => ?_
  simp only [Set.mem_setOf_eq, sub_zero] at hω ⊢
  have hgnn : 0 ≤ min (max (L n ω) 0) c := le_min (le_max_right _ _) hc
  have hle : ‖min (max (L n ω) 0) c‖ ≤ ‖L n ω‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg hgnn, Real.norm_eq_abs]
    exact (min_le_left _ _).trans (max_le (le_abs_self _) (abs_nonneg _))
  exact hω.trans hle

/-- The real measure of the deviation of a sequence converging in measure to a real number
tends to `0`. -/
private theorem tendsto_measureReal_lt_abs_sub_of_tendstoInMeasure
    {X : ℕ → Ω → ℝ} {a : ℝ}
    (h : TendstoInMeasure μ X atTop (fun _ => a)) :
    ∀ η > 0, Tendsto (fun n => μ.real {ω | η < |X n ω - a|}) atTop (𝓝 0) := by
  intro η hη
  have h' := (tendstoInMeasure_iff_measureReal_norm.mp h) (η / 2) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h'
    (fun n => measureReal_nonneg) (fun n => ?_)
  refine measureReal_mono fun ω hω => ?_
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [Real.norm_eq_abs]
  linarith

/-- The integrals of `min (lind, c)` tend to `0` when the conditional Lindeberg sums tend to
`0` in measure. -/
private theorem tendsto_integral_min_lind {Mn : ℕ → ℕ → Ω → ℝ} {δ c : ℝ}
    (hc : 0 ≤ c)
    (h : TendstoInMeasure μ (fun n => lind μ ℱ (Mn n) δ n) atTop (fun _ => 0)) :
    Tendsto (fun n => ∫ ω, min (lind μ ℱ (Mn n) δ n ω) c ∂μ) atTop (𝓝 0) := by
  have hconv : TendstoInMeasure μ (fun n ω => min (max (lind μ ℱ (Mn n) δ n ω) 0) c) atTop
      (fun _ => 0) := tendstoInMeasure_min_max_zero hc h
  have hbound : ∀ n, ∀ᵐ ω ∂μ,
      0 ≤ min (max (lind μ ℱ (Mn n) δ n ω) 0) c ∧
        min (max (lind μ ℱ (Mn n) δ n ω) 0) c ≤ c := by
    intro n
    filter_upwards with ω
    exact ⟨le_min (le_max_right _ _) hc, min_le_right _ _⟩
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun ω => min (max (lind μ ℱ (Mn n) δ n ω) 0) c) μ :=
    fun n => ((continuous_id.max continuous_const).min continuous_const).comp_aestronglyMeasurable
      (aestronglyMeasurable_lind μ ℱ (Mn n) δ n)
  have hint := tendsto_integral_of_tendstoInMeasure_of_bounded hmeas hbound hconv
  have hcongr : ∀ n, ∫ ω, min (lind μ ℱ (Mn n) δ n ω) c ∂μ
      = ∫ ω, min (max (lind μ ℱ (Mn n) δ n ω) 0) c ∂μ := by
    intro n
    refine integral_congr_ae ?_
    filter_upwards [lind_nonneg μ ℱ (Mn n) δ n] with ω hω
    have hω' : (0 : ℝ) ≤ lind μ ℱ (Mn n) δ n ω := by simpa only [Pi.zero_apply] using hω
    rw [max_eq_left hω']
  exact Tendsto.congr' (Eventually.of_forall fun n => (hcongr n).symm) hint

end Limit

section BoundLimit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A nonnegative sequence bounded by `B δ η n` for all `δ, η > 0` with `η ≤ 1`, where
`B δ η · → R δ η` and `R δ η` can be made arbitrarily small, tends to `0`. -/
private theorem tendsto_zero_of_forall_bound {Y : ℕ → ℝ} {B : ℝ → ℝ → ℕ → ℝ}
    {R : ℝ → ℝ → ℝ} (hYnn : ∀ n, 0 ≤ Y n)
    (hB : ∀ δ η, 0 < δ → 0 < η → η ≤ 1 →
      Tendsto (fun n => B δ η n) atTop (𝓝 (R δ η)))
    (hY : ∀ δ η, 0 < δ → 0 < η → η ≤ 1 → ∀ n, Y n ≤ B δ η n)
    (hR : ∀ ε > 0, ∃ δ η, 0 < δ ∧ 0 < η ∧ η ≤ 1 ∧ R δ η < ε) :
    Tendsto Y atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, η, hδ, hη, hη1, hRlt⟩ := hR ε hε
  have hev : ∀ᶠ n in atTop, B δ η n < ε :=
    (hB δ η hδ hη hη1).eventually (gt_mem_nhds hRlt)
  filter_upwards [hev] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hYnn n)]
  exact lt_of_le_of_lt (hY δ η hδ hη hη1 n) hn

end BoundLimit

/-- For an array of square-integrable martingales started at `0` whose conditional Lindeberg
sums tend to `0` in measure and whose predictable brackets tend to `v` in measure, the
characteristic function of the last term of row `n` converges to that of the centered Gaussian of
variance `v`. -/
theorem array_charFun_tendsto
    (hG2 : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ),
      Martingale M ℱ μ → (∀ k, MemLp (M k) 2 μ) → (∀ ω, M 0 ω = 0) →
      ∀ v : ℝ, 0 ≤ v → ∀ (n : ℕ) (t δ η : ℝ), 0 < δ → 0 < η → η ≤ 1 →
      ‖∫ ω, Complex.exp (t * M n ω * Complex.I) ∂μ
          - Complex.exp (-(t ^ 2 * v / 2 : ℝ))‖ ≤
        2 * μ.real {ω | η < |CERW.predBracket μ ℱ M M n ω - v|} +
        Real.exp (t ^ 2 * (v + 1)) *
          (t ^ 4 / 8 * ((v + 1) * (δ ^ 2 + ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
            4 * (δ * |t| ^ 3 * (v + 1) +
              t ^ 2 * ∫ ω, min (lind μ ℱ M δ n ω) (v + 1) ∂μ)) +
        Real.exp (t ^ 2 * (v + 1) / 2) *
          (t ^ 2 / 2 * (η + (v + 1) *
            μ.real {ω | η < |CERW.predBracket μ ℱ M M n ω - v|})) )
    : ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M : ℕ → ℕ → Ω → ℝ) (v : ℝ≥0),
      (∀ n, Martingale (M n) ℱ μ) → (∀ n k, MemLp (M n k) 2 μ) →
      (∀ n ω, M n 0 ω = 0) →
      (∀ δ : ℝ, 0 < δ →
        TendstoInMeasure μ (fun n => lind μ ℱ (M n) δ n) atTop (fun _ => 0)) →
      TendstoInMeasure μ (fun n => CERW.predBracket μ ℱ (M n) (M n) n) atTop
        (fun _ => (v : ℝ)) →
      ∀ t : ℝ, Tendsto (fun n => ∫ ω, Complex.exp (t * M n n ω * Complex.I) ∂μ) atTop
        (𝓝 (Complex.exp (-(t ^ 2 * v / 2 : ℝ)))) := by
  intro Ω m0 μ hprob ℱ M v hMart hLp hzero hLind hBr t
  set c : ℝ := (v : ℝ) + 1 with hcdef
  have hc : 0 ≤ c := by rw [hcdef]; positivity
  set E1 : ℝ := Real.exp (t ^ 2 * c) with hE1def
  set E2 : ℝ := Real.exp (t ^ 2 * c / 2) with hE2def
  set p : ℕ → ℝ → ℝ := fun n η =>
    μ.real {ω | η < |CERW.predBracket μ ℱ (M n) (M n) n ω - (v : ℝ)|} with hpdef
  set i : ℕ → ℝ → ℝ := fun n δ =>
    ∫ ω, min (lind μ ℱ (M n) δ n ω) c ∂μ with hidef
  set K1 : ℝ := E1 * (t ^ 4 / 8 * c + 4 * |t| ^ 3 * c) with hK1def
  set K2 : ℝ := E2 * (t ^ 2 / 2) with hK2def
  have hK1nn : 0 ≤ K1 := by rw [hK1def, hE1def]; positivity
  have hK2nn : 0 ≤ K2 := by rw [hK2def, hE2def]; positivity
  set R : ℝ → ℝ → ℝ := fun δ η =>
    E1 * (t ^ 4 / 8 * c * δ ^ 2 + 4 * (δ * |t| ^ 3 * c)) + E2 * (t ^ 2 / 2 * η) with hRdef
  set B : ℝ → ℝ → ℕ → ℝ := fun δ η n =>
    2 * p n η + E1 * (t ^ 4 / 8 * (c * (δ ^ 2 + i n δ)) +
      4 * (δ * |t| ^ 3 * c + t ^ 2 * i n δ)) +
      E2 * (t ^ 2 / 2 * (η + c * p n η)) with hBdef
  have hp : ∀ η > 0, Tendsto (fun n => p n η) atTop (𝓝 0) := by
    intro η hη
    simpa only [hpdef] using tendsto_measureReal_lt_abs_sub_of_tendstoInMeasure hBr η hη
  have hi : ∀ δ > 0, Tendsto (fun n => i n δ) atTop (𝓝 0) := by
    intro δ hδ
    simpa only [hidef, hcdef] using
      tendsto_integral_min_lind (μ := μ) (ℱ := ℱ) hc (hLind δ hδ)
  have hY : ∀ δ η, 0 < δ → 0 < η → η ≤ 1 → ∀ n,
      ‖∫ ω, Complex.exp (t * M n n ω * Complex.I) ∂μ
        - Complex.exp (-(t ^ 2 * (v : ℝ) / 2 : ℝ))‖ ≤ B δ η n := by
    intro δ η hδ hη hη1 n
    have h := hG2 μ ℱ (M n) (hMart n) (fun k => hLp n k) (hzero n) (v : ℝ) v.2
      n t δ η hδ hη hη1
    simpa only [hBdef, hpdef, hidef, hcdef, hE1def, hE2def] using h
  have hB : ∀ δ η, 0 < δ → 0 < η → η ≤ 1 →
      Tendsto (fun n => B δ η n) atTop (𝓝 (R δ η)) := by
    intro δ η hδ hη hη1
    have hpη : Tendsto (fun n => p n η) atTop (𝓝 0) := hp η hη
    have hiδ : Tendsto (fun n => i n δ) atTop (𝓝 0) := hi δ hδ
    have hfun : (fun n => B δ η n) =
        fun n => R δ η + p n η * (2 + E2 * (t ^ 2 / 2 * c)) +
          i n δ * (E1 * (t ^ 4 / 8 * c) + E1 * (4 * t ^ 2)) := by
      funext n
      rw [hBdef, hRdef]
      ring
    rw [hfun]
    have : Tendsto (fun n => R δ η + p n η * (2 + E2 * (t ^ 2 / 2 * c)) +
          i n δ * (E1 * (t ^ 4 / 8 * c) + E1 * (4 * t ^ 2))) atTop
        (𝓝 (R δ η + 0 * (2 + E2 * (t ^ 2 / 2 * c)) +
          0 * (E1 * (t ^ 4 / 8 * c) + E1 * (4 * t ^ 2)))) :=
      (tendsto_const_nhds.add (hpη.mul_const _)).add (hiδ.mul_const _)
    simpa using this
  have hR : ∀ ε > 0, ∃ δ η, 0 < δ ∧ 0 < η ∧ η ≤ 1 ∧ R δ η < ε := by
    intro ε hε
    let e : ℝ := ε / (4 * (K1 + K2 + 1))
    have hepos : 0 < e := by dsimp [e]; positivity
    refine ⟨min 1 e, min 1 e, lt_min one_pos hepos, lt_min one_pos hepos,
      min_le_left _ _, ?_⟩
    have hδle : min 1 e ≤ e := min_le_right _ _
    have hδ1 : min 1 e ≤ 1 := min_le_left _ _
    have hsq : (min 1 e) ^ 2 ≤ e := by
      have h0 : 0 < min 1 e := lt_min one_pos hepos
      have h2 : (min 1 e) ^ 2 ≤ min 1 e := by nlinarith
      exact h2.trans hδle
    have hbound : R (min 1 e) (min 1 e) ≤ (K1 + K2) * e := by
      rw [hRdef, hK1def, hK2def]
      have h1 : E1 * (t ^ 4 / 8 * c * (min 1 e) ^ 2) ≤ E1 * (t ^ 4 / 8 * c) * e := by
        have hc' : 0 ≤ t ^ 4 / 8 * c := by positivity
        calc E1 * (t ^ 4 / 8 * c * (min 1 e) ^ 2)
            = E1 * ((t ^ 4 / 8 * c) * (min 1 e) ^ 2) := by ring
          _ ≤ E1 * ((t ^ 4 / 8 * c) * e) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hc')
                (by rw [hE1def]; positivity)
          _ = E1 * (t ^ 4 / 8 * c) * e := by ring
      have h2 : E1 * (4 * ((min 1 e) * |t| ^ 3 * c)) ≤ E1 * (4 * |t| ^ 3 * c) * e := by
        have hc' : 0 ≤ 4 * |t| ^ 3 * c := by positivity
        calc E1 * (4 * ((min 1 e) * |t| ^ 3 * c))
            = E1 * ((4 * |t| ^ 3 * c) * (min 1 e)) := by ring
          _ ≤ E1 * ((4 * |t| ^ 3 * c) * e) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδle hc')
                (by rw [hE1def]; positivity)
          _ = E1 * (4 * |t| ^ 3 * c) * e := by ring
      have h3 : E2 * (t ^ 2 / 2 * (min 1 e)) ≤ E2 * (t ^ 2 / 2) * e := by
        have hc' : 0 ≤ t ^ 2 / 2 := by positivity
        calc E2 * (t ^ 2 / 2 * (min 1 e))
            = E2 * ((t ^ 2 / 2) * (min 1 e)) := by ring
          _ ≤ E2 * ((t ^ 2 / 2) * e) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδle hc')
                (by rw [hE2def]; positivity)
          _ = E2 * (t ^ 2 / 2) * e := by ring
      linarith
    have hlt : (K1 + K2) * e < ε := by
      have hKnn : 0 ≤ K1 + K2 := add_nonneg hK1nn hK2nn
      have hpos : 0 < 4 * (K1 + K2 + 1) := by positivity
      have heq : e = ε / (4 * (K1 + K2 + 1)) := rfl
      rw [heq]
      have hD : 0 < 4 * (K1 + K2 + 1) := by positivity
      rw [show (K1 + K2) * (ε / (4 * (K1 + K2 + 1))) =
          (K1 + K2) * ε / (4 * (K1 + K2 + 1)) by ring]
      rw [div_lt_iff₀ hD]
      nlinarith
    linarith
  have hYnn : ∀ n, 0 ≤ ‖∫ ω, Complex.exp (t * M n n ω * Complex.I) ∂μ
      - Complex.exp (-(t ^ 2 * (v : ℝ) / 2 : ℝ))‖ := fun n => norm_nonneg _
  have hlim := tendsto_zero_of_forall_bound (Y := fun n =>
    ‖∫ ω, Complex.exp (t * M n n ω * Complex.I) ∂μ
      - Complex.exp (-(t ^ 2 * (v : ℝ) / 2 : ℝ))‖) hYnn hB hY hR
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hlim

end CERW.Generic.Martingale.CLT
