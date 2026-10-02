import CERW.Generic.Martingale.Tilt.SharpLowerTailLimit
import CERW.Generic.Martingale.LilLower.ConditionedBlock

/-!
# The lower bound for one block, conditioned on an earlier event

Let `M` be a square-integrable martingale and `σ ≤ ρ` stopping times, `ρ` almost surely finite, and
let `F` be an event determined by time `σ`, of positive probability. Suppose the increments of `M`
between `σ` and `ρ` are bounded by `b`, and that the sum of the conditional variances of `M` over
the times `σ ≤ t < ρ` is, almost surely on `F`, at most `v` at every time and eventually at least
`v (1 - r)`. Then the
increment of `M` between `σ` and `ρ` is at least `a` with conditional probability at least
`exp (-(1 + η) a² / (2 v))` given `F`, whenever `a² ≥ A₀ v`, `a b ≤ ε₀ v` and `r ≤ ρ₀`. This is the
sharp lower tail for the conditioned increments `blockIncrement M σ ρ F`.
-/

universe u

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory ProbabilityTheory Filter Topology

/-- The increment of a martingale between two stopping times, kept on an event determined by the
earlier one, is measurable. -/
private lemma measurable_blockLimit {Ω : Type u} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℕ m0}
    {μ : Measure Ω} {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ μ) {σ ρ : Ω → WithTop ℕ}
    (hσ : IsStoppingTime ℱ σ) (hρ : IsStoppingTime ℱ ρ) {F : Set Ω}
    (hF : MeasurableSet[hσ.measurableSpace] F) :
    Measurable (F.indicator (fun ω => stoppedValue M ρ ω - stoppedValue M σ ω)) := by
  have hprog := hM.1.isStronglyProgressive_of_discrete
  have h1 : Measurable (stoppedValue M ρ) :=
    (measurable_stoppedValue hprog hρ).mono hρ.measurableSpace_le le_rfl
  have h2 : Measurable (stoppedValue M σ) :=
    (measurable_stoppedValue hprog hσ).mono hσ.measurableSpace_le le_rfl
  exact (h1.sub h2).indicator ((hσ.measurableSet F).1 hF).1

/-- The partial sums of the block increments eventually equal the increment of `M` between `σ` and
`ρ` on `F`, at every point where `ρ` is finite. -/
private lemma eventually_sum_blockIncrement_eq {Ω : Type u} (M : ℕ → Ω → ℝ)
    {σ ρ : Ω → WithTop ℕ} (hσρ : ∀ ω, σ ω ≤ ρ ω) (F : Set Ω) {ω : Ω} (hω : ρ ω ≠ ⊤) :
    ∀ᶠ n in atTop, ∑ t ∈ Finset.range n, blockIncrement M σ ρ F t ω =
      F.indicator (fun ω => stoppedValue M ρ ω - stoppedValue M σ ω) ω := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hω
  filter_upwards [eventually_ge_atTop m] with n hn
  have hρn : ρ ω ≤ (n : WithTop ℕ) := by
    rw [← hm]
    exact WithTop.coe_le_coe.mpr hn
  have hσn : σ ω ≤ (n : WithTop ℕ) := (hσρ ω).trans hρn
  rw [sum_blockIncrement M hσρ F n ω]
  by_cases hωF : ω ∈ F
  · simp only [Set.indicator_of_mem hωF, stoppedValue, min_eq_left hρn, min_eq_left hσn]
  · simp only [Set.indicator_of_notMem hωF]

/-- The conditional measure of the event `{a ≤ L}`, for `L` the increment kept on `F`, bounds
the measure of `F ∩ {a ≤ x - y}` from below, after multiplication by the measure of `F`. -/
private lemma mul_toReal_le_of_cond {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] {F : Set Ω} (hF : MeasurableSet F) (hμF : μ F ≠ 0)
    {x y : Ω → ℝ} {a c : ℝ} (ha : 0 < a)
    (h : c ≤ (μ[|F] {ω | a ≤ F.indicator (fun ω => x ω - y ω) ω}).toReal) :
    c * (μ F).toReal ≤ (μ (F ∩ {ω | a ≤ x ω - y ω})).toReal := by
  have hset : {ω | a ≤ F.indicator (fun ω => x ω - y ω) ω} = F ∩ {ω | a ≤ x ω - y ω} := by
    ext ω
    by_cases hω : ω ∈ F
    · simp [hω]
    · simp [hω, ha.not_ge]
  have hpos : 0 < (μ F).toReal := ENNReal.toReal_pos hμF (measure_ne_top μ F)
  rw [hset, cond_inter_self hF, cond_apply hF, ENNReal.toReal_mul, ENNReal.toReal_inv] at h
  calc c * (μ F).toReal ≤ ((μ F).toReal⁻¹ * (μ (F ∩ {ω | a ≤ x ω - y ω})).toReal) *
        (μ F).toReal := mul_le_mul_of_nonneg_right h hpos.le
    _ = (μ (F ∩ {ω | a ≤ x ω - y ω})).toReal := by field_simp

/-- **The conditional lower bound for one block.** -/
theorem block_lower_bound {η : ℝ} (hη : 0 < η) :
    ∃ ρ₀ ε₀ A₀ : ℝ, 0 < ρ₀ ∧ 0 < ε₀ ∧
      ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) {M : ℕ → Ω → ℝ} (_hM : Martingale M ℱ μ)
        (_hL2 : ∀ n, MemLp (M n) 2 μ) {σ ρ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ)
        (_hρ : IsStoppingTime ℱ ρ) (_hσρ : ∀ ω, σ ω ≤ ρ ω) (_hfin : ∀ᵐ ω ∂μ, ρ ω ≠ ⊤)
        {F : Set Ω} (_hF : MeasurableSet[hσ.measurableSpace] F) (_hμF : μ F ≠ 0) {b : ℝ}
        (_hb : 0 ≤ b)
        (_hbound : ∀ (t : ℕ) (ω : Ω), σ ω ≤ (t : WithTop ℕ) → (t : WithTop ℕ) < ρ ω →
          |M (t + 1) ω - M t ω| ≤ b) {v a r : ℝ},
        0 < v → 0 < a → 0 ≤ r → r ≤ ρ₀ →
        (∀ᵐ ω ∂μ, ω ∈ F → ∀ n, ∑ t ∈ Finset.range n,
          (if σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω then (1 : ℝ) else 0) *
            (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω ≤ v) →
        (∀ᵐ ω ∂μ, ω ∈ F → ∀ᶠ n in atTop, v * (1 - r) ≤ ∑ t ∈ Finset.range n,
          (if σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω then (1 : ℝ) else 0) *
            (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω) →
        A₀ * v ≤ a ^ 2 → a * b ≤ ε₀ * v →
        Real.exp (-((1 + η) * (a ^ 2 / (2 * v)))) * (μ F).toReal ≤
          (μ (F ∩ {ω | a ≤ stoppedValue M ρ ω - stoppedValue M σ ω})).toReal := by
  obtain ⟨ρ₀, ε₀, A₀, hρ₀, hε₀, H⟩ := CERW.Generic.Martingale.Tilt.sharp_lower_tail_limit.{u} η hη
  refine ⟨ρ₀, ε₀, A₀, hρ₀, hε₀, ?_⟩
  intro Ω m0 μ _ ℱ M _hM hL2 σ ρ hσ hρ _hσρ _hfin F _hF _hμF b _hb _hbound v a r hv ha hr hrρ
    hvar hlow hA hab
  haveI := cond_isProbabilityMeasure _hμF
  have hF0 : MeasurableSet F := ((hσ.measurableSet F).1 _hF).1
  have hac : μ[|F] ≪ μ := cond_absolutelyContinuous
  refine mul_toReal_le_of_cond μ hF0 _hμF ha (H (μ[|F]) ℱ (blockIncrement M σ ρ F) b _
    (measurable_blockLimit _hM hσ hρ _hF)
    (increments_blockIncrement μ ℱ _hM hσ hρ _hF _hμF _hb _hbound) hv ha hr hrρ ?_ ?_ ?_ hA hab)
  · intro n
    filter_upwards [varSum_blockIncrement μ ℱ hL2 hσ hρ _hF _hμF n, hac.ae_le hvar,
      ae_cond_mem hF0] with ω h1 h2 h3
    rw [h1]
    exact h2 h3 n
  · filter_upwards [ae_all_iff.2 fun n => varSum_blockIncrement μ ℱ hL2 hσ hρ _hF _hμF n,
      hac.ae_le hlow, ae_cond_mem hF0] with ω h1 h2 h3
    filter_upwards [h2 h3] with n hn
    rw [h1 n]
    exact hn
  · filter_upwards [hac.ae_le _hfin] with ω hω
    exact eventually_sum_blockIncrement_eq M _hσρ F hω

end CERW.Generic.Martingale.LilLower
