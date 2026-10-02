import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Optional stopping for a martingale bounded in `L²`

A square-integrable martingale whose second moments are bounded has the same expectation at an
almost surely finite stopping time as at time `0`, and its value there is integrable. The time is
not assumed bounded: the stopped values at the bounded times `min τ N` are bounded in `L²`, hence
uniformly integrable, and converge almost surely.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory Filter Topology

/-- The stopped value at the bounded time `min τ N` is a conditional expectation of `Z N`. -/
private lemma stoppedValue_min_ae_eq_condExp {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hZ : Martingale Z ℱ μ) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (N : ℕ) :
    ∃ m : MeasurableSpace Ω, m ≤ m0 ∧
      stoppedValue Z (fun ω => min (τ ω) (N : WithTop ℕ)) =ᵐ[μ] μ[Z N | m] := by
  have hτN := hτ.min_const N
  have hle : ∀ ω, min (τ ω) (N : WithTop ℕ) ≤ N := fun ω => min_le_right _ _
  exact ⟨hτN.measurableSpace, hτN.measurableSpace_le_of_le hle,
    hZ.stoppedValue_ae_eq_condExp_of_le_const hτN hle⟩

/-- The expectation of a martingale at a fixed time equals its expectation at time `0`. -/
private lemma integral_martingale_eq_zero {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hZ : Martingale Z ℱ μ) (N : ℕ) : ∫ ω, Z N ω ∂μ = ∫ ω, Z 0 ω ∂μ := by
  rw [← integral_condExp (ℱ.le 0) (f := Z N) (μ := μ)]
  exact integral_congr_ae (hZ.2 0 N (Nat.zero_le N))

/-- The stopped value at a bounded time is integrable with the same expectation as time `0`,
lies in `L²`, and has second moment bounded by that of the underlying time. -/
private lemma stoppedValue_min_facts {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hZ : Martingale Z ℱ μ) {B : ℝ} (hL2 : ∀ n, MemLp (Z n) 2 μ)
    (hB : ∀ n, ∫ ω, Z n ω ^ 2 ∂μ ≤ B) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (N : ℕ) :
    MemLp (stoppedValue Z (fun ω => min (τ ω) (N : WithTop ℕ))) 2 μ ∧
      ∫ ω, stoppedValue Z (fun ω => min (τ ω) (N : WithTop ℕ)) ω ∂μ = ∫ ω, Z 0 ω ∂μ ∧
      ∫ ω, stoppedValue Z (fun ω => min (τ ω) (N : WithTop ℕ)) ω ^ 2 ∂μ ≤ B := by
  obtain ⟨m, hm, hae⟩ := stoppedValue_min_ae_eq_condExp hZ hτ N
  have : SigmaFinite (μ.trim hm) := inferInstance
  refine ⟨((hL2 N).condExp one_le_two).ae_eq hae.symm, ?_, ?_⟩
  · rw [integral_congr_ae hae, integral_condExp hm]
    exact integral_martingale_eq_zero hZ N
  · have hint : Integrable (fun ω => ‖Z N ω‖ ^ (2 : ℝ)) μ := by
      simpa using (hL2 N).integrable_sq
    have h := integral_norm_condExp_rpow_le (μ := μ) (m := m) (p := 2) one_le_two (f := Z N)
      (by simpa using hint)
    simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs] at h
    calc ∫ ω, stoppedValue Z (fun ω => min (τ ω) (N : WithTop ℕ)) ω ^ 2 ∂μ
        = ∫ ω, (μ[Z N | m]) ω ^ 2 ∂μ :=
          integral_congr_ae (hae.mono fun ω hω => by dsimp only; rw [hω])
      _ ≤ ∫ ω, Z N ω ^ 2 ∂μ := h
      _ ≤ B := hB N

/-- A pointwise bound used for the tail estimate of a function with bounded second moment. -/
private lemma norm_indicator_le_sq_div {Ω : Type*} {C : NNReal} (hC : 0 < C) (g : Ω → ℝ)
    (x : Ω) : ‖{y | C ≤ ‖g y‖₊}.indicator g x‖ ≤ g x ^ 2 / C := by
  by_cases hg : C ≤ ‖g x‖₊
  · rw [Set.indicator_of_mem (by exact hg)]
    have hg' : (C : ℝ) ≤ |g x| := by
      rw [← Real.norm_eq_abs, ← coe_nnnorm]
      exact_mod_cast hg
    have hC' : (0 : ℝ) < C := hC
    rw [Real.norm_eq_abs, le_div_iff₀ hC', ← sq_abs (g x), sq]
    exact mul_le_mul_of_nonneg_left hg' (abs_nonneg _)
  · rw [Set.indicator_of_notMem (by exact hg)]
    simp only [norm_zero]
    positivity

/-- A sequence of real functions in `L²` with uniformly bounded second moments is uniformly
integrable in the `L¹` sense. -/
private lemma uniformIntegrable_one_of_integral_sq_le {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {B : ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hB : ∀ n, ∫ ω, f n ω ^ 2 ∂μ ≤ B) :
    UniformIntegrable f 1 μ := by
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top (fun n => (hf n).1) fun ε hε => ?_
  obtain ⟨C, hCpos, hCε⟩ : ∃ C : NNReal, 0 < C ∧ B / ε ≤ C :=
    ⟨(max (B / ε) 1).toNNReal, Real.toNNReal_pos.2 (lt_max_of_lt_right one_pos),
      (le_max_left _ _).trans (Real.le_coe_toNNReal _)⟩
  have hC' : (0 : ℝ) < C := hCpos
  refine ⟨C, fun i => ?_⟩
  have hint : Integrable (fun ω => f i ω ^ 2 / C) μ := (hf i).integrable_sq.div_const _
  calc eLpNorm ({x | C ≤ ‖f i x‖₊}.indicator (f i)) 1 μ
      = ∫⁻ ω, ‖{x | C ≤ ‖f i x‖₊}.indicator (f i) ω‖ₑ ∂μ := eLpNorm_one_eq_lintegral_enorm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (f i ω ^ 2 / C) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_indicator_le_sq_div hCpos (f i) ω)
    _ = ENNReal.ofReal (∫ ω, f i ω ^ 2 / C ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun ω => by positivity)).symm
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div, div_le_iff₀ hC']
        exact (hB i).trans (((div_le_iff₀ hε).1 hCε).trans_eq (mul_comm _ _))

/-- Where the time is finite, the stopped values at the truncated times are eventually constant,
equal to the stopped value at the time itself. -/
private lemma tendsto_stoppedValue_min {Ω : Type*} {Z : ℕ → Ω → ℝ} {τ : Ω → WithTop ℕ} {ω : Ω}
    (hω : τ ω ≠ ⊤) :
    Tendsto (fun N : ℕ => stoppedValue Z (fun ω => min (τ ω) (N : WithTop ℕ)) ω) atTop
      (𝓝 (stoppedValue Z τ ω)) := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hω
  refine tendsto_atTop_of_eventually_const (i₀ := k) fun N hN => ?_
  have hle : τ ω ≤ N := by rw [← hk]; exact WithTop.coe_le_coe.2 hN
  simp only [stoppedValue, min_eq_left hle]

/-- Optional stopping at an almost surely finite stopping time for a martingale bounded in `L²`. -/
theorem integrable_and_integral_stoppedValue_of_L2_bounded {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hZ : Martingale Z ℱ μ) {B : ℝ} (hL2 : ∀ n, MemLp (Z n) 2 μ)
    (hB : ∀ n, ∫ ω, Z n ω ^ 2 ∂μ ≤ B) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ)
    (hfin : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Integrable (stoppedValue Z τ) μ ∧ ∫ ω, stoppedValue Z τ ω ∂μ = ∫ ω, Z 0 ω ∂μ := by
  have hfac := stoppedValue_min_facts hZ hL2 hB hτ
  have hUI : UniformIntegrable
      (fun N : ℕ => stoppedValue Z (fun ω => min (τ ω) (N : WithTop ℕ))) 1 μ :=
    uniformIntegrable_one_of_integral_sq_le (fun N => (hfac N).1) (fun N => (hfac N).2.2)
  have hae : ∀ᵐ ω ∂μ, Tendsto
      (fun N : ℕ => stoppedValue Z (fun ω => min (τ ω) (N : WithTop ℕ)) ω) atTop
      (𝓝 (stoppedValue Z τ ω)) := hfin.mono fun ω hω => tendsto_stoppedValue_min hω
  have hlim : Integrable (stoppedValue Z τ) μ := hUI.integrable_of_ae_tendsto hae
  refine ⟨hlim, ?_⟩
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top (fun N => hUI.1 N)
    (memLp_one_iff_integrable.2 hlim) hUI.2.1 hae
  have hint := tendsto_integral_of_L1' _ hlim.1
    (Eventually.of_forall fun N => (hfac N).1.integrable one_le_two) hL1
  simp only [(fun N => (hfac N).2.1)] at hint
  exact tendsto_nhds_unique hint tendsto_const_nhds

end CERW.Generic.Martingale.LilLower
