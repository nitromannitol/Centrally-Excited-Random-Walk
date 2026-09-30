import Mathlib.Probability.Martingale.Basic

/-!
# Martingales with almost surely bounded increments

Freedman's inequality, as used here, asks for increments bounded at every sample point. A
martingale whose increments are bounded by `b` only almost surely agrees almost surely, at all
times at once, with the martingale `M_0 + Σ_{j<i} clamp_b(M_{j+1} - M_j)`. That martingale has
surely bounded increments. The clamped increment is a.s. equal to the original one, so its
conditional mean is still `0`.
-/

namespace CERW.Generic.Martingale

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- Clamp a real number to the interval `[-b, b]`. -/
private noncomputable def clamp (b x : ℝ) : ℝ := max (-b) (min b x)

/-- The process formed from `M` by clamping every increment to `[-b, b]`. -/
private noncomputable def clamped (M : ℕ → Ω → ℝ) (b : ℝ) : ℕ → Ω → ℝ :=
  fun i ω => M 0 ω + ∑ j ∈ range i, clamp b (M (j + 1) ω - M j ω)

/-- The clamped value lies in `[-b, b]`. -/
private lemma abs_clamp_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |clamp b x| ≤ b := by
  rw [abs_le]
  simp only [clamp]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clamping leaves a value already in `[-b, b]` unchanged. -/
private lemma clamp_eq_self {b x : ℝ} (hx : |x| ≤ b) : clamp b x = x := by
  rw [abs_le] at hx
  simp only [clamp]
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Clamping is continuous. -/
private lemma continuous_clamp (b : ℝ) : Continuous (clamp b) := by
  unfold clamp
  exact continuous_const.max (continuous_const.min continuous_id)

/-- Consecutive values of `clamped M b` differ by the clamped increment. -/
private lemma clamped_succ_sub (M : ℕ → Ω → ℝ) (b : ℝ) (i : ℕ) (ω : Ω) :
    clamped M b (i + 1) ω - clamped M b i ω = clamp b (M (i + 1) ω - M i ω) := by
  simp only [clamped, sum_range_succ]
  ring

/-- If every increment of `M` is already in `[-b, b]`, then `clamped M b` agrees with `M`. -/
private lemma clamped_eq_of (M : ℕ → Ω → ℝ) (b : ℝ) {ω : Ω}
    (h : ∀ j, clamp b (M (j + 1) ω - M j ω) = M (j + 1) ω - M j ω) (i : ℕ) :
    clamped M b i ω = M i ω := by
  simp only [clamped]
  rw [sum_congr rfl (fun j _ => h j), sum_range_sub (fun j => M j ω)]
  ring

/-- `clamped M b` is strongly adapted whenever `M` is. -/
private lemma stronglyAdapted_clamped {ℱ : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hadp : StronglyAdapted ℱ M) (b : ℝ) : StronglyAdapted ℱ (clamped M b) := by
  intro i
  have h0 : StronglyMeasurable[ℱ i] (M 0) := (hadp 0).mono (ℱ.mono (Nat.zero_le i))
  have hsum : StronglyMeasurable[ℱ i]
      (fun ω => ∑ j ∈ range i, clamp b (M (j + 1) ω - M j ω)) := by
    have hfun : StronglyMeasurable[ℱ i]
        (∑ j ∈ range i, fun ω => clamp b (M (j + 1) ω - M j ω)) := by
      refine Finset.stronglyMeasurable_sum
        (f := fun j (ω : Ω) => clamp b (M (j + 1) ω - M j ω)) (range i) ?_
      intro j hj
      have hji : j + 1 ≤ i := Nat.succ_le_of_lt (mem_range.mp hj)
      have hjm : j ≤ i := le_trans (Nat.le_succ j) hji
      exact (continuous_clamp b).comp_stronglyMeasurable
        (((hadp (j + 1)).mono (ℱ.mono hji)).sub ((hadp j).mono (ℱ.mono hjm)))
    have heq : (∑ j ∈ range i, fun ω => clamp b (M (j + 1) ω - M j ω)) =
        fun ω => ∑ j ∈ range i, clamp b (M (j + 1) ω - M j ω) := by
      funext ω
      exact Finset.sum_apply ω (range i) fun j (ω : Ω) => clamp b (M (j + 1) ω - M j ω)
    rwa [heq] at hfun
  change StronglyMeasurable[ℱ i]
    (fun ω => M 0 ω + ∑ j ∈ range i, clamp b (M (j + 1) ω - M j ω))
  exact h0.add hsum

/-- A martingale with increments bounded by `b` almost surely agrees almost surely, at all times
at once, with a martingale with the same initial value whose increments are bounded by `b`
everywhere. -/
theorem exists_martingale_clamp {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℕ m0}
    {M : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P) {b : ℝ} (hb : 0 ≤ b)
    (hinc : ∀ i, ∀ᵐ ω ∂P, |M (i + 1) ω - M i ω| ≤ b) :
    ∃ M' : ℕ → Ω → ℝ, Martingale M' ℱ P ∧ (∀ i ω, |M' (i + 1) ω - M' i ω| ≤ b) ∧
      (∀ ω, M' 0 ω = M 0 ω) ∧ ∀ᵐ ω ∂P, ∀ i, M' i ω = M i ω := by
  have hgood : ∀ᵐ ω ∂P, ∀ j, clamp b (M (j + 1) ω - M j ω) = M (j + 1) ω - M j ω :=
    ae_all_iff.mpr fun j => (hinc j).mono fun ω hω => clamp_eq_self hω
  refine ⟨clamped M b, ?_, ?_, ?_, ?_⟩
  · exact hmart.congr (stronglyAdapted_clamped hmart.stronglyAdapted b)
      (fun t => hgood.mono fun ω hω => (clamped_eq_of M b hω t).symm)
  · intro i ω
    rw [clamped_succ_sub M b i ω]
    exact abs_clamp_le hb _
  · intro ω
    simp only [clamped, sum_range_zero, add_zero]
  · exact hgood.mono fun ω hω i => clamped_eq_of M b hω i

end CERW.Generic.Martingale
