import CERW.Generic.Martingale.Clamp

/-!
# Martingales with increments bounded by a predictable level

The version of `CERW.Generic.Martingale.exists_martingale_clamp` with a predictable level
`B_{n+1}` in place of a constant. The increments are clamped to `[-(B_{n+1} ∨ 0), B_{n+1} ∨ 0]`.
The conditioned blocks of the lower half of the law of the iterated logarithm need increments
bounded at every sample point.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Finset

/-- Clamp a real number to the interval `[-b, b]`. -/
private noncomputable def cp_clamp (b x : ℝ) : ℝ := max (-b) (min b x)

/-- The process formed from `M` by clamping the increment `n → n + 1` to the predictable level
`max (B (n + 1)) 0`. -/
private noncomputable def cp_clamped {Ω : Type*} (M B : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun i ω => M 0 ω + ∑ j ∈ range i, cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω)

/-- The clamped value lies in `[-b, b]`. -/
private lemma cp_abs_clamp_le {b : ℝ} (hb : 0 ≤ b) (x : ℝ) : |cp_clamp b x| ≤ b := by
  rw [abs_le]
  simp only [cp_clamp]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clamping leaves a value already in `[-b, b]` unchanged. -/
private lemma cp_clamp_eq_self {b x : ℝ} (hx : |x| ≤ b) : cp_clamp b x = x := by
  rw [abs_le] at hx
  simp only [cp_clamp]
  rw [min_eq_right hx.2, max_eq_right hx.1]

/-- Consecutive values of `cp_clamped M B` differ by the clamped increment. -/
private lemma cp_clamped_succ_sub {Ω : Type*} (M B : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) :
    cp_clamped M B (i + 1) ω - cp_clamped M B i ω =
      cp_clamp (max (B (i + 1) ω) 0) (M (i + 1) ω - M i ω) := by
  simp only [cp_clamped, sum_range_succ]
  ring

/-- If every increment of `M` is already within its level, then `cp_clamped M B` agrees
with `M`. -/
private lemma cp_clamped_eq_of {Ω : Type*} (M B : ℕ → Ω → ℝ) {ω : Ω}
    (h : ∀ j, cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω) = M (j + 1) ω - M j ω)
    (i : ℕ) : cp_clamped M B i ω = M i ω := by
  simp only [cp_clamped]
  rw [sum_congr rfl (fun j _ => h j), sum_range_sub (fun j => M j ω)]
  ring

/-- The clamped increment `j → j + 1` is `ℱ (j + 1)`-measurable. -/
private lemma cp_measurable_term {Ω : Type*} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℕ m0}
    {M B : ℕ → Ω → ℝ} (hadp : StronglyAdapted ℱ M)
    (hB : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) (j : ℕ) :
    Measurable[ℱ (j + 1)]
      (fun ω => cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω)) := by
  have hBm : Measurable[ℱ (j + 1)] (B (j + 1)) :=
    ((hB j).mono (ℱ.mono (Nat.le_succ j))).measurable
  have hM1 : Measurable[ℱ (j + 1)] (M (j + 1)) := (hadp (j + 1)).measurable
  have hM0 : Measurable[ℱ (j + 1)] (M j) :=
    ((hadp j).mono (ℱ.mono (Nat.le_succ j))).measurable
  have hlev : Measurable[ℱ (j + 1)] (fun ω => max (B (j + 1) ω) 0) :=
    hBm.max measurable_const
  have hdiff : Measurable[ℱ (j + 1)] (fun ω => M (j + 1) ω - M j ω) := hM1.sub hM0
  unfold cp_clamp
  exact hlev.neg.max (hlev.min hdiff)

/-- `cp_clamped M B` is strongly adapted whenever `M` is and `B (n + 1)` is `ℱ n`-measurable. -/
private lemma cp_stronglyAdapted_clamped {Ω : Type*} {m0 : MeasurableSpace Ω}
    {ℱ : Filtration ℕ m0} {M B : ℕ → Ω → ℝ} (hadp : StronglyAdapted ℱ M)
    (hB : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) : StronglyAdapted ℱ (cp_clamped M B) := by
  intro i
  have h0 : StronglyMeasurable[ℱ i] (M 0) := (hadp 0).mono (ℱ.mono (Nat.zero_le i))
  have hsum : StronglyMeasurable[ℱ i]
      (∑ j ∈ range i, fun ω => cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω)) := by
    refine Finset.stronglyMeasurable_sum
      (f := fun j (ω : Ω) => cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω)) (range i) ?_
    intro j hj
    have hji : j + 1 ≤ i := Nat.succ_le_of_lt (mem_range.mp hj)
    exact ((cp_measurable_term hadp hB j).mono (ℱ.mono hji) le_rfl).stronglyMeasurable
  have heq : (∑ j ∈ range i, fun ω => cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω)) =
      fun ω => ∑ j ∈ range i, cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω) := by
    funext ω
    exact Finset.sum_apply ω (range i)
      fun j (ω : Ω) => cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω)
  rw [heq] at hsum
  change StronglyMeasurable[ℱ i]
    (fun ω => M 0 ω + ∑ j ∈ range i, cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω))
  exact h0.add hsum

/-- A martingale with increments bounded almost surely by a predictable `B_{n+1}` agrees almost
surely, at all times at once, with a martingale whose increments are surely at most
`B_{n+1} ∨ 0`. -/
theorem exists_martingale_clamp_pred {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ m0} {M B : ℕ → Ω → ℝ} (hmart : Martingale M ℱ P)
    (hB : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)))
    (hinc : ∀ᵐ ω ∂P, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω) :
    ∃ M' : ℕ → Ω → ℝ, Martingale M' ℱ P ∧
      (∀ n ω, |M' (n + 1) ω - M' n ω| ≤ max (B (n + 1) ω) 0) ∧ (∀ ω, M' 0 ω = M 0 ω) ∧
      ∀ᵐ ω ∂P, ∀ n, M' n ω = M n ω := by
  have hgood : ∀ᵐ ω ∂P, ∀ j, cp_clamp (max (B (j + 1) ω) 0) (M (j + 1) ω - M j ω) =
      M (j + 1) ω - M j ω :=
    hinc.mono fun ω hω j => cp_clamp_eq_self ((hω j).trans (le_max_left _ _))
  refine ⟨cp_clamped M B, ?_, ?_, ?_, ?_⟩
  · exact hmart.congr (cp_stronglyAdapted_clamped hmart.stronglyAdapted hB)
      (fun t => hgood.mono fun ω hω => (cp_clamped_eq_of M B hω t).symm)
  · intro n ω
    rw [cp_clamped_succ_sub M B n ω]
    exact cp_abs_clamp_le (le_max_right _ _) _
  · intro ω
    simp only [cp_clamped, sum_range_zero, add_zero]
  · exact hgood.mono fun ω hω i => cp_clamped_eq_of M B hω i

end CERW.Generic.Martingale.LilAssembly
