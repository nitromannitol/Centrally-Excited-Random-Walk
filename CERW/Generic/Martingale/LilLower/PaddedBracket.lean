import CERW.Generic.Martingale.LilLower.ProdCondExp

/-!
# The bracket of the padded process

The padded process takes the increment of `S` while a gate `G` is open and a unit sign afterwards.
Its conditional second moments are `G j * c j + (1 - G j)`, where `c j` is that of `S`, so its
bracket `paddedBracket c G n = ∑_{j<n} (G j * c j + (1 - G j))` depends only on the point of the
first factor. Along a path with `c j ≥ 0`, a gate with values `0` and `1` that never reopens, and
divergent `∑ c j`, the padded bracket tends to infinity.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory Filter Topology

variable {Ω : Type*}

/-- The bracket of the padded process: `c j` while the gate is open and `1` once it has closed. -/
noncomputable def paddedBracket (c G : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, (G j ω * c j ω + (1 - G j ω))

/-- The increment of the padded bracket at time `n`. -/
theorem paddedBracket_succ_sub (c G : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    paddedBracket c G (n + 1) ω - paddedBracket c G n ω = G n ω * c n ω + (1 - G n ω) := by
  unfold paddedBracket
  rw [Finset.sum_range_succ, add_sub_cancel_left]

/-- The padded bracket is nondecreasing along a path with nonnegative `c` and a gate with values
`0` and `1`. -/
theorem paddedBracket_mono {c G : ℕ → Ω → ℝ} {ω : Ω} (hc : ∀ j, 0 ≤ c j ω)
    (hG : ∀ j, G j ω = 0 ∨ G j ω = 1) (n : ℕ) :
    paddedBracket c G n ω ≤ paddedBracket c G (n + 1) ω := by
  have h := paddedBracket_succ_sub c G n ω
  have h0 := hc n
  rcases hG n with h1 | h1 <;> rw [h1] at h <;> linarith

/-- While the gate has been open at every time before `n`, the padded bracket is the bracket. -/
theorem paddedBracket_eq_of_gate {c G : ℕ → Ω → ℝ} {ω : Ω} {n : ℕ} (h : ∀ j < n, G j ω = 1) :
    paddedBracket c G n ω = ∑ j ∈ Finset.range n, c j ω := by
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j (Finset.mem_range.1 hj)]
  ring

/-- The one-step increment of the padded bracket is at most `max (c n) 1`. -/
theorem paddedBracket_jump_le {c G : ℕ → Ω → ℝ} {ω : Ω}
    (hG : ∀ j, G j ω = 0 ∨ G j ω = 1) (n : ℕ) :
    paddedBracket c G (n + 1) ω - paddedBracket c G n ω ≤ max (c n ω) 1 := by
  rw [paddedBracket_succ_sub]
  rcases hG n with h | h <;> rw [h]
  · simp
  · simp

/-- The padded bracket tends to infinity along a path whose bracket does, for a gate with values
`0` and `1` that never reopens: either the gate stays open and the padded bracket is the bracket,
or it closes at some time and the padded bracket then grows by `1` at each step. -/
theorem tendsto_paddedBracket_atTop {c G : ℕ → Ω → ℝ} {ω : Ω} (hc : ∀ j, 0 ≤ c j ω)
    (hG : ∀ j, G j ω = 0 ∨ G j ω = 1) (hanti : ∀ j, G (j + 1) ω ≤ G j ω)
    (hP : Tendsto (fun n => ∑ j ∈ Finset.range n, c j ω) atTop atTop) :
    Tendsto (fun n => paddedBracket c G n ω) atTop atTop := by
  by_cases hopen : ∀ j, G j ω = 1
  · refine hP.congr fun n => ?_
    exact (paddedBracket_eq_of_gate fun j _ => hopen j).symm
  · obtain ⟨j₀, hj₀⟩ := not_forall.1 hopen
    have hzero : ∀ m, G (j₀ + m) ω = 0 := by
      intro m
      induction m with
      | zero => exact (hG j₀).resolve_right hj₀
      | succ m ih =>
        have h1 := hanti (j₀ + m)
        rw [ih] at h1
        rcases hG (j₀ + m + 1) with h | h
        · exact h
        · rw [h] at h1
          exact absurd h1 (by norm_num)
    have hgrow : ∀ m : ℕ, (m : ℝ) ≤ paddedBracket c G (j₀ + m) ω := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.cast_zero, add_zero]
        exact Finset.sum_nonneg fun j _ => by
          have h0 := hc j
          rcases hG j with h1 | h1 <;> rw [h1] <;> linarith
      | succ m ih =>
        have h := paddedBracket_succ_sub c G (j₀ + m) ω
        rw [hzero m] at h
        rw [← add_assoc, Nat.cast_succ]
        linarith
    refine tendsto_atTop_atTop.2 fun b => ⟨j₀ + ⌈b⌉₊, fun a ha => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right _ _) ha)
    have hm : ⌈b⌉₊ ≤ m := by omega
    exact (Nat.le_ceil b).trans ((Nat.cast_le.2 hm).trans (hgrow m))

/-- A function of the first coordinate that is measurable for a sub-σ-algebra of the first factor
is measurable for the join with any sub-σ-algebra of the second factor. -/
theorem stronglyMeasurable_comp_fst_joinSigma {Ξ : Type*} {𝒢 : MeasurableSpace Ω}
    (ℋ : MeasurableSpace Ξ) {f : Ω → ℝ} (hf : StronglyMeasurable[𝒢] f) :
    StronglyMeasurable[joinSigma 𝒢 ℋ] (fun z : Ω × Ξ => f z.1) := by
  have hfst : @Measurable _ _ (joinSigma 𝒢 ℋ) 𝒢 Prod.fst := Measurable.of_comap_le le_sup_left
  exact hf.comp_measurable hfst

end CERW.Generic.Martingale.LilLower
