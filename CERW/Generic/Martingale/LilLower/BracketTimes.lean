import Mathlib.Probability.Process.Stopping

/-!
# First passage of a predictable process

For a process `V` with `V (k + 1)` measurable for the `k`-th σ-algebra, the first index `n` with
`x ≤ V (n + 1)` is a stopping time. This file records that it is a stopping time, where it is
finite, how it is ordered in the level `x`, and how large `V` is just before it.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory Filter Topology

/-- The first index `n` such that the process at time `n + 1` reaches the level `x`, and `⊤` if
there is none. -/
noncomputable def firstPassage {Ω : Type*} (V : ℕ → Ω → ℝ) (x : ℝ) (ω : Ω) : WithTop ℕ :=
  open scoped Classical in
  if h : ∃ m : ℕ, x ≤ V (m + 1) ω then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

section FirstPassage

variable {Ω : Type*} {V : ℕ → Ω → ℝ} {x y : ℝ} {ω : Ω}

/-- Where the first passage is the index `n`, the level is reached at time `n + 1` and not at any
earlier time `m + 1` with `m < n`. -/
theorem firstPassage_spec {n : ℕ} (h : firstPassage V x ω = (n : WithTop ℕ)) :
    x ≤ V (n + 1) ω ∧ ∀ m < n, V (m + 1) ω < x := by
  unfold firstPassage at h
  split_ifs at h with hex
  · have hn : Nat.find hex = n := by exact_mod_cast h
    refine ⟨?_, fun m hm => ?_⟩
    · rw [← hn]
      exact Nat.find_spec hex
    · exact not_le.1 (Nat.find_min hex (hn ▸ hm))
  · simp at h

/-- The first passage is the index `n` as soon as the level is reached at time `n + 1` and not at
any earlier time. -/
theorem firstPassage_eq_of {n : ℕ} (h1 : x ≤ V (n + 1) ω) (h2 : ∀ m < n, V (m + 1) ω < x) :
    firstPassage V x ω = (n : WithTop ℕ) := by
  have hex : ∃ m : ℕ, x ≤ V (m + 1) ω := ⟨n, h1⟩
  unfold firstPassage
  rw [dif_pos hex]
  have hn : Nat.find hex = n := (Nat.find_eq_iff hex).2 ⟨h1, fun m hm => not_le.2 (h2 m hm)⟩
  rw [hn]

/-- The first passage is finite exactly when the level is reached at some time `m + 1`. -/
theorem firstPassage_ne_top_iff : firstPassage V x ω ≠ ⊤ ↔ ∃ m : ℕ, x ≤ V (m + 1) ω := by
  unfold firstPassage
  split_ifs with hex
  · simp [hex]
  · simp [hex]

/-- A higher level is passed no earlier than a lower one. -/
theorem firstPassage_mono (hxy : x ≤ y) : firstPassage V x ω ≤ firstPassage V y ω := by
  by_cases hy : ∃ m : ℕ, y ≤ V (m + 1) ω
  · have hx : ∃ m : ℕ, x ≤ V (m + 1) ω := hy.imp fun m hm => hxy.trans hm
    unfold firstPassage
    rw [dif_pos hx, dif_pos hy]
    exact_mod_cast Nat.find_min' hx (hxy.trans (Nat.find_spec hy))
  · have hy' : firstPassage V y ω = ⊤ := by
      unfold firstPassage
      rw [dif_neg hy]
    rw [hy']
    exact le_top

/-- If the process tends to infinity along the path, every level is eventually passed. -/
theorem firstPassage_ne_top_of_tendsto (h : Tendsto (fun n => V n ω) atTop atTop) :
    firstPassage V x ω ≠ ⊤ := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 (h.eventually_ge_atTop x)
  exact firstPassage_ne_top_iff.2 ⟨n, hn (n + 1) (Nat.le_succ n)⟩

/-- For levels `xs k` tending to infinity, the first passage times eventually exceed any fixed
index: the process is real valued, so it is bounded on the first `N + 1` times. -/
theorem eventually_le_firstPassage {xs : ℕ → ℝ} (hxs : Tendsto xs atTop atTop) (N : ℕ) :
    ∀ᶠ k in atTop, (N : WithTop ℕ) ≤ firstPassage V (xs k) ω := by
  filter_upwards [hxs.eventually_gt_atTop (∑ m ∈ Finset.range N, |V (m + 1) ω|)] with k hk
  cases hf : firstPassage V (xs k) ω using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    by_contra hlt
    have hnN : n < N := WithTop.coe_lt_coe.1 (not_le.1 hlt)
    have h1 := (firstPassage_spec hf).1
    have h2 : |V (n + 1) ω| ≤ ∑ m ∈ Finset.range N, |V (m + 1) ω| :=
      Finset.single_le_sum (f := fun m => |V (m + 1) ω|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 hnN)
    linarith [le_abs_self (V (n + 1) ω)]

/-- When the process starts at `0` and its increments along the path are at most `J`, the value
just before the first passage of a positive level `x` lies in `[x - J, x)`. -/
theorem firstPassage_window {J : ℝ} (hx : 0 < x) (h0 : V 0 ω = 0)
    (hJ : ∀ k, V (k + 1) ω - V k ω ≤ J) {n : ℕ}
    (h : firstPassage V x ω = (n : WithTop ℕ)) : x - J ≤ V n ω ∧ V n ω < x := by
  obtain ⟨h1, h2⟩ := firstPassage_spec h
  rcases n with _ | n
  · have h3 := hJ 0
    rw [h0] at h3 ⊢
    exact ⟨by linarith, hx⟩
  · have h3 := hJ (n + 1)
    exact ⟨by linarith, h2 n (Nat.lt_succ_self n)⟩

/-- A predictable process gives a stopping time: the event `firstPassage V x ≤ n` is a union of
the events `x ≤ V (m + 1)` for `m ≤ n`, each measurable at time `m`. -/
theorem isStoppingTime_firstPassage {m0 : MeasurableSpace Ω} {ℱ : Filtration ℕ m0}
    (hV : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) (x : ℝ) :
    IsStoppingTime ℱ (firstPassage V x) := by
  intro i
  have hset : {ω | firstPassage V x ω ≤ WithTop.some i} =
      ⋃ m ∈ Finset.range (i + 1), {ω | x ≤ V (m + 1) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · intro h
      have hne : firstPassage V x ω ≠ ⊤ := ne_top_of_le_ne_top (WithTop.natCast_ne_top i) h
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
      have hn' : firstPassage V x ω = (n : WithTop ℕ) := hn.symm
      refine ⟨n, ?_, (firstPassage_spec hn').1⟩
      rw [hn'] at h
      have hni : n ≤ i := WithTop.coe_le_coe.1 h
      omega
    · rintro ⟨m, hm, hxm⟩
      have hex : ∃ m : ℕ, x ≤ V (m + 1) ω := ⟨m, hxm⟩
      unfold firstPassage
      rw [dif_pos hex]
      exact WithTop.coe_le_coe.2 ((Nat.find_min' hex hxm).trans (Nat.lt_succ_iff.1 hm))
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun m hm => ?_
  have hmi : m ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  exact ℱ.mono hmi _ (measurableSet_le measurable_const (hV m).measurable)

end FirstPassage

end CERW.Generic.Martingale.LilLower
