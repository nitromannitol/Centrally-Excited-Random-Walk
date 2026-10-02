import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# A cumulative predictable level gate

For an adapted process `K` the gate `levelGate K ε N j` is `1` while no value `K i` with
`N ≤ i ≤ j` has exceeded the level `ε`, and `0` from the first time one does. It is open before
time `N`, takes only the values `0` and `1`, never reopens once closed, and is measurable at time
`j`. Along a path with `K i ≤ ε` for all `i ≥ N` it is open at every time.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory Filter Topology

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

open scoped Classical in
/-- The gate that is open at time `j` exactly when `K i ≤ ε` for every `i` with `N ≤ i ≤ j`. -/
noncomputable def levelGate (K : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) (j : ℕ) (ω : Ω) : ℝ :=
  if ∀ i, N ≤ i → i ≤ j → K i ω ≤ ε then 1 else 0

/-- The gate takes only the values `0` and `1`. -/
theorem levelGate_eq_zero_or_one (K : ℕ → Ω → ℝ) (ε : ℝ) (N j : ℕ) (ω : Ω) :
    levelGate K ε N j ω = 0 ∨ levelGate K ε N j ω = 1 := by
  unfold levelGate
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The gate is open at time `j` exactly when `K i ≤ ε` for every `i` with `N ≤ i ≤ j`. -/
theorem levelGate_eq_one_iff (K : ℕ → Ω → ℝ) (ε : ℝ) (N j : ℕ) (ω : Ω) :
    levelGate K ε N j ω = 1 ↔ ∀ i, N ≤ i → i ≤ j → K i ω ≤ ε := by
  unfold levelGate
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false zero_ne_one h

/-- The gate is open before time `N`. -/
theorem levelGate_eq_one_of_lt (K : ℕ → Ω → ℝ) (ε : ℝ) {N j : ℕ} (hj : j < N) (ω : Ω) :
    levelGate K ε N j ω = 1 := by
  rw [levelGate_eq_one_iff]
  intro i hi hij
  omega

/-- Once the gate has closed it stays closed. -/
theorem levelGate_antitone (K : ℕ → Ω → ℝ) (ε : ℝ) (N j : ℕ) (ω : Ω) :
    levelGate K ε N (j + 1) ω ≤ levelGate K ε N j ω := by
  rcases levelGate_eq_zero_or_one K ε N (j + 1) ω with h | h
  · rw [h]
    rcases levelGate_eq_zero_or_one K ε N j ω with h' | h'
    · rw [h']
    · rw [h']
      exact zero_le_one
  · have h1 := (levelGate_eq_one_iff K ε N (j + 1) ω).1 h
    have h2 : levelGate K ε N j ω = 1 :=
      (levelGate_eq_one_iff K ε N j ω).2 fun i hi hij => h1 i hi (Nat.le_succ_of_le hij)
    rw [h, h2]

/-- If `K i ω ≤ ε` for all `i ≥ N`, the gate is open at every time. -/
theorem levelGate_eq_one_of_forall_le (K : ℕ → Ω → ℝ) (ε : ℝ) (N : ℕ) {ω : Ω}
    (h : ∀ i, N ≤ i → K i ω ≤ ε) (j : ℕ) : levelGate K ε N j ω = 1 := by
  rw [levelGate_eq_one_iff]
  exact fun i hi _ => h i hi

/-- The gate at time `j` is measurable at time `j` when every `K i` is measurable at time `i`. -/
theorem stronglyMeasurable_levelGate {ℱ : Filtration ℕ m0} {K : ℕ → Ω → ℝ}
    (hK : ∀ i, StronglyMeasurable[ℱ i] (K i)) (ε : ℝ) (N j : ℕ) :
    StronglyMeasurable[ℱ j] (levelGate K ε N j) := by
  have hset : MeasurableSet[ℱ j] {ω | ∀ i, N ≤ i → i ≤ j → K i ω ≤ ε} := by
    have h : {ω | ∀ i, N ≤ i → i ≤ j → K i ω ≤ ε} = ⋂ i ∈ Finset.Icc N j, {ω | K i ω ≤ ε} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_Icc, and_imp]
    rw [h]
    refine Finset.measurableSet_biInter _ fun i hi => ?_
    exact ℱ.mono (Finset.mem_Icc.1 hi).2 _
      (measurableSet_le (hK i).measurable measurable_const)
  refine Measurable.stronglyMeasurable ?_
  exact Measurable.ite hset measurable_const measurable_const

/-- A sequence tending to `0` stays below any positive level from some time on. -/
theorem exists_forall_le_of_tendsto_zero {K : ℕ → ℝ} (h : Tendsto K atTop (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ i, N ≤ i → K i ≤ ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually_le_const hε)
  exact ⟨N, hN⟩

end CERW.Generic.Martingale.LilLower
