module

public import CERW.LimitShapes.Event
public import CERW.Support.Law.Dynkin
public import Mathlib.Probability.Process.Stopping

@[expose] public section

/-!
# Bounded stopping for distance crossings

The first stop in `eq:distance-crossing` detects distance, exterior occupation,
or the terminal horizon. All stopping decisions depend only on the finite past.
-/

namespace CERW.LimitShapes.Crossing.ExponentialExit

open CERW LatticeProb MeasureTheory CERW.Support.Law

variable {d : ℕ} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (a : ℝ) (L : ℕ) (s : ℝ)

/-- The first distance or occupation crossing, capped at the terminal horizon. -/
noncomputable def crossingStop (N : ℕ) (X : ℕ → Site d) : ℕ :=
  Nat.find (show ∃ t, t ≤ N ∧ (t = N ∨
    s ≤ Metric.infDist (toSpace (X t)) {v | Ψ v ≤ a} ∨
    L + 1 ≤ exteriorLocalTime Ψ X t a) from ⟨N, le_rfl, Or.inl rfl⟩)

/-- The stopping time is bounded and satisfies one of its three stopping conditions. -/
theorem crossingStop_spec (N : ℕ) (X : ℕ → Site d) :
    crossingStop Ψ a L s N X ≤ N ∧
      (crossingStop Ψ a L s N X = N ∨
      s ≤ Metric.infDist (toSpace (X (crossingStop Ψ a L s N X))) {v | Ψ v ≤ a} ∨
      L + 1 ≤ exteriorLocalTime Ψ X (crossingStop Ψ a L s N X) a) :=
  by
    unfold crossingStop
    exact Nat.find_spec (show ∃ t, t ≤ N ∧ (t = N ∨
      s ≤ Metric.infDist (toSpace (X t)) {v | Ψ v ≤ a} ∨
      L + 1 ≤ exteriorLocalTime Ψ X t a) from ⟨N, le_rfl, Or.inl rfl⟩)

/-- Every time strictly before the stop is below the horizon and both thresholds. -/
theorem crossingStop_before (N : ℕ) (X : ℕ → Site d) {j : ℕ}
    (hj : j < crossingStop Ψ a L s N X) :
    j < N ∧ Metric.infDist (toSpace (X j)) {v | Ψ v ≤ a} < s ∧
      exteriorLocalTime Ψ X j a ≤ L := by
  have hb := (crossingStop_spec Ψ a L s N X).1
  have hn := Nat.find_min (show ∃ t, t ≤ N ∧ (t = N ∨
    s ≤ Metric.infDist (toSpace (X t)) {v | Ψ v ≤ a} ∨
    L + 1 ≤ exteriorLocalTime Ψ X t a) from ⟨N, le_rfl, Or.inl rfl⟩) hj
  have hdist : ¬ s ≤ Metric.infDist (toSpace (X j)) {v | Ψ v ≤ a} :=
    fun h => hn ⟨by omega, Or.inr (Or.inl h)⟩
  have hlocal : ¬ L + 1 ≤ exteriorLocalTime Ψ X j a :=
    fun h => hn ⟨by omega, Or.inr (Or.inr h)⟩
  exact ⟨by omega, lt_of_not_ge hdist, by omega⟩

/-- Stopping by a given time is equivalent to a qualifying time in its finite past. -/
theorem crossingStop_le_iff (N : ℕ) (X : ℕ → Site d) (n : ℕ) :
    crossingStop Ψ a L s N X ≤ n ↔ ∃ t ≤ n, t ≤ N ∧
      (t = N ∨ s ≤ Metric.infDist (toSpace (X t)) {v | Ψ v ≤ a} ∨
        L + 1 ≤ exteriorLocalTime Ψ X t a) := by
  constructor
  · intro h
    exact ⟨_, h, crossingStop_spec Ψ a L s N X⟩
  · rintro ⟨t, htn, ht⟩
    exact (Nat.find_min' _ ht).trans htn

/-- A local time outside the norm ball is bounded by the exterior maximum. -/
theorem localTime_le_exterior (X : ℕ → Site d) (n : ℕ) (z : Site d)
    (hz : a ≤ Ψ (toSpace z)) : localTime X n z ≤ exteriorLocalTime Ψ X n a := by
  classical
  by_cases hm : z ∈ departureRange X n
  · exact Finset.le_sup (Finset.mem_filter.mpr ⟨hm, hz⟩)
  · have hzero : localTime X n z = 0 := by
      have := mt mem_departureRange_iff.mpr hm
      omega
    rw [hzero]
    exact Nat.zero_le _

/-- The exterior maximum increases by at most one per departure. -/
theorem exteriorLocalTime_succ_le (X : ℕ → Site d) (n : ℕ) :
    exteriorLocalTime Ψ X (n + 1) a ≤ exteriorLocalTime Ψ X n a + 1 := by
  classical
  refine Finset.sup_le fun z hz => ?_
  have hlocal := localTime_le_exterior Ψ a X n z (Finset.mem_filter.mp hz).2
  have hstep : localTime X (n + 1) z ≤ localTime X n z + 1 := by
    simp only [localTime, Finset.range_add_one, Finset.filter_insert]
    split_ifs
    · exact Finset.card_insert_le _ _
    · omega
  omega

/-- Occupation at the first crossing overshoots the threshold by at most one. -/
theorem exteriorLocalTime_crossingStop_le (N : ℕ) (X : ℕ → Site d) :
    exteriorLocalTime Ψ X (crossingStop Ψ a L s N X) a ≤ L + 1 := by
  generalize ht : crossingStop Ψ a L s N X = t
  cases t with
  | zero => simp [exteriorLocalTime, departureRange]
  | succ k =>
    have hb := (crossingStop_before Ψ a L s N X (j := k) (by omega)).2.2
    have hs := exteriorLocalTime_succ_le Ψ a X k
    omega

/-- The exterior maximum is monotone in elapsed time. -/
theorem exteriorLocalTime_mono (X : ℕ → Site d) {m n : ℕ} (hmn : m ≤ n) :
    exteriorLocalTime Ψ X m a ≤ exteriorLocalTime Ψ X n a := by
  classical
  refine Finset.sup_le fun z hz => ?_
  have hlocal : localTime X m z ≤ localTime X n z := by
    exact Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.range_subset_range.mpr hmn))
  exact hlocal.trans (localTime_le_exterior Ψ a X n z (Finset.mem_filter.mp hz).2)

/-- A distance crossing attained with low occupation stops at the distance threshold. -/
theorem distance_le_at_crossingStop (N : ℕ) (X : ℕ → Site d)
    (h : ∃ t ≤ N, exteriorLocalTime Ψ X t a ≤ L ∧
      ∃ j ≤ t, s ≤ Metric.infDist (toSpace (X j)) {v | Ψ v ≤ a}) :
    s ≤ Metric.infDist (toSpace (X (crossingStop Ψ a L s N X))) {v | Ψ v ≤ a} := by
  obtain ⟨t, htN, htL, j, hjt, hj⟩ := h
  have hstop : crossingStop Ψ a L s N X ≤ j :=
    (crossingStop_le_iff Ψ a L s N X j).mpr
      ⟨j, le_rfl, hjt.trans htN, Or.inr (Or.inl hj)⟩
  rcases (crossingStop_spec Ψ a L s N X).2 with hN | hd | hL
  · have heq : crossingStop Ψ a L s N X = j := by omega
    simpa only [heq] using hj
  · exact hd
  · have hm := exteriorLocalTime_mono Ψ a X (hstop.trans hjt)
    omega

/-- Exterior occupation is determined by departures in the observed prefix. -/
theorem exteriorLocalTime_congr {X Y : ℕ → Site d} {n : ℕ}
    (h : ∀ j ≤ n, X j = Y j) : exteriorLocalTime Ψ X n a =
      exteriorLocalTime Ψ Y n a := by
  classical
  have hr : departureRange X n = departureRange Y n :=
    Finset.image_congr fun j hj => h j (Finset.mem_range.mp hj).le
  have hl (z : Site d) : localTime X n z = localTime Y n z := by
    unfold localTime
    congr 1
    apply Finset.filter_congr
    intro j hj
    rw [h j (Finset.mem_range.mp hj).le]
  unfold exteriorLocalTime
  rw [hr]
  exact Finset.sup_congr rfl (fun z _ => hl z)

/-- The bounded crossing time is a stopping time for the actual path filtration. -/
theorem isStoppingTime_crossingStop {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ j, Measurable (X j)) (N : ℕ) :
    IsStoppingTime (pathFiltration hX)
      (fun ω => (crossingStop Ψ a L s N (X · ω) : WithTop ℕ)) := by
  intro n
  change MeasurableSet[pathFiltration hX n]
    {ω | (crossingStop Ψ a L s N (X · ω) : WithTop ℕ) ≤ (n : WithTop ℕ)}
  have hp : {ω | (crossingStop Ψ a L s N (X · ω) : WithTop ℕ) ≤
      (n : WithTop ℕ)} =
      (pastPath X n) ⁻¹' {p | crossingStop Ψ a L s N (extendPath p) ≤ n} := by
    ext ω
    change ((crossingStop Ψ a L s N (X · ω) : WithTop ℕ) ≤
      (n : WithTop ℕ)) ↔ crossingStop Ψ a L s N (extendPath (pastPath X n ω)) ≤ n
    rw [show ((crossingStop Ψ a L s N (X · ω) : WithTop ℕ) ≤
      (n : WithTop ℕ)) ↔ crossingStop Ψ a L s N (X · ω) ≤ n by exact_mod_cast Iff.rfl]
    simp only [crossingStop_le_iff]
    apply exists_congr
    intro t
    by_cases ht : t ≤ n
    · have heq := extendPath_pastPath X ht ω
      have hext := exteriorLocalTime_congr Ψ a
        (fun j hj => extendPath_pastPath X (hj.trans ht) ω)
      simp only [heq, hext]
    · simp only [ht, false_and]
  rw [hp]
  exact (Set.to_countable _).measurableSet.preimage (comap_measurable (pastPath X n))

end CERW.LimitShapes.Crossing.ExponentialExit
