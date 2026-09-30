import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.Cells

/-!
# The contact cell

Let `D = D_n` be the cell set of the walk, and let `b = inf {|y| : y ∉ D}` be its centred
inradius (`eq:bm`). The open ball `B(0, b)` lies in `D`. Some point `y₀` with `|y₀| = b` lies in
the closure of the complement. Only finitely many cells meet a neighbourhood of `y₀`, so the
closure of one unoccupied cell `C_z` contains `y₀`. Hence `ℓ_n(z) = 0`, `|z - y₀| ≤ √d/2` and
`|z| ≥ b` (`eq:contactcell`). No regularity of `∂D` is used.
-/

namespace CERW.Support.Contact

open LatticeProb CERW CERW.Support.Occupation

variable {d : ℕ}

/-- A nonempty set of `ℝ^d` has a point in its closure whose norm is the infimum of the norms
over the set. -/
theorem exists_mem_closure_norm_eq_sInf {E : Set (EuclideanSpace ℝ (Fin d))} (hE : E.Nonempty) :
    ∃ y₀ ∈ closure E, ‖y₀‖ = sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' E) := by
  set b := sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' E) with hb
  have hbdd : BddBelow ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' E) :=
    ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg y⟩
  have hle : ∀ y ∈ E, b ≤ ‖y‖ := fun y hy => csInf_le hbdd ⟨y, hy, rfl⟩
  have hFc : IsCompact (closure E ∩ Metric.closedBall 0 (b + 1)) :=
    (isCompact_closedBall 0 (b + 1)).inter_left isClosed_closure
  have hlt : b < b + 1 := by linarith
  obtain ⟨_, ⟨y1, hy1, rfl⟩, h1⟩ := exists_lt_of_csInf_lt (hE.image _) hlt
  have hFne : (closure E ∩ Metric.closedBall 0 (b + 1)).Nonempty :=
    ⟨y1, subset_closure hy1, by rw [mem_closedBall_zero_iff]; exact h1.le⟩
  obtain ⟨y₀, hy₀F, hmin⟩ := hFc.exists_isMinOn hFne continuous_norm.continuousOn
  refine ⟨y₀, hy₀F.1, le_antisymm ?_ ?_⟩
  · refine le_of_not_gt fun hcon => ?_
    obtain ⟨_, ⟨y2, hy2, rfl⟩, h2⟩ := exists_lt_of_csInf_lt (hE.image _) (lt_min hcon hlt)
    have hy2F : y2 ∈ closure E ∩ Metric.closedBall 0 (b + 1) :=
      ⟨subset_closure hy2, by
        rw [mem_closedBall_zero_iff]
        exact (h2.trans_le (min_le_right _ _)).le⟩
    have h3 : ‖y₀‖ ≤ ‖y2‖ := isMinOn_iff.mp hmin y2 hy2F
    have h4 := h2.trans_le (min_le_left _ _)
    linarith
  · exact closure_minimal hle (isClosed_le continuous_const continuous_norm) hy₀F.1

/-- A point of the closure of the complement of `D_n` lies in the closure of the cell of an
unvisited site: only finitely many cells meet a unit ball around it. -/
theorem exists_unvisited_mem_closure_cell (X : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy : y₀ ∈ closure (cellSet X n)ᶜ) :
    ∃ z : Site d, z ∉ departureRange X n ∧ y₀ ∈ closure (cell z) := by
  classical
  set T : Finset (Site d) :=
    (ballFinset d (‖y₀‖ + 1 + Real.sqrt d / 2)).filter fun z => z ∉ departureRange X n with hT
  have hcl : y₀ ∈ closure (⋃ z ∈ T, cell z) := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨v, ⟨hvt, hvball⟩, hvD⟩ := mem_closure_iff_nhds.mp hy (t ∩ Metric.ball y₀ 1)
      (Filter.inter_mem ht (Metric.ball_mem_nhds y₀ one_pos))
    refine ⟨v, hvt, ?_⟩
    rw [Set.mem_iUnion₂]
    refine ⟨cellCenter v, ?_, mem_cell_cellCenter v⟩
    rw [hT, Finset.mem_filter, mem_ballFinset_iff]
    refine ⟨?_, fun h => hvD ((mem_cellSet_iff X n v).mpr h)⟩
    rw [← norm_toSpace]
    have h1 := norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter v)
    have h2 : ‖v - y₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hvball
    have h3 : ‖v‖ ≤ ‖y₀‖ + ‖v - y₀‖ := norm_le_norm_add_norm_sub' v y₀
    have h4 : ‖toSpace (cellCenter v)‖ ≤ ‖v‖ + ‖toSpace (cellCenter v) - v‖ :=
      norm_le_norm_add_norm_sub' _ v
    rw [norm_sub_rev] at h4
    linarith
  rw [Finset.closure_biUnion, Set.mem_iUnion₂] at hcl
  obtain ⟨z, hzT, hz⟩ := hcl
  exact ⟨z, (Finset.mem_filter.mp hzT).2, hz⟩

/-- A point of the closure of the cell `C_x` is within `√d / 2` of `x`. -/
theorem norm_sub_toSpace_le_of_mem_closure_cell {x : Site d} {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ closure (cell x)) : ‖y - toSpace x‖ ≤ Real.sqrt d / 2 := by
  have hclosed : IsClosed {v : EuclideanSpace ℝ (Fin d) | ‖v - toSpace x‖ ≤ Real.sqrt d / 2} :=
    isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  exact closure_minimal (fun v hv => norm_sub_toSpace_le_of_mem_cell hv) hclosed hy

/-- `eq:bm` and `eq:contactcell`: with `b = inf {|y| : y ∉ D_n}`, the ball `B(0, b)` lies in
`D_n`, and there are `y₀` with `|y₀| = b` and an unvisited site `z` with `|z - y₀| ≤ √d/2` and
`|z| ≥ b`. -/
theorem exists_contact_cell (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) :
    let D := cellSet X n
    let b := sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' Dᶜ)
    Metric.ball 0 b ⊆ D ∧ ∃ y₀ : EuclideanSpace ℝ (Fin d), ‖y₀‖ = b ∧ ∃ z : Site d,
      localTime X n z = 0 ∧ ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 ∧ b ≤ euclidNorm z := by
  intro D b
  have hDb : D ⊆ Metric.ball 0 (maxRadius X n + Real.sqrt d) := cellSet_subset_ball hd X n
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : Dᶜ.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    have hbdd : Bornology.IsBounded (Set.univ : Set (EuclideanSpace ℝ (Fin d))) := by
      rw [← h]
      exact Metric.isBounded_ball.subset hDb
    exact NormedSpace.unbounded_univ ℝ _ hbdd
  have hbdd : BddBelow ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' Dᶜ) :=
    ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg y⟩
  obtain ⟨y₀, hy₀cl, hy₀norm⟩ := exists_mem_closure_norm_eq_sInf hne
  obtain ⟨z, hzA, hzcl⟩ := exists_unvisited_mem_closure_cell X n hy₀cl
  refine ⟨?_, y₀, hy₀norm, z, ?_, ?_, ?_⟩
  · intro y hy
    by_contra hyD
    rw [mem_ball_zero_iff] at hy
    exact absurd (csInf_le hbdd ⟨y, hyD, rfl⟩) (not_le.mpr hy)
  · rwa [mem_departureRange_iff, not_lt, Nat.le_zero] at hzA
  · rw [norm_sub_rev]
    exact norm_sub_toSpace_le_of_mem_closure_cell hzcl
  · rw [← norm_toSpace]
    exact csInf_le hbdd ⟨toSpace z, fun h => hzA ((toSpace_mem_cellSet_iff X n z).mp h), rfl⟩

end CERW.Support.Contact
