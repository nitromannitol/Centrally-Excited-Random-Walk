import CERW.Support.Outer.Radius.WeightedKernelTail

/-!
# Occupation Kernel

Occupation counts rewrite the bracket sum as a weighted local-time sum. Kernel summation and the
potential at an unvisited site control its far contributions.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The bracket sum equals the local-time weighted kernel sum over any finite set of sites
containing the departure range. -/
lemma ev_braSum_eq (X : ℕ → Site d) (n : ℕ) {S : Finset (Site d)}
    (hS : departureRange X n ⊆ S) (y : Site d) :
    braSum X n y = ∑ x ∈ S, (localTime X n x : ℝ) * ev_kern d (x - y) := by
  show ∑ j ∈ Finset.range n, ev_kern d (X j - y) = _
  rw [CERW.Support.LocalTime.sum_range_eq_sum_localTime X n (fun w => ev_kern d (w - y))]
  refine Finset.sum_subset hS fun x _ hx => ?_
  rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hx
  rw [hx, Nat.cast_zero, zero_mul]

/-- A path with `|X_j| ≤ j` has `H_n ≤ n`. -/
lemma ev_maxRadius_le_nat (X : ℕ → Site d) (n : ℕ) (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    maxRadius X n ≤ n := by
  unfold maxRadius
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact (hXn j).trans (by exact_mod_cast hjn)

/-- The lattice departure range lies in the lattice ball of radius `2n`. -/
lemma ev_departureRange_subset_ballFinset_two_mul {X : ℕ → Site d} {n : ℕ}
    (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    departureRange X n ⊆ LatticeProb.ballFinset d (2 * n) := by
  intro x hx
  have h1 := CERW.Support.Occupation.departureRange_subset_ballFinset X n hx
  rw [LatticeProb.mem_ballFinset_iff] at h1 ⊢
  have h2 := ev_maxRadius_le_nat X n hXn
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The lattice step: there are constants `c₀, α₁` depending only on `d` and `C₁` such that the
bracket at a site `z` whose cell is near `y₀` satisfies
`c₀ W_z ≤ 2 Σ_{y} a(y) U(y) + α₁ L`. -/
lemma ev_kernel_sum_le (hd : 3 ≤ d) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    ∃ c₀ α₁ : ℝ, 0 < c₀ ∧ 0 ≤ α₁ ∧ ∀ (X : ℕ → Site d) (n : ℕ) (U : Site d → ℝ),
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - U y| ≤
          C₁ * (Real.sqrt (braSum X n y * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2))) →
      ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (z : Site d), ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 →
        c₀ * braSum X n z ≤
          2 * ∑ y ∈ LatticeProb.ballFinset d (2 * n), ev_cellWeight d y₀ y * U y +
            α₁ * Real.log ((n : ℝ) + 2) := by
  obtain ⟨K₀, hK₀pos, hK⟩ := CERW.Generic.Lattice.sum_finset_rpow_two_sub_two_mul_le hd
  have hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, ev_kern d (y - u) ≤ K₀ :=
    fun F u => hK F u
  have hd1 : 1 ≤ d := by omega
  set A₀ : ℝ := 2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀ with hA₀
  have hA₀pos : 0 < A₀ := by
    rw [hA₀]
    exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) hK₀pos
  have hsq : 0 < 1 + Real.sqrt d := by linarith [Real.sqrt_nonneg (d : ℝ)]
  set c₁ : ℝ := (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) with hc₁
  have hc₁pos : 0 < c₁ := Real.rpow_pos_of_pos hsq _
  set c₀ : ℝ := c₁⁻¹ with hc₀
  have hc₀pos : 0 < c₀ := inv_pos.mpr hc₁pos
  set γ : ℝ := c₀ / (2 * (c₁ * A₀)) with hγ
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ' : γ * (c₁ * A₀) ≤ c₀ / 2 := by
    rw [hγ]
    have : 0 < c₁ * A₀ := mul_pos hc₁pos hA₀pos
    field_simp
    exact le_refl _
  refine ⟨c₀, 2 * (C₁ + C₁ ^ 2 / (4 * γ)) * (c₁ * K₀), hc₀pos, by positivity, ?_⟩
  intro X n U hXn hfine y₀ z hz
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  set S : Finset (Site d) := LatticeProb.ballFinset d (2 * n) with hS
  have hAS : departureRange X n ⊆ S := ev_departureRange_subset_ballFinset_two_mul hXn
  have hℓ0 : ∀ y : Site d, 0 ≤ (localTime X n y : ℝ) := fun y => Nat.cast_nonneg _
  have hw := fun y => ev_cellWeight_bounds hd hz y
  have hfine' : ∀ y ∈ S, (localTime X n y : ℝ) ≤ U y +
      C₁ * (Real.sqrt ((∑ x ∈ S, (localTime X n x : ℝ) * ev_kern d (x - y)) * L) + L) := by
    intro y hy
    rw [hS, LatticeProb.mem_ballFinset_iff] at hy
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h := hfine y (by linarith)
    rw [ev_braSum_eq X n hAS y] at h
    have := (abs_le.mp h).2
    linarith
  have habs := ev_absorb_sum (S := S) (z := z) (c₀ := c₀) (c₁ := c₁) (K₀ := K₀) (A₀ := A₀)
    (C₁ := C₁) (L := L) (γ := γ) (ℓ := fun y => (localTime X n y : ℝ)) (U := U)
    (a := ev_cellWeight d y₀) hK₀ (fun F x => ev_sum_kern_mul_kern_le hd1 hK₀ F z x) hc₀pos
    hc₁pos hA₀pos.le (fun y => by
      have := hw y
      rw [hc₀]
      exact this) hℓ0 hC₁ hL0 hγpos hγ' hfine'
  have hlow : c₀ * braSum X n z ≤
      ∑ y ∈ S, ev_cellWeight d y₀ y * (localTime X n y : ℝ) := by
    rw [ev_braSum_eq X n hAS z, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc c₀ * ((localTime X n x : ℝ) * ev_kern d (x - z))
        = (localTime X n x : ℝ) * (c₀ * ev_kern d (z - x)) := by
          rw [ev_kern_sub_comm x z]; ring
      _ ≤ (localTime X n x : ℝ) * ev_cellWeight d y₀ x :=
          mul_le_mul_of_nonneg_left (hw x).1 (hℓ0 x)
      _ = ev_cellWeight d y₀ x * (localTime X n x : ℝ) := by ring
  calc c₀ * braSum X n z
      ≤ ∑ y ∈ S, ev_cellWeight d y₀ y * (localTime X n y : ℝ) := hlow
    _ ≤ 2 * ∑ y ∈ S, ev_cellWeight d y₀ y * U y +
          2 * ((C₁ + C₁ ^ 2 / (4 * γ)) * L) * (c₁ * K₀) := habs
    _ = 2 * ∑ y ∈ S, ev_cellWeight d y₀ y * U y +
          2 * (C₁ + C₁ ^ 2 / (4 * γ)) * (c₁ * K₀) * L := by ring

/-- The logarithm of `1 + max 1 b` is at most a constant multiple of `log (n + 2)` when
`b ≤ 2 Λ n`. -/
lemma ev_log_one_add_max_le {Λ b : ℝ} {n : ℕ} (hn : 2 ≤ n) (hb : b ≤ Λ * (2 * n)) :
    Real.log (1 + max 1 b) ≤
      (1 + Real.log (1 + max 1 (2 * Λ))) * Real.log ((n : ℝ) + 2) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set Λ' : ℝ := max 1 (2 * Λ) with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_left _ _
  have hΛ'2 : 2 * Λ ≤ Λ' := le_max_right _ _
  have hn2 : 1 ≤ (n : ℝ) + 2 := by linarith
  have hT : max 1 b ≤ Λ' * ((n : ℝ) + 2) := by
    refine max_le ?_ ?_
    · exact one_le_mul_of_one_le_of_one_le hΛ'1 hn2
    · calc b ≤ Λ * (2 * n) := hb
        _ = (2 * Λ) * n := by ring
        _ ≤ Λ' * n := mul_le_mul_of_nonneg_right hΛ'2 hn0
        _ ≤ Λ' * ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h1 : 1 + max 1 b ≤ (1 + Λ') * ((n : ℝ) + 2) := by
    calc 1 + max 1 b ≤ 1 + Λ' * ((n : ℝ) + 2) := by linarith
      _ ≤ (1 + Λ') * ((n : ℝ) + 2) := by linarith
  have hpos1 : 0 < 1 + max 1 b := by linarith [le_max_left (1 : ℝ) b]
  have hpos2 : 0 < 1 + Λ' := by linarith
  have hpos3 : 0 < (n : ℝ) + 2 := by linarith
  have hL : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn
  have hlog0 : 0 ≤ Real.log (1 + Λ') := Real.log_nonneg (by linarith)
  calc Real.log (1 + max 1 b) ≤ Real.log ((1 + Λ') * ((n : ℝ) + 2)) :=
        Real.log_le_log hpos1 h1
    _ = Real.log (1 + Λ') + Real.log ((n : ℝ) + 2) := Real.log_mul hpos2.ne' hpos3.ne'
    _ ≤ (1 + Real.log (1 + Λ')) * Real.log ((n : ℝ) + 2) := by
        linarith [mul_nonneg hlog0 (sub_nonneg.mpr hL)]

/-- The far-field bound: at a point of the complement of the cells of the ball of radius `2n`,
the potential of `D_n` is at least `-4ε/ω_d`. -/
lemma ev_neg_le_potential_of_not_mem (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {X : ℕ → Site d} {n : ℕ} (hn : 2 ≤ n) (hn4 : 4 * Real.sqrt d ≤ n)
    (hXn : ∀ j, euclidNorm (X j) ≤ j) {ζ : EuclideanSpace ℝ (Fin d)}
    (hζ : ζ ∉ ⋃ y ∈ LatticeProb.ballFinset d (2 * n), cell y) :
    -(2 * ε / unitBallVolume d * 2) ≤ potential d ε (cellSet X n) ζ := by
  have hω := unitBallVolume_pos d
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmax : maxRadius X n ≤ n := ev_maxRadius_le_nat X n hXn
  have hc : cellCenter ζ ∉ LatticeProb.ballFinset d (2 * n) := fun hcS =>
    hζ (Set.mem_iUnion₂.mpr ⟨cellCenter ζ, hcS, mem_cell_cellCenter ζ⟩)
  rw [LatticeProb.mem_ballFinset_iff, not_le] at hc
  have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter ζ)
  have hζn : 2 * (n : ℝ) - Real.sqrt d / 2 < ‖ζ‖ := by
    have h2 : ‖toSpace (cellCenter ζ)‖ ≤ ‖ζ‖ + ‖ζ - toSpace (cellCenter ζ)‖ := by
      calc ‖toSpace (cellCenter ζ)‖ = ‖ζ - (ζ - toSpace (cellCenter ζ))‖ := by
            rw [sub_sub_cancel]
        _ ≤ ‖ζ‖ + ‖ζ - toSpace (cellCenter ζ)‖ := norm_sub_le _ _
    rw [norm_toSpace] at h2
    linarith
  have hfar : ∀ v ∈ cellSet X n, (n : ℝ) / 2 ≤ ‖v - ζ‖ := by
    intro v hv
    have hvn := CERW.Support.Occupation.norm_le_of_mem_cellSet X n hv
    have h3 : ‖ζ‖ - ‖v‖ ≤ ‖ζ - v‖ := norm_sub_norm_le ζ v
    rw [norm_sub_rev] at h3
    linarith [Real.sqrt_nonneg (d : ℝ)]
  have hDfin : volume (cellSet X n) ≠ ⊤ := by
    rw [CERW.Support.Occupation.volume_cellSet]
    exact ENNReal.natCast_ne_top _
  have hvol : (volume (cellSet X n)).toReal ≤ n := by
    rw [CERW.Support.Occupation.volume_cellSet, ENNReal.toReal_natCast]
    exact_mod_cast CERW.Support.Occupation.card_departureRange_le X n
  have hpot := ev_abs_potential_le_of_far hd hε hDfin (R := (n : ℝ) / 2) (by linarith) hfar
  have hratio : (volume (cellSet X n)).toReal / ((n : ℝ) / 2) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hc0 : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hbound := hpot.trans (mul_le_mul_of_nonneg_left hratio hc0)
  exact (neg_le_neg_iff.mpr hbound).trans (neg_abs_le _)

end CERW.Support.Outer.Radius
