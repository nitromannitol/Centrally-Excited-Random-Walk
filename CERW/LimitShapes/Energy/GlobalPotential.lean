import CERW.LimitShapes.Energy.FarPotential

/-!
# Global one-sided potentials

The cell modulus extends lattice estimates to the ball of radius `2n`. The uniform
far-field estimate completes `eq:square-one-sided` on the whole space.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb
open CERW.Support.Occupation
open private cell_modulus_of_path from CERW.Support.Norm.ContactEvent
open private CERW.Support.Norm.ContactHigh.normMax_nonneg
  from CERW.Support.Norm.ContactPotential

/-- Site estimates imply the global one-sided and exterior bounds of
`eq:square-one-sided`. -/
theorem exists_global_one_sided_of_sites {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
      ∀ delta : ℝ, Real.log ((n : ℝ) + 2) ≤ delta →
        (∀ z : Site d, euclidNorm z ≤ 3 * (n : ℝ) →
          (CERW.localTime X n z : ℝ) / 2 - Cs * delta ≤
            CERW.normPotential d ε Ψ (CERW.cellSet X n) (CERW.toSpace z) ∧
          (CERW.localTime X n z = 0 →
            |CERW.normPotential d ε Ψ (CERW.cellSet X n) (CERW.toSpace z)| ≤ Cs * delta)) →
        (∀ v : EuclideanSpace ℝ (Fin d),
          CERW.cellLocalTime X n v / 2 - C * delta ≤
            CERW.normPotential d ε Ψ (CERW.cellSet X n) v) ∧
        (∀ v : EuclideanSpace ℝ (Fin d), v ∉ CERW.cellSet X n →
          |CERW.normPotential d ε Ψ (CERW.cellSet X n) v| ≤ C * delta) := by
  obtain ⟨M, hM, hmod⟩ :=
    CERW.Support.Norm.ContactModulus.exists_normPotential_cell_modulus hd hΨ
  let K := M * ε * (1 + Real.log (1 + Real.sqrt d))
  let F := 2 * ε / unitBallVolume d * (2 * normMax Ψ)
  have hK : 0 ≤ K := by
    have : 0 ≤ Real.log (1 + Real.sqrt d) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (d : ℝ)])
    dsimp [K]
    positivity
  have hF : 0 ≤ F := by
    have := CERW.Support.Norm.ContactHigh.normMax_nonneg hΨ (by omega : 1 ≤ d)
    have := unitBallVolume_pos d
    dsimp [F]
    positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.sqrt (d : ℝ))
  refine ⟨Cs + K + F + 1, by positivity, max 2 N, le_max_left _ _, ?_⟩
  intro X n hn hpath delta hdelta hsites
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hs : Real.sqrt d ≤ (n : ℝ) :=
    hN.trans (Nat.cast_le.mpr ((le_max_right _ _).trans hn))
  have hX : ∀ j, euclidNorm (X j) ≤ j :=
    euclidNorm_le_of_steps X hpath.1 hpath.2
  have hd1 : 1 ≤ delta :=
    (CERW.Support.Law.one_le_log_add_two hn2).trans hdelta
  have hδ : 0 ≤ delta := by linarith
  have hCK : (Cs + K) * delta ≤ (Cs + K + F + 1) * delta := by
    nlinarith
  have hCF : F ≤ (Cs + K + F + 1) * delta := by
    nlinarith
  have hnear : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ 2 * (n : ℝ) →
      cellLocalTime X n v / 2 - (Cs + K) * delta ≤
        normPotential d ε Ψ (cellSet X n) v ∧
      (v ∉ cellSet X n → |normPotential d ε Ψ (cellSet X n) v| ≤
        (Cs + K) * delta) := by
    intro v hv
    have hc := norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter v)
    have hz : euclidNorm (cellCenter v) ≤ 3 * (n : ℝ) := by
      have ht := norm_sub_le v (v - toSpace (cellCenter v))
      rw [sub_sub_cancel, norm_toSpace] at ht
      linarith
    have hm := cell_modulus_of_path hd hε.le hM hmod X n hn2 hX v
      (toSpace (cellCenter v)) (by linarith [Real.sqrt_nonneg (d : ℝ)])
      (by linarith [Real.sqrt_nonneg (d : ℝ)])
    have hm' : |normPotential d ε Ψ (cellSet X n) v -
        normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter v))| ≤ K * delta :=
      hm.trans (mul_le_mul_of_nonneg_left hdelta hK)
    obtain ⟨hl, hu⟩ := hsites _ hz
    constructor
    · change (localTime X n (cellCenter v) : ℝ) / 2 - _ ≤ _
      have := (abs_le.mp hm').1
      linarith
    · intro hnot
      have hzero := cellLocalTime_eq_zero_of_not_mem X n hnot
      have hz0 : localTime X n (cellCenter v) = 0 := by
        change (localTime X n (cellCenter v) : ℝ) = 0 at hzero
        exact_mod_cast hzero
      have ht := abs_add_le (normPotential d ε Ψ (cellSet X n) v -
        normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter v)))
        (normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter v)))
      rw [sub_add_cancel] at ht
      have := hu hz0
      linarith
  constructor
  · intro v
    by_cases hv : ‖v‖ ≤ 2 * (n : ℝ)
    · have := (hnear v hv).1
      linarith
    · obtain ⟨hz, hb⟩ := far_potential_bound hd hΨ hε.le hn2 hs hX (lt_of_not_ge hv)
      rw [hz]
      have := (abs_le.mp hb).1
      dsimp [F] at hCF
      linarith
  · intro v hnot
    by_cases hv : ‖v‖ ≤ 2 * (n : ℝ)
    · exact ((hnear v hv).2 hnot).trans hCK
    · exact (far_potential_bound hd hΨ hε.le hn2 hs hX (lt_of_not_ge hv)).2.trans hCF

end CERW.LimitShapes.Energy
