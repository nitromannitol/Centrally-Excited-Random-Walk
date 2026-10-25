module

public import CERW.Support.Norm.ContactEvent
public import CERW.Support.Occupation.Cells

@[expose] public section

/-!
# Uniform far-field potential bound

The potential is uniformly bounded outside the ball of radius `2n`, as used in
`eq:square-one-sided`.
-/

open MeasureTheory

namespace CERW.LimitShapes.Energy

open CERW LatticeProb
open CERW.Support.Occupation
open private abs_normPotential_le_of_far CERW.Support.Norm.ContactHigh.normMax_nonneg
  from CERW.Support.Norm.ContactPotential

/-- Outside radius `2n`, the finite volume and separation of the departed cells bound
both the potential and the cell occupation, as in `eq:square-one-sided`. -/
theorem far_potential_bound {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 ≤ ε) {X : ℕ → Site d} {n : ℕ} (hn : 2 ≤ n)
    (hs : Real.sqrt d ≤ (n : ℝ)) (hX : ∀ j, euclidNorm (X j) ≤ j)
    {v : EuclideanSpace ℝ (Fin d)} (hv : 2 * (n : ℝ) < ‖v‖) :
    cellLocalTime X n v = 0 ∧
      |normPotential d ε Ψ (cellSet X n) v| ≤
        2 * ε / unitBallVolume d * (2 * normMax Ψ) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm := CERW.Support.Norm.ContactShared.maxRadius_le_nat X n hX
  have hfar : ∀ w ∈ cellSet X n, (n : ℝ) / 2 ≤ ‖w - v‖ := by
    intro w hw
    have hw' := norm_le_of_mem_cellSet X n hw
    have ht := norm_sub_norm_le v w
    rw [norm_sub_rev] at ht
    linarith
  have hnot : v ∉ cellSet X n := by
    intro h
    have := norm_le_of_mem_cellSet X n h
    linarith
  refine ⟨cellLocalTime_eq_zero_of_not_mem X n hnot, ?_⟩
  have hfin : volume (cellSet X n) ≠ ⊤ := by
    rw [volume_cellSet]
    exact ENNReal.natCast_ne_top _
  have hvol : (volume (cellSet X n)).toReal ≤ n := by
    rw [volume_cellSet, ENNReal.toReal_natCast]
    exact_mod_cast card_departureRange_le X n
  have hΛ := CERW.Support.Norm.ContactHigh.normMax_nonneg hΨ (by omega : 1 ≤ d)
  have hr : normMax Ψ * (volume (cellSet X n)).toReal / ((n : ℝ) / 2) ≤
      2 * normMax Ψ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hvol hΛ]
  have hω := unitBallVolume_pos d
  exact (abs_normPotential_le_of_far hΨ hd hε hfin (by linarith) hfar).trans
    (mul_le_mul_of_nonneg_left hr (by positivity))

end CERW.LimitShapes.Energy
