import CERW.Model.Martingales
import CERW.Support.Drift.StepProb
import CERW.Support.Drift.Bridge

/-!
# Brackets controlled by step energy

The conditional variance and shifted-square comparisons used in Lemma `lem:contact`.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb
open CERW.Support.Drift

/-- The Dynkin bracket is bounded by the unweighted step energy in Lemma `lem:contact`. -/
theorem dynkinBracket_le_step_energy {d : ℕ} (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 ≤ ε) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (g : Site d → ℝ) (X : ℕ → Site d) (n : ℕ) :
    CERW.dynkinBracket (CERW.driftStepProb d ε ξ) g g X n ≤
      ∑ j ∈ Finset.range n, ∑ e ∈ CERW.unitSteps d,
        (g (X j + e) - g (X j)) ^ 2 := by
  unfold dynkinBracket
  apply Finset.sum_le_sum
  intro j _
  have hp : ∀ e ∈ unitSteps d, driftStepProb d ε ξ X j e ≤ 1 := by
    intro e he
    rw [← sum_driftStepProb hd ε ξ X j]
    exact Finset.single_le_sum (fun e _ => driftStepProb_nonneg hε hξ X j e) he
  calc
    _ ≤ ∑ e ∈ unitSteps d,
        driftStepProb d ε ξ X j e * (g (X j + e) - g (X j)) ^ 2 := by
      simp only [← pow_two]
      exact sub_le_self _ (sq_nonneg _)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_of_le_one_left (sq_nonneg _) (hp e he)

/-- Squaring a function bounded by `G` multiplies its step energy by at most `4 * G²`. -/
private theorem shifted_square_increment_sq_le (a b γ G : ℝ) (hG : 0 ≤ G)
    (ha : |a - γ| ≤ G) (hb : |b - γ| ≤ G) :
    ((a - γ) ^ 2 - (b - γ) ^ 2) ^ 2 ≤ 4 * G ^ 2 * (a - b) ^ 2 := by
  have hab : |(a - γ) + (b - γ)| ≤ 2 * G :=
    (abs_add_le _ _).trans (by linarith)
  have hs : ((a - γ) + (b - γ)) ^ 2 ≤ (2 * G) ^ 2 := by
    nlinarith [sq_nonneg (2 * G - |(a - γ) + (b - γ)|),
      sq_abs ((a - γ) + (b - γ)), abs_nonneg ((a - γ) + (b - γ))]
  calc
    _ = ((a - γ) + (b - γ)) ^ 2 * (a - b) ^ 2 := by ring
    _ ≤ (2 * G) ^ 2 * (a - b) ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by ring

/-- The shifted-square bracket comparison used in Lemma `lem:contact`. -/
theorem shifted_square_bracket_le_step_energy {d : ℕ} (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 ≤ ε) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (g : Site d → ℝ) (γ G : ℝ) (hG : 0 ≤ G) (X : ℕ → Site d) (n : ℕ)
    (hbound : ∀ j : ℕ, j < n → |g (X j) - γ| ≤ G ∧
      ∀ e ∈ CERW.unitSteps d, |g (X j + e) - γ| ≤ G) :
    CERW.dynkinBracket (CERW.driftStepProb d ε ξ)
      (fun z => (g z - γ) ^ 2) (fun z => (g z - γ) ^ 2) X n ≤
        4 * G ^ 2 * ∑ j ∈ Finset.range n, ∑ e ∈ CERW.unitSteps d,
          (g (X j + e) - g (X j)) ^ 2 := by
  refine (dynkinBracket_le_step_energy hd hε ξ hξ (fun z => (g z - γ) ^ 2) X n).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨hj, he'⟩ := hbound j (Finset.mem_range.mp hj)
  exact shifted_square_increment_sq_le _ _ γ G hG (he' e he) hj

end CERW.LimitShapes.Energy
