module

public import CERW.LimitShapes.Energy.Identity
public import CERW.LimitShapes.Energy.Bracket

@[expose] public section

/-!
# Absorption of the shifted-square martingale

The finite algebraic absorption by Young's inequality used in Lemma `lem:contact`.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb

/-- Young's inequality absorbs a square root controlled by the energy. -/
private theorem sqrt_absorption (E B L Q k A H : ℝ)
    (hE : 0 ≤ E) (hQ : 0 ≤ Q) (hk : 0 ≤ k) (hA : 0 ≤ A)
    (hB : B * L ≤ E * (k * Q)) (h : E ≤ H + A * Real.sqrt (B * L)) :
    E ≤ 2 * H + A ^ 2 * k * Q := by
  have hs : Real.sqrt (B * L) ≤ Real.sqrt E * Real.sqrt (k * Q) := by
    rw [← Real.sqrt_mul hE]
    exact Real.sqrt_le_sqrt hB
  have hy := sq_nonneg (Real.sqrt E - A * Real.sqrt (k * Q))
  have he := Real.sq_sqrt hE
  have hq := Real.sq_sqrt (mul_nonneg hk hQ)
  have hm := mul_le_mul_of_nonneg_left hs hA
  nlinarith

/-- The shifted-square martingale is absorbed into kernel energy in Lemma `lem:contact`. -/
theorem exists_kernelEnergy_le {d : ℕ} (hd : 1 ≤ d) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 ≤ ε →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d), ξ 0 = 0 →
        (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ (g : Site d → ℝ) (y : Site d),
        (∀ x, LatticeProb.walkOp g x - g x = if x = y then 1 else 0) →
      ∀ (γ G L D : ℝ), 1 ≤ G → 1 ≤ L → 0 ≤ D → |γ - g y| ≤ G →
      ∀ (X : ℕ → Site d) (n : ℕ), |g (X 0) - γ| ≤ G →
        |g (X n) - γ| ≤ G →
        (∀ j : ℕ, j < n → |g (X j) - γ| ≤ G ∧
          ∀ e ∈ CERW.unitSteps d, |g (X j + e) - γ| ≤ G) →
        ε * |∑ x ∈ CERW.departureRange X n,
          inner ℝ (ξ x) (CERW.Support.Law.centralDiff (fun z => (g z - γ) ^ 2) x)| ≤ D →
        |CERW.dynkinMart (CERW.driftStepProb d ε ξ) (fun z => (g z - γ) ^ 2) X n| ≤
          A * (Real.sqrt (CERW.dynkinBracket (CERW.driftStepProb d ε ξ)
            (fun z => (g z - γ) ^ 2) (fun z => (g z - γ) ^ 2) X n * L) + G * L) →
        kernelEnergy g X n ≤ C * (G * (CERW.localTime X n y : ℝ) + G ^ 2 * L + D) := by
  classical
  let k : ℝ := 8 * (d : ℝ)
  let C : ℝ := 6 + 2 * A + A ^ 2 * k
  have hk : 0 ≤ k := by positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ε hε ξ hξ0 hξ g y hg γ G L D hG hL hD hy X n _hstart hend hbound hξD hmart
  have hG0 : 0 ≤ G := by linarith
  have hL0 : 0 ≤ L := by linarith
  have htime : 0 ≤ (localTime X n y : ℝ) := Nat.cast_nonneg _
  let E := kernelEnergy g X n
  let B := dynkinBracket (driftStepProb d ε ξ)
    (fun z => (g z - γ) ^ 2) (fun z => (g z - γ) ^ 2) X n
  let S := ∑ j ∈ Finset.range n, ∑ e ∈ unitSteps d,
    (g (X j + e) - g (X j)) ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hES : E = 1 / (2 * (d : ℝ)) * S := kernelEnergy_eq_time_sum g X n
  have hE : 0 ≤ E := by rw [hES]; positivity
  have hSE : S = 2 * (d : ℝ) * E := by rw [hES]; field_simp
  have hB : B ≤ k * G ^ 2 * E := by
    have hb := shifted_square_bracket_le_step_energy hd hε ξ hξ
      g γ G hG0 X n hbound
    change B ≤ 4 * G ^ 2 * S at hb
    rw [hSE] at hb
    dsimp [k]
    nlinarith only [hb]
  have hBL : B * L ≤ E * (k * (G ^ 2 * L)) := by
    calc
      B * L ≤ (k * G ^ 2 * E) * L := mul_le_mul_of_nonneg_right hB hL0
      _ = _ := by ring
  have hGL : G * L ≤ G ^ 2 * L := by
    have : G ≤ G ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hL0
  have hend2 : (g (X n) - γ) ^ 2 ≤ G ^ 2 := by
    nlinarith [sq_abs (g (X n) - γ), abs_nonneg (g (X n) - γ)]
  have hcontact : 2 * (γ - g y) * (localTime X n y : ℝ) ≤
      2 * G * (localTime X n y : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self (γ - g y)]) htime
  have hdrift : ε * (∑ x ∈ departureRange X n,
      inner ℝ (ξ x) (Support.Law.centralDiff (fun z => (g z - γ) ^ 2) x)) ≤ D := by
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) hε).trans hξD
  have hid := shifted_square_energy_identity hd g y hg ε γ ξ hξ0 X n
  have hupper : E ≤ (2 * G * (localTime X n y : ℝ) +
      (1 + A) * (G ^ 2 * L) + D) + A * Real.sqrt (B * L) := by
    have hendpoint : G ^ 2 ≤ G ^ 2 * L := le_mul_of_one_le_right (sq_nonneg G) hL
    have hm := neg_le_abs (dynkinMart (driftStepProb d ε ξ)
      (fun z => (g z - γ) ^ 2) X n)
    change E = _ at hid
    change |dynkinMart (driftStepProb d ε ξ) (fun z => (g z - γ) ^ 2) X n| ≤
      A * (Real.sqrt (B * L) + G * L) at hmart
    nlinarith [sq_nonneg (g (X 0) - γ), mul_le_mul_of_nonneg_left hGL hA.le]
  have habs := sqrt_absorption E B L (G ^ 2 * L) k A
    (2 * G * (localTime X n y : ℝ) + (1 + A) * (G ^ 2 * L) + D)
    hE (mul_nonneg (sq_nonneg G) hL0) hk hA.le hBL hupper
  change E ≤ _
  have ht := mul_nonneg hG0 htime
  have hq := mul_nonneg (sq_nonneg G) hL0
  have hc : 0 ≤ A ^ 2 * k := mul_nonneg (sq_nonneg A) hk
  dsimp [C]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 2 + 2 * A + A ^ 2 * k) ht,
    mul_nonneg (by linarith : 0 ≤ 4 + 2 * A + A ^ 2 * k) hD]

end CERW.LimitShapes.Energy
