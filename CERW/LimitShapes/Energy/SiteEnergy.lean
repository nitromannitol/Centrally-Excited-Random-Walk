module

public import CERW.LimitShapes.Energy.Absorption
public import CERW.LimitShapes.Energy.DriftBound
public import CERW.LimitShapes.Energy.ValueBound
public import CERW.LimitShapes.Energy.SitePointwise

@[expose] public section

/-!
# Kernel energy on the common event

Absorption of the actual shifted-square Freedman estimate in Lemma `lem:contact`.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb
open CERW.Support.Norm CERW.Support.Norm.ContactEvent

open private norm_drift_le normMax_nonneg_of_isNorm from CERW.Support.Norm.LocalTime

/-- The common event controls kernel energy by local time and the dimensional scale. -/
theorem exists_site_energy_bound {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    (K : CERW.LimitShapes.EventConstants) (hCo : 0 ≤ K.CCo) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), 3 ≤ n →
        1 ≤ Real.log n → 2 ≤ scale d Ψ ε n → Real.log n ^ 3 ≤ scale d Ψ ε n →
        PathTyping d X → CERW.LimitShapes.EventEstimates Ψ ε ξ K X n →
      ∀ y : Site d, euclidNorm y ≤ 3 * (n : ℝ) →
        kernelEnergy (fun z => latticeKernel d (z - y)) X n ≤
          B * ((if d = 2 then Real.log n else 1) * (localTime X n y : ℝ) +
            (if d = 2 then scale d Ψ ε n else Real.log n)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨G₀, hG₀, hg⟩ := exists_centered_kernel_value_bound hd hΨ hε
  obtain ⟨D₀, hD₀, hdri⟩ := exists_path_square_drift_bound hd
    (K.CCo + 1) (by linarith) (normMax Ψ) (normMax_nonneg_of_isNorm hΨ)
  let A := max K.CSquare 0 + 1
  have hA : 0 < A := by dsimp [A]; linarith [le_max_right K.CSquare 0]
  have hKA : K.CSquare ≤ A := by dsimp [A]; linarith [le_max_left K.CSquare 0]
  obtain ⟨B₀, hB₀, habs⟩ := exists_kernelEnergy_le hd1 A hA
  let B := B₀ * (G₀ + G₀ ^ 2 + 2 * ε * D₀ + 1)
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro ξ hξ hξ0 X n hn hL hr hcube hty hev y hy
  let r := scale d Ψ ε n
  let L := Real.log (n : ℝ)
  let p : ℝ := if d = 2 then L else 1
  let q : ℝ := if d = 2 then r else L
  let g : Site d → ℝ := fun z => latticeKernel d (z - y)
  let γ := CERW.LimitShapes.kernelShift d Ψ ε n
  have hp : 1 ≤ p := by dsimp [p, L]; split_ifs <;> first | exact hL | norm_num
  have hq : 0 ≤ q := by dsimp [q, r, L]; split_ifs <;> linarith
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hG : 1 ≤ G₀ * p := by
    calc 1 ≤ p := hp
         _ = 1 * p := (one_mul p).symm
         _ ≤ G₀ * p := mul_le_mul_of_nonneg_right hG₀ (by linarith)
  have hξc := subgradient_coordinate_bound hΨ hε.le hell ξ hξ hξ0
  have hnorm := CERW.Support.Occupation.euclidNorm_le_of_steps X hty.1 hty.2
  have hnormn (j : ℕ) (hj : j < n) : euclidNorm (X j) ≤ (n : ℝ) :=
    (hnorm j).trans (by exact_mod_cast hj.le)
  have hcard : ((departureRange X n).card : ℝ) ≤ (K.CCo + 1) * r ^ d := by
    have hc := hev.1.2.1
    exact hc.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0 d))
  have hdr := hdri r hr X n (by omega) hnormn hcard ξ (norm_drift_le hΨ hξ hξ0) y hy
  have hdlog : (if d = 2 then r else Real.log ((n : ℝ) + 2)) ≤ 2 * q := by
    dsimp [q, L]
    split_ifs
    · linarith
    · exact log_add_two_le_two_log hn
  have hD : ε * |∑ x ∈ departureRange X n,
      inner ℝ (ξ x) (CERW.Support.Law.centralDiff (fun z => (g z - γ) ^ 2) x)| ≤
        2 * ε * D₀ * q := by
    calc
      _ ≤ ε * (D₀ * (if d = 2 then r else Real.log ((n : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left hdr hε.le
      _ ≤ ε * (D₀ * (2 * q)) := by gcongr
      _ = _ := by ring
  have hval (z : Site d) (hz : euclidNorm (z - y) ≤ 4 * (n : ℝ) + 1) :
      |g z - γ| ≤ G₀ * p := hg n hn (z - y) hz
  have hxn (j : ℕ) (hj : j ≤ n) : |g (X j) - γ| ≤ G₀ * p := by
    apply hval
    exact (CERW.Support.Occupation.euclidNorm_sub_le _ _).trans
      (by have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj
          linarith [hnorm j])
  have hbound : ∀ j : ℕ, j < n → |g (X j) - γ| ≤ G₀ * p ∧
      ∀ e ∈ unitSteps d, |g (X j + e) - γ| ≤ G₀ * p := by
    intro j hj
    refine ⟨hxn j hj.le, ?_⟩
    intro e he
    apply hval
    have he1 := CERW.Support.Law.euclidNorm_of_mem_unitSteps he
    have htri := CERW.Support.Occupation.euclidNorm_sub_le (X j + e) y
    have hadd := CERW.Support.Occupation.euclidNorm_add_le (X j) e
    linarith [hnormn j hj]
  have hmart : |dynkinMart (driftStepProb d ε ξ) (fun z => (g z - γ) ^ 2) X n| ≤
      A * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ)
        (fun z => (g z - γ) ^ 2) (fun z => (g z - γ) ^ 2) X n * L) + G₀ * p * L) := by
    have hm := hev.2.2.2.1 y hy
    change |dynkinMart (driftStepProb d ε ξ) (fun z => (g z - γ) ^ 2) X n| ≤
      K.CSquare * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ)
        (fun z => (g z - γ) ^ 2) (fun z => (g z - γ) ^ 2) X n * L) + p * L) at hm
    refine hm.trans ((mul_le_mul_of_nonneg_right hKA (by positivity)).trans ?_)
    apply mul_le_mul_of_nonneg_left _ hA.le
    have := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left (by linarith : 0 ≤ p) hG₀) hL0
    linarith
  have hpois : ∀ x, walkOp g x - g x = if x = y then 1 else 0 := by
    obtain ⟨h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
    intro x
    rw [CERW.Support.LocalTime.walkOp_comp_sub, hK.poisson]
    simp only [sub_eq_zero]
  have hgy : |γ - g y| ≤ G₀ * p := by
    rw [abs_sub_comm]
    apply hval
    simp only [sub_self, euclidNorm_zero]
    positivity
  have he := habs ε hε.le ξ hξ0 hξc g y hpois γ (G₀ * p) L
    (2 * ε * D₀ * q) hG hL (by positivity) hgy X n (hxn 0 (by omega))
    (hxn n le_rfl) hbound hD hmart
  have hpq : p ^ 2 * L ≤ q := by
    dsimp [p, q, r, L]
    split_ifs with hd2
    · nlinarith only [hcube]
    · simp only [one_pow, one_mul, le_refl]
  have hsq : (G₀ * p) ^ 2 * L ≤ G₀ ^ 2 * q := by
    nlinarith only [mul_le_mul_of_nonneg_left hpq (sq_nonneg G₀)]
  have ht : 0 ≤ p * (localTime X n y : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hinside : G₀ * p * (localTime X n y : ℝ) + (G₀ * p) ^ 2 * L +
      2 * ε * D₀ * q ≤ (G₀ + G₀ ^ 2 + 2 * ε * D₀ + 1) *
        (p * (localTime X n y : ℝ) + q) := by
    have h1 := mul_nonneg (by positivity : 0 ≤ G₀ ^ 2 + 2 * ε * D₀ + 1) ht
    have h2 := mul_nonneg (by linarith : 0 ≤ G₀ + 1) hq
    nlinarith only [hsq, h1, h2]
  exact he.trans (by
    dsimp [B]
    calc
      _ ≤ B₀ * ((G₀ + G₀ ^ 2 + 2 * ε * D₀ + 1) *
          (p * (localTime X n y : ℝ) + q)) :=
        mul_le_mul_of_nonneg_left hinside hB₀.le
      _ = _ := by ring)

end CERW.LimitShapes.Energy
