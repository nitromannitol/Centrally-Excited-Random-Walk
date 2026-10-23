import CERW.LimitShapes.Exit.BootstrapAux

/-!
# Exit-time bootstrap at a finite horizon

The first exit-or-martingale-threshold time in Proposition `prop:coarse` occurs
before the prescribed horizon. The bracket estimate rules out the threshold alternative.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb

/-- The deterministic finite-horizon exit bootstrap of Proposition `prop:coarse`. -/
theorem exists_exit_bootstrap {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) →
        ξ 0 = 0 → (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ (R : ℝ), R₀ ≤ R → ∀ N : ℕ, C * R ^ (d + 1) < (N : ℝ) →
      ∀ X : ℕ → Site d, X 0 = 0 →
        (∀ j : ℕ, j < N → X (j + 1) - X j ∈ CERW.unitSteps d) →
        (∀ t : ℕ, t ≤ N → ∀ y : Site d,
          euclidNorm y ≤ (2 / CERW.normMin Ψ + 2 * Real.sqrt d) * R →
          |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
            (fun z => CERW.latticeKernel d (z - y)) X t| ≤
            A * (Real.sqrt (CERW.dynkinBracket (CERW.driftStepProb d ε ξ)
              (fun z => CERW.latticeKernel d (z - y))
              (fun z => CERW.latticeKernel d (z - y)) X t * Real.log R) + Real.log R)) →
        ∃ τ : ℕ, τ ≤ N ∧ R ≤ Ψ (CERW.toSpace (X τ)) ∧
          (∀ j : ℕ, j < τ → Ψ (CERW.toSpace (X j)) < R) ∧
          (∀ y : Site d, (CERW.localTime X τ y : ℝ) ≤ C * R) ∧
          (∀ y : Site d,
            euclidNorm y ≤ (2 / CERW.normMin Ψ + 2 * Real.sqrt d) * R →
            |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
              (fun z => CERW.latticeKernel d (z - y)) X τ| ≤
              C * Real.sqrt R * Real.log R) := by
  classical
  obtain ⟨C₀, hC₀, hlocal⟩ := exists_localTime_le_abs_dynkin_add_radius hd hΨ hε
  obtain ⟨Cb, hCb, hbracket⟩ := exists_kernel_bracket_le_localTime_log hd
  obtain ⟨hm, hcoerce⟩ := Generic.Norm.normMin_pos_mul_le hΨ (by omega)
  let K := C₀ + 2
  let b := 3 / normMin Ψ + 2 * Real.sqrt d + 1
  let E := 2 * Cb * K
  let D := A * (Real.sqrt E + 1)
  have hK : 0 < K := by dsimp [K]; linarith
  have hb : 1 ≤ b := by
    dsimp [b]
    have : 0 ≤ 3 / normMin Ψ := by positivity
    linarith [Real.sqrt_nonneg (d : ℝ)]
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨r, hr⟩ := eventually_sqrt_mul_log_lt D hD
  let V := K * (2 / normMin Ψ + 1) ^ d
  let C := max (max K D) V + 1
  have hKC : K ≤ C := by
    dsimp [C]
    linarith [le_max_left K D, le_max_left (max K D) V]
  have hDC : D ≤ C := by
    dsimp [C]
    linarith [le_max_right K D, le_max_left (max K D) V]
  have hVC : V ≤ C := by dsimp [C]; linarith [le_max_right (max K D) V]
  have hC : 0 < C := lt_of_lt_of_le hK hKC
  let R₀ := max (max 2 (b + 2)) (max (Real.exp 1) r)
  have hR₀ : 2 ≤ R₀ := (le_max_left 2 (b + 2)).trans (le_max_left _ _)
  refine ⟨C, hC, R₀, hR₀, ?_⟩
  intro ξ hξ hξ0 hprob R hR N hN X h0 hstep hF
  have hR2 : 2 ≤ R := hR₀.trans hR
  have hR1 : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hbR : b + 2 ≤ R :=
    (le_max_right 2 (b + 2)).trans ((le_max_left _ _).trans hR)
  have heR : Real.exp 1 ≤ R :=
    (le_max_left (Real.exp 1) r).trans ((le_max_right _ _).trans hR)
  have hrR : r ≤ R :=
    (le_max_right (Real.exp 1) r).trans ((le_max_right _ _).trans hR)
  let M := fun n y => dynkinMart (driftStepProb d ε ξ)
    (fun z => latticeKernel d (z - y)) X n
  let P := fun y : Site d => euclidNorm y ≤
    (2 / normMin Ψ + 2 * Real.sqrt d) * R
  let inside := fun j => Ψ (toSpace (X j)) < R
  have hrange : ∀ n, (∀ j, j < n → inside j) →
      ∀ z ∈ departureRange X n, euclidNorm z ≤ R / normMin Ψ := by
    intro n hi z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    apply (le_div_iff₀ hm).mpr
    have hc := hcoerce (toSpace (X j))
    rw [norm_toSpace] at hc
    linarith [hi j (Finset.mem_range.mp hj)]
  have hterminal : ∀ n, n ≤ N → (∀ j, j < n → inside j) →
      (∀ y, (localTime X n y : ℝ) ≤ (C₀ + 1) * R + 1) →
      ∀ y, (localTime X n y : ℝ) ≤ K * R := by
    intro n _ _ hl y
    dsimp [K]
    linarith [hl y]
  have hmart : ∀ n, n ≤ N → (∀ j, j < n → inside j) →
      (∀ y, (localTime X n y : ℝ) ≤ K * R) →
      ∀ y, P y → |M n y| ≤ D * Real.sqrt R * Real.log R := by
    intro n hn hi hl y hy
    have hdist : ∀ z ∈ departureRange X n, euclidNorm (z - y) ≤ b * R := by
      intro z hz
      have hzR := hrange n hi z hz
      have hs := CERW.Support.Occupation.euclidNorm_sub_le z y
      dsimp [P] at hy
      dsimp [b]
      have hid : R / normMin Ψ = (1 / normMin Ψ) * R := by ring
      rw [hid] at hzR
      simp only [div_eq_mul_inv, one_mul] at hzR hy ⊢
      nlinarith
    have hv := kernel_bracket_le_radius_log Cb hbracket hCb.le hε.le ξ hprob
      X n y hb hK.le hR2 hbR heR hdist hl
    exact (hF n hn y hy).trans
      (freedman_le_sqrt_mul_log hA.le hE hR1 (Real.log_nonneg hR1) hv)
  have hBN : V * R ^ (d + 1) < (N : ℝ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hVC (by positivity)) hN
  obtain ⟨τ, htN, hexit, hi, hl⟩ := finite_bootstrap_stop X N inside P M R
    ((C₀ + 1) * R) (V * R ^ (d + 1)) (by positivity) hBN
    (fun n hn hi hsmall y => by
      by_cases hy : P y
      · have hh := hlocal ξ hξ hξ0 X n R hR1 h0
          (fun j hj => hstep j (lt_of_lt_of_le hj hn)) hi y
        have hs := hsmall y hy
        change (localTime X n y : ℝ) ≤ (C₀ + 1) * R
        dsimp [M] at hs
        nlinarith
      · have hz : localTime X n y = 0 := by
          by_contra hz
          have hym := mem_departureRange_iff.mpr (Nat.pos_of_ne_zero hz)
          have hh := hrange n hi y hym
          apply hy
          dsimp [P]
          have hid : R / normMin Ψ = (1 / normMin Ψ) * R := by ring
          rw [hid] at hh
          have hs := Real.sqrt_nonneg (d : ℝ)
          have hm' : 0 ≤ 1 / normMin Ψ := by positivity
          simp only [div_eq_mul_inv, one_mul] at hh hm' ⊢
          nlinarith
        rw [hz, Nat.cast_zero]
        positivity)
    (fun n hn hi hl => time_le_of_localTime_bound (by omega) hΨ X n hR1 hK.le hi
      (hterminal n hn hi hl))
    (fun n hn hi hl y hy => (hmart n hn hi (hterminal n hn hi hl) y hy).trans_lt
      (hr R hrR))
  have hlK := hterminal τ htN hi hl
  refine ⟨τ, htN, le_of_not_gt hexit, hi, ?_, ?_⟩
  · intro y
    exact (hlK y).trans (mul_le_mul_of_nonneg_right hKC hRpos.le)
  · intro y hy
    exact (hmart τ htN hi hlK y hy).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDC (Real.sqrt_nonneg R)) (Real.log_nonneg hR1))

end CERW.LimitShapes.Exit
