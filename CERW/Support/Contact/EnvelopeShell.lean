import CERW.Model.Occupation

/-!
# Two consequences of the envelope

`eq:shellW`: if `ℓ_n(y) ≤ c₀ (b - |y|)_+ + A` everywhere, then every site of the shell
`||y| - r| ≤ 3` with `r ≥ b + 3` has `ℓ_n(y) ≤ A`, so `M_sh(r) ≤ A`. `eq:global`: if
`M_n ≤ C₀ N` with `N ≥ 1`, the error scale satisfies `e_n(M_n) ≤ C √N L` for `d = 2`, and
`e_n(M_n) ≤ C (√(NL) + L)` for `d ≥ 3`.
-/

namespace CERW.Support.Contact

open LatticeProb CERW

variable {d : ℕ}

/-- `eq:shellW`: an envelope `ℓ_n ≤ c₀ (b - |·|)_+ + A` gives `M_sh(r) ≤ A` for
`r ≥ b + 3`. -/
theorem shellMax_le_of_envelope (X : ℕ → Site d) (n r : ℕ) {c₀ b A : ℝ} (hA : 0 ≤ A)
    (henv : ∀ y : Site d, (localTime X n y : ℝ) ≤ c₀ * max (b - euclidNorm y) 0 + A)
    (hr : b + 3 ≤ r) : (shellMax X n r : ℝ) ≤ A := by
  classical
  have hsup : shellMax X n r ≤ ⌊A⌋₊ := by
    rw [shellMax]
    refine Finset.sup_le ?_
    intro y hy
    obtain ⟨-, hshell⟩ := Finset.mem_filter.mp hy
    have hb_le : b ≤ euclidNorm y := by
      have h1 : -3 ≤ euclidNorm y - (r : ℝ) := (abs_le.mp hshell).1
      linarith [hr, h1]
    refine Nat.le_floor ?_
    have hmax : max (b - euclidNorm y) 0 = 0 := max_eq_right (by linarith)
    have henvY := henv y
    rw [hmax, mul_zero, zero_add] at henvY
    exact henvY
  calc (shellMax X n r : ℝ) ≤ (⌊A⌋₊ : ℝ) := by exact_mod_cast hsup
    _ ≤ A := Nat.floor_le hA

/-- `eq:global`: if `0 ≤ M ≤ C₀ N` with `N ≥ 1` and `L ≥ 1`, then
`√M L + L ≤ (√C₀ + 1) √N L` and `√(M L) + L ≤ (√C₀ + 1) (√(N L) + L)`. -/
theorem error_scale_le {M N L C₀ : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀) (hMN : M ≤ C₀ * N)
    (hN : 1 ≤ N) (hL : 1 ≤ L) :
    Real.sqrt M * L + L ≤ (Real.sqrt C₀ + 1) * (Real.sqrt N * L) ∧
      Real.sqrt (M * L) + L ≤ (Real.sqrt C₀ + 1) * (Real.sqrt (N * L) + L) := by
  have hLnn : 0 ≤ L := by linarith
  have _ : 0 ≤ M := hM
  constructor
  · have hsq : Real.sqrt M ≤ Real.sqrt C₀ * Real.sqrt N := by
      calc Real.sqrt M ≤ Real.sqrt (C₀ * N) := Real.sqrt_le_sqrt hMN
        _ = Real.sqrt C₀ * Real.sqrt N := Real.sqrt_mul hC₀ N
    have h1 : Real.sqrt M * L ≤ Real.sqrt C₀ * Real.sqrt N * L :=
      mul_le_mul_of_nonneg_right hsq hLnn
    have h2 : L ≤ Real.sqrt N * L := by
      have hs : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
      simpa using mul_le_mul_of_nonneg_right hs hLnn
    calc Real.sqrt M * L + L
        ≤ Real.sqrt C₀ * Real.sqrt N * L + Real.sqrt N * L := add_le_add h1 h2
      _ = (Real.sqrt C₀ + 1) * (Real.sqrt N * L) := by ring
  · have hle : M * L ≤ C₀ * (N * L) := by
      calc M * L ≤ (C₀ * N) * L := mul_le_mul_of_nonneg_right hMN hLnn
        _ = C₀ * (N * L) := by ring
    have hsq : Real.sqrt (M * L) ≤ Real.sqrt C₀ * Real.sqrt (N * L) := by
      calc Real.sqrt (M * L) ≤ Real.sqrt (C₀ * (N * L)) := Real.sqrt_le_sqrt hle
        _ = Real.sqrt C₀ * Real.sqrt (N * L) := Real.sqrt_mul hC₀ (N * L)
    calc Real.sqrt (M * L) + L
        ≤ Real.sqrt C₀ * Real.sqrt (N * L) + L := by linarith [hsq]
      _ ≤ (Real.sqrt C₀ + 1) * (Real.sqrt (N * L) + L) := by
          have hprod : 0 ≤ Real.sqrt C₀ * L + Real.sqrt (N * L) := by
            have h1 : 0 ≤ Real.sqrt C₀ * L := mul_nonneg (Real.sqrt_nonneg C₀) hLnn
            have h2 : 0 ≤ Real.sqrt (N * L) := Real.sqrt_nonneg (N * L)
            linarith
          nlinarith [hprod]

end CERW.Support.Contact
