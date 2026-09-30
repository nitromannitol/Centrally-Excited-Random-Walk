import CERW.Support.Occupation.SiteArith
import CERW.Support.Crossing.LastEntrance
import CERW.Model.Kernel

/-!
# Crossing and halving arithmetic

A nearest-neighbour path from the origin that reaches radius `r` crosses every slab
`{b < v · x ≤ b + 1}` of the direction `v` of its exit point, and it has a last entrance time
into the half-space `{v · x > b}` (`exists_crossing_interval`). The crossing exponent
`γ = 2d/(2d-1)` is positive. At a halving step, the radial inequality forces either halving or a
definite drop (`step_dichotomy`).
-/

namespace CERW.Support.Coarse

open LatticeProb Finset CERW CERW.Support.Crossing CERW.Support.Occupation

variable {d : ℕ}

/-- If the path exceeds radius `r > b + 1` by time `n`, then at the first time `t` it reaches
radius `r` there is a crossing interval `[s, t)` in the direction `v = X_t / |X_t|`: all sites of
the interval have `v · x > b` and `|x| < r`, and the projected gain over it is at least
`r - (b + 1)`. -/
theorem exists_crossing_interval {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ)
    (h0 : X 0 ω = 0) (hstep : ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d) {b r : ℝ}
    (hb : 0 ≤ b) (hbr : b + 1 < r) (hH : r < maxRadius (fun j => X j ω) n) :
    ∃ s t : ℕ, s < t ∧ t ≤ n ∧ ∃ v : EuclideanSpace ℝ (Fin d), ‖v‖ = 1 ∧
      (∀ j ∈ Ico s t, b < inner ℝ v (toSpace (X j ω)) ∧ euclidNorm (X j ω) < r) ∧
      r - (b + 1) ≤ inner ℝ v (toSpace (X t ω) - toSpace (X s ω)) := by
  classical
  have hzero : euclidNorm (X 0 ω) = 0 := by
    rw [← norm_toSpace, h0, toSpace_zero, norm_zero]
  have hexn : ∃ j ∈ Finset.range (n + 1), r < euclidNorm (X j ω) :=
    (Finset.lt_sup'_iff _).mp hH
  have hex : ∃ j, r ≤ euclidNorm (X j ω) := by
    obtain ⟨j, -, hj⟩ := hexn
    exact ⟨j, hj.le⟩
  obtain ⟨τ, hτspec, hτmin⟩ :
      ∃ τ, r ≤ euclidNorm (X τ ω) ∧ ∀ j < τ, euclidNorm (X j ω) < r := by
    exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_le.mp (Nat.find_min hex hj)⟩
  have hτn : τ ≤ n := by
    obtain ⟨j, hj, hjr⟩ := hexn
    by_contra hlt
    rw [not_le] at hlt
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact absurd hjr (not_lt.mpr (hτmin j (lt_of_le_of_lt hjn hlt)).le)
  have hτpos : 0 < τ := by
    rcases Nat.eq_zero_or_pos τ with hτ | hτ
    · rw [hτ, hzero] at hτspec
      linarith
    · exact hτ
  have hxτ : toSpace (X τ ω) ≠ 0 := by
    intro hx
    rw [← norm_toSpace, hx, norm_zero] at hτspec
    linarith
  set v : EuclideanSpace ℝ (Fin d) := unitDir (toSpace (X τ ω)) with hvdef
  have hv : ‖v‖ = 1 := norm_unitDir_eq_one hxτ
  have hfτ : inner ℝ v (toSpace (X τ ω)) = euclidNorm (X τ ω) := by
    rw [hvdef, inner_unitDir_self, norm_toSpace]
  obtain ⟨s, hs0, hsτ, hfs, hfin⟩ := exists_last_entrance
    (f := fun j => inner ℝ v (toSpace (X j ω))) (b := b) (τ := τ)
    (by rw [h0, toSpace_zero, inner_zero_right]; exact hb)
    (fun j => by
      have hsub : inner ℝ v (toSpace (X (j + 1) ω)) - inner ℝ v (toSpace (X j ω)) ≤ 1 := by
        rw [← inner_sub_right, ← toSpace_sub]
        exact inner_toSpace_le_one hv (hstep j)
      linarith)
    hτpos
  have hslt : s < τ := by
    refine lt_of_le_of_ne hsτ ?_
    rintro rfl
    rw [hfτ] at hfs
    linarith
  refine ⟨s, τ, hslt, hτn, v, hv, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_Ico] at hj
    exact ⟨hfin j hj.1 hj.2, hτmin j hj.2⟩
  · rw [inner_sub_right, hfτ]
    linarith

/-- The exponent `γ = 2d/(2d - 1)` of the crossing bound is positive once `d ≥ 1`. -/
theorem gamma_pos (hd : 1 ≤ d) : 0 < (2 * d : ℝ) / (2 * d - 1) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_pos (by linarith) (by linarith)

/-- Either `F(r + b')` is at most `A/2`, or the drop across the grid cell is at least
`A / K` with `K = 4 Cr (S + 1)`. -/
theorem step_dichotomy {Crad Cr S Ssh Fm Fp Fm' Fp' A err : ℝ} (hCrad : 0 < Crad)
    (hCrad' : Crad ≤ Cr) (hS0 : 0 ≤ S) (hS : S ≤ Ssh) (hFp' : Fp' ≤ Fp)
    (hFm : Fm ≤ Fm') (hFpm : Fp ≤ Fm) (hrad : Fp ≤ Crad * S * (Fm - Fp) + err)
    (herr : err ≤ A / 4) :
    Fp' ≤ A / 2 ∨ A / (4 * Cr * (Ssh + 1)) ≤ Fm' - Fp' := by
  rcases le_or_gt Fp' (A / 2) with h | h
  · exact Or.inl h
  · right
    have hCr0 : 0 < Cr := lt_of_lt_of_le hCrad hCrad'
    have hD : 0 ≤ Fm - Fp := sub_nonneg.mpr hFpm
    have h1 : A / 4 < Crad * S * (Fm - Fp) := by linarith
    have h2 : Crad * S * (Fm - Fp) ≤ Cr * (Ssh + 1) * (Fm - Fp) := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact mul_le_mul hCrad' (by linarith) hS0 hCr0.le
    have h3 : Fm - Fp ≤ Fm' - Fp' := by linarith
    have hSsh0 : 0 ≤ Ssh := le_trans hS0 hS
    have h4 : Cr * (Ssh + 1) * (Fm - Fp) ≤ Cr * (Ssh + 1) * (Fm' - Fp') :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have hpos : 0 < 4 * Cr * (Ssh + 1) := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith

end CERW.Support.Coarse
