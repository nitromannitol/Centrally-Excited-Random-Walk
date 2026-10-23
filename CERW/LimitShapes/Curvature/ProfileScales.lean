import CERW.LimitShapes.Curvature.EventScales

/-!
# Logarithmic scales for the global profile

The annular error scale in `sec:global-profile` is bounded by the scale in
Theorem `thm:fluctuations` (iii).
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory Filter
open CERW.Support.Norm.ContactEvent

/-- The planar profile scale is the contact error times one logarithm. -/
theorem sqrt_mul_mul_eq_profile {r L : ℝ} (hr : 0 ≤ r) (hL : 0 < L) :
    Real.sqrt (r * L) * L = Real.sqrt r * L ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_mul hr, Real.sqrt_eq_rpow L, mul_assoc]
  congr 1
  calc
    L ^ ((1 : ℝ) / 2) * L = L ^ ((1 : ℝ) / 2) * L ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    _ = L ^ ((1 : ℝ) / 2 + 1) := (Real.rpow_add hL _ _).symm
    _ = _ := by norm_num

/-- Numeric bounds on the three errors entering the profile estimate. -/
theorem profile_scale_bounds {d : ℕ} (hd : 2 ≤ d) {r L M Co : ℝ}
    (hL : 1 ≤ L) (hr : L ^ (2 * d) ≤ r) (_hM : 0 ≤ M) (hCo : 0 ≤ Co)
    (hMc : M ≤ Co * r) :
    let delta := if d = 2 then Real.sqrt (r * L) else L
    let S := if d = 2 then Real.sqrt r * L ^ ((3 : ℝ) / 2)
      else Real.sqrt (r * L)
    L ≤ S ∧ delta ≤ S ∧ delta * L ^ (d - 1) ≤ S ∧
      (if d = 2 then Real.sqrt M * L else Real.sqrt (M * L)) ≤ Real.sqrt Co * S := by
  have hL0 : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hpow1 : 1 ≤ L ^ (2 * d) := one_le_pow₀ hL
  have hr1 : 1 ≤ r := hpow1.trans hr
  have hr0 : 0 ≤ r := by linarith
  have hLr : L ≤ r := by
    have hp : L ≤ L ^ (2 * d) := by
      obtain ⟨m, hm⟩ : ∃ m, 2 * d = m + 1 := ⟨2 * d - 1, by omega⟩
      rw [hm, pow_succ']
      exact le_mul_of_one_le_right hL0 (one_le_pow₀ hL)
    exact hp.trans hr
  have hLs : L ≤ Real.sqrt (r * L) :=
    (Real.le_sqrt hL0 (mul_nonneg hr0 hL0)).mpr (by nlinarith)
  have hrootM : Real.sqrt M ≤ Real.sqrt Co * Real.sqrt r := by
    rw [← Real.sqrt_mul hCo]
    exact Real.sqrt_le_sqrt hMc
  dsimp only
  by_cases h2 : d = 2
  · simp only [h2, if_true]
    have heq := sqrt_mul_mul_eq_profile hr0 hLpos
    have hds : Real.sqrt (r * L) ≤ Real.sqrt r * L ^ ((3 : ℝ) / 2) := by
      rw [← heq]
      exact le_mul_of_one_le_right (Real.sqrt_nonneg _) hL
    refine ⟨hLs.trans hds, hds, ?_, ?_⟩
    · simpa only [h2, Nat.reduceSub, pow_one] using heq.le
    · calc
        Real.sqrt M * L ≤ Real.sqrt Co * Real.sqrt r * L :=
          mul_le_mul_of_nonneg_right hrootM hL0
        _ ≤ Real.sqrt Co * (Real.sqrt r * L ^ ((3 : ℝ) / 2)) := by
          have hs : Real.sqrt r * L ≤ Real.sqrt (r * L) * L :=
            mul_le_mul_of_nonneg_right
              (Real.sqrt_le_sqrt (le_mul_of_one_le_right hr0 hL)) hL0
          rw [heq] at hs
          nlinarith [mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg Co)]
  · simp only [h2, if_false]
    refine ⟨hLs, hLs, ?_, ?_⟩
    · have hp : L ^ d ≤ Real.sqrt (r * L) := by
        apply (Real.le_sqrt (pow_nonneg hL0 _) (mul_nonneg hr0 hL0)).mpr
        calc
          (L ^ d) ^ 2 = L ^ (2 * d) := by rw [← pow_mul, Nat.mul_comm]
          _ ≤ r := hr
          _ ≤ r * L := le_mul_of_one_le_right hr0 hL
      have heq : L * L ^ (d - 1) = L ^ d := by
        rw [← pow_succ']; congr 1; omega
      rwa [heq]
    · rw [← Real.sqrt_mul hCo]
      exact Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_right hMc hL0])

/-- All logarithmic powers needed by the profile comparison are eventually below the radius. -/
theorem exists_profile_scale_threshold {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 ≤ Real.log n ∧
      Real.log n ^ (2 * d) ≤ scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n := by
  have hΨ := CERW.Support.Norm.EuclideanCoarse.isNorm_euclidean (d := d)
  have hV := CERW.Support.Norm.ContactAssembly.normBallVolume_pos' (by omega : 1 ≤ d) hΨ
  have hp := CERW.Support.Norm.CoarseVolume.eventually_mul_log_pow_le_coarseScale
    (Ψ := fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (by omega : 1 ≤ d) hε hV
    (K := 1) one_pos (2 * d)
  obtain ⟨Np, hp⟩ := eventually_atTop.mp hp
  obtain ⟨Ns, hNs, hs⟩ := Energy.exists_site_scale_threshold hd hΨ hε
  refine ⟨max Np Ns, by omega, ?_⟩
  intro n hn
  refine ⟨(hs n (by omega)).1, ?_⟩
  simpa only [one_mul, CERW.Support.Norm.CoarseVolume.coarseScale, scale] using
    hp n (by omega)

end CERW.LimitShapes.Curvature
