module

public import CERW.LimitShapes.Event
public import CERW.Support.Norm.CoarseVolume

@[expose] public section

/-!
# Scale comparisons for the site estimate

The logarithmic comparisons and the error scale in Lemma `lem:contact`.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb Filter
open CERW.Support.Norm.ContactEvent

/-- The logarithm at `n + 2` is controlled by the logarithm at `n`. -/
theorem log_add_two_le_two_log {n : ℕ} (hn : 3 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
    _ = _ := by rw [Real.log_pow]; norm_num

/-- Eventually the radius dominates the cube of the logarithm and exceeds two. -/
theorem exists_site_scale_threshold {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, 3 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      1 ≤ Real.log n ∧ 2 ≤ scale d Ψ ε n ∧ Real.log n ^ 3 ≤ scale d Ψ ε n := by
  have hd1 : 1 ≤ d := by omega
  have hV := CERW.Support.Norm.ContactAssembly.normBallVolume_pos' hd1 hΨ
  have hcube := CERW.Support.Norm.CoarseVolume.eventually_mul_log_pow_le_coarseScale
    (Ψ := Ψ) hd1 hε hV (K := 1) (by norm_num) 3
  have hr := CERW.Support.Norm.CoarseVolume.eventually_mul_log_pow_le_coarseScale
    (Ψ := Ψ) hd1 hε hV (K := 2) (by norm_num) 0
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcube.and hr)
  refine ⟨max N 5, by omega, ?_⟩
  intro n hn
  obtain ⟨hc, hr⟩ := hN n (le_trans (le_max_left _ _) hn)
  have hn5 : 5 ≤ n := le_trans (le_max_right _ _) hn
  refine ⟨?_, ?_, ?_⟩
  · have h := CERW.Support.Law.one_le_log_add_two (n := n - 2) (by omega)
    have heq : ((n - 2 : ℕ) : ℝ) + 2 = n := by
      have : n - 2 + 2 = n := by omega
      exact_mod_cast this
    rwa [heq] at h
  · simpa only [pow_zero, mul_one, CERW.Support.Norm.CoarseVolume.coarseScale,
      scale] using hr
  · simpa only [one_mul, CERW.Support.Norm.CoarseVolume.coarseScale, scale] using hc

/-- The product of the contact radius and rate is the dimensional error scale. -/
theorem scale_mul_contactRate {d : ℕ} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (ε : ℝ) (n : ℕ) (hr : 0 < scale d Ψ ε n) :
    scale d Ψ ε n * contactRate d Ψ ε n =
      if d = 2 then Real.sqrt (scale d Ψ ε n * Real.log n) else Real.log n := by
  unfold contactRate
  split_ifs
  · exact CERW.Support.Norm.ContactAssembly.mul_sqrt_div_eq hr
  · exact mul_div_cancel₀ _ hr.ne'

end CERW.LimitShapes.Energy
