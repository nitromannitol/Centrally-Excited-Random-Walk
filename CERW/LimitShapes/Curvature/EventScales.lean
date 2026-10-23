import CERW.LimitShapes.Energy.SiteScales
import CERW.Support.Norm.EuclideanCoarse

/-!
# Event scale thresholds

Uniform scale comparisons used for the annulus in `eq:mass`.
-/

namespace CERW.LimitShapes.Curvature

open CERW LatticeProb MeasureTheory Filter
open CERW.Support.Norm.ContactEvent

/-- The contact rate is eventually small, while the contact error exceeds one. -/
theorem exists_annular_scale_threshold {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {Ci : ℝ} (hCi : 0 < Ci) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      2 ≤ scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n ∧
      1 ≤ scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
        contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n ∧
      Ci * contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n ≤ 1 / 2 := by
  let Ψ := fun v : EuclideanSpace ℝ (Fin d) => ‖v‖
  have hΨ := CERW.Support.Norm.EuclideanCoarse.isNorm_euclidean (d := d)
  obtain ⟨Ns, hNs, hs⟩ := Energy.exists_site_scale_threshold hd hΨ hε
  have hV := CERW.Support.Norm.ContactAssembly.normBallVolume_pos' (by omega : 1 ≤ d) hΨ
  have ht := CERW.Support.Norm.CoarseVolume.eventually_mul_log_pow_le_coarseScale
    (Ψ := Ψ) (by omega : 1 ≤ d) hε hV (K := (2 * Ci + 1) ^ 2) (by positivity) 1
  obtain ⟨Nt, ht⟩ := eventually_atTop.mp ht
  refine ⟨max Ns Nt, by omega, ?_⟩
  intro n hn
  obtain ⟨hl, hr, hc⟩ := hs n (by omega)
  have hk : (2 * Ci + 1) ^ 2 * Real.log n ≤ scale d Ψ ε n := by
    simpa only [pow_one, CERW.Support.Norm.CoarseVolume.coarseScale, scale] using
      ht n (by omega)
  have hrp : 0 < scale d Ψ ε n := by linarith
  have htpos : 0 < 2 * Ci + 1 := by positivity
  have hquot : Real.log n / scale d Ψ ε n ≤ (1 / (2 * Ci + 1)) ^ 2 := by
    apply (div_le_iff₀ hrp).mpr
    have := mul_le_mul_of_nonneg_left hk (le_of_lt (sq_pos_of_pos htpos))
    field_simp
    nlinarith
  have hq : contactRate d Ψ ε n ≤ 1 / (2 * Ci + 1) := by
    unfold contactRate
    split_ifs
    · exact (Real.sqrt_le_iff).mpr ⟨by positivity, hquot⟩
    · have htone : 1 ≤ 2 * Ci + 1 := by linarith
      have hinv : 0 ≤ 1 / (2 * Ci + 1) := by positivity
      have hinv1 : 1 / (2 * Ci + 1) ≤ 1 := (div_le_one htpos).mpr htone
      exact hquot.trans (by nlinarith)
  refine ⟨hr, ?_, ?_⟩
  · rw [Energy.scale_mul_contactRate Ψ ε n hrp]
    split_ifs
    · apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
      nlinarith
    · exact hl
  · have hmul := mul_le_mul_of_nonneg_left hq hCi.le
    have hhalf : Ci * (1 / (2 * Ci + 1)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ htpos]
      linarith
    exact hmul.trans hhalf

end CERW.LimitShapes.Curvature
