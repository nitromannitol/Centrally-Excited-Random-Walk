module

public import CERW.LimitShapes.Energy.SitePointwise
public import CERW.LimitShapes.Energy.FarPotential

@[expose] public section

/-!
# Continuum approximation at the first exit

The site comparison and cell modulus give the approximation in Proposition `prop:coarse`.
The far field uses the deterministic potential estimate.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory
open CERW.Support.Occupation CERW.Support.Norm.ContactEvent
open private cell_modulus_of_path from CERW.Support.Norm.ContactEvent

/-- Actual site martingale bounds give the continuum approximation needed by the lower bound. -/
theorem exists_exit_approximation {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ A : ℝ, 0 < A ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), 3 ≤ n → Real.sqrt d ≤ (n : ℝ) →
        PathTyping d X → ∀ R : ℝ, 1 ≤ R → 1 ≤ Real.log R →
        Real.log ((n : ℝ) + 2) ≤ (d + 2 : ℝ) * Real.log R →
        (∀ z : Site d, euclidNorm z ≤ (2 / normMin Ψ + 2 * Real.sqrt d) * R →
          |dynkinMart (driftStepProb d ε ξ) (fun w => latticeKernel d (w - z)) X n| ≤
            B * Real.sqrt R * Real.log R) →
        ∀ v : EuclideanSpace ℝ (Fin d),
          ‖v‖ ≤ (1 / normMin Ψ + Real.sqrt d) * R →
          |cellLocalTime X n v - normPotential d ε Ψ (cellSet X n) v| ≤
            A * Real.sqrt R * Real.log R := by
  obtain ⟨P, hP, hpoint⟩ := Energy.exists_site_pointwise_bound hd hΨ hε
  obtain ⟨M, hM, hmod⟩ :=
    CERW.Support.Norm.ContactModulus.exists_normPotential_cell_modulus hd hΨ
  let K := M * ε * (1 + Real.log (1 + Real.sqrt d))
  let F := 2 * ε / unitBallVolume d * (2 * normMax Ψ)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (mul_nonneg hM hε.le)
      (by
        have hs : 1 ≤ 1 + Real.sqrt d := by linarith [Real.sqrt_nonneg (d : ℝ)]
        linarith [Real.log_nonneg hs])
  have hΛ : 0 < normMax Ψ :=
    (Generic.Norm.normMin_pos_mul_le hΨ (by omega)).1.trans_le
      (CERW.Support.Norm.ContactAssembly.normMin_le_normMax (by omega) hΨ)
  have hω := unitBallVolume_pos d
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  refine ⟨B + (P + K) * (d + 2 : ℝ) + F + 1, by positivity, ?_⟩
  intro ξ hξ hξ0 X n hn hs hX R hR hlog htime hmart v hv
  have hRn : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR
  have hsqrt : 1 ≤ Real.sqrt R := Real.one_le_sqrt.mpr hR
  have hprod : 1 ≤ Real.sqrt R * Real.log R := by nlinarith
  have hnorm := euclidNorm_le_of_steps X hX.1 hX.2
  by_cases hnear : ‖v‖ ≤ 2 * (n : ℝ)
  · have hcell := norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter v)
    have hz : euclidNorm (cellCenter v) ≤ ‖v‖ + Real.sqrt d := by
      have hh := norm_le_norm_add_norm_sub' (toSpace (cellCenter v)) v
      rw [norm_sub_rev] at hh
      rw [norm_toSpace] at hh
      linarith [Real.sqrt_nonneg (d : ℝ)]
    have hztime : euclidNorm (cellCenter v) ≤ 3 * (n : ℝ) := by linarith
    have hzspace : euclidNorm (cellCenter v) ≤
        (2 / normMin Ψ + 2 * Real.sqrt d) * R := by
      have hm := (Generic.Norm.normMin_pos_mul_le hΨ (by omega)).1
      have hT : 0 ≤ 1 / normMin Ψ + Real.sqrt d := by positivity
      have hsqR : Real.sqrt d ≤ Real.sqrt d * R :=
        le_mul_of_one_le_right (Real.sqrt_nonneg _) hR
      have he : 2 / normMin Ψ = 2 * (1 / normMin Ψ) := by ring
      rw [he]
      have hbase : 0 ≤ (1 / normMin Ψ) * R := by positivity
      nlinarith only [hz, hv, hsqR, hbase]
    have hp := hpoint ξ hξ hξ0 X n hn hX (cellCenter v) hztime
    have hmt := hmart (cellCenter v) hzspace
    have hmd := cell_modulus_of_path hd hε.le hM hmod X n (by omega) hnorm
      v (toSpace (cellCenter v)) (by linarith [Real.sqrt_nonneg (d : ℝ)])
      (hcell.trans (by linarith [Real.sqrt_nonneg (d : ℝ)]))
    have hln : Real.log n ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by linarith)
    have herror : |cellLocalTime X n v - normPotential d ε Ψ (cellSet X n) v| ≤
        B * Real.sqrt R * Real.log R +
          (P + K) * ((d + 2 : ℝ) * Real.log R) := by
      have hab := abs_add_le
        ((localTime X n (cellCenter v) : ℝ) -
          normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter v)) +
          dynkinMart (driftStepProb d ε ξ)
            (fun w => latticeKernel d (w - cellCenter v)) X n)
        (-dynkinMart (driftStepProb d ε ξ)
          (fun w => latticeKernel d (w - cellCenter v)) X n)
      have htri := abs_sub
        ((localTime X n (cellCenter v) : ℝ) -
          normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter v)))
        (normPotential d ε Ψ (cellSet X n) v -
          normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter v)))
      simp only [add_neg_cancel_right, abs_neg] at hab
      have he : (localTime X n (cellCenter v) : ℝ) -
          normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter v)) -
          (normPotential d ε Ψ (cellSet X n) v -
            normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter v))) =
          cellLocalTime X n v - normPotential d ε Ψ (cellSet X n) v := by
        rw [cellLocalTime]
        ring
      rw [he] at htri
      have hpt := mul_le_mul_of_nonneg_left (hln.trans htime) hP
      have hmdt := mul_le_mul_of_nonneg_left htime hK
      change |_| ≤ K * Real.log ((n : ℝ) + 2) at hmd
      linarith only [hab, htri, hp, hmt, hmd, hpt, hmdt]
    apply herror.trans
    have hsc := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ (P + K) * (d + 2 : ℝ) * Real.log R by positivity)
    have hrest : 0 ≤ (F + 1) * Real.sqrt R * Real.log R := by positivity
    nlinarith only [hsc, hrest]
  · obtain ⟨hz, hf⟩ := Energy.far_potential_bound hd hΨ hε.le (by omega) hs hnorm
      (lt_of_not_ge hnear)
    rw [hz, zero_sub, abs_neg]
    apply hf.trans
    have hnon : 0 ≤ B + (P + K) * (d + 2 : ℝ) + 1 := by positivity
    have hh := mul_le_mul_of_nonneg_left hprod hF
    nlinarith only [hh, mul_nonneg hnon (le_trans (by norm_num) hprod)]

end CERW.LimitShapes.Exit
