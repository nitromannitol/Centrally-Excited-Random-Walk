import CERW.LimitShapes.Energy.SiteEnergy
import CERW.LimitShapes.Energy.LocalError

/-!
# The site estimate on the common event

The square-energy argument and Young's inequality give the one-sided potential estimate
and the exterior estimate of Lemma `lem:contact`.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb
open CERW.Support.Norm.ContactEvent

/-- The sitewise one-sided and exterior potential estimates of Lemma `lem:contact`. -/
theorem exists_site_one_sided {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ))
    (K : CERW.LimitShapes.EventConstants) (hCo : 0 ≤ K.CCo) (hMart : 0 ≤ K.CMart) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates Ψ ε ξ K X n →
      ∀ y : Site d, euclidNorm y ≤ 3 * (n : ℝ) →
        (CERW.localTime X n y : ℝ) / 2 -
            C * CERW.Support.Norm.ContactEvent.scale d Ψ ε n *
              CERW.Support.Norm.ContactEvent.contactRate d Ψ ε n ≤
          CERW.normPotential d ε Ψ (CERW.cellSet X n) (CERW.toSpace y) ∧
        (CERW.localTime X n y = 0 →
          |CERW.normPotential d ε Ψ (CERW.cellSet X n) (CERW.toSpace y)| ≤
            C * CERW.Support.Norm.ContactEvent.scale d Ψ ε n *
              CERW.Support.Norm.ContactEvent.contactRate d Ψ ε n) := by
  obtain ⟨B, hB, he⟩ := exists_site_energy_bound hd hΨ hε hell K hCo
  obtain ⟨P, hP, hp⟩ := exists_site_pointwise_bound hd hΨ hε
  let A := B + P + K.CMart + 2 * (d : ℝ) + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hBA : B ≤ A := by dsimp [A]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hPA : P ≤ A := by dsimp [A]; linarith
  have hMA : K.CMart ≤ A := by dsimp [A]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hdA : 2 * (d : ℝ) ≤ A := by dsimp [A]; linarith
  obtain ⟨C, hC, hc⟩ := exists_local_error_and_one_sided hd A hA
  obtain ⟨N, hN3, hN⟩ := exists_site_scale_threshold hd hΨ hε
  refine ⟨C, hC, N, hN3, ?_⟩
  intro ξ hξ hξ0 X n hn hty hev y hy
  have hn3 := hN3.trans hn
  obtain ⟨hL, hr, hcube⟩ := hN n hn
  let g : Site d → ℝ := fun z => latticeKernel d (z - y)
  let E := kernelEnergy g X n
  let V := dynkinBracket (driftStepProb d ε ξ) g g X n
  have hE0 : 0 ≤ E := by
    dsimp [E, kernelEnergy]
    positivity
  have hEn := he ξ hξ hξ0 X n hn3 hL hr hcube hty hev y hy
  have hEnA : E ≤ A * ((if d = 2 then Real.log n else 1) *
      (localTime X n y : ℝ) + (if d = 2 then scale d Ψ ε n else Real.log n)) := by
    refine hEn.trans (mul_le_mul_of_nonneg_right hBA ?_)
    have hp0 : 0 ≤ (if d = 2 then Real.log (n : ℝ) else 1) := by
      split_ifs <;> linarith
    have hq0 : 0 ≤ (if d = 2 then scale d Ψ ε n else Real.log n) := by
      split_ifs <;> linarith
    positivity
  have hξc := subgradient_coordinate_bound hΨ hε.le hell ξ hξ hξ0
  have hv := dynkinBracket_le_step_energy (by omega : 1 ≤ d) hε.le ξ hξc g X n
  have hsum : (∑ j ∈ Finset.range n, ∑ e ∈ unitSteps d,
      (g (X j + e) - g (X j)) ^ 2) = 2 * (d : ℝ) * E := by
    dsimp [E]
    rw [kernelEnergy_eq_time_sum]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp
  have hV : V ≤ A * E := by
    change V ≤ _ at hv
    rw [hsum] at hv
    exact hv.trans (mul_le_mul_of_nonneg_right hdA hE0)
  have hm := hev.2.2.2.2.1 y hy
  have hM : |dynkinMart (driftStepProb d ε ξ) g X n| ≤
      A * (Real.sqrt (V * Real.log n) + Real.log n) :=
    hm.trans (mul_le_mul_of_nonneg_right hMA (by positivity))
  have herr := (hp ξ hξ hξ0 X n hn3 hty y hy).trans
    (mul_le_mul_of_nonneg_right hPA (by linarith : 0 ≤ Real.log (n : ℝ)))
  have ht := hc (scale d Ψ ε n) (Real.log n) (localTime X n y : ℝ) E V
    (dynkinMart (driftStepProb d ε ξ) g X n)
    (normPotential d ε Ψ (cellSet X n) (toSpace y)) (by linarith) hL hcube
    (Nat.cast_nonneg _) hE0 hEnA hV hM herr
  have hscale := scale_mul_contactRate Ψ ε n (by linarith : 0 < scale d Ψ ε n)
  rw [← hscale] at ht
  refine ⟨?_, ?_⟩
  · simpa only [mul_assoc] using ht.2.1
  · intro hz
    have hzR : (localTime X n y : ℝ) = 0 := by exact_mod_cast hz
    simpa only [mul_assoc] using ht.2.2 hzR

end CERW.LimitShapes.Energy
