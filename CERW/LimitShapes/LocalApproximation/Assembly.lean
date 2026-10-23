import CERW.LimitShapes.LocalApproximation.Pointwise
import CERW.LimitShapes.LocalApproximation.Weights

/-!
# Final-time assembly of the local approximation

Pointwise Dynkin error, the actual bracket bound, and the cell modulus give
Lemma `lem:local` without interval maxima.
-/

open LatticeProb CERW MeasureTheory

namespace CERW.LimitShapes.LocalApproximationProof

open private log_add_two_le_two_mul_log from CERW.Support.Norm.LocalTime
open private cell_modulus_of_path from CERW.Support.Norm.ContactEvent

/-- The bracket scale under the square root is the dimensional approximation error. -/
lemma sqrt_bracket_scale {d : ℕ} {B M L : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hL : 0 ≤ L) :
    Real.sqrt (B * M * (if d = 2 then L else 1) * L) =
      Real.sqrt B * (if d = 2 then Real.sqrt M * L else Real.sqrt (M * L)) := by
  split_ifs
  · rw [show B * M * L * L = B * (M * L ^ 2) by ring,
      Real.sqrt_mul hB, Real.sqrt_mul hM, Real.sqrt_sq hL]
  · rw [mul_one, mul_assoc, Real.sqrt_mul hB]

/-- Final-time Freedman and the cell modulus imply the local approximation on legal paths. -/
theorem exists_path_approximation {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → Real.sqrt d ≤ n → X 0 = 0 →
      (∀ j, euclidNorm (X j) ≤ j) → LocalMartingaleBound ε ξ A X n →
      LocalApproximation Ψ ε K X n := by
  obtain ⟨_, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨P, hP, hp⟩ := exists_pointwise_bound.{0} hd hΨ hK
  obtain ⟨B, hB, hb⟩ := exists_bracket_max_bound hd
  obtain ⟨Q, hQ, hq⟩ :=
    CERW.Support.Norm.ContactModulus.exists_normPotential_cell_modulus hd hΨ
  let T := Q * ε * (1 + Real.log (1 + Real.sqrt d))
  have hT : 0 ≤ T := by
    have : 0 ≤ Real.log (1 + Real.sqrt d) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (d : ℝ)])
    dsimp [T]
    positivity
  refine ⟨2 * P * (1 + ε) + 2 * T + A * (Real.sqrt B + 1), by positivity, ?_⟩
  intro ξ hξ hξ0 X n hn hsq h0 hx hm y hy
  obtain ⟨hL, hlog⟩ := log_add_two_le_two_mul_log hn
  have hξ' : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) :=
    CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
  have hyz := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell
    (mem_cell_cellCenter y)
  have hz : euclidNorm (cellCenter y) ≤ 3 * n := by
    have h := norm_le_norm_add_norm_sub' (toSpace (cellCenter y)) y
    rw [norm_toSpace, norm_sub_rev] at h
    linarith
  have hpt := hp ε hε.le ξ hξ hξ0 (fun j (_ : Unit) => X j) () h0 hx n
    (by omega) (cellCenter y) hz
  rw [← CERW.Support.Drift.dynkinMart_driftStepProb_eq_driftDynkin
    (by omega : 1 ≤ d) ε ξ (fun z => latticeKernel d (z - cellCenter y))
    (fun j (_ : Unit) => X j) n ()] at hpt
  have hpt' := hpt.trans (mul_le_mul_of_nonneg_left hlog
    (mul_nonneg hP (by positivity : 0 ≤ 1 + ε)))
  have hbr := hb ε ξ hε.le hξ' X n hn hx (cellCenter y) hz
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hbr hL.le)
  rw [sqrt_bracket_scale hB (Nat.cast_nonneg _) hL.le] at hroot
  have hmart := (hm (cellCenter y) hz).trans
    (mul_le_mul_of_nonneg_left (add_le_add hroot le_rfl) hA)
  have hmod := cell_modulus_of_path hd hε.le hQ hq X n hn hx y
    (toSpace (cellCenter y)) (by linarith [Real.sqrt_nonneg (d : ℝ)])
    (by linarith [Real.sqrt_nonneg (d : ℝ)])
  have hmod' := hmod.trans (mul_le_mul_of_nonneg_left hlog hT)
  let E : ℝ := if d = 2 then Real.sqrt (maxLocalTime X n) * Real.log n
    else Real.sqrt (maxLocalTime X n * Real.log n)
  have hE : 0 ≤ E := by dsimp [E]; split_ifs <;> positivity
  have hsum : |(localTime X n (cellCenter y) : ℝ) -
      normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter y))| ≤
      2 * P * (1 + ε) * Real.log n + A * (Real.sqrt B * E + Real.log n) := by
    have ht := abs_sub
      ((localTime X n (cellCenter y) : ℝ) -
        normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter y)) +
        dynkinMart (driftStepProb d ε ξ)
          (fun z => latticeKernel d (z - cellCenter y)) X n)
      (dynkinMart (driftStepProb d ε ξ)
        (fun z => latticeKernel d (z - cellCenter y)) X n)
    simp only [add_sub_cancel_right] at ht
    exact ht.trans (by dsimp [E]; nlinarith only [hpt', hmart])
  have htotal := abs_sub
    ((localTime X n (cellCenter y) : ℝ) -
      normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter y)))
    (normPotential d ε Ψ (cellSet X n) y -
      normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter y)))
  have hid : ((localTime X n (cellCenter y) : ℝ) -
      normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter y))) -
      (normPotential d ε Ψ (cellSet X n) y -
        normPotential d ε Ψ (cellSet X n) (toSpace (cellCenter y))) =
      cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y := by
    change _ = (localTime X n (cellCenter y) : ℝ) - _
    ring
  rw [hid] at htotal
  have hfin := htotal.trans (add_le_add hsum hmod')
  change _ ≤ _ + _ * E
  nlinarith [mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg B)) hL.le,
    mul_nonneg hA hE, mul_nonneg (show 0 ≤ 2 * P * (1 + ε) + 2 * T by positivity) hE]

end CERW.LimitShapes.LocalApproximationProof
