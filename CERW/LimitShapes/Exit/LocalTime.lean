module

public import CERW.Support.Norm.LocalTime
public import CERW.Support.LocalTime.LatticeKernelFacts
public import CERW.Support.Occupation
public import CERW.Generic.Norm
public import CERW.Support.Drift.Dynkin

@[expose] public section

/-!
# Local times before the first exit

The deterministic estimate in Proposition `prop:coarse` follows from `eq:dynkin`,
`eq:gradient`, and lattice packing, before any martingale stopping argument.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb
open CERW.Support.Occupation CERW.Support.Law CERW.Support.Drift
open private norm_drift_le norm_centralDiff_le_of_step from CERW.Support.Norm.LocalTime

/-- The gradient weights on a finite set in a ball have a linear radius bound. -/
private lemma sum_weights_le {d : ℕ} (hd : 1 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (F : Finset (Site d)) (y : Site d) (r : ℝ), 0 ≤ r →
      (∀ z ∈ F, euclidNorm (z - y) ≤ r) →
      ∑ z ∈ F, (1 + euclidNorm (z - y)) ^ (1 - (d : ℝ)) ≤ A * (r + 1) := by
  classical
  obtain ⟨A, hA, hbound⟩ := CERW.Generic.Lattice.sum_ballFinset_rpow_one_sub_le (d := d) hd
  refine ⟨A, hA, fun F y r hr hF => ?_⟩
  calc
    _ = ∑ z ∈ F.image (fun z => z - y),
        (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact sub_left_injective hab
    _ ≤ ∑ z ∈ ballFinset d r, (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
        exact mem_ballFinset_iff.mpr (hF w hw)
      · intro z _ _
        exact Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
    _ ≤ A * (r + 1) := hbound r hr

/-- Before the first exit, the local time is bounded by its Dynkin martingale and
an error linear in the radius, as used in Proposition `prop:coarse`. -/
theorem exists_localTime_le_abs_dynkin_add_radius {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) →
        ξ 0 = 0 → ∀ (X : ℕ → Site d) (n : ℕ) (R : ℝ), 1 ≤ R → X 0 = 0 →
        (∀ j : ℕ, j < n → X (j + 1) - X j ∈ CERW.unitSteps d) →
        (∀ j : ℕ, j < n → Ψ (CERW.toSpace (X j)) < R) →
        ∀ y : Site d, (CERW.localTime X n y : ℝ) ≤
          |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
            (fun z => CERW.latticeKernel d (z - y)) X n| + C * R := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hmin, hcoercive⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  obtain ⟨h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨Cb, hgrowth⟩ := hK.growth
  obtain ⟨A, hA, hweights⟩ := sum_weights_le (d := d) hd1
  let a : ℝ := 1 / normMin Ψ
  let B : ℝ := max Cb 0
  let D : ℝ := max (normMax Ψ) 0 * (Real.sqrt d * max Cg 0)
  have ha : 0 < a := one_div_pos.mpr hmin
  have hB : 0 ≤ B := le_max_right _ _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C : ℝ := 2 * B * (2 * a + 3) + ε * D * A * (2 * a + 1) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun ξ hξ hξ0 X n R hR h0 hstep hinside y => ?_⟩
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  by_cases hy : y ∈ departureRange X n
  · have hsite : ∀ z ∈ departureRange X n, euclidNorm z ≤ a * R := by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      have hc := hcoercive (toSpace (X j))
      rw [norm_toSpace] at hc
      have hjR := hinside j (Finset.mem_range.mp hj)
      have hdiv : euclidNorm (X j) ≤ R / normMin Ψ :=
        (le_div_iff₀ hmin).mpr (by nlinarith)
      simpa [a, div_eq_mul_inv, mul_comm] using hdiv
    have hyR := hsite y hy
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := by omega
      simp [hn0, departureRange] at hy
    have hend : euclidNorm (X n) ≤ a * R + 1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      have hk : k < k + 1 := Nat.lt_succ_self k
      have hkR := hsite (X k) (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩)
      have hs := euclidNorm_add_le (X k) (X (k + 1) - X k)
      rw [add_sub_cancel, CERW.Support.Law.euclidNorm_of_mem_unitSteps (hstep k hk)] at hs
      linarith
    have hgrowth' : ∀ z : Site d, euclidNorm z ≤ (2 * a + 1) * R →
        |latticeKernel d z| ≤ B * (2 * a + 3) * R := by
      intro z hz
      have hp : 0 < euclidNorm z + 2 := by linarith [euclidNorm_nonneg z]
      have hlog0 : 0 ≤ Real.log (euclidNorm z + 2) :=
        Real.log_nonneg (by linarith [euclidNorm_nonneg z])
      have hb := (hgrowth z).trans
        (mul_le_mul_of_nonneg_right (le_max_left Cb 0) hlog0)
      have hl := Real.log_le_sub_one_of_pos hp
      have hlR : Real.log (euclidNorm z + 2) ≤ (2 * a + 3) * R := by nlinarith
      exact hb.trans (by nlinarith)
    have hnval : |latticeKernel d (X n - y)| ≤ B * (2 * a + 3) * R := by
      apply hgrowth'
      have hs := euclidNorm_sub_le (X n) y
      nlinarith
    have hzeroval : |latticeKernel d (-y)| ≤ B * (2 * a + 3) * R := by
      apply hgrowth'
      rw [CERW.Generic.Lattice.euclidNorm_neg]
      nlinarith
    have hsum : |∑ z ∈ departureRange X n,
        inner ℝ (ξ z) (centralDiff (latticeKernel d) (z - y))| ≤
        D * A * (2 * a + 1) * R := by
      have hterm : ∀ z ∈ departureRange X n,
          |inner ℝ (ξ z) (centralDiff (latticeKernel d) (z - y))| ≤
            D * (1 + euclidNorm (z - y)) ^ (1 - (d : ℝ)) := by
        intro z _
        have hz := norm_centralDiff_le_of_step (le_max_right Cg 0)
          (le_max_left Cg 0) hgrad (z - y)
        have hξz := (norm_drift_le hΨ hξ hξ0 z).trans (le_max_left (normMax Ψ) 0)
        calc
          _ ≤ ‖ξ z‖ * ‖centralDiff (latticeKernel d) (z - y)‖ :=
            abs_real_inner_le_norm _ _
          _ ≤ max (normMax Ψ) 0 *
              (Real.sqrt d * (max Cg 0 *
                (1 + euclidNorm (z - y)) ^ (1 - (d : ℝ)))) :=
            mul_le_mul hξz hz (norm_nonneg _) (le_max_right _ _)
          _ = _ := by dsimp [D]; ring
      have hw := hweights (departureRange X n) y (2 * a * R) (by positivity)
        (fun z hz => (euclidNorm_sub_le z y).trans (by linarith [hsite z hz]))
      calc
        _ ≤ ∑ z ∈ departureRange X n,
            |inner ℝ (ξ z) (centralDiff (latticeKernel d) (z - y))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ z ∈ departureRange X n,
            D * (1 + euclidNorm (z - y)) ^ (1 - (d : ℝ)) := Finset.sum_le_sum hterm
        _ = D * ∑ z ∈ departureRange X n,
            (1 + euclidNorm (z - y)) ^ (1 - (d : ℝ)) := (Finset.mul_sum ..).symm
        _ ≤ D * (A * (2 * a * R + 1)) := mul_le_mul_of_nonneg_left hw hD
        _ ≤ D * A * (2 * a + 1) * R := by nlinarith [mul_nonneg hD hA.le]
    have hid := CERW.Support.Norm.ContactDynkin.localTime_eq_driftDynkin
      hK.poisson ε ξ hξ0 (fun j (_ : Unit) => X j) () h0 n y
    rw [← dynkinMart_driftStepProb_eq_driftDynkin hd1] at hid
    have hm := neg_le_abs (dynkinMart (driftStepProb d ε ξ)
      (fun z => latticeKernel d (z - y)) X n)
    have hs := le_abs_self (∑ z ∈ departureRange X n,
      inner ℝ (ξ z) (centralDiff (latticeKernel d) (z - y)))
    have hv := le_abs_self (latticeKernel d (X n - y))
    have hv0 := neg_le_abs (latticeKernel d (-y))
    dsimp [C]
    nlinarith
  · have hzero : localTime X n y = 0 := by
      have := mt mem_departureRange_iff.mpr hy
      omega
    rw [hzero, Nat.cast_zero]
    exact add_nonneg (abs_nonneg _) (mul_nonneg hC.le hR0)

end CERW.LimitShapes.Exit
