import CERW.LimitShapes.Energy.Gradient
import CERW.LimitShapes.Energy.PlanarEnvelope
import CERW.Generic.Lattice.Centered
import CERW.Model.Occupation

/-!
# Summing the shifted-square drift along a path

The pointwise gradient envelope of Lemma `lem:contact` sums to a linear planar
bound and a logarithmic bound in higher dimensions on the actual departure range.
-/

namespace CERW.LimitShapes.Energy

open CERW LatticeProb

/-- Translation of a function translates its central difference. -/
private lemma centralDiff_translate {d : ℕ} (f : Site d → ℝ) (x y : Site d) :
    CERW.Support.Law.centralDiff (fun z => f (z - y)) x =
      CERW.Support.Law.centralDiff f (x - y) := by
  ext i
  change (f (x + unit i - y) - f (x - unit i - y)) / 2 =
    (f (x - y + unit i) - f (x - y - unit i)) / 2
  simp only [show x + unit i - y = x - y + unit i by abel,
    show x - unit i - y = x - y - unit i by abel]

/-- The actual shifted-square drift has the pathwise bound used in Lemma `lem:contact`. -/
theorem exists_path_square_drift_bound {d : ℕ} (hd : 2 ≤ d)
    (A : ℝ) (hA : 0 < A) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n →
        (∀ j : ℕ, j < n → euclidNorm (X j) ≤ (n : ℝ)) →
        ((CERW.departureRange X n).card : ℝ) ≤ A * R ^ d →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d), (∀ x, ‖ξ x‖ ≤ Λ) →
      ∀ y : Site d, euclidNorm y ≤ 3 * (n : ℝ) →
        |∑ x ∈ CERW.departureRange X n,
          inner ℝ (ξ x) (CERW.Support.Law.centralDiff
            (fun z => (CERW.latticeKernel d (z - y) -
              (if d = 2 then (2 / Real.pi) * Real.log R else 0)) ^ 2) x)| ≤
          C * (if d = 2 then R else Real.log ((n : ℝ) + 2)) := by
  classical
  obtain ⟨G, hG, hg⟩ := exists_shifted_square_centralDiff_bound hd
  have hsum (R : ℝ) (hR : 2 ≤ R) (S : Finset (Site d))
      (ξ : Site d → EuclideanSpace ℝ (Fin d)) (hξ : ∀ x, ‖ξ x‖ ≤ Λ)
      (y : Site d) :
      |∑ x ∈ S, inner ℝ (ξ x) (CERW.Support.Law.centralDiff
        (fun z => (latticeKernel d (z - y) -
          (if d = 2 then (2 / Real.pi) * Real.log R else 0)) ^ 2) x)| ≤
      Λ * G * ∑ x ∈ S, (if d = 2 then
        (1 + euclidNorm (x - y))⁻¹ *
          (1 + |Real.log ((1 + euclidNorm (x - y)) / R)|)
        else (1 + euclidNorm (x - y)) ^ ((3 : ℝ) - 2 * d)) := by
    calc
      _ ≤ ∑ x ∈ S, |inner ℝ (ξ x) (CERW.Support.Law.centralDiff
          (fun z => (latticeKernel d (z - y) -
            (if d = 2 then (2 / Real.pi) * Real.log R else 0)) ^ 2) x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ S, Λ * (G * (if d = 2 then
          (1 + euclidNorm (x - y))⁻¹ *
            (1 + |Real.log ((1 + euclidNorm (x - y)) / R)|)
          else (1 + euclidNorm (x - y)) ^ ((3 : ℝ) - 2 * d))) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [centralDiff_translate
          (fun z => (latticeKernel d z -
            (if d = 2 then (2 / Real.pi) * Real.log R else 0)) ^ 2) x y]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (hξ x) (hg R hR (x - y)) (norm_nonneg _) hΛ)
      _ = _ := by simp only [← mul_assoc, ← Finset.mul_sum]
  by_cases hd2 : d = 2
  · subst d
    obtain ⟨P, hP, hp⟩ := exists_sum_planar_envelope_le A hA
    refine ⟨Λ * G * P + 1, by positivity, ?_⟩
    intro R hR X n hn hX hcard ξ hξ y hy
    have hs := hsum R hR (departureRange X n) ξ hξ y
    simp only [if_true] at hs ⊢
    calc
      _ ≤ Λ * G * _ := hs
      _ ≤ Λ * G * (P * R) :=
        mul_le_mul_of_nonneg_left (hp R hR _ y hcard) (by positivity)
      _ ≤ (Λ * G * P + 1) * R := by nlinarith
  · obtain ⟨B, hB, hb⟩ :=
      CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) (by omega)
    refine ⟨2 * (Λ * G * B) + 1, by positivity, ?_⟩
    intro R hR X n hn hX hcard ξ hξ y hy
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hball : ∀ x ∈ departureRange X n, euclidNorm (x - y) ≤ 4 * (n : ℝ) := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hj' := hX j (Finset.mem_range.mp hj)
      exact (CERW.Support.Occupation.euclidNorm_sub_le _ _).trans (by linarith)
    have hs := hsum R hR (departureRange X n) ξ hξ y
    simp only [if_neg hd2] at hs ⊢
    have hexp : (3 : ℝ) - 2 * d ≤ -(d : ℝ) := by
      have : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
      linarith
    have hweight :
        ∑ x ∈ departureRange X n,
          (1 + euclidNorm (x - y)) ^ ((3 : ℝ) - 2 * d) ≤
          B * Real.log (4 * (n : ℝ) + 2) := by
      refine (Finset.sum_le_sum fun x _ =>
        Real.rpow_le_rpow_of_exponent_le (by linarith [euclidNorm_nonneg (x - y)])
          hexp).trans (hb _ y (4 * (n : ℝ)) (by linarith) hball)
    have hlog : Real.log (4 * (n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) := by
      calc
        _ ≤ Real.log (((n : ℝ) + 2) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
        _ = _ := by rw [Real.log_pow]; norm_num
    have hlogpos : 0 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    calc
      _ ≤ Λ * G * _ := hs
      _ ≤ Λ * G * (B * Real.log (4 * (n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hweight (by positivity)
      _ ≤ Λ * G * (B * (2 * Real.log ((n : ℝ) + 2))) := by gcongr
      _ ≤ (2 * (Λ * G * B) + 1) * Real.log ((n : ℝ) + 2) := by nlinarith

end CERW.LimitShapes.Energy
