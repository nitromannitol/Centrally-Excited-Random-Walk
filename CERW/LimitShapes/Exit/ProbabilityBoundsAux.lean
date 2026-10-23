import CERW.LimitShapes.Exit.Approximation
import CERW.LimitShapes.Exit.Crossing
import CERW.LimitShapes.Exit.Lower

/-!
# Time comparisons for the two-sided exit estimate

These deterministic comparisons connect the upper exit event to the approximation in
Proposition `prop:coarse`.
-/

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory

/-- The upper exit time has a logarithm bounded by a fixed multiple of the scale logarithm. -/
theorem exit_time_log_bound {d n : ℕ} {R B : ℝ} (hR : 2 ≤ R) (hBR : B + 2 ≤ R)
    (ht : (n : ℝ) ≤ B * R ^ (d + 1)) :
    Real.log ((n : ℝ) + 2) ≤ (d + 2 : ℝ) * Real.log R := by
  have hR1 : 1 ≤ R := by linarith
  have hp : 1 ≤ R ^ (d + 1) := one_le_pow₀ hR1
  have he : (n : ℝ) + 2 ≤ R ^ (d + 2) := by
    calc (n : ℝ) + 2 ≤ B * R ^ (d + 1) + 2 := by linarith
      _ ≤ R * R ^ (d + 1) := by nlinarith
      _ = R ^ (d + 2) := by rw [pow_succ]; ring
  have hh := Real.log_le_log (by positivity : 0 < (n : ℝ) + 2) he
  simpa only [Real.log_pow, Nat.cast_add, Nat.cast_ofNat] using hh

/-- Legal paths exiting a sufficiently large norm ball exceed the fixed time thresholds. -/
theorem exit_time_large {d : ℕ} (hd : 1 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ)
    {X : ℕ → Site d} (hX : CERW.Support.Norm.ContactEvent.PathTyping d X)
    {R : ℝ} {n : ℕ} (hR : normMax Ψ * (3 + Real.sqrt d) ≤ R)
    (hex : R ≤ Ψ (toSpace (X n))) : 3 ≤ n ∧ Real.sqrt d ≤ (n : ℝ) := by
  have hΛ : 0 < normMax Ψ :=
    (Generic.Norm.normMin_pos_mul_le hΨ hd).1.trans_le
      (CERW.Support.Norm.ContactAssembly.normMin_le_normMax hd hΨ)
  have hh := Generic.Norm.le_normMax_mul hΨ (toSpace (X n))
  rw [norm_toSpace] at hh
  have ht := CERW.Support.Occupation.euclidNorm_le_of_steps X hX.1 hX.2 n
  have he := mul_le_mul_of_nonneg_left ht hΛ.le
  have hn : 3 + Real.sqrt d ≤ (n : ℝ) := by nlinarith only [hR, hex, hh, he, hΛ]
  constructor
  · exact_mod_cast (show (3 : ℝ) ≤ n by linarith [Real.sqrt_nonneg (d : ℝ)])
  · linarith

end CERW.LimitShapes.Exit
