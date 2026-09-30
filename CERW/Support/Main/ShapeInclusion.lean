import CERW.Support.Main.GoodEvent
import CERW.Support.Main.ScaleLimits

/-!
# The shape theorem from the fluctuation event: inclusions and profile

If the fluctuation event `fluctGood d ε C Y n` holds for all large `n`, then the rates
`C Q → 0`, `C Q^{1/d} L → 0` and `C Q^{1/d} → 0` give the ball inclusions and the uniform
profile convergence of `thm:shape`.
-/

namespace CERW.Support.Main

open Filter Topology MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- The inclusion and profile clauses of `thm:shape` for a path on which the fluctuation event
holds eventually. -/
theorem sandwich_and_profile_of_good (hd : 2 ≤ d) {ε C : ℝ} {Y : ℕ → Site d}
    (hY : ∀ᶠ n in atTop, fluctGood d ε C Y n) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      {x : Site d | euclidNorm x < (a - η) * N n} ⊆ ↑(departureRange Y n) ∧
      (↑(departureRange Y n) : Set (Site d)) ⊆ ↑(visitedRange Y n) ∧
      (↑(visitedRange Y n) : Set (Site d)) ⊆ {x | euclidNorm x < (a + η) * N n}) ∧
    (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x : Site d,
      |(localTime Y n x : ℝ) / N n - 2 * d * ε * max (a - euclidNorm x / N n) 0| ≤ η) := by
  dsimp only
  have hQ0 : Tendsto (fun n : ℕ => if d = 2
      then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
      else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
      atTop (𝓝 0) := tendsto_rate_zero hd
  have hQdL0 : Tendsto (fun n : ℕ => (if d = 2
      then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
      else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
      ^ ((1 : ℝ) / d) * Real.log (n + 2)) atTop (𝓝 0) := tendsto_rate_rpow_mul_log_zero hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  constructor
  · intro η hη
    have hCQ : ∀ᶠ n : ℕ in atTop, C * (if d = 2
        then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
        else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
        ≤ η :=
      (hQ0.const_mul C).eventually_le_const (show C * 0 < η by simpa using hη)
    have hQL : ∀ᶠ n : ℕ in atTop, C * (if d = 2
        then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
        else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
        ^ ((1 : ℝ) / d) * Real.log (n + 2) ≤ η := by
      have h := (hQdL0.const_mul C).eventually_le_const (show C * 0 < η by simpa using hη)
      simpa only [mul_assoc] using h
    filter_upwards [hY, hCQ, hQL] with n hn hCQ' hQL'
    dsimp only [fluctGood] at hn
    obtain ⟨h1, h2, h3, -, -⟩ := hn
    have hN : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    refine ⟨?_, h2, ?_⟩
    · intro x hx
      exact h1 (lt_of_lt_of_le hx (mul_le_mul_of_nonneg_right (by linarith) hN))
    · intro x hx
      exact lt_of_lt_of_le (h3 hx) (mul_le_mul_of_nonneg_right (by linarith) hN)
  · intro η hη
    have hp : (0 : ℝ) < (1 : ℝ) / d := div_pos zero_lt_one hdpos
    have hQpow0 : Tendsto (fun n : ℕ => (if d = 2
        then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
        else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
        ^ ((1 : ℝ) / d)) atTop (𝓝 0) := by
      have h := hQ0.rpow_const (Or.inr hp.le)
      rwa [Real.zero_rpow hp.ne'] at h
    have hCQpow : ∀ᶠ n : ℕ in atTop, C * (if d = 2
        then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
        else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
        ^ ((1 : ℝ) / d) ≤ η :=
      (hQpow0.const_mul C).eventually_le_const (show C * 0 < η by simpa using hη)
    filter_upwards [hY, hCQpow] with n hn hCQpow'
    dsimp only [fluctGood] at hn
    obtain ⟨-, -, -, -, h5⟩ := hn
    intro x
    exact le_trans (h5 x) hCQpow'

end CERW.Support.Main
