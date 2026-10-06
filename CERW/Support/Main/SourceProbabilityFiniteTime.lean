import CERW.Support.Lower.SourceProbabilityConsequences

/-!
# The planar width bound for every `n ≥ 2`

`SourceProbabilityConsequences.planar_width_fluctuation_bound` proves, in the plane, that for every
`p > 0` there is `C > 0` such that for every `n ≥ 3`, with probability at least `1 - C n^{-p}`,
`R_out(n) - R_in(n) ≤ C √r_n (log n)^{5/2}`. The estimate of `thm:fluctuations` (line 131) from
which it is derived, and the standing convention at line 308 ("All estimates concern integers
`n ≥ 2`"), concern every `n ≥ 2`.

`planar_width_fluctuation_bound_all` is the same statement, with every other binder, quantifier and
constant ordering unchanged, for every `n ≥ 2`. Given the constant `C₃` of the theorem for `n ≥ 3`,
the constant is `C = max(C₃, 2^p) > 0`, selected after `p` and before the realization, the law, the
walk and `n`. For `n ≥ 3` the factor `√r_n (log n)^{5/2}` is nonnegative, so the event on which the
width exceeds `C √r_n (log n)^{5/2}` lies in the corresponding event for `C₃`, and the right side
`C n^{-p}` is at least `C₃ n^{-p}`. For `n = 2` the probability is at most `1` and
`C 2^{-p} ≥ 1`. No cutoff depends on the law, and nothing is assumed.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Main.SourceProbabilityFiniteTime

/-- **In the plane, with high probability, `R_out(n) - R_in(n) ≤ C √r_n (log n)^{5/2}`, for every
`n ≥ 2`** (line 194, from `thm:fluctuations` (i), line 131; line 308). For every `p > 0` there is
`C > 0`, chosen before the realization, the law, the walk and `n`, such that for every `n ≥ 2`, with
probability at least `1 - C n^{-p}`, the width is at most `C √r_n (log n)^{5/2}`. -/
theorem planar_width_fluctuation_bound_all {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n ≤
            C * (Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)))} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  subst hd
  intro ωd ε hε hεd r p hp
  obtain ⟨C₃, hC₃, h3⟩ :=
    CERW.Support.Lower.SourceProbabilityConsequences.planar_width_fluctuation_bound.{u}
      (d := 2) rfl ε hε hεd p hp
  refine ⟨max C₃ (2 ^ p), lt_max_of_lt_left hC₃, fun {Ω} _ μ _ X hX n hn2 => ?_⟩
  by_cases hn3 : 3 ≤ n
  · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hS : 0 ≤ Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
    refine le_trans (measure_mono ?_) ((h3 μ X hX n hn3).trans (ENNReal.ofReal_le_ofReal ?_))
    · intro ω hω hle
      exact hω (hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hS))
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · have hn : n = 2 := by omega
    subst hn
    refine le_trans prob_le_one ?_
    rw [ENNReal.one_le_ofReal]
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    have h2p : (0 : ℝ) < 2 ^ p := Real.rpow_pos_of_pos two_pos p
    rw [h2, Real.rpow_neg two_pos.le]
    calc (1 : ℝ) = 2 ^ p * ((2 : ℝ) ^ p)⁻¹ := (mul_inv_cancel₀ h2p.ne').symm
      _ ≤ max C₃ (2 ^ p) * ((2 : ℝ) ^ p)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.2 h2p.le)

end CERW.Support.Main.SourceProbabilityFiniteTime
