import CERW.Support.Main.GoodEvent

/-!
# Monotonicity of the fluctuation event

Every clause of `fluctGood d ε C Y n` weakens as `C` grows, since `N`, `L` and `Q` are
nonnegative.
-/

namespace CERW.Support.Main

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- `fluctGood` is monotone in its constant. -/
theorem fluctGood_mono {ε C C' : ℝ} (hCC' : C ≤ C') {Y : ℕ → Site d} {n : ℕ}
    (hG : fluctGood d ε C Y n) : fluctGood d ε C' Y n := by
  have hN : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hL : (0 : ℝ) ≤ Real.log (n + 2) :=
    Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hQ : (0 : ℝ) ≤ if d = 2
      then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
      else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)) := by
    split_ifs <;> exact Real.rpow_nonneg (div_nonneg hL hN) _
  obtain ⟨hin, hAV, hout, hvol, hprof⟩ := hG
  refine ⟨fun x hx => hin ?_, hAV, fun x hx => ?_, hvol.trans ?_, fun x => (hprof x).trans ?_⟩
  · simp only [Set.mem_setOf_eq] at hx ⊢
    exact lt_of_lt_of_le hx (by gcongr)
  · have := hout hx
    simp only [Set.mem_setOf_eq] at this ⊢
    refine lt_of_lt_of_le this ?_
    have := Real.rpow_nonneg hQ ((1 : ℝ) / d)
    gcongr
  · exact ENNReal.ofReal_le_ofReal (by gcongr)
  · have := Real.rpow_nonneg hQ ((1 : ℝ) / d)
    gcongr

end CERW.Support.Main
