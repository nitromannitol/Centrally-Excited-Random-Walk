import CERW.Generic.Martingale.Arith
import CERW.Generic.Martingale.Shift

/-!
# Freedman's inequality at a logarithmic threshold, uniformly in the bracket

The paper applies Freedman's inequality with the threshold `C(√(vL) + BL)` at every dyadic
value `v = 2^j` of the bracket (the dyadic bounds behind `eq:interval-mart`, `eq:localmart`,
`eq:radialmart`, `eq:vector` and `eq:quadraticerror`). If the bracket increment over `[s, s+k]`
never exceeds `W ≥ 1`, then
`|M_{s+k} - M_s| ≤ c (√(max(V_{s+k} - V_s, 1) L) + bL)` fails with probability at most
`(⌈log₂ W⌉ + 1) · 2e^{-KL}`. The constant `c` depends only on `K`.
-/

namespace CERW.Generic.Martingale

open MeasureTheory ProbabilityTheory

/-- The dyadic Freedman bound: for `K ≥ 0` there is `c ≥ 1` such that, for every martingale with
increments at most `b` on `[s, s+k]` and every predictable bracket whose increment over `[s, s+k]`
is at most `W ≥ 1`, the bound `|M_{s+k} - M_s| ≤ c (√(max(V_{s+k} - V_s, 1) L) + bL)` fails with
probability at most `(⌈log₂ W⌉ + 1) · 2e^{-KL}`. -/
theorem exists_dyadic_bound {K : ℝ} (hK : 0 ≤ K) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
      [IsProbabilityMeasure P] {ℱ : Filtration ℕ m0} {M V : ℕ → Ω → ℝ},
      Martingale M ℱ P → (∀ j, StronglyMeasurable[ℱ j] (V (j + 1))) → (∀ ω, V 0 ω = 0) →
      (∀ j ω, V j ω ≤ V (j + 1) ω) →
      (∀ j, P[fun ω => (M (j + 1) ω - M j ω) ^ 2 | ℱ j] ≤ᵐ[P]
        fun ω => V (j + 1) ω - V j ω) →
      ∀ {b : ℝ}, 0 < b → ∀ s k : ℕ,
      (∀ i, s ≤ i → i < s + k → ∀ ω, |M (i + 1) ω - M i ω| ≤ b) →
      ∀ {W L : ℝ}, 1 ≤ W → 0 < L → (∀ ω, V (s + k) ω - V s ω ≤ W) →
        P {ω | c * (Real.sqrt (max (V (s + k) ω - V s ω) 1 * L) + b * L) <
            |M (s + k) ω - M s ω|} ≤
          ENNReal.ofReal ((Nat.clog 2 ⌈W⌉₊ + 1) * (2 * Real.exp (-(K * L)))) := by
  obtain ⟨cA, hcA1, hcA⟩ := le_freedman_exponent hK
  refine ⟨Real.sqrt 2 * cA, ?_, ?_⟩
  · have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [hcA1, hsqrt2, Real.sqrt_nonneg 2]
  · intro Ω m0 P hP ℱ M V hmart hVpred hV0 hVmono hVdom b hb s k hinc W L hW hL hVW
    haveI := hP
    set m : ℕ := Nat.clog 2 ⌈W⌉₊ with hm
    set t : ℕ → ℝ := fun j => cA * (Real.sqrt ((2 : ℝ) ^ j * L) + b * L) with ht
    set S : ℕ → Set Ω := fun j =>
      {ω | t j ≤ |M (s + k) ω - M s ω| ∧ V (s + k) ω - V s ω ≤ (2 : ℝ) ^ j} with hS
    set B : Set Ω := {ω | Real.sqrt 2 * cA *
      (Real.sqrt (max (V (s + k) ω - V s ω) 1 * L) + b * L) <
        |M (s + k) ω - M s ω|} with hB
    have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsub : B ⊆ ⋃ j ∈ Finset.range (m + 1), S j := by
      intro ω hω
      rw [hB] at hω
      have hm_pow : max (V (s + k) ω - V s ω) 1 ≤ (2 : ℝ) ^ m := by
        have h2 : max (V (s + k) ω - V s ω) 1 ≤ W := max_le (hVW ω) hW
        have h3 : W ≤ (⌈W⌉₊ : ℝ) := Nat.le_ceil W
        have h4 : (⌈W⌉₊ : ℝ) ≤ (2 : ℝ) ^ m := by
          have h := Nat.le_pow_clog (b := 2) (by norm_num : 1 < 2) ⌈W⌉₊
          rw [hm]
          calc (⌈W⌉₊ : ℝ) ≤ ((2 ^ Nat.clog 2 ⌈W⌉₊ : ℕ) : ℝ) := by
                exact_mod_cast h
            _ = (2 : ℝ) ^ Nat.clog 2 ⌈W⌉₊ := by rw [Nat.cast_pow]; norm_num
        linarith
      have Hex : ∃ n, max (V (s + k) ω - V s ω) 1 ≤ (2 : ℝ) ^ n := ⟨m, hm_pow⟩
      set j : ℕ := Nat.find Hex with hj_def
      have hj_spec : max (V (s + k) ω - V s ω) 1 ≤ (2 : ℝ) ^ j := by
        rw [hj_def]; exact Nat.find_spec Hex
      have hj_le : j ≤ m := by
        rw [hj_def]; exact Nat.find_min' Hex hm_pow
      have hVj : V (s + k) ω - V s ω ≤ (2 : ℝ) ^ j :=
        le_trans (le_max_left _ _) hj_spec
      refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj_le), ?_⟩⟩
      refine ⟨?_, hVj⟩
      have hbad : Real.sqrt 2 * cA *
          (Real.sqrt (max (V (s + k) ω - V s ω) 1 * L) + b * L) <
            |M (s + k) ω - M s ω| := hω
      by_cases hj0 : j = 0
      · rw [hj0] at hj_spec ⊢
        have hmax1 : max (V (s + k) ω - V s ω) 1 = 1 := by
          refine le_antisymm ?_ (le_max_right _ _)
          simpa using hj_spec
        have hbL : 0 ≤ b * L := mul_nonneg hb.le hL.le
        have hbase : 0 ≤ cA * (Real.sqrt L + b * L) :=
          mul_nonneg (by linarith) (add_nonneg (Real.sqrt_nonneg _) hbL)
        have htCD : t 0 ≤ Real.sqrt 2 * cA *
            (Real.sqrt (max (V (s + k) ω - V s ω) 1 * L) + b * L) := by
          calc t 0 = cA * (Real.sqrt L + b * L) := by simp only [ht, pow_zero, one_mul]
            _ ≤ Real.sqrt 2 * (cA * (Real.sqrt L + b * L)) := by
                simpa using mul_le_mul_of_nonneg_right hsqrt2 hbase
            _ = Real.sqrt 2 * cA *
                (Real.sqrt (max (V (s + k) ω - V s ω) 1 * L) + b * L) := by
                rw [hmax1, one_mul]; ring
        exact le_of_lt (lt_of_le_of_lt htCD hbad)
      · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        have hmin : ¬ max (V (s + k) ω - V s ω) 1 ≤ (2 : ℝ) ^ (j - 1) :=
          Nat.find_min Hex (by omega)
        have h2j : (2 : ℝ) ^ j < 2 * max (V (s + k) ω - V s ω) 1 := by
          have hlt : (2 : ℝ) ^ (j - 1) < max (V (s + k) ω - V s ω) 1 := not_le.mp hmin
          have hsucc : j - 1 + 1 = j := Nat.sub_add_cancel hjpos
          calc (2 : ℝ) ^ j = (2 : ℝ) ^ (j - 1 + 1) := by rw [hsucc]
            _ = (2 : ℝ) ^ (j - 1) * 2 := pow_succ _ _
            _ < max (V (s + k) ω - V s ω) 1 * 2 :=
                mul_lt_mul_of_pos_right hlt (by norm_num)
            _ = 2 * max (V (s + k) ω - V s ω) 1 := by ring
        have hsqrt_le : Real.sqrt ((2 : ℝ) ^ j * L) ≤
            Real.sqrt 2 * Real.sqrt (max (V (s + k) ω - V s ω) 1 * L) := by
          have hle : (2 : ℝ) ^ j * L ≤ 2 * (max (V (s + k) ω - V s ω) 1 * L) := by
            have := mul_lt_mul_of_pos_right h2j hL
            linarith
          calc Real.sqrt ((2 : ℝ) ^ j * L)
              ≤ Real.sqrt (2 * (max (V (s + k) ω - V s ω) 1 * L)) :=
                Real.sqrt_le_sqrt hle
            _ = Real.sqrt 2 * Real.sqrt (max (V (s + k) ω - V s ω) 1 * L) :=
                Real.sqrt_mul (by norm_num) _
        have hbL : 0 ≤ b * L := mul_nonneg hb.le hL.le
        have hbL_le : b * L ≤ Real.sqrt 2 * (b * L) := by
          simpa using mul_le_mul_of_nonneg_right hsqrt2 hbL
        have htCD : t j ≤ Real.sqrt 2 * cA *
            (Real.sqrt (max (V (s + k) ω - V s ω) 1 * L) + b * L) := by
          calc t j = cA * (Real.sqrt ((2 : ℝ) ^ j * L) + b * L) := by simp only [ht]
            _ ≤ cA * (Real.sqrt 2 * Real.sqrt (max (V (s + k) ω - V s ω) 1 * L)
                  + b * L) :=
                mul_le_mul_of_nonneg_left (add_le_add_left hsqrt_le (b * L))
                  (by linarith)
            _ ≤ cA * (Real.sqrt 2 * Real.sqrt (max (V (s + k) ω - V s ω) 1 * L)
                  + Real.sqrt 2 * (b * L)) :=
                mul_le_mul_of_nonneg_left
                  (add_le_add_right hbL_le (Real.sqrt 2 * Real.sqrt
                    (max (V (s + k) ω - V s ω) 1 * L))) (by linarith)
            _ = Real.sqrt 2 * cA *
                (Real.sqrt (max (V (s + k) ω - V s ω) 1 * L) + b * L) := by ring
        exact le_of_lt (lt_of_le_of_lt htCD hbad)
    have hlevel : ∀ j, P (S j) ≤ ENNReal.ofReal (2 * Real.exp (-(K * L))) := by
      intro j
      have ht_nonneg : 0 ≤ t j := by
        simp only [ht]
        exact mul_nonneg (by linarith)
          (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hb.le hL.le))
      have hv : 0 ≤ (2 : ℝ) ^ j := pow_nonneg (by norm_num) j
      have hbase := measure_le_abs_sub_and_le (P := P) hmart hVpred hV0 hVmono hVdom hb s k
        hinc (v := (2 : ℝ) ^ j) (t := t j) hv ht_nonneg
      have hbaseS : P (S j) ≤ ENNReal.ofReal (2 * Real.exp
          (-(t j ^ 2 / (2 * ((2 : ℝ) ^ j + b * t j / 3))))) := by
        simpa only [hS] using hbase
      have harith : K * L ≤ t j ^ 2 / (2 * ((2 : ℝ) ^ j + b * t j)) := by
        have := hcA ((2 : ℝ) ^ j) b L hv hb hL
        simpa only [ht] using this
      have hExp : K * L ≤ t j ^ 2 / (2 * ((2 : ℝ) ^ j + b * t j / 3)) := by
        have hden_small_pos : 0 < 2 * ((2 : ℝ) ^ j + b * t j / 3) := by
          have h2j : 0 < (2 : ℝ) ^ j := pow_pos (by norm_num) j
          have hbt : 0 ≤ b * t j / 3 :=
            div_nonneg (mul_nonneg hb.le ht_nonneg) (by norm_num)
          linarith
        have hden_le : 2 * ((2 : ℝ) ^ j + b * t j / 3) ≤
            2 * ((2 : ℝ) ^ j + b * t j) := by
          have hbt3 : b * t j / 3 ≤ b * t j := by
            rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
            nlinarith [mul_nonneg hb.le ht_nonneg]
          linarith
        exact le_trans harith
          (div_le_div_of_nonneg_left (sq_nonneg (t j)) hden_small_pos hden_le)
      have hexp : Real.exp (-(t j ^ 2 / (2 * ((2 : ℝ) ^ j + b * t j / 3)))) ≤
          Real.exp (-(K * L)) := Real.exp_le_exp.mpr (by linarith)
      calc P (S j) ≤ ENNReal.ofReal (2 * Real.exp
            (-(t j ^ 2 / (2 * ((2 : ℝ) ^ j + b * t j / 3))))) := hbaseS
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(K * L))) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp (by norm_num))
    calc P B ≤ P (⋃ j ∈ Finset.range (m + 1), S j) := measure_mono hsub
      _ ≤ ∑ j ∈ Finset.range (m + 1), P (S j) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ Finset.range (m + 1), ENNReal.ofReal (2 * Real.exp (-(K * L))) := by
            apply Finset.sum_le_sum
            intro j hj
            exact hlevel j
      _ = (Finset.range (m + 1)).card • ENNReal.ofReal (2 * Real.exp (-(K * L))) := by
            rw [Finset.sum_const]
      _ = ENNReal.ofReal (((m : ℝ) + 1) * (2 * Real.exp (-(K * L)))) := by
            rw [Finset.card_range, nsmul_eq_mul]
            rw [show ((m + 1 : ℕ) : ENNReal) = ENNReal.ofReal ((m : ℝ) + 1) by
              rw [← ENNReal.ofReal_natCast]
              congr 1
              push_cast
              ring]
            rw [← ENNReal.ofReal_mul (by positivity)]

end CERW.Generic.Martingale
