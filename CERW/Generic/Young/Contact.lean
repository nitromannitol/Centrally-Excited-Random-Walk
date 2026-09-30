import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Absorbing the excess volume in the contact inequality

In dimension `d ≥ 3` the contact inequality reads `m ≤ c N^{d-1} (m^{1/(2d)} √L + L)`
(`fluctuations.tex`, before `eq:masshigh`). Either the second term dominates and
`m ≤ 2c N^{d-1} L`, or raising `m^{1-1/(2d)} ≤ 2c N^{d-1} √L` to the power `2d/(2d-1)` gives
`m ≤ C N^{2d(d-1)/(2d-1)} L^{d/(2d-1)}`.
-/

namespace CERW.Generic.Young

/-- `(1 - 1/(2d)) * (2d/(2d-1)) = 1` for real `d ≥ 1`. -/
lemma one_sub_inv_mul_ratio (d : ℕ) (hd : 1 ≤ d) :
    (1 - 1 / (2 * (d : ℝ))) * (2 * (d : ℝ) / (2 * (d : ℝ) - 1)) = 1 := by
  have h : (0 : ℝ) < 2 * (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  field_simp

/-- `(↑d - 1) * (2↑d/(2↑d-1)) = 2↑d(↑d-1)/(2↑d-1)` for `d ≥ 1`. -/
lemma sub_one_mul_ratio (d : ℕ) (hd : 1 ≤ d) :
    ((d : ℝ) - 1) * (2 * (d : ℝ) / (2 * (d : ℝ) - 1))
      = (2 * (d : ℝ) * ((d : ℝ) - 1)) / (2 * (d : ℝ) - 1) := by
  have h : (0 : ℝ) < 2 * (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  field_simp

/-- `(1/2) * (2↑d/(2↑d-1)) = ↑d/(2↑d-1)` for `d ≥ 1`. -/
lemma half_mul_ratio (d : ℕ) (hd : 1 ≤ d) :
    (1 / 2) * (2 * (d : ℝ) / (2 * (d : ℝ) - 1)) = (d : ℝ) / (2 * (d : ℝ) - 1) := by
  have h : (0 : ℝ) < 2 * (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  field_simp

/-- The absorption behind `eq:masshigh`: `m ≤ c N^{d-1}(m^{1/(2d)} √L + L)` with
`m, N, L ≥ 0` forces `m ≤ C (N^{2d(d-1)/(2d-1)} L^{d/(2d-1)} + N^{d-1} L)`. -/
theorem le_of_le_mul_rpow_mul_sqrt_add {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ m N L : ℝ, 0 ≤ m → 0 ≤ N → 0 ≤ L →
      m ≤ c * N ^ ((d : ℝ) - 1) * (m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L + L) →
        m ≤ C * (N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1)) * L ^ ((d : ℝ) / (2 * d - 1))
          + N ^ ((d : ℝ) - 1) * L) := by
  have hD1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * (d : ℝ) - 1 := by linarith
  have hnum : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  let g : ℝ := 2 * (d : ℝ) / (2 * (d : ℝ) - 1)
  have hgpos : 0 < g := by
    dsimp only [g]
    exact div_pos hnum hden
  have h1 : (1 - 1 / (2 * (d : ℝ))) * g = 1 := one_sub_inv_mul_ratio d hd
  have h2 : ((d : ℝ) - 1) * g = (2 * (d : ℝ) * ((d : ℝ) - 1)) / (2 * (d : ℝ) - 1) :=
    sub_one_mul_ratio d hd
  have h3 : (1 / 2) * g = (d : ℝ) / (2 * (d : ℝ) - 1) := half_mul_ratio d hd
  refine ⟨(2 * c) ^ g + 2 * c, ?_, ?_⟩
  · have h1p : (0 : ℝ) < (2 * c) ^ g := Real.rpow_pos_of_pos (by linarith) _
    linarith
  · intro m N L hm hN hL hmain
    have hcoef : (0 : ℝ) ≤ c * N ^ ((d : ℝ) - 1) := by positivity
    by_cases hle : m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L ≤ L
    · have h2L : m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L + L ≤ 2 * L := by linarith
      have hb : m ≤ 2 * c * N ^ ((d : ℝ) - 1) * L := by
        calc m ≤ c * N ^ ((d : ℝ) - 1)
              * (m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L + L) := hmain
          _ ≤ c * N ^ ((d : ℝ) - 1) * (2 * L) := mul_le_mul_of_nonneg_left h2L hcoef
          _ = 2 * c * N ^ ((d : ℝ) - 1) * L := by ring
      have hbase : 2 * c ≤ (2 * c) ^ g + 2 * c := by
        have : (0 : ℝ) ≤ (2 * c) ^ g := Real.rpow_nonneg (by linarith) _
        linarith
      have habs : 2 * c * N ^ ((d : ℝ) - 1) ≤ ((2 * c) ^ g + 2 * c) * N ^ ((d : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hN _)
      calc m ≤ 2 * c * N ^ ((d : ℝ) - 1) * L := hb
        _ ≤ ((2 * c) ^ g + 2 * c) * N ^ ((d : ℝ) - 1) * L :=
              mul_le_mul_of_nonneg_right habs hL
        _ = ((2 * c) ^ g + 2 * c) * (N ^ ((d : ℝ) - 1) * L) := by ring
        _ ≤ ((2 * c) ^ g + 2 * c)
              * (N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1)) * L ^ ((d : ℝ) / (2 * d - 1))
                + N ^ ((d : ℝ) - 1) * L) := by
              have hle2 : N ^ ((d : ℝ) - 1) * L
                    ≤ N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1))
                        * L ^ ((d : ℝ) / (2 * d - 1))
                      + N ^ ((d : ℝ) - 1) * L :=
                le_add_of_nonneg_left (by positivity)
              exact mul_le_mul_of_nonneg_left hle2 (by positivity)
    · have hlt : L < m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L := not_le.mp hle
      have h2m : m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L + L
            ≤ 2 * (m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L) := by linarith
      have hb : m ≤ 2 * (c * N ^ ((d : ℝ) - 1))
            * (m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L) := by
        calc m ≤ c * N ^ ((d : ℝ) - 1)
              * (m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L + L) := hmain
          _ ≤ c * N ^ ((d : ℝ) - 1)
              * (2 * (m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L)) :=
                mul_le_mul_of_nonneg_left h2m hcoef
          _ = 2 * (c * N ^ ((d : ℝ) - 1))
              * (m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L) := by ring
      by_cases hm0 : m = 0
      · subst hm0
        positivity
      · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
        have hapos : 0 < m ^ ((1 : ℝ) / (2 * d)) := Real.rpow_pos_of_pos hmpos _
        have hdiv : m / m ^ ((1 : ℝ) / (2 * d))
              ≤ 2 * (c * N ^ ((d : ℝ) - 1)) * Real.sqrt L := by
          rw [div_le_iff₀ hapos]
          calc m ≤ 2 * (c * N ^ ((d : ℝ) - 1))
                * (m ^ ((1 : ℝ) / (2 * d)) * Real.sqrt L) := hb
            _ = (2 * (c * N ^ ((d : ℝ) - 1)) * Real.sqrt L)
                * m ^ ((1 : ℝ) / (2 * d)) := by ring
        have hmroot : m ^ (1 - 1 / (2 * (d : ℝ)))
              ≤ 2 * (c * N ^ ((d : ℝ) - 1)) * Real.sqrt L := by
          rw [Real.rpow_sub hmpos 1 (1 / (2 * (d : ℝ))), Real.rpow_one]
          exact hdiv
        have hpow : (m ^ (1 - 1 / (2 * (d : ℝ)))) ^ g
              ≤ (2 * (c * N ^ ((d : ℝ) - 1)) * Real.sqrt L) ^ g :=
          Real.rpow_le_rpow (Real.rpow_nonneg hm _) hmroot (le_of_lt hgpos)
        have hLHS : (m ^ (1 - 1 / (2 * (d : ℝ)))) ^ g = m := by
          rw [← Real.rpow_mul hm (1 - 1 / (2 * (d : ℝ))) g, h1, Real.rpow_one]
        have hRHS : (2 * (c * N ^ ((d : ℝ) - 1)) * Real.sqrt L) ^ g
              = (2 * c) ^ g
                * (N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1))
                  * L ^ ((d : ℝ) / (2 * d - 1))) := by
          have hfac : 2 * (c * N ^ ((d : ℝ) - 1)) * Real.sqrt L
              = (2 * c) * (N ^ ((d : ℝ) - 1) * Real.sqrt L) := by ring
          rw [hfac,
            Real.mul_rpow (by linarith : (0 : ℝ) ≤ 2 * c)
              (mul_nonneg (Real.rpow_nonneg hN _) (Real.sqrt_nonneg L))]
          rw [Real.mul_rpow (Real.rpow_nonneg hN _) (Real.sqrt_nonneg L)]
          rw [← Real.rpow_mul hN, Real.sqrt_eq_rpow L, ← Real.rpow_mul hL]
          rw [h2, h3]
        have hfinal : m ≤ (2 * c) ^ g
              * (N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1))
                * L ^ ((d : ℝ) / (2 * d - 1))) := by
          rw [← hLHS, ← hRHS]
          exact hpow
        have hbnd : (2 * c) ^ g ≤ (2 * c) ^ g + 2 * c := by
          have : (0 : ℝ) ≤ (2 * c) ^ g := Real.rpow_nonneg (by linarith) _
          linarith
        calc m ≤ (2 * c) ^ g
              * (N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1))
                * L ^ ((d : ℝ) / (2 * d - 1))) := hfinal
          _ ≤ ((2 * c) ^ g + 2 * c)
              * (N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1))
                * L ^ ((d : ℝ) / (2 * d - 1))) :=
                mul_le_mul_of_nonneg_right hbnd (by positivity)
          _ ≤ ((2 * c) ^ g + 2 * c)
              * (N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1)) * L ^ ((d : ℝ) / (2 * d - 1))
                + N ^ ((d : ℝ) - 1) * L) := by
              have hle2 :
                    N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1))
                        * L ^ ((d : ℝ) / (2 * d - 1))
                      ≤ N ^ ((2 * d * ((d : ℝ) - 1)) / (2 * d - 1))
                          * L ^ ((d : ℝ) / (2 * d - 1))
                        + N ^ ((d : ℝ) - 1) * L :=
                le_add_of_nonneg_right (by positivity)
              exact mul_le_mul_of_nonneg_left hle2 (by positivity)

end CERW.Generic.Young
