import CERW.Generic.Young.Radius
import CERW.Model.Potential

/-!
# The inradius from the elapsed time

`eq:inradius`, arithmetically. Divide `eq:quadratic`, `|X_n|² = n - 2ε Σ_{x ∈ A_n} |x| + 𝒬_n`, by
`n = N^{d+1}`. Insert the cell replacement `|Σ|x| - ∫_D|v|| ≤ C N^d` and the ball split
`∫_D |v| = (d ω_d/(d+1)) b^{d+1} + ∫_E |v|`. With `|X_n|² ≤ C N²`, `0 ≤ ∫_E |v| ≤ C N^{d+1} Q`,
`|𝒬_n| ≤ C N^{d+1} Q`, `N^{1-d} ≤ Q` and `N^{-1} ≤ Q`, this gives
`|1 - (2dε ω_d/(d+1)) (b/N)^{d+1}| ≤ C Q`. Radius inversion then gives `|b/N - a| ≤ C' Q`, with
`a = ((d+1)/(2dε ω_d))^{1/(d+1)}`.
-/

namespace CERW.Support.Contact

open CERW

variable {d : ℕ}

/-- `N^2 / N^(d+1) = N^(1-d)` for positive `N`. -/
private lemma sq_div_pow_eq_rpow {N : ℝ} (hN : 0 < N) :
    N ^ 2 / N ^ (d + 1) = N ^ (1 - (d : ℝ)) := by
  have h2 : N ^ 2 = N ^ (2 : ℝ) := (Real.rpow_natCast N 2).symm
  have hd1 : N ^ (d + 1) = N ^ (((d + 1 : ℕ) : ℝ)) :=
    (Real.rpow_natCast N (d + 1)).symm
  calc
    N ^ 2 / N ^ (d + 1) = N ^ (2 : ℝ) / N ^ (((d + 1 : ℕ) : ℝ)) := by
      rw [h2, hd1]
    _ = N ^ (2 : ℝ) * N ^ (-(((d + 1 : ℕ) : ℝ))) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hN.le]
    _ = N ^ ((2 : ℝ) + -(((d + 1 : ℕ) : ℝ))) := by
      rw [← Real.rpow_add hN]
    _ = N ^ (1 - (d : ℝ)) := by
      congr 1
      push_cast
      ring

/-- `N^d / N^(d+1) = N⁻¹` for positive `N`. -/
private lemma pow_div_pow_eq_inv {N : ℝ} (hN : 0 < N) :
    N ^ d / N ^ (d + 1) = N⁻¹ := by
  have hd : N ^ d = N ^ ((d : ℕ) : ℝ) := (Real.rpow_natCast N d).symm
  have hd1 : N ^ (d + 1) = N ^ (((d + 1 : ℕ) : ℝ)) :=
    (Real.rpow_natCast N (d + 1)).symm
  calc
    N ^ d / N ^ (d + 1) = N ^ ((d : ℕ) : ℝ) / N ^ (((d + 1 : ℕ) : ℝ)) := by
      rw [hd, hd1]
    _ = N ^ ((d : ℕ) : ℝ) * N ^ (-(((d + 1 : ℕ) : ℝ))) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hN.le]
    _ = N ^ (((d : ℕ) : ℝ) + -(((d + 1 : ℕ) : ℝ))) := by
      rw [← Real.rpow_add hN]
    _ = N⁻¹ := by
      have hexp : ((d : ℕ) : ℝ) + -(((d + 1 : ℕ) : ℝ)) = -1 := by
        push_cast
        ring
      rw [hexp, Real.rpow_neg_one]

/-- `eq:inradius`, from the quadratic identity and the displayed bounds on its terms. -/
theorem exists_abs_div_sub_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (b S I IE Qn Xsq Q : ℝ), 1 ≤ n → 0 ≤ b → 0 ≤ Q →
      Xsq = n - 2 * ε * S + Qn → 0 ≤ Xsq → Xsq ≤ C₁ * ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ 2 →
      |S - I| ≤ C₁ * ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d →
      I = d * unitBallVolume d * b ^ (d + 1) / (d + 1) + IE → 0 ≤ IE →
      IE ≤ C₁ * n * Q → |Qn| ≤ C₁ * n * Q →
      ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ (1 - (d : ℝ)) ≤ Q →
      ((n : ℝ) ^ ((1 : ℝ) / (d + 1)))⁻¹ ≤ Q →
        |b / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) -
            ((d + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))| ≤ C * Q := by
  let ω : ℝ := unitBallVolume d
  have hωdef : ω = unitBallVolume d := rfl
  have hωpos : 0 < ω := by rw [hωdef]; exact unitBallVolume_pos d
  let a : ℝ := ((d + 1) / (2 * d * ε * ω)) ^ ((1 : ℝ) / (d + 1))
  have hadef : a = ((d + 1) / (2 * d * ε * ω)) ^ ((1 : ℝ) / (d + 1)) := rfl
  refine ⟨a * (2 * C₁ + 4 * ε * C₁) + 1, ?hCpos, ?hmain⟩
  · have hbase : 0 < (d + 1) / (2 * d * ε * ω) := by
      apply div_pos <;> positivity
    have ha : 0 < a := by
      rw [hadef]
      exact Real.rpow_pos_of_pos hbase _
    have hcoef : 0 ≤ 2 * C₁ + 4 * ε * C₁ := by positivity
    nlinarith [mul_nonneg ha.le hcoef]
  · intro n b S I IE Qn Xsq Q hn hb hQ hX hX0 hXub hSI hI hIE0 hIEub hQnub hNQ1 hNQ2
    let c : ℝ := 2 * d * ε * ω / (d + 1)
    have hcdef : c = 2 * d * ε * ω / (d + 1) := rfl
    let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    have hNdef : N = (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := rfl
    rw [← hωdef] at hI ⊢
    rw [← hNdef] at hXub hSI hNQ1 hNQ2 ⊢
    rw [← hadef] at ⊢
    have hnpos : 0 < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hNpos : 0 < N := by
      rw [hNdef]
      exact Real.rpow_pos_of_pos hnpos _
    have hNpow : N ^ (d + 1) = (n : ℝ) := by
      rw [hNdef]
      have hx : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hnpos
      rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
        rw [one_div, Nat.cast_add, Nat.cast_one]]
      exact Real.rpow_inv_natCast_pow hx (by omega)
    have hN2divn : N ^ 2 / (n : ℝ) = N ^ (1 - (d : ℝ)) := by
      rw [← hNpow]
      exact sq_div_pow_eq_rpow hNpos
    have hNddn : N ^ d / (n : ℝ) = N⁻¹ := by
      rw [← hNpow]
      exact pow_div_pow_eq_inv hNpos
    have hE : 1 - c * (b / N) ^ (d + 1) =
        (Xsq - Qn + 2 * ε * (S - I)) / (n : ℝ) + 2 * ε * IE / (n : ℝ) := by
      rw [hX, hI, div_pow, hNpow, hcdef]
      field_simp
      ring
    have hE' : 1 - c * (b / N) ^ (d + 1) =
        (Xsq - Qn + 2 * ε * (S - I) + 2 * ε * IE) / (n : ℝ) := by
      rw [hE, ← add_div]
    have hXQ : |Xsq - Qn| ≤ C₁ * N ^ 2 + C₁ * n * Q := by
      have h1 : |Xsq - Qn| ≤ Xsq + |Qn| := by
        calc
          |Xsq - Qn| = |Xsq + (-Qn)| := by rw [sub_eq_add_neg]
          _ ≤ |Xsq| + |-Qn| := abs_add_le Xsq (-Qn)
          _ = Xsq + |Qn| := by rw [abs_of_nonneg hX0, abs_neg]
      have h2 : Xsq + |Qn| ≤ C₁ * N ^ 2 + C₁ * n * Q := add_le_add hXub hQnub
      linarith
    have hSI2 : 2 * ε * |S - I| ≤ 2 * ε * C₁ * N ^ d := by
      have h : 2 * ε * |S - I| ≤ 2 * ε * (C₁ * N ^ d) :=
        mul_le_mul_of_nonneg_left hSI (by positivity)
      linarith
    have hIE2 : 2 * ε * IE ≤ 2 * ε * C₁ * n * Q := by
      have h : 2 * ε * IE ≤ 2 * ε * (C₁ * n * Q) :=
        mul_le_mul_of_nonneg_left hIEub (by positivity)
      linarith
    have hnum : |Xsq - Qn + 2 * ε * (S - I) + 2 * ε * IE| ≤
        C₁ * N ^ 2 + C₁ * n * Q + 2 * ε * C₁ * N ^ d + 2 * ε * C₁ * n * Q := by
      have h1 := abs_add_le (Xsq - Qn + 2 * ε * (S - I)) (2 * ε * IE)
      have h2 := abs_add_le (Xsq - Qn) (2 * ε * (S - I))
      have h3 : |2 * ε * (S - I)| = 2 * ε * |S - I| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ε)]
      have h4 : |2 * ε * IE| = 2 * ε * IE := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ε), abs_of_nonneg hIE0]
      linarith
    have hEbound : |1 - c * (b / N) ^ (d + 1)| ≤ (2 * C₁ + 4 * ε * C₁) * Q := by
      rw [hE', abs_div, abs_of_nonneg (le_of_lt hnpos)]
      calc
        |Xsq - Qn + 2 * ε * (S - I) + 2 * ε * IE| / (n : ℝ)
            ≤ (C₁ * N ^ 2 + C₁ * n * Q + 2 * ε * C₁ * N ^ d
                + 2 * ε * C₁ * n * Q) / (n : ℝ) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hnpos)
        _ = C₁ * (N ^ 2 / (n : ℝ)) + C₁ * Q
            + 2 * ε * C₁ * (N ^ d / (n : ℝ)) + 2 * ε * C₁ * Q := by
          field_simp
        _ = C₁ * N ^ (1 - (d : ℝ)) + C₁ * Q + 2 * ε * C₁ * N⁻¹ + 2 * ε * C₁ * Q := by
          rw [hN2divn, hNddn]
        _ ≤ (2 * C₁ + 4 * ε * C₁) * Q := by
          have h1 : C₁ * N ^ (1 - (d : ℝ)) ≤ C₁ * Q :=
            mul_le_mul_of_nonneg_left hNQ1 hC₁
          have h2 : 2 * ε * C₁ * N⁻¹ ≤ 2 * ε * C₁ * Q :=
            mul_le_mul_of_nonneg_left hNQ2 (by positivity)
          linarith
    have hbase : 0 < (d + 1) / (2 * d * ε * ω) := by
      apply div_pos <;> positivity
    have hapos : 0 < a := by
      rw [hadef]
      exact Real.rpow_pos_of_pos hbase _
    have hapow : a ^ (d + 1) = (d + 1) / (2 * d * ε * ω) := by
      rw [hadef]
      have hnn : (0 : ℝ) ≤ (d + 1) / (2 * d * ε * ω) := le_of_lt hbase
      rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
        rw [one_div, Nat.cast_add, Nat.cast_one]]
      exact Real.rpow_inv_natCast_pow hnn (by omega)
    have hca : c * a ^ (d + 1) = 1 := by
      rw [hapow, hcdef]
      field_simp
    have hbound : |b / N - a| ≤ a * ((2 * C₁ + 4 * ε * C₁) * Q) :=
      CERW.Generic.Young.abs_sub_le_of_abs_one_sub_mul_pow
        (div_nonneg hb (le_of_lt hNpos)) hapos (by omega : 1 ≤ d + 1) hca hEbound
    have hfinal : a * ((2 * C₁ + 4 * ε * C₁) * Q)
        ≤ (a * (2 * C₁ + 4 * ε * C₁) + 1) * Q := by
      nlinarith [hQ]
    linarith

end CERW.Support.Contact
