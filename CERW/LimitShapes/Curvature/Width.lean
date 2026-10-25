module

public import CERW.Support.Outer.Radius.HigherDimensionWidth

@[expose] public section

/-!
# Width absorption and profile error

Young's inequality absorbs the width term in `eq:outer-reduction`.
The resulting width estimate controls the positive potential in `sec:global-profile`.
-/

namespace CERW.LimitShapes.Curvature

/-- Young absorption gives the width bound in `eq:outer-reduction`. -/
theorem exists_width_bound {d : ℕ} (hd : 2 ≤ d)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w delta L : ℝ), 0 ≤ w → 1 ≤ delta → 1 ≤ L →
      w ≤ A * (1 + B * ((delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) + delta)) * L →
      w ≤ C * delta * L ^ d := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hc : 0 < A * B := mul_pos hA hB
  let K := A * B * (2 * (A * B)) ^ m
  refine ⟨2 * (A + K + A * B), by dsimp [K]; positivity, ?_⟩
  intro w delta L hw hdelta hL hwidth
  have hd0 : 0 ≤ delta := by linarith
  have hL0 : 0 < L := by linarith
  let a := (delta * w ^ (m + 1 - 1)) ^ ((1 : ℝ) / (m + 1 : ℕ))
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by positivity) _
  have ha : a ^ (m + 1) = delta * w ^ m := by
    dsimp [a]
    rw [one_div, Real.rpow_inv_natCast_pow (by positivity) (Nat.succ_ne_zero m)]
  have hy := CERW.Support.Outer.Radius.ar_young m hL0 hd0 hw ha0
    (inv_pos.mpr (show 0 < 2 * (A * B) by positivity)) ha
  have hab : A * B * (L * a) ≤ w / 2 + K * (delta * L ^ (m + 1)) := by
    calc
      A * B * (L * a) ≤ A * B *
          ((2 * (A * B))⁻¹ * w + L ^ (m + 1) * delta /
            ((2 * (A * B))⁻¹) ^ m) := mul_le_mul_of_nonneg_left hy hc.le
      _ = w / 2 + K * (delta * L ^ (m + 1)) := by
        dsimp [K]
        rw [inv_pow, div_inv_eq_mul]
        field_simp
  have hLp : L ≤ L ^ (m + 1) := by
    calc
      L = L * 1 := (mul_one L).symm
      _ ≤ L * L ^ m := mul_le_mul_of_nonneg_left (one_le_pow₀ hL) hL0.le
      _ = L ^ (m + 1) := (pow_succ' L m).symm
  have hfirst : L ≤ delta * L ^ (m + 1) :=
    hLp.trans (le_mul_of_one_le_left (by positivity) hdelta)
  have hlast : delta * L ≤ delta * L ^ (m + 1) :=
    mul_le_mul_of_nonneg_left hLp hd0
  have hfirst' := mul_le_mul_of_nonneg_left hfirst hA.le
  have hlast' := mul_le_mul_of_nonneg_left hlast hc.le
  change w ≤ A * (1 + B * (a + delta)) * L at hwidth
  nlinarith only [hwidth, hab, hfirst', hlast']

/-- Substituting the width bound controls the profile error in `sec:global-profile`. -/
theorem exists_profile_error_le_of_width {d : ℕ} (hd : 2 ≤ d)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w delta L : ℝ), 0 ≤ w → 1 ≤ delta → 1 ≤ L →
      w ≤ A * delta * L ^ d →
      B * ((delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) + delta) ≤
        C * delta * L ^ (d - 1) := by
  let K := A ^ (d - 1) + 1
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith [pow_nonneg hA.le (d - 1)]
  have hK0 : 0 ≤ K := by linarith
  refine ⟨B * (K + 1), by positivity, ?_⟩
  intro w delta L hw hdelta hL hwidth
  have hd0 : 0 ≤ delta := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hpow := pow_le_pow_left₀ hw hwidth (d - 1)
  have hAK : A ^ (d - 1) ≤ K ^ d := by
    have hkd : K ≤ K ^ d := by
      obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
      rw [hm, pow_succ']
      exact le_mul_of_one_le_right hK0 (one_le_pow₀ hK)
    have : A ^ (d - 1) ≤ K := by dsimp [K]; linarith
    exact this.trans hkd
  have hbase : delta * w ^ (d - 1) ≤ (K * delta * L ^ (d - 1)) ^ d := by
    calc
      delta * w ^ (d - 1) ≤ delta * (A * delta * L ^ d) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left hpow hd0
      _ = A ^ (d - 1) * delta ^ d * L ^ (d * (d - 1)) := by
        rw [mul_pow, mul_pow, ← pow_mul]
        have he : d = (d - 1) + 1 := by omega
        conv_rhs => arg 1; arg 2; rw [he, pow_succ]
        ring
      _ ≤ K ^ d * delta ^ d * L ^ (d * (d - 1)) := by
        gcongr
      _ = (K * delta * L ^ (d - 1)) ^ d := by
        rw [mul_pow, mul_pow, ← pow_mul]
        congr 1
        congr 1
        exact Nat.mul_comm _ _
  have hroot : (delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) ≤
      K * delta * L ^ (d - 1) := by
    have hr := Real.rpow_le_rpow (by positivity) hbase
      (show 0 ≤ (1 : ℝ) / d by positivity)
    rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega : d ≠ 0)] at hr
    simpa only [one_div] using hr
  have hlow : delta ≤ delta * L ^ (d - 1) :=
    le_mul_of_one_le_right hd0 (one_le_pow₀ hL)
  nlinarith only [mul_le_mul_of_nonneg_left hroot hB.le,
    mul_le_mul_of_nonneg_left hlow hB.le]

end CERW.LimitShapes.Curvature
