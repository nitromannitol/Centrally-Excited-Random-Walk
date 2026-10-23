import CERW.LimitShapes.Exit.CoarseScales

/-!
# Uniform constants for the coarse bounds

The six conclusions of Proposition `prop:coarse` follow from two upper bounds and
occupation, with constants chosen independently of the path.
-/

universe u

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory

/-- The six pathwise bounds in Proposition `prop:coarse`, at radius scale `r`. -/
def CoarseBounds {d : ℕ} (c C r : ℝ) (x : ℕ → Site d) (n : ℕ) : Prop :=
  c * r ^ d ≤ ((departureRange x n).card : ℝ) ∧
  ((departureRange x n).card : ℝ) ≤ C * r ^ d ∧
  c * r ≤ (maxLocalTime x n : ℝ) ∧ (maxLocalTime x n : ℝ) ≤ C * r ∧
  c * r ≤ maxRadius x n ∧ maxRadius x n ≤ C * r

/-- Enlarging the upper constant preserves the six bounds. -/
theorem coarseBounds_mono {d : ℕ} {c C D r : ℝ} {x : ℕ → Site d} {n : ℕ}
    (hCD : C ≤ D) (hr : 0 ≤ r) (h : CoarseBounds c C r x n) :
    CoarseBounds c D r x n :=
  ⟨h.1, h.2.1.trans (mul_le_mul_of_nonneg_right hCD (pow_nonneg hr _)),
    h.2.2.1, h.2.2.2.1.trans (mul_le_mul_of_nonneg_right hCD hr),
    h.2.2.2.2.1, h.2.2.2.2.2.trans (mul_le_mul_of_nonneg_right hCD hr)⟩

/-- The occupation and packing arguments in Proposition `prop:coarse` use uniform
constants and a fixed lower threshold for the radius scale. -/
theorem exists_coarse_constants {d : ℕ} (hd : 1 ≤ d) {κ H L : ℝ}
    (hκ : 0 < κ) (hH : 0 < H) (hL : 0 < L) :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ (x : ℕ → Site d) (n : ℕ) (r : ℝ), T ≤ r →
      (n : ℝ) = κ * r ^ (d + 1) →
      maxRadius x n ≤ H * r → (maxLocalTime x n : ℝ) ≤ L * r →
      CoarseBounds c C r x n := by
  let a := κ / L
  let U := (2 * H + 1) ^ d
  let b := a ^ ((1 : ℝ) / d)
  let c := min a (min (κ / U) (b / 4))
  let C := H + L + U + 1
  let T := max 1 (2 / b)
  have ha : 0 < a := div_pos hκ hL
  have hU : 0 < U := pow_pos (by positivity) _
  have hb : 0 < b := Real.rpow_pos_of_pos ha _
  have hc : 0 < c := lt_min ha (lt_min (div_pos hκ hU) (by positivity))
  have hC : 0 < C := by dsimp [C]; positivity
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨c, C, T, hc, hC, hT, ?_⟩
  intro x n r hTr ht hh hl
  have hr : 1 ≤ r := (le_max_left _ _).trans hTr
  have hr0 : 0 ≤ r := by linarith
  have hbr : 2 ≤ b * r := by
    have h := (le_max_right 1 (2 / b)).trans hTr
    have h' := (div_le_iff₀ hb).mp h
    nlinarith only [h']
  obtain ⟨hcard, hcardU, hlocal⟩ :=
    occupation_bounds_of_maxima x n hr hH.le hL hκ ht hh hl
  have hrad := radius_lower_of_card hd x n ha hr0 hbr hcard
  have hca : c ≤ a := min_le_left _ _
  have hcU : c ≤ κ / U := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ b / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hUC : U ≤ C := by dsimp [C]; linarith
  have hLC : L ≤ C := by dsimp [C]; linarith
  have hHC : H ≤ C := by dsimp [C]; linarith
  exact ⟨(mul_le_mul_of_nonneg_right hca (pow_nonneg hr0 _)).trans hcard,
    hcardU.trans (mul_le_mul_of_nonneg_right hUC (pow_nonneg hr0 _)),
    (mul_le_mul_of_nonneg_right hcU hr0).trans hlocal,
    hl.trans (mul_le_mul_of_nonneg_right hLC hr0),
    (mul_le_mul_of_nonneg_right hcb hr0).trans hrad,
    hh.trans (mul_le_mul_of_nonneg_right hHC hr0)⟩

end CERW.LimitShapes.Exit
