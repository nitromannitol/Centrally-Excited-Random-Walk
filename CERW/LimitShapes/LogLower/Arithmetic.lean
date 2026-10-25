module

public import CERW.LimitShapes.LogLower.Tail

@[expose] public section

/-!
# The Gaussian exponent at the limit-shape radius

The stopped quadratic Azuma exponent has the scale `r^(d-3) h²` used in
Proposition 9.4 (`prop:log-lower`).
-/

namespace CERW.LimitShapes.LogLower

/-- The radius identity converts the bounded-increment exponent to the required scale. -/
theorem azuma_exponent {d : ℕ} (hd : 2 ≤ d) {ε ω c r h n : ℝ}
    (hε : 0 < ε) (hω : 0 < ω) (hc : 0 < c) (hr : 1 ≤ r)
    (hh : 0 < h) (hhr : 8 * h ≤ r)
    (hn : n = 2 * d * ε * ω * r ^ (d + 1) / (d + 1)) :
    c ^ 2 / (169 * ε * ω) * r ^ ((d : ℝ) - 3) * h ^ 2 ≤
      (c * r ^ d * h) ^ 2 / (2 * n * (2 * (2 * (r + h) + 1)) ^ 2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hrpos : 0 < r := by linarith
  have hnpos : 0 < n := by rw [hn]; positivity
  have hnle : n ≤ 2 * ε * ω * r ^ (d + 1) := by
    rw [hn, div_le_iff₀ (by positivity)]
    have hnonneg : 0 ≤ 2 * ε * ω * r ^ (d + 1) := by positivity
    nlinarith
  have hA : 2 * (2 * (r + h) + 1) ≤ 13 / 2 * r := by linarith
  have hA0 : 0 ≤ 2 * (2 * (r + h) + 1) := by linarith
  have hden : 2 * n * (2 * (2 * (r + h) + 1)) ^ 2 ≤
      (169 * ε * ω) * r ^ (d + 3) := by
    calc
      _ ≤ 2 * (2 * ε * ω * r ^ (d + 1)) * (13 / 2 * r) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnle (by norm_num))
          (pow_le_pow_left₀ hA0 hA 2) (by positivity) (by positivity)
      _ = _ := by ring
  have hrpow : r ^ ((d : ℝ) - 3) = r ^ d / r ^ 3 := by
    rw [Real.rpow_sub hrpos, Real.rpow_natCast]
    norm_num
  calc
    _ = (c * r ^ d * h) ^ 2 / ((169 * ε * ω) * r ^ (d + 3)) := by
      rw [hrpow]
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden

/-- The stopped quadratic lower tail at the radius scale, proved using Azuma. -/
theorem outer_quadratic_tail {d : ℕ} (hd : 2 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {X : ℕ → Ω → LatticeProb.Site d}
    (hX : CERW.IsCERW μ ε X) {c r h : ℝ} {n : ℕ}
    (hc : 0 < c) (hr : 1 ≤ r) (hh : 0 < h) (hhr : 8 * h ≤ r)
    (hn : (n : ℝ) = 2 * d * ε * CERW.unitBallVolume d * r ^ (d + 1) / (d + 1)) :
    μ {ω | (∀ j ≤ n, LatticeProb.euclidNorm (X j ω) ≤ r + h) ∧
        CERW.quadraticMart ε (fun j => X j ω) n ≤ -(c * r ^ d * h)} ≤
      ENNReal.ofReal (Real.exp (-(c ^ 2 / (169 * ε * CERW.unitBallVolume d) *
        r ^ ((d : ℝ) - 3) * h ^ 2))) := by
  have hω : 0 < CERW.unitBallVolume d := CERW.unitBallVolume_pos d
  have ht : 0 ≤ c * r ^ d * h := by positivity
  have he := azuma_exponent hd hε hω hc hr hh hhr hn
  exact (quadratic_lower_tail hd hε hεd hX (by linarith) ht n).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg he)))

end CERW.LimitShapes.LogLower
