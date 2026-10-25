module

public import CERW.LimitShapes.NormRates.Quadratic

@[expose] public section

/-!
# Normalization of the quadratic radius comparison

Dividing the quadratic comparison by the deterministic time scale gives the
radius-volume inequality in Proposition `prop:norm-shape`.
-/

open MeasureTheory Filter
open LatticeProb (Site)
open CERW.Support.Norm.ContactEvent (scale PathTyping)
open private tendsto_scale nat_eq_scale_pow from CERW.Support.Norm.ShapeRates
open CERW CERW.Support.Norm

namespace CERW.LimitShapes.NormRates

/-- The quadratic time scale factors out of the square-root fluctuation. -/
theorem sqrt_time_mul_log {d : ℕ} {a r ℓ nn : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hn : nn = a * r ^ (d + 1)) :
    Real.sqrt (nn * ℓ) = Real.sqrt a * r ^ (((d : ℝ) + 1) / 2) * Real.sqrt ℓ := by
  have hs : Real.sqrt (r ^ (d + 1)) = r ^ (((d : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    push_cast
    ring
  rw [hn, Real.sqrt_mul (mul_nonneg ha.le (pow_nonneg hr.le _)),
    Real.sqrt_mul ha.le, hs]

/-- Normalizing a power difference yields the radius-volume error, with exact exponents. -/
theorem radius_volume_normalization {d : ℕ}
    {a r b ℓ nn Ev CQ CM CE : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (hn : nn = a * r ^ (d + 1))
    (hcmp : |nn - a * b ^ (d + 1)| ≤
      CQ * r * Real.sqrt (nn * ℓ) + CM * r ^ d + CE * r * Ev) :
    |1 - (b / r) ^ (d + 1)| ≤
      (CQ * Real.sqrt a / a) * (r ^ ((1 - (d : ℝ)) / 2) * Real.sqrt ℓ) +
        (CM / a) * r⁻¹ + (CE / a) * (Ev * r ^ (-(d : ℝ))) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hden : 0 < a * r ^ (d + 1) := mul_pos ha (pow_pos hr0 _)
  have hid : |1 - (b / r) ^ (d + 1)| =
      |nn - a * b ^ (d + 1)| / (a * r ^ (d + 1)) := by
    have heq : 1 - (b / r) ^ (d + 1) =
        (nn - a * b ^ (d + 1)) / (a * r ^ (d + 1)) := by
      rw [hn, div_pow]
      field_simp
    rw [heq, abs_div, abs_of_pos hden]
  have hpQ : r * r ^ (((d : ℝ) + 1) / 2) / r ^ (d + 1) =
      r ^ ((1 - (d : ℝ)) / 2) := by
    calc _ = r ^ (1 + ((d : ℝ) + 1) / 2 - ((d + 1 : ℕ) : ℝ)) := by
          rw [Real.rpow_sub hr0, Real.rpow_add hr0,
            Real.rpow_one, Real.rpow_natCast]
      _ = _ := by congr 1; push_cast; ring
  have hpM : r ^ d / r ^ (d + 1) = r⁻¹ := by
    rw [pow_succ]
    field_simp
  have hpE : r / r ^ (d + 1) = r ^ (-(d : ℝ)) := by
    rw [pow_succ, Real.rpow_neg hr0.le, Real.rpow_natCast]
    field_simp
  rw [hid]
  apply (div_le_div_of_nonneg_right hcmp hden.le).trans_eq
  rw [sqrt_time_mul_log ha hr0 hn]
  calc (CQ * r * (Real.sqrt a * r ^ (((d : ℝ) + 1) / 2) * Real.sqrt ℓ) +
        CM * r ^ d + CE * r * Ev) / (a * r ^ (d + 1)) =
      (CQ * Real.sqrt a / a) *
          (r * r ^ (((d : ℝ) + 1) / 2) / r ^ (d + 1)) * Real.sqrt ℓ +
        (CM / a) * (r ^ d / r ^ (d + 1)) +
        (CE / a) * (Ev * (r / r ^ (d + 1))) := by ring
    _ = _ := by rw [hpQ, hpM, hpE]; ring

/-- The radius-volume estimate of Proposition `prop:norm-shape` on the actual common event. -/
theorem radius_volume_of_event {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (K : EventConstants) (hCo : 0 < K.CCo) (hQ : 0 < K.CQuad) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) →
        ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
          EventEstimates Ψ ε ξ K X n →
          let r := scale d Ψ ε n
          let b := normInnerRadius Ψ X n
          let E := cellSet X n \ {v | Ψ v < b}
          |1 - (b / r) ^ (d + 1)| ≤ C *
            (r ^ ((1 - (d : ℝ)) / 2) * Real.sqrt (Real.log n) + r⁻¹ +
              (volume E).toReal * r ^ (-(d : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  have hV := ContactAssembly.normBallVolume_pos' hd1 hΨ
  have hΛ : 0 < normMax Ψ :=
    lt_of_lt_of_le (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1).1
      (ContactAssembly.normMin_le_normMax hd1 hΨ)
  let a : ℝ := 2 * ε * d * normBallVolume Ψ / (d + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  let CM := K.CCo ^ 2 + ε * normMax Ψ * Real.sqrt d * K.CCo
  let CE := 2 * ε * normMax Ψ * (K.CCo + 1)
  let CQ := K.CQuad * Real.sqrt a / a
  have hCM : 0 ≤ CM := by dsimp [CM]; positivity
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  have hCQ : 0 < CQ := by dsimp [CQ]; positivity
  let C := CQ + CM / a + CE / a + 1
  have hC : 0 < C := by dsimp [C]; linarith [div_nonneg hCM ha.le, div_nonneg hCE ha.le]
  have hX : 0 < 2 * (d : ℝ) * ε * normBallVolume Ψ := by positivity
  have ht := tendsto_scale d hX
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      max 1 (Real.sqrt d) ≤ scale d Ψ ε n := by
    filter_upwards [eventually_ge_atTop 2,
      ht.eventually_ge_atTop (max 1 (Real.sqrt d))] with n hn hr
    exact ⟨hn, hr⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  refine ⟨C, hC, max N 2, le_max_right _ _, ?_⟩
  intro ξ hξ X n hn hpath hE
  dsimp only
  obtain ⟨hn2, hr⟩ := hN n ((le_max_left _ _).trans hn)
  have hr1 : 1 ≤ scale d Ψ ε n := (le_max_left _ _).trans hr
  have hrd : Real.sqrt d ≤ scale d Ψ ε n := (le_max_right _ _).trans hr
  have hr0 := lt_of_lt_of_le zero_lt_one hr1
  have hnr : (n : ℝ) = a * scale d Ψ ε n ^ (d + 1) := by
    have h := nat_eq_scale_pow d hX n
    change (n : ℝ) = (2 * d * ε * normBallVolume Ψ) *
      scale d Ψ ε n ^ (d + 1) / (d + 1) at h
    rw [h]
    dsimp [a]
    ring
  have hraw := abs_time_sub_inner_ball_of_event hd hΨ hε hξ
    (by omega : 0 < n) hpath hE hrd
  have hcard := hE.1.2.1
  have hpow : scale d Ψ ε n ^ (2 : ℕ) ≤ scale d Ψ ε n ^ d :=
    pow_le_pow_right₀ hr1 hd
  have hcmp : |(n : ℝ) - a * normInnerRadius Ψ X n ^ (d + 1)| ≤
      K.CQuad * scale d Ψ ε n * Real.sqrt (n * Real.log n) +
        CM * scale d Ψ ε n ^ d + CE * scale d Ψ ε n *
          (volume (cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n})).toReal := by
    have hsq := mul_le_mul_of_nonneg_left hpow (sq_nonneg K.CCo)
    have hc := mul_le_mul_of_nonneg_left hcard
      (by positivity : 0 ≤ ε * normMax Ψ * Real.sqrt d)
    dsimp [CM, CE, a]
    convert hraw.trans ?_ using 1 <;> try { congr 1 <;> ring }
    rw [mul_pow]
    nlinarith [hsq, hc]
  have hb := radius_volume_normalization ha hr1 hnr hcmp
  apply hb.trans
  have h1 : CQ ≤ C := by dsimp [C]; linarith [div_nonneg hCM ha.le, div_nonneg hCE ha.le]
  have h2 : CM / a ≤ C := by dsimp [C]; linarith [div_nonneg hCM ha.le, div_nonneg hCE ha.le]
  have h3 : CE / a ≤ C := by dsimp [C]; linarith [div_nonneg hCM ha.le, div_nonneg hCE ha.le]
  calc
    _ ≤ C * (scale d Ψ ε n ^ ((1 - (d : ℝ)) / 2) * Real.sqrt (Real.log n)) +
        C * (scale d Ψ ε n)⁻¹ + C *
          ((volume (cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n})).toReal *
            scale d Ψ ε n ^ (-(d : ℝ))) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right h1 (by positivity))
        (mul_le_mul_of_nonneg_right h2 (by positivity)))
        (mul_le_mul_of_nonneg_right h3 (by positivity))
    _ = _ := by ring

end CERW.LimitShapes.NormRates
