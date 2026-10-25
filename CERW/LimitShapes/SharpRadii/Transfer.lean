module

public import CERW.LimitShapes.SharpRadii.CoarseBracket

@[expose] public section

/-!
# Radius transfer on a coarse ball

The cubic identity for the moment radius transfers both signs of a quadratic
martingale deviation to the radii in Theorem 1.3(i). The coarse ball constant
is arbitrary and is chosen before the walk realization.
-/

universe u

open MeasureTheory LatticeProb

namespace CERW.LimitShapes.SharpRadii

open CERW
open private momentRadius_pow_three momentRadius_nonneg sub_moment_ge
  measureReal_le_of_ae_inter from CERW.Support.Lower.SharpRadii

/-- The upward cubic transfer with a general bound on the moment radius. -/
private lemma moment_sub_ge_of_le {ε w r m E n y Q q B : ℝ}
    (hε : 0 < ε) (hw : 0 < w) (hr : 0 < r) (hm : 0 ≤ m) (hB : 0 ≤ B)
    (hmb : m ≤ B * r) (hmE : m ^ 3 = 3 / (2 * w) * E)
    (hrn : r ^ 3 = 3 * n / (4 * ε * w)) (hQ : Q = 2 * ε * E - n + y)
    (hy : 2 * y ≤ q) (hq : 0 < q) (hQq : q ≤ Q) :
    3 * q / (8 * ε * w * (B ^ 2 + B + 1) * r ^ 2) ≤ m - r := by
  have hD : 3 * q ≤ (m ^ 3 - r ^ 3) * (8 * ε * w) := by
    have he : (m ^ 3 - r ^ 3) * (4 * ε * w) = 3 * (2 * ε * E - n) := by
      rw [hmE, hrn]
      field_simp
      ring
    nlinarith
  have hmr : r < m := by
    by_contra h
    have hc := pow_le_pow_left₀ hm (not_lt.mp h) 3
    have hp : 0 ≤ (r ^ 3 - m ^ 3) * (8 * ε * w) :=
      mul_nonneg (sub_nonneg.mpr hc) (by positivity)
    linarith
  have hb : m ^ 2 + m * r + r ^ 2 ≤ (B ^ 2 + B + 1) * r ^ 2 := by
    have hs := pow_le_pow_left₀ hm hmb 2
    have ht := mul_le_mul_of_nonneg_right hmb hr.le
    nlinarith
  have hf : m ^ 3 - r ^ 3 ≤ (m - r) * ((B ^ 2 + B + 1) * r ^ 2) := by
    calc
      _ = (m - r) * (m ^ 2 + m * r + r ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by linarith)
  rw [div_le_iff₀ (by positivity)]
  have hh := mul_le_mul_of_nonneg_right hf (by positivity : 0 ≤ 8 * ε * w)
  nlinarith only [hD, hh]

/-- On an event contained in a coarse ball, both signs of a martingale agreeing
with the quadratic martingale give radius deviations, with the event error
subtracted once. This is the radius algebra in Theorem 1.3(i). -/
theorem radii_of_quadratic_deviations
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} {S : ℕ → Ω → ℝ} {E : Set Ω} {n : ℕ}
    {ε r k B q P α CS CI : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hB : 0 ≤ B)
    (hrn : r ^ 3 = 3 * n / (4 * ε * unitBallVolume 2))
    (hE : MeasurableSet E) (hEc : μ.real Eᶜ ≤ α)
    (hag : ∀ᵐ ω ∂μ, ω ∈ E → S n ω = quadraticMart ε (X · ω) n ∧
      maxRadius (X · ω) n ≤ k * r)
    (hCS : ∀ Y : ℕ → Site 2, momentRadius Y n ≤ maxRadius Y n + CS)
    (hCI : ∀ Y : ℕ → Site 2, innerRadius Y n ≤ momentRadius Y n + CI)
    (hCSr : k * r + CS ≤ B * r) (hq : 0 < q) (hqR : 2 * (k * r) ^ 2 ≤ q)
    (hplus : P ≤ μ.real {ω | q ≤ S n ω})
    (hminus : P ≤ μ.real {ω | S n ω ≤ -q}) :
    P - α ≤ μ.real {ω |
      3 * q / (8 * ε * unitBallVolume 2 * (B ^ 2 + B + 1) * r ^ 2) - CS ≤
        maxRadius (X · ω) n - r} ∧
    P - α ≤ μ.real {ω |
      q / (4 * ε * unitBallVolume 2 * r ^ 2) - CI ≤ r - innerRadius (X · ω) n} := by
  have hw := unitBallVolume_pos 2
  constructor
  · have ht : ∀ᵐ ω ∂μ, ω ∈ {ω | q ≤ S n ω} → ω ∈ E → ω ∈ {ω |
        3 * q / (8 * ε * unitBallVolume 2 * (B ^ 2 + B + 1) * r ^ 2) - CS ≤
          maxRadius (X · ω) n - r} := by
      filter_upwards [hag] with ω hω hplus hωE
      obtain ⟨hSn, hout⟩ := hω hωE
      have hyn : euclidNorm (X n ω) ^ 2 ≤ (k * r) ^ 2 :=
        pow_le_pow_left₀ (euclidNorm_nonneg _) ((euclidNorm_le_maxRadius _ le_rfl).trans
          hout) 2
      have hm := hCS (X · ω)
      have ht := moment_sub_ge_of_le hε hw hr (momentRadius_nonneg _ n) hB
        (by linarith : momentRadius (X · ω) n ≤ B * r)
        (momentRadius_pow_three _ n) hrn rfl (le_trans (by linarith :
          2 * euclidNorm (X n ω) ^ 2 ≤ 2 * (k * r) ^ 2) hqR) hq
        (by simpa only [hSn, quadraticMart] using hplus)
      linarith
    have hp := measureReal_le_of_ae_inter hE ht
    linarith
  · have ht : ∀ᵐ ω ∂μ, ω ∈ {ω | S n ω ≤ -q} → ω ∈ E → ω ∈ {ω |
        q / (4 * ε * unitBallVolume 2 * r ^ 2) - CI ≤
          r - innerRadius (X · ω) n} := by
      filter_upwards [hag] with ω hω hminus hωE
      obtain ⟨hSn, _⟩ := hω hωE
      have ht := sub_moment_ge hε hw hr (momentRadius_nonneg _ n)
        (momentRadius_pow_three _ n) hrn rfl (sq_nonneg (euclidNorm (X n ω))) hq.le
        (by simpa only [hSn, quadraticMart] using hminus)
      have hi := hCI (X · ω)
      linarith
    have hp := measureReal_le_of_ae_inter hE ht
    linarith

end CERW.LimitShapes.SharpRadii
