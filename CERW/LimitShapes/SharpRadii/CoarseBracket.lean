import CERW.LimitShapes.EuclideanEvent
import CERW.Support.Lower.SharpRadii

/-!
# Quadratic bracket bounds from the coarse event

The occupation estimate in Proposition 4.1 supplies the lower bracket bound used
in Theorem 1.3(i). The bounded martingale is the clamped quadratic transform;
its agreement with the quadratic martingale is part of the conclusion.
-/

open MeasureTheory LatticeProb

namespace CERW.LimitShapes.SharpRadii

open CERW CERW.Support.Law CERW.Support.Contact
open CERW.Support.Norm.ContactEvent
open private exists_truncated_martingale lower_sum_localTime sum_srw_times_eq
  from CERW.Support.Lower.SharpRadii

/-- Explicit large-scale conditions imply both occupation inequalities needed for
Theorem 1.3(i), with the coarse local-time bound equal to `R`. -/
theorem coarse_bracket_geometry {R θ a N : ℝ} (hR : 1 ≤ R)
    (hθ : 0 < θ) (ha : 0 < a) (hθa : θ ^ 2 = a / 18)
    (hθR : 1 ≤ θ * R) (hlarge : 400 / (θ ^ 2 * a) ≤ R)
    (hN : N = a * R ^ 3) :
    R * (2 * θ * R + 1) ^ 2 ≤ N / 2 ∧
      4 * R ^ 2 * (4 * R + 1) ^ 2 ≤ θ ^ 2 * R ^ 2 * N / 4 := by
  have hR0 : 0 ≤ R := by linarith
  constructor
  · have hs : (2 * θ * R + 1) ^ 2 ≤ 9 * (θ * R) ^ 2 := by nlinarith
    calc
      _ ≤ R * (9 * (θ * R) ^ 2) := mul_le_mul_of_nonneg_left hs hR0
      _ = N / 2 := by rw [hN, mul_pow, hθa]; ring
  · have hk : 0 < θ ^ 2 * a := mul_pos (sq_pos_of_pos hθ) ha
    have h400 : 400 ≤ (θ ^ 2 * a) * R := by
      simpa only [mul_comm] using (div_le_iff₀ hk).mp hlarge
    have hs : (4 * R + 1) ^ 2 ≤ 25 * R ^ 2 := by nlinarith
    calc
      _ ≤ 4 * R ^ 2 * (25 * R ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 400 * R ^ 4 / 4 := by ring
      _ ≤ ((θ ^ 2 * a) * R) * R ^ 4 / 4 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right h400 (by positivity)) (by norm_num)
      _ = θ ^ 2 * R ^ 2 * N / 4 := by rw [hN]; ring

/-- On the coarse event, the clamped quadratic martingale has bracket of order
`R⁵`. The two geometric inequalities express the half-occupation bound and the
negligibility of the first-departure correction in Theorem 1.3(i). -/
theorem exists_martingale_coarse_bracket
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (2 : ℝ))
    (hX : IsCERW μ ε X) (K : EventConstants) (n : ℕ) {R θ a : ℝ}
    (hR : 1 ≤ R) (hθ : 0 < θ)
    (hscale : R = K.CCo * scale 2 (fun v => ‖v‖) ε n)
    (hn : (n : ℝ) = a * R ^ 3)
    (hhalf : R * (2 * θ * R + 1) ^ 2 ≤ (n : ℝ) / 2)
    (herror : 4 * R ^ 2 * (4 * R + 1) ^ 2 ≤ θ ^ 2 * R ^ 2 * (n : ℝ) / 4) :
    ∃ S : ℕ → Ω → ℝ,
      Martingale S (pathFiltration hX.measurable) μ ∧
      (∀ ω, S 0 ω = 0) ∧
      (∀ t ω, |S (t + 1) ω - S t ω| ≤ 2 * (2 * R + 1)) ∧
      (∀ᵐ ω ∂μ, ω ∈ section5Event (fun v => ‖v‖) ε
          (fun x => unitDir (toSpace x)) K X n →
        S n ω = quadraticMart ε (X · ω) n ∧
        (θ ^ 2 * a / 2) * R ^ 5 ≤
          predBracket μ (pathFiltration hX.measurable) S S n ω ∧
        predBracket μ (pathFiltration hX.measurable) S S n ω ≤ 25 * a * R ^ 5) := by
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨S, hS, hzero, hinc, hagree, hupper, hlower⟩ :=
    exists_truncated_martingale (by norm_num) hε.le hεd hX hR0
      (by norm_num : (0 : ℝ) < 1) n
  refine ⟨S, hS, hzero, ?_, ?_⟩
  · intro t ω
    simpa only [one_mul] using hinc t ω
  filter_upwards [hagree, hupper, hlower] with ω hagree hupper hlower hω
  have hc := hω.1
  have hout : maxRadius (X · ω) n ≤ R := by
    rw [hscale]
    exact hc.2.2.2.2.2
  have hloc : ∀ z, (localTime (X · ω) n z : ℝ) ≤ R := by
    intro z
    calc
      _ ≤ (maxLocalTime (X · ω) n : ℝ) :=
        Nat.cast_le.mpr (localTime_le_maxLocalTime _ _ _)
      _ ≤ R := by rw [hscale]; exact hc.2.2.2.1
  have hstay : ∀ t < n, euclidNorm (X t ω) ≤ R := by
    intro t ht
    exact (euclidNorm_le_maxRadius (X · ω) ht.le).trans hout
  refine ⟨by simpa only [one_mul] using hagree hstay, ?_, ?_⟩
  · have hsum := lower_sum_localTime hθ (by linarith : 0 < R) hR0 hloc
      (hout.trans (by linarith)) hhalf
    have hb := hlower hstay
    rw [sum_srw_times_eq] at hb
    norm_num only [one_pow, one_mul, Nat.cast_ofNat, div_self] at hb
    have hmain : (θ ^ 2 * a / 2) * R ^ 5 =
        2 * (θ ^ 2 * R ^ 2 * (n : ℝ) / 4) := by rw [hn]; ring
    rw [hmain]
    linarith
  · have hb := hupper hstay
    norm_num only [one_pow, one_mul] at hb
    have hsquare : (2 * R + 1) ^ 2 ≤ 25 * R ^ 2 := by nlinarith
    calc
      _ ≤ (n : ℝ) * (2 * R + 1) ^ 2 := hb
      _ ≤ (n : ℝ) * (25 * R ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg n)
      _ = 25 * a * R ^ 5 := by rw [hn]; ring

end CERW.LimitShapes.SharpRadii
