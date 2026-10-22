import CERW.LimitShapes.Crossing.Deterministic
import CERW.LimitShapes.Crossing.RampFamilies
import CERW.Support.Norm.VectorBound

/-!
# The simultaneous distance crossing probability bound

The vector estimate and the prefix ramp estimates for the deterministic projection
directions imply crossings at every time and norm level. The polynomial direction,
time and grid counts are absorbed by increasing the exponent in Freedman's bound.
-/

universe u

open MeasureTheory Filter LatticeProb
open CERW CERW.LimitShapes CERW.LimitShapes.Crossing
open CERW.LimitShapes.Crossing.Directions CERW.Support.Norm.VectorBound

/-- The simultaneous distance crossing estimate, with constants independent of the
subgradient choice, probability space and realization. -/
theorem CERW.LimitShapes.Crossing.Probability.distance_crossing_bound {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ N : ℕ, 2 ≤ N →
        μ {ω | ¬ CERW.LimitShapes.DistanceCrossingBound Ψ C (X · ω) N} ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-p))
:= by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc, _⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc
    (CERW.Support.Norm.ProjectionGeometry.normMin_le_normMax hΨ hd1)
  obtain ⟨Cr, hCr, hRamp⟩ := RampFamilies.exists_prefix_ramp_family_bound.{u}
    hΛ.le (p + (d + 3 : ℕ)) (by positivity)
  obtain ⟨Cv, hCv, hVec⟩ :=
    CERW.Support.Norm.VectorBound.exists_driftCompensated_bound hd1 hε.le hp
  let C₁ := Cr + Cv
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  obtain ⟨Cd, hCd, hDet⟩ := Deterministic.distanceCrossingBound_of_estimates hd hΨ hε hell hC₁
  let Cf := Cr * (normMax Ψ + 2) * 3 ^ d * 2 ^ (d + 3)
  have hCf : 0 < Cf := by dsimp [Cf]; positivity
  refine ⟨Cd + Cv + Cf, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX N hN
  classical
  have hcoord := CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
  let Q := crossingDirections Ψ N
  let Er : Set Ω := {ω | ¬ ∀ n : ℕ, n ≤ N → ∀ q ∈ Q, ∀ k : ℕ, k ≤ N →
    |dynkinMart (driftStepProb d ε ξ)
      (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) (X · ω) n| ≤
      Cr * (Real.sqrt (Real.log N * ∑ z ∈ (departureRange (X · ω) n).filter
        (fun z => k * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
        (localTime (X · ω) n z : ℝ)) + Real.log N)}
  let Ev : Set Ω := {ω | ∃ s t : ℕ, s < t ∧ t ≤ N ∧
    Cv * Real.sqrt (((t : ℝ) - s) * Real.log N) <
      ‖driftCompensated ε ξ (X · ω) t - driftCompensated ε ξ (X · ω) s‖}
  have hEv : μ Ev ≤ ENNReal.ofReal (Cv * (N : ℝ) ^ (-p)) :=
    hVec hcoord hξ0 hX N hN
  have hEr0 := hRamp hd1 μ ε ξ hε.le hcoord X hX N hN Q
    (fun q hq => norm_le_of_mem_crossingDirections hΛ.le hq)
  have hEr : μ Er ≤ ENNReal.ofReal (Cf * (N : ℝ) ^ (-p)) := by
    refine hEr0.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcard := card_crossingDirections_le hΛ.le N
    have hpow := CERW.Generic.Martingale.pow_mul_rpow_neg_le
      (by omega : 1 ≤ N) (d + 3) p
    calc Cr * (Q.card : ℝ) * ((N : ℝ) + 1) ^ 2 *
          (N : ℝ) ^ (-(p + (d + 3 : ℕ)))
        ≤ Cr * ((normMax Ψ + 2) * 3 ^ d * ((N : ℝ) + 1) ^ (d + 1)) *
          ((N : ℝ) + 1) ^ 2 * (N : ℝ) ^ (-(p + (d + 3 : ℕ))) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hCr.le)
              (by positivity)) (by positivity)
      _ = (Cr * (normMax Ψ + 2) * 3 ^ d) *
          (((N : ℝ) + 1) ^ (d + 3) * (N : ℝ) ^ (-(p + (d + 3 : ℕ)))) := by
        have heq : ((N : ℝ) + 1) ^ (d + 3) =
            ((N : ℝ) + 1) ^ (d + 1) * ((N : ℝ) + 1) ^ 2 := by
          rw [show d + 3 = (d + 1) + 2 by omega, pow_add]
        rw [heq]
        ring
      _ ≤ (Cr * (normMax Ψ + 2) * 3 ^ d) * (2 ^ (d + 3) * (N : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = Cf * (N : ℝ) ^ (-p) := by dsimp [Cf]; ring
  have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by rw [ae_iff]; exact hX.start
  have hs := ae_all_iff.mpr (CERW.Support.Drift.ae_sub_mem_unitSteps_drift hd1 hε.le hcoord hX)
  have hsub : {ω | ¬ DistanceCrossingBound Ψ (Cd + Cv + Cf) (X · ω) N} ≤ᵐ[μ]
      (Ev ∪ Er : Set Ω) := by
    filter_upwards [h0, hs] with ω hX0 hstep hbad
    by_cases hv : ω ∈ Ev
    · exact Or.inl hv
    by_cases hr : ω ∈ Er
    · exact Or.inr hr
    have hrGood := Classical.not_not.mp hr
    have hcross : DistanceCrossingBound Ψ Cd (X · ω) N := by
      apply hDet ξ hξ hξ0 (X · ω) hX0 hstep N hN
      · intro s t hst ht
        have h : ‖driftCompensated ε ξ (X · ω) t -
            driftCompensated ε ξ (X · ω) s‖ ≤ Cv * Real.sqrt (((t : ℝ) - s) * Real.log N) :=
          not_lt.mp (fun h => hv ⟨s, t, hst, ht, h⟩)
        exact h.trans (mul_le_mul_of_nonneg_right (by dsimp [C₁]; linarith)
          (Real.sqrt_nonneg _))
      · intro t ht q hq k hk
        exact (hrGood t ht q hq k hk).trans
          (mul_le_mul_of_nonneg_right (by dsimp [C₁]; linarith)
            (add_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg N)))
    exfalso
    apply hbad
    intro t ht a ha j hj
    exact (hcross t ht a ha j hj).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : Cd ≤ Cd + Cv + Cf) (by positivity))
        (Real.log_natCast_nonneg N))
  calc μ {ω | ¬ DistanceCrossingBound Ψ (Cd + Cv + Cf) (X · ω) N}
      ≤ μ (Ev ∪ Er) := measure_mono_ae hsub
    _ ≤ μ Ev + μ Er := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Cv * (N : ℝ) ^ (-p)) +
        ENNReal.ofReal (Cf * (N : ℝ) ^ (-p)) := add_le_add hEv hEr
    _ = ENNReal.ofReal ((Cv + Cf) * (N : ℝ) ^ (-p)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((Cd + Cv + Cf) * (N : ℝ) ^ (-p)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
