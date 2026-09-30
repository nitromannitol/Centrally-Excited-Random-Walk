import CERW.Support.Contact.Kernel
import CERW.Support.Geometry.Newton
import CERW.Support.Geometry.Bound

/-!
# The excess volume pushes the potential up at the contact point

The lower bound of `eq:contactbound`. Suppose `B(0, b) ⊆ D ⊆ B̄(0, S)` and `|y₀| = b`. Then
`U_D(y₀) = U_{B(0,b)}(y₀) + U_E(y₀)` with `E = D \ B(0, b)`, and `U_{B(0,b)}(y₀) = 0` by
`eq:ballpotential`. On `E`, `|v| ≥ |y₀|`, so the integrand is at least
`2^{1-d}|v|^{1-d} ≥ 2^{1-d}S^{1-d}`, except at the single point `v = y₀`. Hence
`U_D(y₀) ≥ (2ε/ω_d) 2^{1-d} S^{1-d} |E|`.
-/

namespace CERW.Support.Contact

open MeasureTheory CERW CERW.Support.Geometry

variable {d : ℕ}

/-- The lower bound of `eq:contactbound`: if `B(0, b) ⊆ D ⊆ B̄(0, S)` and `|y₀| = b`, then
`U_D(y₀) ≥ (2ε/ω_d) 2^{1-d} S^{1-d} |D \ B(0, b)|`. -/
theorem le_potential_contact (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) {b S : ℝ} (hb : 0 ≤ b)
    (hS : 0 < S) (hball : Metric.ball 0 b ⊆ D) (hDS : D ⊆ Metric.closedBall 0 S)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : ‖y₀‖ = b) :
    2 * ε / unitBallVolume d * ((2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ))) *
        (volume (D \ Metric.ball 0 b)).toReal ≤ potential d ε D y₀ := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have _ : (0 : ℝ) < S := hS
  have hcoef : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hDfin : volume D ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hDS) measure_closedBall_lt_top).ne
  have hEfin : volume (D \ Metric.ball 0 b) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (Set.sdiff_subset.trans hDS)) measure_closedBall_lt_top).ne
  have hEmeas : MeasurableSet (D \ Metric.ball 0 b) := hD.diff measurableSet_ball
  let F : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun v => inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d
  have hintD : IntegrableOn F D volume := integrableOn_potentialIntegrand hd1 hD hDfin y₀
  have hintBall : IntegrableOn F (Metric.ball 0 b) volume := hintD.mono_set hball
  have hintE : IntegrableOn F (D \ Metric.ball 0 b) volume := hintD.mono_set Set.sdiff_subset
  have hunion : Metric.ball 0 b ∪ (D \ Metric.ball 0 b) = D := Set.union_sdiff_cancel hball
  have hsplit : ∫ v in D, F v =
      (∫ v in Metric.ball 0 b, F v) + (∫ v in D \ Metric.ball 0 b, F v) := by
    conv_lhs => rw [← hunion]
    exact setIntegral_union Set.disjoint_sdiff_right hEmeas hintBall hintE
  have hballpot : potential d ε (Metric.ball 0 b) y₀ = 0 := by
    rcases eq_or_ne b 0 with hb0 | hb0
    · rw [hb0, Metric.ball_zero]
      unfold potential
      simp
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      rw [potential_ball hd ε hbpos y₀, hy₀]
      simp
  have hballint : (2 * ε / unitBallVolume d) * ∫ v in Metric.ball 0 b, F v = 0 := by
    have h3 : potential d ε (Metric.ball 0 b) y₀ =
        (2 * ε / unitBallVolume d) * ∫ v in Metric.ball 0 b, F v := rfl
    rw [← h3, hballpot]
  have hpotD : potential d ε D y₀ =
      (2 * ε / unitBallVolume d) * ∫ v in D \ Metric.ball 0 b, F v := by
    have h1 : potential d ε D y₀ =
        (2 * ε / unitBallVolume d) * ((∫ v in Metric.ball 0 b, F v) +
          (∫ v in D \ Metric.ball 0 b, F v)) := by
      change (2 * ε / unitBallVolume d) * (∫ v in D, F v) = _
      rw [hsplit]
    rw [h1, mul_add, hballint, zero_add]
  have hy₀ae : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ≠ y₀ := by
    rw [ae_iff]
    simp
  have hc_le : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      v ∈ D \ Metric.ball 0 b → (2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ)) ≤ F v := by
    filter_upwards [hy₀ae] with v hvy hvE
    have hvD : v ∈ D := hvE.1
    have hvnb : v ∉ Metric.ball 0 b := hvE.2
    have hyv : ‖y₀‖ ≤ ‖v‖ := by
      have h1 : b ≤ ‖v‖ := by
        have := not_lt.mp (fun h => hvnb (Metric.mem_ball.mpr h))
        simpa [dist_zero_right] using this
      simpa [hy₀] using h1
    have hvS : ‖v‖ ≤ S := by
      have h1 : dist v 0 ≤ S := Metric.mem_closedBall.mp (hDS hvD)
      simpa [dist_zero_right] using h1
    have hvne0 : v ≠ 0 := by
      intro hv0
      have hy00 : ‖y₀‖ = 0 := by
        have h : ‖y₀‖ ≤ 0 := by simpa [hv0] using hyv
        exact le_antisymm h (norm_nonneg y₀)
      exact hvy (hv0.trans (norm_eq_zero.mp hy00).symm)
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne0
    have hcontact := rpow_le_inner_unitDir_div (d := d) hd hyv hvy
    have hmonoR : (2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ)) ≤
        (2 : ℝ) ^ (1 - (d : ℝ)) * ‖v‖ ^ (1 - (d : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos hvpos hvS (by linarith)
    exact hmonoR.trans hcontact
  have hconstInt : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) =>
      (2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ))) (D \ Metric.ball 0 b) volume :=
    integrableOn_const hEfin
  have hmono : (2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ)) *
      (volume (D \ Metric.ball 0 b)).toReal ≤ ∫ v in D \ Metric.ball 0 b, F v := by
    have hle := setIntegral_mono_on_ae hconstInt hintE hEmeas hc_le
    have hconstval : ∫ v in D \ Metric.ball 0 b,
        (fun _ : EuclideanSpace ℝ (Fin d) => (2 : ℝ) ^ (1 - (d : ℝ)) *
          S ^ (1 - (d : ℝ))) v =
        (2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ)) *
          (volume (D \ Metric.ball 0 b)).toReal := by
      rw [setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
    rwa [hconstval] at hle
  calc 2 * ε / unitBallVolume d * ((2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ))) *
        (volume (D \ Metric.ball 0 b)).toReal
      = (2 * ε / unitBallVolume d) *
        ((2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ)) *
          (volume (D \ Metric.ball 0 b)).toReal) := by ring
    _ ≤ (2 * ε / unitBallVolume d) * ∫ v in D \ Metric.ball 0 b, F v :=
        mul_le_mul_of_nonneg_left hmono hcoef
    _ = potential d ε D y₀ := hpotD.symm

end CERW.Support.Contact
