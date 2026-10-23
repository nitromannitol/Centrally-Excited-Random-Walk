import CERW.LimitShapes.Curvature.AnnulusBound
import CERW.LimitShapes.Curvature.Continuity
import CERW.LimitShapes.Curvature.Harmonic
import CERW.LimitShapes.Curvature.Decay
import CERW.Generic.Harmonic.Exterior

/-! # Global curvature bound

The maximum principle extends the radial estimate of `eq:curvature-improved`
from the annulus to the inner ball and the exterior domain.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The global curvature estimate of `eq:curvature-improved`. -/
theorem curvatureIntegral_le_global {d : ℕ} (hd : 2 ≤ d)
    {ε b R K m delta : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hbR : b ≤ R) (hK : 1 ≤ K) (hRK : R ≤ K * b) (hm : 0 ≤ m) (hdelta : 0 ≤ delta)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R)
    (hmass : volume.real E ≤ m * b ^ (d - 1))
    (hpotential : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ →
      -delta ≤ CERW.potential d ε E y) :
    ∀ y : EuclideanSpace ℝ (Fin d), curvatureIntegral E y ≤
      (2 * K) ^ d * (m + CERW.unitBallVolume d / (2 * ε) * delta) := by
  let M := (2 * K) ^ d * (m + CERW.unitBallVolume d / (2 * ε) * delta)
  have hC : 0 ≤ CERW.unitBallVolume d / (2 * ε) * delta := by
    have := unitBallVolume_pos d
    positivity
  have hM : 0 ≤ M := mul_nonneg (pow_nonneg (by linarith) _) (add_nonneg hm hC)
  by_cases hd2 : d = 2
  · subst d
    intro y
    have hp := planar_curvatureIntegral_le hb hE hband (by simpa using hmass) y
    apply hp.trans
    have hpow : (1 : ℝ) ≤ (2 * K) ^ 2 := one_le_pow₀ (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hpow (add_nonneg hm hC)
    dsimp [M] at *
    linarith
  have hd3 : 3 ≤ d := by omega
  have hann := curvatureIntegral_le_on_annulus_ratio hd3 hε hb hbR hK hRK hm hdelta
    hE hband hmass hpotential
  have hcont := continuous_curvatureIntegral hd hb hbR hE hband
  have hharm := harmonicOnNhd_curvatureIntegral hd3 hb hbR hE hband
  have hclosure : ∀ v ∈ closure E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R := by
    apply closure_minimal (show E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ R} from hband)
    exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hinner : ∀ y ∈ closure (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b),
      curvatureIntegral E y ≤ M := by
    apply CERW.Generic.Harmonic.harmonic_le_of_boundary (by omega)
      Metric.isOpen_ball Metric.isBounded_ball hcont.continuousOn
    · intro y hy
      apply hharm y
      intro hyE
      have hnorm : ‖y‖ < b := by simpa only [Metric.mem_ball, dist_zero_right] using hy
      exact (not_lt_of_ge (hclosure y hyE).1) hnorm
    · intro y hy
      have heq : ‖y‖ = b := by
        have hs := Metric.frontier_ball_subset_sphere hy
        simpa only [Metric.mem_sphere, dist_zero_right] using hs
      exact hann y heq.ge (by rw [heq]; linarith)
  have hexterior : ∀ y : EuclideanSpace ℝ (Fin d), 2 * R ≤ ‖y‖ →
      curvatureIntegral E y ≤ M := by
    apply CERW.Generic.Harmonic.harmonic_le_on_exterior (by omega)
      (by linarith : 0 < 2 * R) hcont
    · intro y hy
      apply hharm y
      intro hyE
      have := (hclosure y hyE).2
      change 2 * R < ‖y‖ at hy
      linarith
    · exact tendsto_curvatureIntegral_cobounded hd3 hb hbR hE hband
    · exact hM
    · intro y hy
      exact hann y (by rw [hy]; linarith) hy.le
  intro y
  by_cases hby : b ≤ ‖y‖
  · by_cases hyR : ‖y‖ ≤ 2 * R
    · exact hann y hby hyR
    · exact hexterior y (le_of_not_ge hyR)
  · apply hinner y
    apply subset_closure
    simpa only [Metric.mem_ball, dist_zero_right] using (lt_of_not_ge hby)

end CERW.LimitShapes.Curvature
