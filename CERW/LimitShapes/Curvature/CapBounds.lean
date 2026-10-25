module

public import CERW.LimitShapes.Curvature.CapMass

@[expose] public section

/-! # Uniform cap bounds from the outer potential (`eq:outer-cap-mass`) -/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The small cap calculation and total mass estimate give a uniform cap constant. -/
theorem exists_cap_bound {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (b w delta : ℝ), 0 < b → 1 ≤ w → 1 ≤ delta →
      ∀ E : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet E →
        (∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w) →
        volume.real E ≤ M * delta * b ^ (d - 1) →
        (∀ y : EuclideanSpace ℝ (Fin d), curvatureIntegral E y ≤ M * delta) →
        (∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ →
          -M * delta ≤ CERW.potential d ε E y) →
      ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
        volume.real (E ∩ Metric.ball ((b + w) • u) t) ≤ L * delta * t ^ (d - 1) := by
  have hω := unitBallVolume_pos d
  have hM0 : 0 ≤ M := by linarith
  let P : ℝ := (5 : ℝ) ^ d * (unitBallVolume d / (2 * ε) * M + M / 2)
  let Q : ℝ := M * (2 : ℝ) ^ (d - 1)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨1 + P + Q, by linarith, ?_⟩
  intro b w delta hb hw hdelta E hE hband hmass hcurv hpot u hu t ht
  have ht0 : 0 < t := by linarith
  have hd0 : 0 ≤ delta := by linarith
  by_cases hsmall : t ≤ b / 2
  · have hy : b ≤ ‖((b + w + 4 * t) • u)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hu, mul_one]
      linarith
    have hc := cap_measure_le_of_curvature hd (delta := M * delta)
      (F₀ := M * delta) hε hb (by linarith : b ≤ b + w)
      ht0 (by linarith : t ≤ (b + w) / 2) (mul_nonneg hM0 hd0)
      (mul_nonneg hM0 hd0) hE hband u hu (by simpa only [neg_mul] using hpot _ hy) (hcurv _)
    calc
      _ ≤ P * delta * t ^ (d - 1) := by dsimp [P]; nlinarith [hc]
      _ ≤ _ := by gcongr; linarith
  · have hb2 : b ≤ 2 * t := by linarith
    have hm : volume.real (E ∩ Metric.ball ((b + w) • u) t) ≤ volume.real E :=
      measureReal_mono Set.inter_subset_left
        (band_measure_ne_top (fun v hv => (hband v hv).2))
    calc
      _ ≤ M * delta * b ^ (d - 1) := hm.trans hmass
      _ ≤ M * delta * (2 * t) ^ (d - 1) := by gcongr
      _ = Q * delta * t ^ (d - 1) := by dsimp [Q]; rw [mul_pow]; ring
      _ ≤ _ := by gcongr; linarith

end CERW.LimitShapes.Curvature
