module

public import CERW.LimitShapes.Curvature.CapBounds
public import CERW.LimitShapes.Curvature.CurvatureIntegralBound
public import CERW.LimitShapes.Curvature.NearFar

@[expose] public section

/-! # Positive potential on an annulus (`eq:positive-bound`) -/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- The cap mass and curvature bounds imply the positive potential bound on the annulus. -/
theorem exists_annulus_positive_bound {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (K M : ℝ) (hK : 1 ≤ K) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b w delta : ℝ), 0 < b → 1 ≤ w → w ≤ K * b → 1 ≤ delta →
      ∀ E : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet E →
        (∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w) →
        volume.real E ≤ M * delta * b ^ (d - 1) →
        (∀ y : EuclideanSpace ℝ (Fin d), curvatureIntegral E y ≤ M * delta) →
        (∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ →
          -M * delta ≤ CERW.potential d ε E y) →
      ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
        positivePotential d ε E y ≤
          C * ((delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) + delta) := by
  obtain ⟨L₀, hL₀, hcap⟩ := exists_cap_bound hd hε M hM
  obtain ⟨C₀, hC₀, hnear⟩ := exists_positivePotential_bound_of_cap hd hε K hK
  let L := L₀ + (K + 1) * M
  have hKM : 0 ≤ (K + 1) * M := by positivity
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := by linarith
  let S := L ^ ((1 : ℝ) / d) + L
  have hroot : 0 < L ^ ((1 : ℝ) / d) := Real.rpow_pos_of_pos hLpos _
  have hS : 0 < S := by dsimp [S]; positivity
  refine ⟨C₀ * S, mul_pos hC₀ hS, ?_⟩
  intro b w delta hb hw hwb hdelta E hE hband hmass hcurv hpot y hy hy'
  have hd0 : 0 ≤ delta := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hlam : 1 ≤ L * delta := by nlinarith
  have hc : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
      volume.real (E ∩ Metric.ball ((b + w) • u) t) ≤
        L * delta * t ^ (d - 1) := by
    intro u hu t ht
    apply (hcap b w delta hb hw hdelta E hE hband hmass hcurv hpot u hu t ht).trans
    have ht0 : 0 ≤ t := hw0.trans ht
    gcongr
    dsimp [L]
    linarith
  have hi : ∀ z : EuclideanSpace ℝ (Fin d),
      ∫ v in E, ‖v - z‖ ^ ((2 : ℝ) - d) ≤ L * delta * b := by
    intro z
    calc
      _ ≤ (b + w) * curvatureIntegral E z :=
        integral_rpow_le_radius_mul_curvature hd hb hE hband z
      _ ≤ (b + w) * (M * delta) :=
        mul_le_mul_of_nonneg_left (hcurv z) (by linarith)
      _ ≤ ((K + 1) * b) * (M * delta) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
      _ ≤ L * delta * b := by
        have hh : (K + 1) * M ≤ L := by dsimp [L]; linarith
        have := mul_le_mul_of_nonneg_right hh (mul_nonneg hd0 hb.le)
        nlinarith
  have hn := hnear b w (L * delta) hb hw hwb hlam E hE hband hc hi y hy hy'
  have heq : (L * delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) =
      L ^ ((1 : ℝ) / d) * (delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) := by
    rw [mul_assoc, Real.mul_rpow hLpos.le (by positivity)]
  rw [heq] at hn
  have hx : 0 ≤ (delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) := by positivity
  calc
    _ ≤ C₀ * (L ^ ((1 : ℝ) / d) *
        (delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) + L * delta) := hn
    _ ≤ (C₀ * S) * ((delta * w ^ (d - 1)) ^ ((1 : ℝ) / d) + delta) := by
      dsimp [S]
      nlinarith [mul_nonneg hroot.le hd0, mul_nonneg hLpos.le hx]

end CERW.LimitShapes.Curvature
