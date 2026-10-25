module

public import CERW.LimitShapes.Frozen.LimitShape
public import CERW.LimitShapes.Frozen.NormCoarseBounds
public import CERW.Support.Main.LimitShape
public import CERW.Support.Drift.Bridge
public import CERW.Support.Norm.Section5Localization
public import CERW.Support.Lower.ExpDeviationAE
public import CERW.Support.Lower.SharpWidth
public import CERW.Generic.Martingale.LilAssembly.StoutLower
public import CERW.Support.Stout

@[expose] public section

/-!
# Planar width lower bounds

The polynomial and iterated-logarithm lower bounds of Theorem `thm:sharp` (iv)
use the current limit shape, the outer radius bound of Proposition `prop:coarse` and the
compensated-position martingale kernels.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.PlanarLower

/-- Proposition `prop:coarse` for the Euclidean norm bounds the planar outer radius by a
multiple of `n^(1/3)`. -/
theorem coarse_radius_from_norm_coarse_bounds :
    CERW.Support.Lower.planar_coarse_radius.{u} := by
  intro ε hε0 hεd p hp
  obtain ⟨hNorm, hSubgrad, hZero, hElliptic⟩ :=
    CERW.Support.Main.euclidean_norm_hypotheses (d := 2) hεd
  obtain ⟨c, C, -, hC, h⟩ :=
    CERW.LimitShapes.norm_coarse_bounds.{u} (d := 2) le_rfl _ hNorm ε hε0 hElliptic p hp
  set K : ℝ := (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) with hK_def
  have hK : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C * K + C, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hDrift := (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX
  have h' := h (fun z => CERW.unitDir (CERW.toSpace z)) hSubgrad hZero μ X hDrift n hn
  have hpow : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hCK : 0 ≤ C * K * (n : ℝ) ^ (-p) := mul_nonneg (mul_pos hC hK).le hpow
  refine le_trans (measure_mono ?_) (h'.trans (ENNReal.ofReal_le_ofReal (by nlinarith)))
  intro ω hω hcon
  have h6 := hcon.2.2.2.2.2
  dsimp only at h6
  rw [CERW.Support.Norm.Section5Localization.normBallVolume_norm, CERW.unitBallVolume,
    CERW.Support.Lower.planar_radius_eq hε0 n] at h6
  have hq : 0 ≤ ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := sq_nonneg _
  have hle : C * (K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) ≤
      (C * K + C) * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := by nlinarith
  exact absurd (h6.trans hle) (not_le.mpr hω)

/-- The polynomial and iterated-logarithm width bounds of Theorem `thm:sharp` (iv). -/
theorem sharp_width_lower_from_norm_shape {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    (∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let E : Set Ω := {ω | c * Real.sqrt (r n * Real.log n)
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n}
        MeasurableSet E ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ E) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
        (Real.sqrt (Real.pi / (3 * ε)) - δ) * Real.sqrt (r n * Real.log (Real.log n))
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n) := by
  intro ωd ε hε0 hε1 r
  exact CERW.Support.Lower.sharp_width_of @CERW.LimitShapes.limit_shape
    @CERW.Support.Lower.exp_deviation_ae_upTo coarse_radius_from_norm_coarse_bounds hd
    (CERW.Support.stoutLIL_full CERW.Generic.Martingale.LilAssembly.stout_lower) ε hε0 hε1

end CERW.LimitShapes.PlanarLower
