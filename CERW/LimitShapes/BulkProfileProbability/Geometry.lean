module

public import CERW.LimitShapes.BulkProfile
public import CERW.Support.Contact.Volume

@[expose] public section

/-!
# Excess volume for the bulk profile

The radius and volume clauses of Theorem `thm:fluctuations` control the excess outside
its actual inner ball. This is the geometric input to Proposition `prop:bulk-profile`.
-/

open MeasureTheory
open scoped symmDiff Pointwise

namespace CERW.LimitShapes

open CERW
open private volume_ball_symmDiff from CERW.Support.Contact.Volume

/-- Radius error and symmetric difference control the volume outside the inner ball. -/
theorem bulk_excess_volume_le {d : ℕ} (hd : 1 ≤ d) {r b A q : ℝ}
    (hr : 0 < r) (hb : 0 ≤ b) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hsmall : A * q ≤ 1) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hbr : |b - r| ≤ A * r * q)
    (hvol : volume ((r⁻¹ • D) ∆ Metric.ball 0 1) ≤ ENNReal.ofReal (A * q)) :
    (volume (D \ Metric.ball 0 b)).toReal ≤
      (A + unitBallVolume d * A * d * 2 ^ (d - 1)) * r ^ d * q := by
  have hω := (unitBallVolume_pos d).le
  have hb2 : b ≤ 2 * r := by
    have := (abs_le.mp hbr).2
    have := mul_le_mul_of_nonneg_right hsmall hr.le
    nlinarith
  have hp : |b ^ d - r ^ d| ≤
      (A * r * q) * d * (2 * r) ^ (d - 1) := by
    apply (abs_pow_sub_pow_le b r d).trans
    have hm : max |b| |r| ≤ 2 * r := by
      rw [abs_of_nonneg hb, abs_of_pos hr]
      exact max_le hb2 (by linarith)
    gcongr
  have hv₁ := CERW.Support.Geometry.toReal_volume_symmDiff_le hr (mul_nonneg hA hq)
    (S := D) hvol
  have hv₂ : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ∆
      Metric.ball 0 r)).toReal ≤
      unitBallVolume d * ((A * r * q) * d * (2 * r) ^ (d - 1)) := by
    rw [volume_ball_symmDiff hd hb hr.le, ENNReal.toReal_ofReal (by positivity)]
    exact mul_le_mul_of_nonneg_left hp hω
  have hf₁ : volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) ≠ ⊤ := by
    rw [CERW.Support.Geometry.volume_symmDiff_ball hr D]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol)
  have hf₂ : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ∆
      Metric.ball 0 r) ≠ ⊤ := by
    rw [volume_ball_symmDiff hd hb hr.le]
    exact ENNReal.ofReal_ne_top
  have hs : volume (D \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) ≤
      volume (D ∆ Metric.ball 0 r) +
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ∆ Metric.ball 0 r) := by
    apply (measure_mono (μ := volume) (show D \ Metric.ball 0 b ⊆
      (D ∆ Metric.ball 0 r) ∪ (Metric.ball 0 b ∆ Metric.ball 0 r) from ?_)).trans
      (measure_union_le _ _)
    intro v hv
    by_cases hvr : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r
    · exact Or.inr (Set.mem_symmDiff.mpr (Or.inr ⟨hvr, hv.2⟩))
    · exact Or.inl (Set.mem_symmDiff.mpr (Or.inl ⟨hv.1, hvr⟩))
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf₁, hf₂⟩) hs
  rw [ENNReal.toReal_add hf₁ hf₂] at ht
  have he : r * r ^ (d - 1) = r ^ d := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  calc
    _ ≤ r ^ d * (A * q) +
        unitBallVolume d * ((A * r * q) * d * (2 * r) ^ (d - 1)) :=
      ht.trans (add_le_add hv₁ hv₂)
    _ = _ := by
      rw [mul_pow]
      calc
        _ = A * q * r ^ d +
            (unitBallVolume d * A * d * 2 ^ (d - 1) * q) *
              (r * r ^ (d - 1)) := by ring
        _ = _ := by rw [he]; ring

end CERW.LimitShapes
