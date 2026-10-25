module

public import CERW.LimitShapes.EventConsequences
public import CERW.LimitShapes.Energy.SiteScales
public import CERW.Support.Outer.Radius.PathBounds

@[expose] public section

/-!
# Combining the deterministic fluctuation estimates

The inner and volume bounds of Proposition `prop:inner` combine with the outer and profile
bounds on the common event to give the predicate in Theorem `thm:fluctuations`.
-/

universe u

open CERW LatticeProb MeasureTheory Filter
open scoped symmDiff Pointwise

namespace CERW.LimitShapes.Curvature

open CERW.Support.Norm.ContactEvent
open CERW.Support.Norm.Section5Localization
open CERW.Support.Outer.Radius (radius)

/-- The four simultaneous conclusions in Theorem `thm:fluctuations`. -/
def fluctuation_good {d : ℕ} (ε C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  (if d = 2 then
      |innerRadius Y n - radius d ε n| ≤ C * Real.sqrt (radius d ε n * Real.log n) ∧
        maxRadius Y n - radius d ε n ≤
          C * Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)
    else
      |innerRadius Y n - radius d ε n| ≤ C * Real.log n ∧
        maxRadius Y n - radius d ε n ≤ C * Real.log n ^ ((d : ℝ) + 1)) ∧
  volume (((radius d ε n)⁻¹ • cellSet Y n) ∆
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
    ENNReal.ofReal (C * if d = 2 then Real.sqrt (Real.log n / radius d ε n)
      else Real.log n / radius d ε n) ∧
  ∀ x : Site d,
    |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
      C * if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)
        else Real.sqrt (radius d ε n * Real.log n)

/-- The Euclidean common-event scale is the radius in Theorem `thm:fluctuations`. -/
theorem euclidean_scale_eq_radius (d : ℕ) (ε : ℝ) (n : ℕ) :
    scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = radius d ε n := by
  simp only [scale, normBallVolume_norm, radius, unitBallVolume]

/-- The inner, outer, volume, and profile estimates hold with any common larger constant. -/
theorem fluctuation_good_of_bounds {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {Ci Co Cl C : ℝ} (hi : Ci ≤ C) (ho : Co ≤ C) (hl : Cl ≤ C)
    {Y : ℕ → Site d} {n : ℕ} (hn : 2 ≤ n)
    (hinner : InnerConclusion d ε Ci Y n)
    (houter : maxRadius Y n ≤ radius d ε n + Co *
      (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)
        else Real.log n ^ ((d : ℝ) + 1)))
    (hprofile : ∀ y : EuclideanSpace ℝ (Fin d),
      |cellLocalTime Y n y - 2 * d * ε * max (radius d ε n - ‖y‖) 0| ≤
        Cl * (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)
          else Real.sqrt (radius d ε n * Real.log n))) :
    fluctuation_good ε C Y n := by
  have hr := scale_pos (d := d) (n := n) (by omega)
    CERW.Support.Norm.EuclideanCoarse.isNorm_euclidean hε (by omega)
  have hlog : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have herr := hinner.1
  rw [mul_assoc, Energy.scale_mul_contactRate _ ε n hr,
    euclidean_scale_eq_radius] at herr
  have herr' : |innerRadius Y n - radius d ε n| ≤
      C * (if d = 2 then Real.sqrt (radius d ε n * Real.log n) else Real.log n) := by
    have ht : 0 ≤ (if d = 2 then Real.sqrt (radius d ε n * Real.log n)
        else Real.log n) := by split_ifs <;> positivity
    have he := herr.trans (mul_le_mul_of_nonneg_right hi ht)
    simpa only [normInnerRadius, innerRadius, euclidean_scale_eq_radius] using he
  have houte : maxRadius Y n - radius d ε n ≤ C *
      (if d = 2 then Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)
        else Real.log n ^ ((d : ℝ) + 1)) := by
    have ht : 0 ≤ (if d = 2 then
        Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)
        else Real.log n ^ ((d : ℝ) + 1)) := by
      split_ifs <;> positivity
    have he := mul_le_mul_of_nonneg_right ho ht
    linarith only [houter, he]
  refine ⟨?_, ?_, ?_⟩
  · split_ifs with hd2
    · simpa only [if_pos hd2, mul_assoc] using And.intro herr' houte
    · simpa only [if_neg hd2] using And.intro herr' houte
  · have hq : 0 ≤ contactRate d (fun v => ‖v‖) ε n := by
      unfold contactRate
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact div_nonneg hlog hr.le
    have hv := hinner.2.1.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hi hq))
    simpa only [contactRate, euclidean_scale_eq_radius] using hv
  · intro x
    have hx := hprofile (toSpace x)
    rw [cellLocalTime_of_mem_cell Y n (toSpace_mem_cell x), norm_toSpace] at hx
    have ht : 0 ≤ (if d = 2 then
        Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)
        else Real.sqrt (radius d ε n * Real.log n)) := by
      split_ifs <;> positivity
    exact hx.trans (mul_le_mul_of_nonneg_right hl ht)

end CERW.LimitShapes.Curvature
