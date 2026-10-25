module

public import CERW.Support.Geometry.Bound
public import CERW.Support.Lower.BulkProfile
public import CERW.Support.Outer.Radius.InnerGeometry

@[expose] public section

/-!
# Bulk potential bounds from the excess set

The deterministic step of Proposition `prop:bulk-profile`: the excess outside an inner
ball is separated from bulk points, so its potential is bounded by its volume times
the kernel bound. Splitting off the ball then gives the bulk cone estimate.
-/

open MeasureTheory Topology

namespace CERW.LimitShapes

open CERW

variable {d : ℕ}

open private abs_potentialIntegrand_le_inv_pow inv_mul_pow_mul_pow
  mul_q_le error_scale_le
  from CERW.Support.Lower.BulkProfile

/-- A separated set contributes at most its volume times the inverse distance power. -/
theorem bulk_excess_potential_le (hd : 1 ≤ d) {ε ρ m : ℝ}
    (hε : 0 ≤ ε) (hρ : 0 < ρ) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hEb : Bornology.IsBounded E) {y : EuclideanSpace ℝ (Fin d)}
    (hfar : ∀ v ∈ E, ρ ≤ ‖v - y‖) (hm : (volume E).toReal ≤ m) :
    |potential d ε E y| ≤
      (2 * ε / unitBallVolume d) * ((ρ ^ (d - 1))⁻¹ * m) := by
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun v => inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) hEb.measure_lt_top
    (fun v hv => (Real.norm_eq_abs _).trans_le
      (abs_potentialIntegrand_le_inv_pow hd hρ (hfar v hv)))
  change |(2 * ε / unitBallVolume d) * _| ≤ _
  rw [abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  exact (Real.norm_eq_abs _ ▸ hi).trans
    (mul_le_mul_of_nonneg_left hm (by positivity))

/-- Points outside the inner ball are separated from bulk points by half the bulk gap. -/
theorem bulk_excess_separation {b r A q θ : ℝ} (hr : 0 ≤ r)
    (hbr : |b - r| ≤ A * r * q) (hsmall : A * q ≤ (1 - θ) / 2)
    {v y : EuclideanSpace ℝ (Fin d)} (hv : v ∉ Metric.ball 0 b)
    (hy : ‖y‖ ≤ θ * r) : (1 - θ) / 2 * r ≤ ‖v - y‖ := by
  have hb : r - A * r * q ≤ b := by
    have := (abs_le.mp hbr).1
    linarith
  have hvb : b ≤ ‖v‖ := not_lt.mp (fun h => hv (mem_ball_zero_iff.mpr h))
  have hg := mul_le_mul_of_nonneg_right hsmall hr
  have hn := norm_sub_norm_le v y
  nlinarith

/-- The excess-set proof of the bulk potential estimate in Proposition `prop:bulk-profile`.
The constant depends only on the dimension, drift, bulk fraction and input constants. -/
theorem bulk_potential_from_excess (hd : 2 ≤ d) {ε b r A V q θ : ℝ}
    (hε : 0 ≤ ε) (hb : 0 < b) (hr : 0 < r) (hθ : θ < 1)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) (hball : Metric.ball 0 b ⊆ D)
    (hbr : |b - r| ≤ A * r * q) (hsmall : A * q ≤ (1 - θ) / 2)
    (hvol : (volume (D \ Metric.ball 0 b)).toReal ≤ V * r ^ d * q)
    {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ ≤ θ * r) :
    |potential d ε D y - 2 * d * ε * (r - ‖y‖)| ≤
      ((2 * ε / unitBallVolume d) * (((1 - θ) / 2) ^ (d - 1))⁻¹ * V +
        2 * d * ε * A) * r * q := by
  have ht : 0 < (1 - θ) / 2 := by linarith
  have hfar : ∀ v ∈ D \ Metric.ball 0 b, (1 - θ) / 2 * r ≤ ‖v - y‖ := by
    intro v hv
    exact bulk_excess_separation hr.le hbr hsmall hv.2 hy
  have hE := bulk_excess_potential_le (by omega : 1 ≤ d) hε
    (mul_pos ht hr) (hDb.subset Set.sdiff_subset) hfar hvol
  have he : (((1 - θ) / 2 * r) ^ (d - 1))⁻¹ * (V * r ^ d * q) =
      (((1 - θ) / 2) ^ (d - 1))⁻¹ * V * r * q := by
    calc
      _ = V * q * ((((1 - θ) / 2 * r) ^ (d - 1))⁻¹ * r ^ d) := by ring
      _ = _ := by rw [inv_mul_pow_mul_pow (by omega : 1 ≤ d) ht hr]; ring
  rw [he] at hE
  have hyb : ‖y‖ ≤ b := by
    have hab := (abs_le.mp hbr).1
    have hs := mul_le_mul_of_nonneg_right hsmall hr.le
    have hgap : 0 ≤ (1 - θ) / 2 * r := (mul_pos ht hr).le
    nlinarith
  rw [CERW.Support.Outer.Radius.potential_split hd ε hD hDb hb hball y,
    max_eq_left (sub_nonneg.mpr hyb)]
  have hc : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  calc
    |2 * d * ε * (b - ‖y‖) + potential d ε (D \ Metric.ball 0 b) y -
        2 * d * ε * (r - ‖y‖)| =
        |potential d ε (D \ Metric.ball 0 b) y + 2 * d * ε * (b - r)| := by
          congr 1
          ring
    _ ≤ |potential d ε (D \ Metric.ball 0 b) y| + |2 * d * ε * (b - r)| :=
      abs_add_le _ _
    _ ≤ (2 * ε / unitBallVolume d) *
          ((((1 - θ) / 2) ^ (d - 1))⁻¹ * V * r * q) +
          2 * d * ε * (A * r * q) := by
      rw [abs_mul, abs_of_nonneg hc]
      exact add_le_add hE (mul_le_mul_of_nonneg_left hbr hc)
    _ = _ := by ring

/-- Adding the common-event local-time approximation to the deterministic bulk bound.
The scale domination hypothesis is the comparison of `r q` with the bulk error scale. -/
theorem bulk_profile_bound_from_excess (hd : 2 ≤ d) {ε b r A V q θ B S ℓ : ℝ}
    (hε : 0 ≤ ε) (hb : 0 < b) (hr : 0 < r) (hθ : θ < 1)
    (hA : 0 ≤ A) (hV : 0 ≤ V)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) (hball : Metric.ball 0 b ⊆ D)
    (hbr : |b - r| ≤ A * r * q) (hsmall : A * q ≤ (1 - θ) / 2)
    (hvol : (volume (D \ Metric.ball 0 b)).toReal ≤ V * r ^ d * q)
    {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ ≤ θ * r)
    (happrox : |ℓ - potential d ε D y| ≤ B * S) (hscale : r * q ≤ S) :
    |ℓ - 2 * d * ε * (r - ‖y‖)| ≤
      (B + (2 * ε / unitBallVolume d) * (((1 - θ) / 2) ^ (d - 1))⁻¹ * V +
        2 * d * ε * A) * S := by
  have hpot := bulk_potential_from_excess hd hε hb hr hθ hD hDb hball
    hbr hsmall hvol hy
  have hω := unitBallVolume_pos d
  have hC : 0 ≤ (2 * ε / unitBallVolume d) *
      (((1 - θ) / 2) ^ (d - 1))⁻¹ * V + 2 * d * ε * A := by
    have ht : 0 < (1 - θ) / 2 := by linarith
    positivity
  calc
    |ℓ - 2 * d * ε * (r - ‖y‖)| ≤
        |ℓ - potential d ε D y| +
          |potential d ε D y - 2 * d * ε * (r - ‖y‖)| := abs_sub_le _ _ _
    _ ≤ B * S + ((2 * ε / unitBallVolume d) *
          (((1 - θ) / 2) ^ (d - 1))⁻¹ * V + 2 * d * ε * A) * (r * q) := by
      simpa only [mul_assoc] using add_le_add happrox hpot
    _ ≤ B * S + ((2 * ε / unitBallVolume d) *
          (((1 - θ) / 2) ^ (d - 1))⁻¹ * V + 2 * d * ε * A) * S :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hscale hC)
    _ = _ := by ring

/-- The excess-set estimate gives the exact sitewise error scale of Proposition
`prop:bulk-profile`, once the inner radius, excess mass and approximation are controlled.
All constants are independent of the path and time. -/
theorem bulk_profile_at_site_from_excess (hd : 2 ≤ d) {ε r A V B Co θ : ℝ}
    (hε : 0 ≤ ε) (hr : 1 ≤ r) (hθ : θ < 1)
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hB : 0 ≤ B) (hCo : 0 ≤ Co)
    (X : ℕ → LatticeProb.Site d) (n : ℕ)
    (hL : 1 ≤ Real.log n) (hLr : Real.log n ≤ r)
    (hlog : Real.log (n + 2) ≤ 2 * Real.log n)
    (hb : 0 < innerRadius X n)
    (hin : |innerRadius X n - r| ≤
      A * r * (if d = 2 then Real.sqrt (Real.log n / r) else Real.log n / r))
    (hsmall : A * (if d = 2 then Real.sqrt (Real.log n / r) else Real.log n / r) ≤
      (1 - θ) / 2)
    (hvol : (volume (cellSet X n \ Metric.ball 0 (innerRadius X n))).toReal ≤
      V * r ^ d * (if d = 2 then Real.sqrt (Real.log n / r) else Real.log n / r))
    (hM : (maxLocalTime X n : ℝ) ≤ Co * r)
    (happrox : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ θ * r →
      |cellLocalTime X n y - potential d ε (cellSet X n) y| ≤ B *
        (if d = 2 then Real.sqrt (maxLocalTime X n) * Real.log (n + 2) +
          Real.log (n + 2)
        else Real.sqrt (maxLocalTime X n * Real.log (n + 2)) + Real.log (n + 2)))
    (y : LatticeProb.Site d) (hy : LatticeProb.euclidNorm y ≤ θ * r) :
    |(localTime X n y : ℝ) - 2 * d * ε * (r - LatticeProb.euclidNorm y)| ≤
      (B * (2 * Real.sqrt (2 * Co) + 2) +
        (2 * ε / unitBallVolume d) * (((1 - θ) / 2) ^ (d - 1))⁻¹ * V +
        2 * d * ε * A) *
      (if d = 2 then Real.sqrt r * Real.log n else Real.sqrt (r * Real.log n)) := by
  have hys : ‖toSpace y‖ ≤ θ * r := by rwa [norm_toSpace]
  have he := error_scale_le d (Nat.cast_nonneg (maxLocalTime X n)) hCo hM hr hL hLr
    (Real.log_nonneg (by norm_cast; omega : (1 : ℝ) ≤ n + 2)) hlog
  have hap := (happrox (toSpace y) hys).trans
    (mul_le_mul_of_nonneg_left he hB)
  rw [cellLocalTime_of_mem_cell X n (toSpace_mem_cell y)] at hap
  have hresult := bulk_profile_bound_from_excess
    (B := B * (2 * Real.sqrt (2 * Co) + 2)) (ℓ := (localTime X n y : ℝ))
    hd hε hb (by linarith) hθ hA hV
    (CERW.Support.Occupation.measurableSet_cellSet X n)
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ d) X n))
    (CERW.Support.Outer.Radius.ball_innerRadius_subset (by omega) X n)
    hin hsmall hvol hys (by simpa only [mul_assoc] using hap) (mul_q_le d hL hLr)
  simpa only [norm_toSpace] using hresult

end CERW.LimitShapes

