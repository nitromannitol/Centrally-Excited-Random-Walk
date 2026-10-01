import CERW.Support.Geometry.Bound

/-!
# Comparing a set with a ball

Facts used whenever a bounded measurable set `D` is compared with the ball `B(0, r)`:

* The measure of the symmetric difference behaves well under dilation: `|S ∆ B(0, r)| =
  r^d |(r⁻¹ S) ∆ B(0, 1)|`. A bound on the symmetric difference of the rescaled set with the unit
  ball therefore gives a bound on `|S ∆ B(0, r)|` of the form `r^d m`.
* The integral of a function over `D` differs from its integral over `B(0, r)` by at most
  `M |D ∆ B(0, r)|` when the function is bounded by `M` on `D ∆ B(0, r)`.
* Applied to the integrand of the potential `U_D(z)`, corrected by a function `h` integrable on
  both sets, this compares the potential of `D` with the potential of the ball.

The file also records the elementary identity `(x^{1/(d+1)})^{d+1} = x`, used to pass between the
radius of the model and the number of steps.
-/

namespace CERW.Support.Geometry

open MeasureTheory
open scoped symmDiff Pointwise

variable {d : ℕ}

/-- For measurable sets of finite volume and a function integrable on both, the difference of
the integrals over `D` and over `B` is at most `M |D ∆ B|` if `|g| ≤ M` on `D ∆ B`. -/
lemma abs_setIntegral_sub_le {g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D B : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hB : MeasurableSet B)
    (hDfin : volume D ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hgD : IntegrableOn g D) (hgB : IntegrableOn g B) {M : ℝ} (hM : ∀ v ∈ D ∆ B, |g v| ≤ M) :
    |(∫ v in D, g v) - ∫ v in B, g v| ≤ M * (volume (D ∆ B)).toReal := by
  have h1 := integral_inter_add_sdiff hB hgD
  have h2 := integral_inter_add_sdiff hD hgB
  rw [Set.inter_comm B D] at h2
  have hdiff : (∫ v in D, g v) - ∫ v in B, g v =
      (∫ v in D \ B, g v) - ∫ v in B \ D, g v := by linarith
  have hfin1 : volume (D \ B) < ⊤ := (measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top
  have hfin2 : volume (B \ D) < ⊤ := (measure_mono Set.sdiff_subset).trans_lt hBfin.lt_top
  have hb1 := norm_setIntegral_le_of_norm_le_const (f := g) (C := M) hfin1
    (fun v hv => by rw [Real.norm_eq_abs]; exact hM v (Or.inl hv))
  have hb2 := norm_setIntegral_le_of_norm_le_const (f := g) (C := M) hfin2
    (fun v hv => by rw [Real.norm_eq_abs]; exact hM v (Or.inr hv))
  rw [Real.norm_eq_abs] at hb1 hb2
  have hsd : (volume (D ∆ B)).toReal = (volume (D \ B)).toReal + (volume (B \ D)).toReal := by
    rw [measure_symmDiff_eq hD.nullMeasurableSet hB.nullMeasurableSet,
      ENNReal.toReal_add hfin1.ne hfin2.ne]
  rw [hdiff, hsd]
  calc |(∫ v in D \ B, g v) - ∫ v in B \ D, g v|
      ≤ |∫ v in D \ B, g v| + |∫ v in B \ D, g v| := abs_sub _ _
    _ ≤ M * (volume (D \ B)).toReal + M * (volume (B \ D)).toReal := add_le_add hb1 hb2
    _ = M * ((volume (D \ B)).toReal + (volume (B \ D)).toReal) := by ring

/-- Scaling by `r` carries `(r⁻¹ • S) ∆ B(0, 1)` to `S ∆ B(0, r)`, so the volumes differ by
`r^d`. -/
lemma volume_symmDiff_ball {r : ℝ} (hr : 0 < r) (S : Set (EuclideanSpace ℝ (Fin d))) :
    volume (S ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) =
      ENNReal.ofReal (r ^ d) *
        volume ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have h : S ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r =
      r • ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [Set.smul_set_symmDiff₀ hr.ne', smul_inv_smul₀ hr.ne', smul_ball hr.ne', smul_zero,
      Real.norm_eq_abs, abs_of_pos hr, mul_one]
  rw [h, Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_pos (pow_pos hr d)]

/-- The volume of `S ∆ B(0, r)` is at most `r^d m` when that of `(r⁻¹ • S) ∆ B(0, 1)` is at
most `m`. -/
lemma toReal_volume_symmDiff_le {r m : ℝ} (hr : 0 < r) (hm0 : 0 ≤ m)
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hm : volume ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ENNReal.ofReal m) :
    (volume (S ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal ≤ r ^ d * m := by
  rw [volume_symmDiff_ball hr S]
  have h : ENNReal.ofReal (r ^ d) *
      volume ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ENNReal.ofReal (r ^ d) * ENNReal.ofReal m := by gcongr
  rw [← ENNReal.ofReal_mul (pow_pos hr d).le] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

/-- Let `D` be bounded and measurable, `h` a function integrable on `D` and on `B(0, r)`, and
suppose the integrand of the potential at `z`, corrected by `h`, is at most `M` in absolute value
on `D ∆ B(0, r)`. Then `U_D(z) - U_{B(0, r)}(z)` equals `(2ε / ω_d)` times the difference of the
integrals of `h` over `D` and over `B(0, r)`, up to an error at most
`(2ε / ω_d) M |D ∆ B(0, r)|`. -/
theorem abs_potential_sub_ball_sub_le (hd : 2 ≤ d) {ε r M : ℝ} (hε : 0 ≤ ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    {z : EuclideanSpace ℝ (Fin d)} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hhD : IntegrableOn h D) (hhB : IntegrableOn h (Metric.ball 0 r))
    (hM : ∀ v ∈ D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
      |inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d - h v| ≤ M) :
    |potential d ε D z - potential d ε (Metric.ball 0 r) z -
        2 * ε / unitBallVolume d *
          ((∫ v in D, h v) - ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, h v)| ≤
      2 * ε / unitBallVolume d *
        (M * (volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal) := by
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hBm : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) :=
    Metric.isOpen_ball.measurableSet
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hBfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hfD := integrableOn_potentialIntegrand (d := d) (by omega) hD hDfin z
  have hfB := integrableOn_potentialIntegrand (d := d) (by omega) hBm hBfin z
  have key := abs_setIntegral_sub_le
    (g := fun v => inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d - h v)
    hD hBm hDfin hBfin (hfD.sub hhD) (hfB.sub hhB) hM
  rw [integral_sub hfD hhD, integral_sub hfB hhB] at key
  have hLHS : potential d ε D z - potential d ε (Metric.ball 0 r) z -
        2 * ε / unitBallVolume d *
          ((∫ v in D, h v) - ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, h v) =
      2 * ε / unitBallVolume d *
        (((∫ v in D, inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d) - ∫ v in D, h v) -
          ((∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
              inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d) -
            ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, h v)) := by
    unfold potential
    ring
  rw [hLHS, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left key hc

/-- Let `D` be bounded and measurable, and suppose the integrand of the potential at `z` is at
most `M` in absolute value on `D ∆ B(0, r)`. Then
`|U_D(z) - U_{B(0, r)}(z)| ≤ (2ε / ω_d) M |D ∆ B(0, r)|`. -/
theorem abs_potential_sub_ball_le_of_integrand_le (hd : 2 ≤ d) {ε r M : ℝ} (hε : 0 ≤ ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    {z : EuclideanSpace ℝ (Fin d)}
    (hM : ∀ v ∈ D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
      |inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d| ≤ M) :
    |potential d ε D z - potential d ε (Metric.ball 0 r) z| ≤
      2 * ε / unitBallVolume d *
        (M * (volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal) := by
  have h := abs_potential_sub_ball_sub_le hd hε hD hDb (z := z) (r := r) (h := fun _ => 0)
    integrableOn_zero integrableOn_zero (fun v hv => by simpa only [sub_zero] using hM v hv)
  simpa only [integral_zero, sub_self, mul_zero, sub_zero] using h

/-- The `d + 1`-st power of `x ^ (1 / (d + 1))` is `x`. -/
lemma rpow_inv_succ_pow (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have h : (1 : ℝ) / (d + 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [h, Real.rpow_one]

end CERW.Support.Geometry
