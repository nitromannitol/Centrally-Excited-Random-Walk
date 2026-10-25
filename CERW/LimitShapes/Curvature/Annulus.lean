module

public import CERW.LimitShapes.Curvature.RadialIntegral
public import CERW.LimitShapes.Curvature.FarPoint
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Curvature bounds on radial bands

The planar curvature kernel is bounded directly by the inverse inner radius.
The higher dimensional estimate uses the integrated radial identity in
`eq:curvature-improved`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- In dimension two, the mass bound directly controls the curvature integral. -/
theorem planar_curvatureIntegral_le {b R m : ℝ} (hb : 0 < b)
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R)
    (hmass : volume.real E ≤ m * b) :
    ∀ y : EuclideanSpace ℝ (Fin 2), curvatureIntegral E y ≤ m := by
  intro y
  have hfin := band_measure_ne_top (fun v hv => (hband v hv).2)
  have hi := integrableOn_curvature (by decide : 2 ≤ 2) hb hE hband y
  have hle := integral_mono_ae hi (integrableOn_const (C := 1 / b) hfin) (by
    apply ae_restrict_of_forall_mem hE
    intro v hv
    simp only [Nat.cast_ofNat, sub_self, Real.rpow_zero]
    exact one_div_le_one_div_of_le hb (hband v hv).1)
  have hbound : curvatureIntegral E y ≤ volume.real E / b := by
    simpa only [curvatureIntegral, integral_const, smul_eq_mul, Measure.real,
      Measure.restrict_apply_univ, mul_one_div] using hle
  exact hbound.trans ((div_le_iff₀ hb).mpr hmass)

/-- The radial identity and a potential lower bound control the annular curvature. -/
theorem curvatureIntegral_le_on_annulus {d : ℕ} (hd : 3 ≤ d)
    {ε b R m delta : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hbR : b ≤ R) (hRb : R ≤ 2 * b) (hm : 0 ≤ m) (hdelta : 0 ≤ delta)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R)
    (hmass : volume.real E ≤ m * b ^ (d - 1))
    (hpotential : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ →
      -delta ≤ CERW.potential d ε E y) :
    ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ 2 * R →
      curvatureIntegral E y ≤ (4 : ℝ) ^ d *
        (m + CERW.unitBallVolume d / (2 * ε) * delta) := by
  intro y hby hyR
  have ht : 0 < ‖y‖ := hb.trans_le hby
  have hR : 0 < R := hb.trans_le hbR
  let u := unitDir y
  let C := unitBallVolume d / (2 * ε) * delta
  have hω := unitBallVolume_pos d
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hu : ‖u‖ = 1 := by
    dsimp [u, unitDir]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']
  have hy : ‖y‖ • u = y := by
    dsimp [u, unitDir]
    rw [smul_inv_smul₀ ht.ne']
  have hfin := band_measure_ne_top (fun v hv => (hband v hv).2)
  have hend := curvatureIntegral_le_far_point hd hb hbR hE hband ((2 * R) • u)
    (by rw [norm_smul, hu, Real.norm_eq_abs, abs_of_pos (by positivity), mul_one])
  have hrpow : R ^ ((2 : ℝ) - d) = 1 / R ^ (d - 2) := by
    rw [show (2 : ℝ) - d = -((d - 2 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega : 2 ≤ d)]; push_cast; ring,
      Real.rpow_neg hR.le, Real.rpow_natCast, one_div]
  have hmass' : volume.real E ≤ m * b * R ^ (d - 2) := by
    calc
      _ ≤ m * b ^ (d - 1) := hmass
      _ = m * b * b ^ (d - 2) := by
        rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hb.le hbR _) (mul_nonneg hm hb.le)
  have hend' : curvatureIntegral E ((2 * R) • u) ≤ m := by
    apply hend.trans
    rw [hrpow]
    have : 0 < b * R ^ (d - 2) := by positivity
    have heq : volume.real E * (1 / R ^ (d - 2) / b) =
        volume.real E / (b * R ^ (d - 2)) := by ring
    rw [heq]
    apply (div_le_iff₀ this).mpr
    simpa only [mul_assoc] using hmass'
  have hid := weighted_radial_integral_identity hd hb hbR hE hband u hu ht hyR
  have hi := (integrable_weighted_radial_curvature_prod hd hE hfin u ht hyR).integral_prod_left
  have hi' : IntervalIntegrable (fun s : ℝ => s ^ (d - 3) *
      (∫ v in E, inner ℝ (unitDir v) (v - s • u) / ‖v - s • u‖ ^ d))
      volume ‖y‖ (2 * R) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hyR).mpr
    simpa only [IntegrableOn, integral_const_mul] using hi
  have hlower : ∀ s ∈ Set.Icc ‖y‖ (2 * R),
      -C * s ^ (d - 3) ≤ s ^ (d - 3) *
        (∫ v in E, inner ℝ (unitDir v) (v - s • u) / ‖v - s • u‖ ^ d) := by
    intro s hs
    have hs0 : 0 < s := ht.trans_le hs.1
    have hp := hpotential (s • u) (by
      rw [norm_smul, hu, Real.norm_eq_abs, abs_of_pos hs0, mul_one]
      exact hby.trans hs.1)
    have hω := unitBallVolume_pos d
    have hk : -C ≤ ∫ v in E,
        inner ℝ (unitDir v) (v - s • u) / ‖v - s • u‖ ^ d := by
      unfold potential at hp
      have hk' : -delta / (2 * ε / unitBallVolume d) ≤
          ∫ v in E, inner ℝ (unitDir v) (v - s • u) / ‖v - s • u‖ ^ d := by
        apply (div_le_iff₀ (show 0 < 2 * ε / unitBallVolume d by positivity)).mpr
        rw [mul_comm]
        exact hp
      calc
        -C = -delta / (2 * ε / unitBallVolume d) := by
          dsimp [C]
          field_simp
        _ ≤ _ := hk'
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hk (pow_nonneg hs0.le (d - 3))
  have hint := intervalIntegral.integral_mono_on hyR
    ((continuous_const.mul (continuous_id.pow (d - 3))).intervalIntegrable _ _) hi' hlower
  dsimp only [Pi.mul_apply, Pi.pow_apply, id_eq] at hint
  rw [intervalIntegral.integral_const_mul, integral_pow] at hint
  have hn : ((d - 3 : ℕ) : ℝ) + 1 = (d : ℝ) - 2 := by
    rw [Nat.cast_sub hd]
    norm_num
    ring
  rw [show d - 3 + 1 = d - 2 by omega, hn] at hint
  have hnpos : 0 < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hint' := mul_le_mul_of_nonneg_left hint hnpos.le
  have hweighted : ‖y‖ ^ (d - 2) * curvatureIntegral E y ≤
      (2 * R) ^ (d - 2) * (m + C) := by
    change (2 * R) ^ (d - 2) * curvatureIntegral E ((2 * R) • u) -
      ‖y‖ ^ (d - 2) * curvatureIntegral E (‖y‖ • u) = _ at hid
    rw [hy] at hid
    have hendmul := mul_le_mul_of_nonneg_left hend'
      (pow_nonneg (by positivity : 0 ≤ 2 * R) (d - 2))
    have hc := mul_nonneg hC (pow_nonneg ht.le (d - 2))
    field_simp at hint'
    nlinarith
  have hpow : (2 * R) ^ (d - 2) ≤ (4 : ℝ) ^ d * ‖y‖ ^ (d - 2) := by
    calc
      _ ≤ (4 * ‖y‖) ^ (d - 2) := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (4 : ℝ) ^ (d - 2) * ‖y‖ ^ (d - 2) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega))
        (pow_nonneg ht.le _)
  have hfinal := hweighted.trans (mul_le_mul_of_nonneg_right hpow (add_nonneg hm hC))
  apply (mul_le_mul_iff_right₀ (pow_pos ht (d - 2))).mp
  convert hfinal using 1; ring

end CERW.LimitShapes.Curvature
