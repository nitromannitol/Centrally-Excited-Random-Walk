import CERW.Generic.Kernel.NewtonField
import CERW.Generic.Kernel.Integrable
import CERW.Generic.Lattice.Centered
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import CERW.Generic.Kernel.Modulus
import CERW.Support.Occupation.SiteArith

/-!
# Replacing kernel values by cell integrals

The second replacement in the proof of `eq:approx`. For a lattice target `y`, a finite set of
sites within distance `R'` of `y`, and directions `w_x` of norm at most `1`, replacing
`w_x · K(x - y)` by `∫_{C_x} w_x · K(v - y) dv` costs `O(log(R' + 2))` in total. For
`|x - y| ≥ 2√d`, the kernel varies by `O(|x - y|^{-d})` across `C_x` (`norm_newtonField_sub_le`).
The boundedly many nearer cells cost `O(1)` each, because `|K(x - y)| ≤ 1` at lattice points and
`|v - y|^{1-d}` is integrable near `y`.
-/

namespace CERW.Support.LocalTime

open MeasureTheory LatticeProb CERW CERW.Generic.Kernel CERW.Support.Occupation

variable {d : ℕ}

/-- The distance of two embedded sites is the Euclidean norm of their lattice difference. -/
private lemma norm_toSpace_sub (x y : Site d) :
    ‖toSpace x - toSpace y‖ = euclidNorm (x - y) := by
  rw [← toSpace_sub, norm_toSpace]

/-- A nonzero lattice site has Euclidean norm at least one. -/
private lemma one_le_euclidNorm_of_ne_zero {x : Site d} (hx : x ≠ 0) :
    1 ≤ euclidNorm x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    exact hx (funext fun i => by simpa using not_not.mp (not_exists.mp h i))
  have h1 : (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |x i| := Int.one_le_abs hi
    exact_mod_cast this
  exact h1.trans (CERW.Support.Law.abs_coord_le_euclidNorm x i)

/-- For `ρ ≥ 1`, `ρ^(-d) ≤ 2^d * (1 + ρ)^(-d)`. -/
private lemma rpow_neg_le_two_pow_mul {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ρ ^ (-(d : ℝ)) ≤ (2 : ℝ) ^ d * (1 + ρ) ^ (-(d : ℝ)) := by
  have hρpos : 0 < ρ := by linarith
  have hle : 1 + ρ ≤ 2 * ρ := by linarith
  have h1 : (2 * ρ) ^ (-(d : ℝ)) ≤ (1 + ρ) ^ (-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + ρ) hle
      (neg_nonpos.mpr (Nat.cast_nonneg d))
  have hmul : (2 * ρ) ^ (-(d : ℝ)) = (2 : ℝ) ^ (-(d : ℝ)) * ρ ^ (-(d : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hρpos.le]
  have hbase : (2 : ℝ) ^ (-(d : ℝ)) = ((2 : ℝ) ^ d)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have h2 : ((2 : ℝ) ^ d)⁻¹ * ρ ^ (-(d : ℝ)) ≤ (1 + ρ) ^ (-(d : ℝ)) := by
    rw [← hbase, ← hmul]
    exact h1
  calc ρ ^ (-(d : ℝ))
      = (2 : ℝ) ^ d * (((2 : ℝ) ^ d)⁻¹ * ρ ^ (-(d : ℝ))) := by
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d (by norm_num : (2 : ℝ) ≠ 0)), one_mul]
    _ ≤ (2 : ℝ) ^ d * (1 + ρ) ^ (-(d : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 h2pow_pos.le

/-- For fixed `w` and `z`, `v ↦ ⟪w, K(v - z)⟫` is measurable. -/
private lemma inner_newtonField_measurable (w : EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ w (newtonField (v - z))) := by
  have hcomp : Measurable (fun v : EuclideanSpace ℝ (Fin d) => newtonField (v - z)) :=
    measurable_newtonField.comp (measurable_id.sub measurable_const)
  have hinner : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      inner ℝ p.1 p.2) := continuous_inner.measurable
  exact hinner.comp (measurable_const.prodMk hcomp)

/-- For `‖w‖ ≤ 1`, `‖⟪w, K(v - z)⟫‖ ≤ ‖v - z‖^(1 - d)`. -/
private lemma norm_inner_newtonField_le (hd : 2 ≤ d) (w : EuclideanSpace ℝ (Fin d))
    (hw : ‖w‖ ≤ 1) (z : EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin d)) :
    ‖inner ℝ w (newtonField (v - z))‖ ≤ ‖v - z‖ ^ (1 - (d : ℝ)) := by
  calc ‖inner ℝ w (newtonField (v - z))‖
      ≤ ‖w‖ * ‖newtonField (v - z)‖ := norm_inner_le_norm _ _
    _ = ‖w‖ * ‖v - z‖ ^ (1 - (d : ℝ)) := by rw [norm_newtonField hd]
    _ ≤ 1 * ‖v - z‖ ^ (1 - (d : ℝ)) := by gcongr
    _ = ‖v - z‖ ^ (1 - (d : ℝ)) := by ring

/-- For `|x - y| < 2√d`, the cell replacement term at `x` is at most `1 + 3√d d ω_d`. -/
private lemma near_term_le (hd : 2 ≤ d)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ ≤ 1) (y : Site d) {x : Site d}
    (hnear : euclidNorm (x - y) < 2 * Real.sqrt d) :
    |inner ℝ w (newtonField (toSpace x - toSpace y)) -
        ∫ v in cell x, inner ℝ w (newtonField (v - toSpace y))|
      ≤ 1 + 3 * Real.sqrt d * ((d:ℝ) * unitBallVolume d) := by
  set δ : ℝ := Real.sqrt d with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; exact Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hρlt : euclidNorm (x - y) < 2 * δ := by rw [hδ]; exact hnear
  have hA : |inner ℝ w (newtonField (toSpace x - toSpace y))| ≤ 1 := by
    have h1 : |inner ℝ w (newtonField (toSpace x - toSpace y))|
        ≤ ‖w‖ * ‖newtonField (toSpace x - toSpace y)‖ := abs_real_inner_le_norm _ _
    have h2 : ‖newtonField (toSpace x - toSpace y)‖ ≤ 1 := by
      rw [norm_newtonField hd (toSpace x - toSpace y)]
      by_cases hb : toSpace x - toSpace y = 0
      · rw [hb, norm_zero, Real.zero_rpow]
        · norm_num
        · have : ((1:ℝ) - d) ≠ 0 := by
            have : (2:ℝ) ≤ d := by exact_mod_cast hd
            linarith
          exact this
      · have hxy : x - y ≠ 0 := by
          intro h
          apply hb
          have hh : toSpace (x - y) = toSpace 0 := congrArg toSpace h
          simpa [toSpace_sub, toSpace_zero] using hh
        have hρ1 : 1 ≤ euclidNorm (x - y) := one_le_euclidNorm_of_ne_zero hxy
        rw [norm_toSpace_sub x y]
        exact Real.rpow_le_one_of_one_le_of_nonpos hρ1 (by
          have : (2:ℝ) ≤ d := by exact_mod_cast hd
          linarith)
    calc |inner ℝ w (newtonField (toSpace x - toSpace y))|
        ≤ ‖w‖ * ‖newtonField (toSpace x - toSpace y)‖ := h1
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have hB : |∫ v in cell x, inner ℝ w (newtonField (v - toSpace y))|
      ≤ 3 * δ * ((d:ℝ) * unitBallVolume d) := by
    have h3δpos : 0 < 3 * δ := by positivity
    have hφball : IntegrableOn (fun v => ‖v - toSpace y‖ ^ (1 - (d:ℝ)))
        (Metric.ball (toSpace y) (3 * δ)) volume :=
      (integrableOn_ball_and_integral_eq (d := d) (by omega : 1 ≤ d) (toSpace y) h3δpos).1
    have hcellball : cell x ⊆ Metric.ball (toSpace y) (3 * δ) := by
      intro v hv
      rw [Metric.mem_ball, dist_eq_norm]
      have hvx := norm_sub_toSpace_le_of_mem_cell hv
      calc ‖v - toSpace y‖ = dist v (toSpace y) := by rw [dist_eq_norm]
        _ ≤ dist v (toSpace x) + dist (toSpace x) (toSpace y) := dist_triangle _ _ _
        _ = ‖v - toSpace x‖ + ‖toSpace x - toSpace y‖ := by rw [dist_eq_norm, dist_eq_norm]
        _ = ‖v - toSpace x‖ + euclidNorm (x - y) := by rw [norm_toSpace_sub]
        _ ≤ δ / 2 + euclidNorm (x - y) := by linarith
        _ < 3 * δ := by linarith
    have hφcell : IntegrableOn (fun v => ‖v - toSpace y‖ ^ (1 - (d:ℝ))) (cell x) volume :=
      hφball.mono_set hcellball
    have hpoint : ∀ v ∈ cell x, ‖inner ℝ w (newtonField (v - toSpace y))‖
        ≤ ‖v - toSpace y‖ ^ (1 - (d:ℝ)) :=
      fun v _ => norm_inner_newtonField_le hd w hw (toSpace y) v
    have h1 : |∫ v in cell x, inner ℝ w (newtonField (v - toSpace y))|
        ≤ ∫ v in cell x, ‖inner ℝ w (newtonField (v - toSpace y))‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    have h2 : ∫ v in cell x, ‖inner ℝ w (newtonField (v - toSpace y))‖
        ≤ ∫ v in cell x, ‖v - toSpace y‖ ^ (1 - (d:ℝ)) :=
      setIntegral_mono_of_nonneg (fun v _ => norm_nonneg _) hpoint hφcell
    have h3 : ∫ v in cell x, ‖v - toSpace y‖ ^ (1 - (d:ℝ))
        ≤ ∫ v in Metric.ball (toSpace y) (3 * δ), ‖v - toSpace y‖ ^ (1 - (d:ℝ)) :=
      setIntegral_mono_set hφball
        (ae_of_all _ (fun v => Real.rpow_nonneg (norm_nonneg _) _))
        (ae_of_all _ (fun v hv => hcellball hv))
    have h4 : ∫ v in Metric.ball (toSpace y) (3 * δ), ‖v - toSpace y‖ ^ (1 - (d:ℝ))
        = (d:ℝ) * unitBallVolume d * (3 * δ) :=
      (integrableOn_ball_and_integral_eq (d := d) (by omega : 1 ≤ d) (toSpace y) h3δpos).2
    calc |∫ v in cell x, inner ℝ w (newtonField (v - toSpace y))|
        ≤ ∫ v in cell x, ‖inner ℝ w (newtonField (v - toSpace y))‖ := h1
      _ ≤ ∫ v in cell x, ‖v - toSpace y‖ ^ (1 - (d:ℝ)) := h2
      _ ≤ ∫ v in Metric.ball (toSpace y) (3 * δ), ‖v - toSpace y‖ ^ (1 - (d:ℝ)) := h3
      _ = (d:ℝ) * unitBallVolume d * (3 * δ) := h4
      _ = 3 * δ * ((d:ℝ) * unitBallVolume d) := by ring
  calc |inner ℝ w (newtonField (toSpace x - toSpace y)) -
        ∫ v in cell x, inner ℝ w (newtonField (v - toSpace y))|
      ≤ |inner ℝ w (newtonField (toSpace x - toSpace y))|
        + |∫ v in cell x, inner ℝ w (newtonField (v - toSpace y))| := by
        rw [abs_sub_le_iff]
        constructor <;> nlinarith [le_abs_self (inner ℝ w (newtonField (toSpace x - toSpace y))),
          neg_abs_le (inner ℝ w (newtonField (toSpace x - toSpace y))),
          le_abs_self (∫ v in cell x, inner ℝ w (newtonField (v - toSpace y))),
          neg_abs_le (∫ v in cell x, inner ℝ w (newtonField (v - toSpace y)))]
    _ ≤ 1 + 3 * δ * ((d:ℝ) * unitBallVolume d) := by linarith
    _ = 1 + 3 * Real.sqrt d * ((d:ℝ) * unitBallVolume d) := by rw [hδ]

/-- For `2√d ≤ |x - y|`, the cell replacement term at `x` is at most
`(2^d + 2d 3^(d-1)) (√d/2) |x - y|^(-d)`. -/
private lemma far_term_le (hd : 2 ≤ d)
    (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ ≤ 1) (y : Site d) {x : Site d}
    (hfar : 2 * Real.sqrt d ≤ euclidNorm (x - y)) :
    |inner ℝ w (newtonField (toSpace x - toSpace y)) -
        ∫ v in cell x, inner ℝ w (newtonField (v - toSpace y))|
      ≤ ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (Real.sqrt d / 2)
          * (euclidNorm (x - y)) ^ (-(d:ℝ)) := by
  set δ : ℝ := Real.sqrt d with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; exact Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  set ρ : ℝ := euclidNorm (x - y) with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith [hfar, hδpos]
  have hb_norm : ‖toSpace x - toSpace y‖ = ρ := by rw [norm_toSpace_sub, hρ]
  have hφball : IntegrableOn (fun v => ‖v - toSpace y‖ ^ (1 - (d:ℝ)))
      (Metric.ball (toSpace y) (ρ + δ + 1)) volume :=
    (integrableOn_ball_and_integral_eq (d := d) (by omega : 1 ≤ d) (toSpace y) (by positivity)).1
  have hcell_sub : cell x ⊆ Metric.ball (toSpace y) (ρ + δ + 1) := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm]
    have hvx := norm_sub_toSpace_le_of_mem_cell hv
    calc ‖v - toSpace y‖ = dist v (toSpace y) := by rw [dist_eq_norm]
      _ ≤ dist v (toSpace x) + dist (toSpace x) (toSpace y) := dist_triangle _ _ _
      _ = ‖v - toSpace x‖ + ‖toSpace x - toSpace y‖ := by rw [dist_eq_norm, dist_eq_norm]
      _ = ‖v - toSpace x‖ + ρ := by rw [hb_norm]
      _ ≤ δ / 2 + ρ := by linarith
      _ < ρ + δ + 1 := by linarith [hδpos]
  have hφcell : IntegrableOn (fun v => ‖v - toSpace y‖ ^ (1 - (d:ℝ))) (cell x) volume :=
    hφball.mono_set hcell_sub
  have hg_int : IntegrableOn (fun v => inner ℝ w (newtonField (v - toSpace y)))
      (cell x) volume :=
    Integrable.mono' hφcell (inner_newtonField_measurable w (toSpace y)).aestronglyMeasurable
      (ae_of_all _ (fun v => norm_inner_newtonField_le hd w hw (toSpace y) v))
  have hc_int : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) =>
      inner ℝ w (newtonField (toSpace x - toSpace y))) (cell x) volume :=
    integrableOn_const (by rw [volume_cell]; exact ENNReal.one_ne_top)
  have hconst : ∫ v in cell x, inner ℝ w (newtonField (toSpace x - toSpace y))
      = inner ℝ w (newtonField (toSpace x - toSpace y)) := by
    rw [setIntegral_const, Measure.real, volume_cell x]; simp
  have heq : inner ℝ w (newtonField (toSpace x - toSpace y)) -
        ∫ v in cell x, inner ℝ w (newtonField (v - toSpace y))
      = ∫ v in cell x,
          inner ℝ w (newtonField (toSpace x - toSpace y) - newtonField (v - toSpace y)) := by
    rw [← hconst, ← integral_sub hc_int hg_int]
    refine setIntegral_congr_fun (measurableSet_cell x) (fun v _ => ?_)
    rw [inner_sub_right]
  rw [heq, ← Real.norm_eq_abs]
  have hpoint : ∀ v ∈ cell x,
      ‖inner ℝ w (newtonField (toSpace x - toSpace y) - newtonField (v - toSpace y))‖
        ≤ ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (δ/2) / ρ^d := by
    intro v hv
    have hvx : ‖v - toSpace x‖ ≤ δ / 2 := by
      rw [hδ]; exact norm_sub_toSpace_le_of_mem_cell hv
    have hdist : (v - toSpace y) - (toSpace x - toSpace y) = v - toSpace x := by abel
    have hcond : 2 * ‖(v - toSpace y) - (toSpace x - toSpace y)‖ ≤ ‖toSpace x - toSpace y‖ := by
      rw [hdist, hb_norm]
      nlinarith [hvx, hfar, hδpos]
    have hnf := norm_newtonField_sub_le (a := v - toSpace y) (b := toSpace x - toSpace y) hcond
    have hstep : ‖newtonField (toSpace x - toSpace y) - newtonField (v - toSpace y)‖
        ≤ ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (δ/2) / ρ^d := by
      rw [norm_sub_rev]
      calc ‖newtonField (v - toSpace y) - newtonField (toSpace x - toSpace y)‖
          ≤ ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * ‖(v - toSpace y) - (toSpace x - toSpace y)‖
              / ‖toSpace x - toSpace y‖ ^ d := hnf
        _ = ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * ‖v - toSpace x‖ / ρ ^ d := by rw [hdist, hb_norm]
        _ ≤ ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (δ/2) / ρ ^ d := by gcongr
    calc ‖inner ℝ w (newtonField (toSpace x - toSpace y) - newtonField (v - toSpace y))‖
        ≤ ‖w‖ * ‖newtonField (toSpace x - toSpace y) - newtonField (v - toSpace y)‖ :=
          norm_inner_le_norm _ _
      _ ≤ 1 * (((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (δ/2) / ρ^d) := by gcongr
      _ = ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (δ/2) / ρ^d := by ring
  calc ‖∫ v in cell x,
        inner ℝ w (newtonField (toSpace x - toSpace y) - newtonField (v - toSpace y))‖
      ≤ (((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (δ/2) / ρ^d) * (volume.real (cell x)) :=
        norm_setIntegral_le_of_norm_le_const (by rw [volume_cell]; norm_num) hpoint
    _ = ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (δ/2) / ρ^d := by
        rw [Measure.real, volume_cell x]; simp
    _ = ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (δ/2) * ρ ^ (-(d:ℝ)) := by
        rw [Real.rpow_neg hρpos.le, Real.rpow_natCast]; ring
    _ = ((2:ℝ)^d + 2*(d:ℝ)*3^(d-1)) * (Real.sqrt d / 2) * (euclidNorm (x - y)) ^ (-(d:ℝ)) := by
        rw [hδ, hρ]

theorem exists_sum_abs_newtonField_sub_setIntegral_le (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Finset (Site d)) (w : Site d → EuclideanSpace ℝ (Fin d))
      (y : Site d) (R' : ℝ), 1 ≤ R' → (∀ x, ‖w x‖ ≤ 1) →
      (∀ x ∈ E, euclidNorm (x - y) ≤ R') →
        ∑ x ∈ E, |inner ℝ (w x) (newtonField (toSpace x - toSpace y)) -
            ∫ v in cell x, inner ℝ (w x) (newtonField (v - toSpace y))|
          ≤ C * Real.log (R' + 2) := by
  obtain ⟨C', hC'pos, hC'⟩ :=
    CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) (by omega : 1 ≤ d)
  set δ : ℝ := Real.sqrt d with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; exact Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hδ1 : 1 ≤ δ := by
    rw [hδ]; exact Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ d))
  set A : ℝ := (2:ℝ)^d + 2*(d:ℝ)*3^(d-1) with hA
  set B : ℝ := 1 + 3*δ*((d:ℝ)*unitBallVolume d) with hB
  have hωpos : 0 < unitBallVolume d := unitBallVolume_pos d
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    have h1 : (0:ℝ) ≤ 2 ^ d := pow_nonneg (by norm_num) d
    have h2 : (0:ℝ) ≤ 2 * (d:ℝ) * 3 ^ (d-1) := by positivity
    linarith
  have hB_nonneg : 0 ≤ B := by
    rw [hB]
    have h1 : 0 ≤ 3 * δ := by positivity
    have h2 : 0 ≤ (d:ℝ) * unitBallVolume d := mul_nonneg (Nat.cast_nonneg d) hωpos.le
    have h3 : 0 ≤ (3 * δ) * ((d:ℝ) * unitBallVolume d) := mul_nonneg h1 h2
    linarith
  refine ⟨A * δ * (2:ℝ)^(d-1) * C' + B * (4 * δ + 1)^d, ?_, ?_⟩
  · have h1 : 0 ≤ A * δ * (2:ℝ)^(d-1) * C' :=
      mul_nonneg (mul_nonneg (mul_nonneg hA_nonneg hδpos.le)
        (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (d-1))) hC'pos.le
    have h2 : 0 ≤ B * (4 * δ + 1)^d :=
      mul_nonneg hB_nonneg (pow_nonneg (by linarith [hδpos] : (0:ℝ) ≤ 4 * δ + 1) d)
    linarith
  · intro E w y R' hR' hw hE
    set T : Site d → ℝ := fun x =>
      |inner ℝ (w x) (newtonField (toSpace x - toSpace y)) -
        ∫ v in cell x, inner ℝ (w x) (newtonField (v - toSpace y))| with hT
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := E) (f := T)
      (p := fun x => euclidNorm (x - y) < 2 * δ)
    rw [← hsplit]
    have hcard : ((E.filter (fun x => euclidNorm (x - y) < 2 * δ)).card : ℝ)
        ≤ (4 * δ + 1)^d := by
      have h1 : (E.filter (fun x => euclidNorm (x - y) < 2 * δ)).card
          ≤ (ballFinset d (2 * δ)).card := by
        refine Finset.card_le_card_of_injOn (fun x => x - y) ?_ ?_
        · intro x hx
          rw [Finset.mem_coe, Finset.mem_filter] at hx
          exact mem_ballFinset_iff.mpr (le_of_lt hx.2)
        · intro a _ b _ hab
          exact sub_left_injective hab
      have h2 : ((ballFinset d (2 * δ)).card : ℝ) ≤ (2 * (2 * δ) + 1)^d :=
        card_ballFinset_le d (by positivity)
      have h3 : (2 * (2 * δ) + 1)^d = (4 * δ + 1)^d := by ring_nf
      calc ((E.filter (fun x => euclidNorm (x - y) < 2 * δ)).card : ℝ)
          ≤ ((ballFinset d (2 * δ)).card : ℝ) := by exact_mod_cast h1
        _ ≤ (2 * (2 * δ) + 1)^d := h2
        _ = (4 * δ + 1)^d := h3
    have hnear : ∑ x ∈ E.filter (fun x => euclidNorm (x - y) < 2 * δ), T x
        ≤ B * (4 * δ + 1)^d := by
      have hterm : ∀ x ∈ E.filter (fun x => euclidNorm (x - y) < 2 * δ), T x ≤ B := by
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [hT]
        have := near_term_le hd (w x) (hw x) y hx.2
        rw [← hδ, ← hB] at this
        exact this
      calc ∑ x ∈ E.filter (fun x => euclidNorm (x - y) < 2 * δ), T x
          ≤ ∑ _x ∈ E.filter (fun x => euclidNorm (x - y) < 2 * δ), B :=
            Finset.sum_le_sum (fun x hx => hterm x hx)
        _ = ((E.filter (fun x => euclidNorm (x - y) < 2 * δ)).card : ℝ) * B := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (4 * δ + 1)^d * B := mul_le_mul_of_nonneg_right hcard hB_nonneg
        _ = B * (4 * δ + 1)^d := by ring
    have hfar : ∑ x ∈ E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ), T x
        ≤ A * δ * (2:ℝ)^(d-1) * (C' * Real.log (R' + 2)) := by
      have hnear1 : ∀ x ∈ E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ),
          1 ≤ euclidNorm (x - y) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        have h2δ : 2 * δ ≤ euclidNorm (x - y) := not_lt.mp hx.2
        linarith [hδ1]
      have hterm : ∀ x ∈ E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ),
          T x ≤ A * (δ/2) * (euclidNorm (x - y)) ^ (-(d:ℝ)) := by
        intro x hx
        rw [Finset.mem_filter] at hx
        have hxfar : 2 * Real.sqrt d ≤ euclidNorm (x - y) := by
          have := not_lt.mp hx.2
          rwa [hδ] at this
        rw [hT]
        have := far_term_le hd (w x) (hw x) y hxfar
        rw [← hδ, ← hA] at this
        exact this
      have hstep : ∀ x ∈ E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ),
          A * (δ/2) * (euclidNorm (x - y)) ^ (-(d:ℝ))
            ≤ A * (δ/2) * ((2:ℝ)^d * (1 + euclidNorm (x - y)) ^ (-(d:ℝ))) := by
        intro x hx
        have hρ1 := hnear1 x hx
        have := rpow_neg_le_two_pow_mul (d := d) hρ1
        gcongr
      have hsum := hC' (E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ)) y R' hR'
        (fun x hx => hE x (Finset.mem_filter.mp hx).1)
      calc ∑ x ∈ E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ), T x
          ≤ ∑ x ∈ E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ),
              A * (δ/2) * (euclidNorm (x - y)) ^ (-(d:ℝ)) :=
            Finset.sum_le_sum (fun x hx => hterm x hx)
        _ ≤ ∑ x ∈ E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ),
              A * (δ/2) * ((2:ℝ)^d * (1 + euclidNorm (x - y)) ^ (-(d:ℝ))) :=
            Finset.sum_le_sum (fun x hx => hstep x hx)
        _ = A * (δ/2) * (2:ℝ)^d
              * ∑ x ∈ E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ),
                  (1 + euclidNorm (x - y)) ^ (-(d:ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
        _ ≤ A * (δ/2) * (2:ℝ)^d * (C' * Real.log (R' + 2)) := by
            apply mul_le_mul_of_nonneg_left hsum
            positivity
        _ = A * δ * (2:ℝ)^(d-1) * (C' * Real.log (R' + 2)) := by
            have hpow : (2:ℝ)^d = 2 * (2:ℝ)^(d-1) := by
              conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ d)]
              rw [pow_succ]; ring
            rw [hpow]; ring
    have hlog1 : 1 ≤ Real.log (R' + 2) := by
      have h3 : (3:ℝ) ≤ R' + 2 := by linarith
      have hlog3 : (1:ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
      have := Real.log_le_log (by norm_num : (0:ℝ) < 3) h3
      linarith
    calc (∑ x ∈ E.filter (fun x => euclidNorm (x - y) < 2 * δ), T x)
          + ∑ x ∈ E.filter (fun x => ¬ euclidNorm (x - y) < 2 * δ), T x
        ≤ B * (4 * δ + 1)^d + A * δ * (2:ℝ)^(d-1) * (C' * Real.log (R' + 2)) :=
          add_le_add hnear hfar
      _ ≤ B * (4 * δ + 1)^d * Real.log (R' + 2)
            + A * δ * (2:ℝ)^(d-1) * (C' * Real.log (R' + 2)) := by
          have hBc : 0 ≤ B * (4 * δ + 1)^d := by positivity
          have : B * (4 * δ + 1)^d ≤ B * (4 * δ + 1)^d * Real.log (R' + 2) := by
            nlinarith [hBc, hlog1]
          linarith
      _ = (A * δ * (2:ℝ)^(d-1) * C' + B * (4 * δ + 1)^d) * Real.log (R' + 2) := by ring

end CERW.Support.LocalTime
