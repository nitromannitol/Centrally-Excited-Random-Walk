import CERW.Model.Space
import LatticeProb.Walk.Ball
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import CERW.Generic.Kernel.LogRadial
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The planar logarithmic lattice sum

`Σ_{x ∈ ℤ², 1 ≤ |x| ≤ r} |x|^{-2} = 2π log r + O(1)`, used for the planar brackets of the
site martingales (`thm:site-fluctuations`, Step 3, and `lem:separated-brackets`).
-/

namespace CERW.Generic.Lattice

open MeasureTheory LatticeProb CERW CERW.Support.Occupation

/-- Half the space diagonal of the unit cell, the maximal distance from a cell's center to a
point of its cell. -/
private noncomputable def cellRad : ℝ := Real.sqrt 2 / 2

/-- The cell radius is positive. -/
private lemma cellRad_pos : 0 < cellRad := by
  rw [cellRad]; positivity

/-- The square of the cell radius is `1/2`. -/
private lemma cellRad_sq : cellRad ^ 2 = 1 / 2 := by
  rw [cellRad, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The cell radius is less than one. -/
private lemma cellRad_lt_one : cellRad < 1 := by
  nlinarith [cellRad_pos, cellRad_sq]

/-- The cell radius is nonnegative. -/
private lemma cellRad_nonneg : 0 ≤ cellRad := le_of_lt cellRad_pos

/-- Every point of a cell is within `cellRad` of the cell's center, so its norm lies in
`[|x| - cellRad, |x| + cellRad]`. -/
private lemma norm_mem_cell_Icc {x : Site 2} {v : EuclideanSpace ℝ (Fin 2)}
    (hv : v ∈ cell x) :
    euclidNorm x - cellRad ≤ ‖v‖ ∧ ‖v‖ ≤ euclidNorm x + cellRad := by
  have hsub : ‖v - toSpace x‖ ≤ cellRad := by
    have := norm_sub_toSpace_le_of_mem_cell (d := 2) hv
    simpa [cellRad] using this
  have h := abs_norm_sub_norm_le v (toSpace x)
  rw [norm_toSpace] at h
  obtain ⟨h1, h2⟩ := abs_le.mp (h.trans hsub)
  constructor <;> linarith

/-- `|v|^{-2}` is integrable on a cell centred at a site of norm at least one. -/
private lemma integrableOn_cell_rpow_neg_two {x : Site 2} (hx : 1 ≤ euclidNorm x) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖ ^ (-(2 : ℝ))) (cell x) := by
  have hc : cellRad < euclidNorm x := lt_of_lt_of_le cellRad_lt_one hx
  have hvol : volume (cell x) ≠ ⊤ := by rw [volume_cell]; exact ENNReal.one_ne_top
  have hdif : 0 < euclidNorm x - cellRad := by linarith
  refine Measure.integrableOn_of_bounded hvol
    (measurable_norm.pow_const _).aestronglyMeasurable
    (M := (euclidNorm x - cellRad) ^ (-(2 : ℝ))) ?_
  filter_upwards [ae_restrict_mem (measurableSet_cell x)] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg v) _)]
  exact Real.rpow_le_rpow_of_nonpos hdif (norm_mem_cell_Icc hv).1 (by norm_num)

/-- The integral of `|v|^{-2}` over a cell is bounded below by `(|x| + cellRad)^{-2}` and
above by `(|x| - cellRad)^{-2}`. -/
private lemma setIntegral_cell_rpow_mem_Icc {x : Site 2} (hx : 1 ≤ euclidNorm x) :
    (euclidNorm x + cellRad) ^ (-(2 : ℝ))
        ≤ ∫ v in cell x, ‖v‖ ^ (-(2 : ℝ)) ∧
      ∫ v in cell x, ‖v‖ ^ (-(2 : ℝ))
        ≤ (euclidNorm x - cellRad) ^ (-(2 : ℝ)) := by
  have hcell : MeasurableSet (cell x) := measurableSet_cell x
  have hvol : volume (cell x) ≠ ⊤ := by rw [volume_cell]; exact ENNReal.one_ne_top
  have hvol_real : (volume (cell x)).toReal = 1 := by
    rw [volume_cell, ENNReal.toReal_one]
  have hfint := integrableOn_cell_rpow_neg_two hx
  have hc : cellRad < euclidNorm x := lt_of_lt_of_le cellRad_lt_one hx
  have hsum : 0 < euclidNorm x + cellRad := by linarith [cellRad_nonneg]
  have hdif : 0 < euclidNorm x - cellRad := by linarith
  constructor
  · have hconst : IntegrableOn
        (fun _ : EuclideanSpace ℝ (Fin 2) => (euclidNorm x + cellRad) ^ (-(2 : ℝ)))
        (cell x) := integrableOn_const hvol
    have h := setIntegral_mono_on hconst hfint hcell fun v hv => by
      have hvpos : 0 < ‖v‖ := by
        have := (norm_mem_cell_Icc hv).1
        linarith
      exact Real.rpow_le_rpow_of_nonpos hvpos (norm_mem_cell_Icc hv).2 (by norm_num)
    rwa [setIntegral_const, measureReal_def, hvol_real, one_smul] at h
  · have hconst : IntegrableOn
        (fun _ : EuclideanSpace ℝ (Fin 2) => (euclidNorm x - cellRad) ^ (-(2 : ℝ)))
        (cell x) := integrableOn_const hvol
    have h := setIntegral_mono_on hfint hconst hcell fun v hv => by
      have hle : euclidNorm x - cellRad ≤ ‖v‖ := (norm_mem_cell_Icc hv).1
      exact Real.rpow_le_rpow_of_nonpos hdif hle (by norm_num)
    rwa [setIntegral_const, measureReal_def, hvol_real, one_smul] at h

/-- The width `(|x| - cellRad)^{-2} - (|x| + cellRad)^{-2}` of the cell comparison is at most
`16 |x|^{-3}`. -/
private lemma cellRad_width_le (a : ℝ) (ha : 1 ≤ a) :
    (a - cellRad) ^ (-(2 : ℝ)) - (a + cellRad) ^ (-(2 : ℝ))
      ≤ 16 * a ^ (-(3 : ℝ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hc0 : 0 ≤ cellRad := cellRad_nonneg
  have hc1 : cellRad < 1 := cellRad_lt_one
  have hc2 : cellRad ^ 2 = 1 / 2 := cellRad_sq
  have hm : 0 < a - cellRad := by linarith
  have hp : 0 < a + cellRad := by linarith
  have hkey : (a - cellRad) ^ (-(2 : ℝ)) - (a + cellRad) ^ (-(2 : ℝ))
      = 4 * a * cellRad / (a ^ 2 - cellRad ^ 2) ^ 2 := by
    rw [Real.rpow_neg (le_of_lt hm), Real.rpow_neg (le_of_lt hp),
      Real.rpow_two, Real.rpow_two]
    rw [inv_sub_inv (by positivity) (by positivity)]
    ring_nf
  have hden_ge : a ^ 4 / 4 ≤ (a ^ 2 - cellRad ^ 2) ^ 2 := by
    have hle : a ^ 2 / 2 ≤ a ^ 2 - cellRad ^ 2 := by nlinarith [hc2, ha]
    calc a ^ 4 / 4 = (a ^ 2 / 2) ^ 2 := by ring
      _ ≤ (a ^ 2 - cellRad ^ 2) ^ 2 := by
          exact sq_le_sq' (by linarith [hle]) hle
  rw [hkey]
  have hstep : 4 * a * cellRad / (a ^ 2 - cellRad ^ 2) ^ 2 ≤ 4 * a / (a ^ 4 / 4) :=
    div_le_div₀ (by positivity) (by nlinarith [hc0, hc1]) (by positivity) hden_ge
  have hval : 4 * a / (a ^ 4 / 4) = 16 * a ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt ha0),
      show a ^ (3 : ℝ) = a ^ 3 from Real.rpow_natCast a 3]
    field_simp
    ring
  exact hstep.trans_eq hval

/-- `|x|^{-2}` differs from the integral of `|v|^{-2}` over its cell by at most
`16 |x|^{-3}`. -/
private lemma cell_integral_error {x : Site 2} (hx : 1 ≤ euclidNorm x) :
    |(∫ v in cell x, ‖v‖ ^ (-(2 : ℝ))) - euclidNorm x ^ (-(2 : ℝ))|
      ≤ 16 * euclidNorm x ^ (-(3 : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := setIntegral_cell_rpow_mem_Icc hx
  have hc : cellRad < euclidNorm x := lt_of_lt_of_le cellRad_lt_one hx
  have ha : 0 < euclidNorm x := lt_of_lt_of_le zero_lt_one hx
  have hm : 0 < euclidNorm x - cellRad := by linarith
  have hlo' : (euclidNorm x + cellRad) ^ (-(2 : ℝ)) ≤ euclidNorm x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha (by linarith [cellRad_nonneg]) (by norm_num)
  have hhi' : euclidNorm x ^ (-(2 : ℝ)) ≤ (euclidNorm x - cellRad) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm (by linarith [cellRad_nonneg]) (by norm_num)
  have hwidth := cellRad_width_le (euclidNorm x) hx
  have hlow : -(16 * euclidNorm x ^ (-(3 : ℝ)))
      ≤ (euclidNorm x + cellRad) ^ (-(2 : ℝ)) - (euclidNorm x - cellRad) ^ (-(2 : ℝ)) :=
    by linarith [hwidth]
  have hmid : (euclidNorm x + cellRad) ^ (-(2 : ℝ)) - (euclidNorm x - cellRad) ^ (-(2 : ℝ))
      ≤ (∫ v in cell x, ‖v‖ ^ (-(2 : ℝ))) - euclidNorm x ^ (-(2 : ℝ)) :=
    sub_le_sub hlo hhi'
  have hhi2 : (∫ v in cell x, ‖v‖ ^ (-(2 : ℝ))) - euclidNorm x ^ (-(2 : ℝ))
      ≤ 16 * euclidNorm x ^ (-(3 : ℝ)) :=
    (sub_le_sub hhi hlo').trans hwidth
  rw [abs_le]
  exact ⟨hlow.trans hmid, hhi2⟩

/-- The summand `(euclidNorm x ^ 2)⁻¹` is the real power `euclidNorm x ^ (-2)`. -/
private lemma euclidNorm_rpow_neg_two (x : Site 2) :
    euclidNorm x ^ (-(2 : ℝ)) = (euclidNorm x ^ 2)⁻¹ := by
  rw [Real.rpow_neg (euclidNorm_nonneg x),
    show euclidNorm x ^ (2 : ℝ) = euclidNorm x ^ 2 from Real.rpow_natCast _ 2]

/-- For `|x| ≥ 1`, the cube weight is comparable to `(1 + |x|)^{-3}`. -/
private lemma rpow_neg_three_le {x : Site 2} (hx : 1 ≤ euclidNorm x) :
    euclidNorm x ^ (-(3 : ℝ)) ≤ 8 * (1 + euclidNorm x) ^ (-(3 : ℝ)) := by
  have hx0 : 0 < euclidNorm x := lt_of_lt_of_le zero_lt_one hx
  have hle : 1 + euclidNorm x ≤ 2 * euclidNorm x := by linarith
  have h2 : (2 * euclidNorm x) ^ (-(3 : ℝ)) ≤ (1 + euclidNorm x) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [hx0]) hle (by norm_num)
  have h3 : (2 * euclidNorm x) ^ (-(3 : ℝ))
      = (1 / 8) * euclidNorm x ^ (-(3 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) (le_of_lt hx0), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      show (2 : ℝ) ^ (3 : ℝ) = 2 ^ 3 from Real.rpow_natCast 2 3]
    norm_num
  linarith

/-- The tail `Σ_{1 ≤ |x| ≤ r} |x|^{-3}` is bounded uniformly in `r`. -/
private lemma sum_cube_le (r : ℝ) :
    ∑ x ∈ (ballFinset 2 r).filter (fun x => 1 ≤ euclidNorm x), euclidNorm x ^ (-(3 : ℝ))
      ≤ 8 * ∑' y : Site 2, (1 + euclidNorm y) ^ (-(3 : ℝ)) := by
  have hsum : Summable (fun y : Site 2 => (1 + euclidNorm y) ^ (-(3 : ℝ))) :=
    summable_one_add_euclidNorm_rpow 2 (by norm_num)
  calc ∑ x ∈ (ballFinset 2 r).filter (fun x => 1 ≤ euclidNorm x), euclidNorm x ^ (-(3 : ℝ))
      ≤ ∑ x ∈ (ballFinset 2 r).filter (fun x => 1 ≤ euclidNorm x),
          8 * (1 + euclidNorm x) ^ (-(3 : ℝ)) :=
        Finset.sum_le_sum fun x hx => rpow_neg_three_le (Finset.mem_filter.mp hx).2
    _ = 8 * ∑ x ∈ (ballFinset 2 r).filter (fun x => 1 ≤ euclidNorm x),
          (1 + euclidNorm x) ^ (-(3 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 8 * ∑' y : Site 2, (1 + euclidNorm y) ^ (-(3 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact hsum.sum_le_tsum _ fun y _ =>
          Real.rpow_nonneg (by linarith [euclidNorm_nonneg y]) _

/-- The half-open planar annulus `ρ ≤ |v| < R`. -/
private def annSet (ρ R : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.ball 0 R \ Metric.ball 0 ρ

/-- Membership in the half-open annulus. -/
private lemma mem_annSet {ρ R : ℝ} {v : EuclideanSpace ℝ (Fin 2)} :
    v ∈ annSet ρ R ↔ ρ ≤ ‖v‖ ∧ ‖v‖ < R := by
  rw [annSet, Set.mem_sdiff]
  constructor
  · rintro ⟨hR, hρ⟩
    have hR' : ‖v‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hR
    have hρ' : ρ ≤ ‖v‖ := by
      exact le_of_not_gt (by simpa [Metric.mem_ball, dist_eq_norm] using hρ)
    exact ⟨hρ', hR'⟩
  · rintro ⟨hρ, hR⟩
    exact ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hR,
      by simpa [Metric.mem_ball, dist_eq_norm] using not_lt_of_ge hρ⟩

/-- The integral of `|v|^{-2}` over the planar annulus is `2π log(R/ρ)`. -/
private lemma integral_annSet {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    ∫ v in annSet ρ R, ‖v‖ ^ (-(2 : ℝ)) = 2 * unitBallVolume 2 * Real.log (R / ρ) := by
  rw [show annSet ρ R = Metric.ball 0 R \ Metric.ball 0 ρ from rfl]
  exact (CERW.Generic.Kernel.integrableOn_annulus_norm_rpow_and_integral_eq
    (d := 2) (by norm_num) hρ hρR).2

/-- `|v|^{-2}` is integrable on the planar annulus. -/
private lemma integrableOn_annSet {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖ ^ (-(2 : ℝ))) (annSet ρ R) := by
  rw [show annSet ρ R = Metric.ball 0 R \ Metric.ball 0 ρ from rfl]
  exact (CERW.Generic.Kernel.integrableOn_annulus_norm_rpow_and_integral_eq
    (d := 2) (by norm_num) hρ hρR).1

/-- The volume of the planar unit ball is `π`. -/
private lemma unitBallVolume_two : unitBallVolume 2 = Real.pi := by
  rw [unitBallVolume, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1),
    ENNReal.toReal_ofReal Real.pi_pos.le]
  norm_num

/-- The additive constant bounding the boundary correction of the cell sum. -/
private noncomputable def logBoundConst : ℝ :=
  2 * Real.pi * Real.log ((2 + cellRad) / (1 - cellRad))

/-- The outer annulus integral exceeds `2π log r` by at most `logBoundConst`. -/
private lemma annOuter_sub_log_le (r : ℝ) (hr : 1 ≤ r) :
    (∫ v in annSet (1 - cellRad) (r + cellRad + 1), ‖v‖ ^ (-(2 : ℝ)))
      - 2 * Real.pi * Real.log r ≤ logBoundConst := by
  have hc1 : 0 < 1 - cellRad := by linarith [cellRad_lt_one]
  have hρR : 1 - cellRad ≤ r + cellRad + 1 := by linarith [hr, cellRad_nonneg]
  have hr0 : 0 < r := by linarith
  rw [integral_annSet hc1 hρR, unitBallVolume_two, logBoundConst]
  have hnum : 0 < (r + cellRad + 1) / (1 - cellRad) :=
    div_pos (by linarith [hr, cellRad_nonneg]) hc1
  have hsplit : 2 * Real.pi * Real.log ((r + cellRad + 1) / (1 - cellRad))
      - 2 * Real.pi * Real.log r
      = 2 * Real.pi * Real.log (((r + cellRad + 1) / (1 - cellRad)) / r) := by
    rw [← mul_sub, ← Real.log_div (ne_of_gt hnum) (ne_of_gt hr0)]
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.log_le_log (by positivity)
  have hsimp : ((r + cellRad + 1) / (1 - cellRad)) / r
      = (r + cellRad + 1) / ((1 - cellRad) * r) := by rw [div_div]
  rw [hsimp]
  rw [div_le_div_iff₀ (mul_pos hc1 hr0) hc1]
  have hfac : (2 + cellRad) * ((1 - cellRad) * r) - (r + cellRad + 1) * (1 - cellRad)
      = (1 - cellRad ^ 2) * (r - 1) := by ring
  have hnn : 0 ≤ (1 - cellRad ^ 2) * (r - 1) :=
    mul_nonneg (by nlinarith [cellRad_sq, cellRad_lt_one]) (by linarith)
  linarith [hfac, hnn]

/-- The inner annulus integral falls short of `2π log r` by at most `logBoundConst`. -/
private lemma log_sub_annInner_le (r : ℝ) (hr : 1 ≤ r) :
    2 * Real.pi * Real.log r
      - (∫ v in annSet (1 + cellRad) (r - cellRad), ‖v‖ ^ (-(2 : ℝ)))
      ≤ logBoundConst := by
  have hr0 : 0 < r := by linarith
  have hc1 : 0 < 1 - cellRad := by linarith [cellRad_lt_one]
  by_cases h : 1 + cellRad ≤ r - cellRad
  · have hden : 0 < r - cellRad := by linarith [cellRad_lt_one]
    have hnum : 0 < (r - cellRad) / (1 + cellRad) :=
      div_pos hden (by linarith [cellRad_nonneg])
    rw [integral_annSet (by linarith [cellRad_nonneg]) h, unitBallVolume_two, logBoundConst]
    have hsplit : 2 * Real.pi * Real.log r
        - 2 * Real.pi * Real.log ((r - cellRad) / (1 + cellRad))
        = 2 * Real.pi * Real.log (r / ((r - cellRad) / (1 + cellRad))) := by
      rw [← mul_sub, ← Real.log_div (ne_of_gt hr0) (ne_of_gt hnum)]
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply Real.log_le_log (by positivity)
    have hsimp : r / ((r - cellRad) / (1 + cellRad)) = r * (1 + cellRad) / (r - cellRad) := by
      field_simp
    rw [hsimp]
    rw [div_le_div_iff₀ hden hc1]
    have hfac : (2 + cellRad) * (r - cellRad) - r * (1 + cellRad) * (1 - cellRad)
        = (r - 1) * (3 / 2 + cellRad) + (1 - cellRad) := by
      nlinarith [cellRad_sq]
    nlinarith [hfac, hr, cellRad_nonneg, cellRad_lt_one]
  · have hempty : annSet (1 + cellRad) (r - cellRad) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro v hv
      rw [mem_annSet] at hv
      linarith [hv.1, hv.2]
    rw [hempty, setIntegral_empty, sub_zero, logBoundConst]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply Real.log_le_log (by linarith)
    rw [le_div_iff₀ hc1]
    have hrlt : r < 1 + 2 * cellRad := by linarith
    nlinarith [hrlt, cellRad_sq, cellRad_nonneg, cellRad_lt_one]

/-- The planar sum of `|x|^{-2}` over `1 ≤ |x| ≤ r` is `2π log r` up to a bounded error. -/
theorem abs_sum_inv_sq_sub_log_le :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      |∑ x ∈ (ballFinset 2 r).filter (fun x => 1 ≤ euclidNorm x), (euclidNorm x ^ 2)⁻¹
        - 2 * Real.pi * Real.log r| ≤ C := by
  let T : ℝ := ∑' y : Site 2, (1 + euclidNorm y) ^ (-(3 : ℝ))
  refine ⟨128 * T + logBoundConst, fun r hr => ?_⟩
  let A : Finset (Site 2) := (ballFinset 2 r).filter (fun x => 1 ≤ euclidNorm x)
  let U : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ x ∈ A, cell x
  have hA : A = (ballFinset 2 r).filter (fun x => 1 ≤ euclidNorm x) := rfl
  have hUint : (∫ v in U, ‖v‖ ^ (-(2 : ℝ)))
      = ∑ x ∈ A, ∫ v in cell x, ‖v‖ ^ (-(2 : ℝ)) := by
    change (∫ v in ⋃ x ∈ A, cell x, ‖v‖ ^ (-(2 : ℝ))) = _
    exact integral_biUnion_finset A (fun x _ => measurableSet_cell x)
      (fun x _ y _ hxy => cell_disjoint hxy)
      (fun x hx => integrableOn_cell_rpow_neg_two (Finset.mem_filter.mp hx).2)
  have hU_int : IntegrableOn (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖ ^ (-(2 : ℝ))) U := by
    change IntegrableOn _ (⋃ x ∈ A, cell x)
    exact integrableOn_finset_iUnion.mpr
      (fun x hx => integrableOn_cell_rpow_neg_two (Finset.mem_filter.mp hx).2)
  have hInner_sub : annSet (1 + cellRad) (r - cellRad) ⊆ U := by
    intro v hv
    rw [mem_annSet] at hv
    obtain ⟨hv1, hv2⟩ := hv
    change v ∈ ⋃ x ∈ A, cell x
    refine Set.mem_iUnion₂.mpr ⟨cellCenter v, ?_, mem_cell_cellCenter v⟩
    rw [hA, Finset.mem_filter, mem_ballFinset_iff]
    have hvc := norm_mem_cell_Icc (mem_cell_cellCenter v)
    exact ⟨by linarith [hvc.2, hv2], by linarith [hvc.1, hv1]⟩
  have hOuter_sub : U ⊆ annSet (1 - cellRad) (r + cellRad + 1) := by
    intro v hv
    change v ∈ ⋃ x ∈ A, cell x at hv
    rw [Set.mem_iUnion₂] at hv
    obtain ⟨x, hx, hvx⟩ := hv
    rw [hA] at hx
    obtain ⟨hxball, hx1⟩ := Finset.mem_filter.mp hx
    have hxle : euclidNorm x ≤ r := mem_ballFinset_iff.mp hxball
    rw [mem_annSet]
    have hvc := norm_mem_cell_Icc hvx
    exact ⟨by linarith [hvc.1, hx1], by linarith [hvc.2, hxle, cellRad_nonneg]⟩
  have hU_le_outer : (∫ v in U, ‖v‖ ^ (-(2 : ℝ)))
      ≤ ∫ v in annSet (1 - cellRad) (r + cellRad + 1), ‖v‖ ^ (-(2 : ℝ)) :=
    setIntegral_mono_set
      (integrableOn_annSet (by linarith [cellRad_lt_one])
        (by linarith [hr, cellRad_nonneg]))
      (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg v) _))
      (Filter.Eventually.of_forall hOuter_sub)
  have hInner_le_U : (∫ v in annSet (1 + cellRad) (r - cellRad), ‖v‖ ^ (-(2 : ℝ)))
      ≤ ∫ v in U, ‖v‖ ^ (-(2 : ℝ)) :=
    setIntegral_mono_set hU_int
      (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg v) _))
      (Filter.Eventually.of_forall hInner_sub)
  have hann : (∫ v in annSet 1 r, ‖v‖ ^ (-(2 : ℝ))) = 2 * Real.pi * Real.log r := by
    rw [integral_annSet (by norm_num) hr, unitBallVolume_two]
    simp
  have hD1 := annOuter_sub_log_le r hr
  have hD2 := log_sub_annInner_le r hr
  have hbd : |(∫ v in U, ‖v‖ ^ (-(2 : ℝ))) - 2 * Real.pi * Real.log r|
      ≤ logBoundConst := by
    rw [abs_le]
    exact ⟨by linarith [hInner_le_U, hD2], by linarith [hU_le_outer, hD1]⟩
  have hS_eq : (∑ x ∈ A, (euclidNorm x ^ 2)⁻¹)
      = ∑ x ∈ A, ‖toSpace x‖ ^ (-(2 : ℝ)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_toSpace]
    exact (euclidNorm_rpow_neg_two x).symm
  have hdiff : |(∑ x ∈ A, ‖toSpace x‖ ^ (-(2 : ℝ)))
      - (∫ v in U, ‖v‖ ^ (-(2 : ℝ)))| ≤ 128 * T := by
    rw [hUint]
    calc |(∑ x ∈ A, ‖toSpace x‖ ^ (-(2 : ℝ)))
            - ∑ x ∈ A, ∫ v in cell x, ‖v‖ ^ (-(2 : ℝ))|
        = |∑ x ∈ A, (‖toSpace x‖ ^ (-(2 : ℝ))
            - ∫ v in cell x, ‖v‖ ^ (-(2 : ℝ)))| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ x ∈ A, |‖toSpace x‖ ^ (-(2 : ℝ))
            - ∫ v in cell x, ‖v‖ ^ (-(2 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ A, 16 * euclidNorm x ^ (-(3 : ℝ)) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hx1 : 1 ≤ euclidNorm x := (Finset.mem_filter.mp hx).2
          have h := cell_integral_error hx1
          rw [norm_toSpace, abs_sub_comm]
          exact h
      _ = 16 * ∑ x ∈ A, euclidNorm x ^ (-(3 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 16 * (8 * T) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [show T = ∑' y : Site 2, (1 + euclidNorm y) ^ (-(3 : ℝ)) from rfl, hA]
          exact sum_cube_le r
      _ = 128 * T := by ring
  calc |(∑ x ∈ A, (euclidNorm x ^ 2)⁻¹) - 2 * Real.pi * Real.log r|
      = |(∑ x ∈ A, ‖toSpace x‖ ^ (-(2 : ℝ))) - 2 * Real.pi * Real.log r| := by rw [hS_eq]
    _ = |((∑ x ∈ A, ‖toSpace x‖ ^ (-(2 : ℝ))) - (∫ v in U, ‖v‖ ^ (-(2 : ℝ))))
            + ((∫ v in U, ‖v‖ ^ (-(2 : ℝ))) - 2 * Real.pi * Real.log r)| := by ring_nf
    _ ≤ |(∑ x ∈ A, ‖toSpace x‖ ^ (-(2 : ℝ))) - (∫ v in U, ‖v‖ ^ (-(2 : ℝ)))|
          + |(∫ v in U, ‖v‖ ^ (-(2 : ℝ))) - 2 * Real.pi * Real.log r| := abs_add_le _ _
    _ ≤ 128 * T + logBoundConst := add_le_add hdiff hbd

end CERW.Generic.Lattice
