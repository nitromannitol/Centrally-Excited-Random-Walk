import CERW.Support.Main.GoodEvent
import CERW.Support.Main.HausdorffArith
import CERW.Support.Main.ScaleLimits
import CERW.Support.Occupation.CellNorm
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The Hausdorff bound from the fluctuation event

On the event `fluctGood d ε C Y n`, the rescaled visited set `N⁻¹ V_n` is within Hausdorff
distance `C' Q^{1/d} L` of the closed ball `B̄(0, a)`. The outer inclusion bounds the distance
from each point of `N⁻¹ V_n` to the ball by `C Q^{1/d} L`. The inner inclusion puts a point of
`N⁻¹ A_n ⊆ N⁻¹ V_n` within `C Q + 2√d/N` of every point of the ball. By `excess_rate` and
`planar_excess_rate` this is the rate of `eq:hausdorff`. In the plane the inner inclusion reads
`{|x| < aN - C n^{1/6} √L} ⊆ A_n`, since `N Q = n^{1/6} √L` (`planar_inner_rate`).
-/

namespace CERW.Support.Main

open MeasureTheory Filter LatticeProb CERW
open scoped Topology

variable {d : ℕ}

/-- The rate `Q` is nonnegative. -/
private lemma rate_nonneg (d n : ℕ) :
    0 ≤ (if d = 2 then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
      else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1))) := by
  have hbase : 0 ≤ Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
    · positivity
  by_cases h : d = 2
  · rw [if_pos h]; exact Real.rpow_nonneg hbase _
  · rw [if_neg h]; exact Real.rpow_nonneg hbase _

/-- In the plane, `N⁻¹ ≤ Q^{1/2}` as soon as `N = n^{1/3} ≥ 1` and `log(n+2) ≥ 1`. -/
private lemma rate_inv_le_planar {n : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ Real.log (n + 2)) :
    (((n : ℝ) ^ ((1 : ℝ) / 3))⁻¹)
      ≤ ((Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2))
          ^ ((1 : ℝ) / 2) := by
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3) with hNdef
  set L : ℝ := Real.log (n + 2) with hLdef
  set Q : ℝ := (L / N) ^ ((1 : ℝ) / 2) with hQdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < N := by rw [hNdef]; exact Real.rpow_pos_of_pos hn0 _
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  have hNnonneg : 0 ≤ N := le_of_lt hNpos
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNdef]
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hbase_nonneg : 0 ≤ L / N := div_nonneg hLnonneg hNnonneg
  have hQpow : Q ^ ((1 : ℝ) / 2) = (L / N) ^ ((1 : ℝ) / 4) := by
    rw [hQdef, ← Real.rpow_mul hbase_nonneg]
    norm_num
  have hNpow : N * N ^ (-(1 : ℝ) / 4) = N ^ ((3 : ℝ) / 4) := by
    nth_rewrite 1 [← Real.rpow_one N]
    rw [← Real.rpow_add hNpos]
    norm_num
  have hprod : N * Q ^ ((1 : ℝ) / 2) = N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := by
    rw [hQpow, Real.div_rpow hLnonneg hNnonneg, div_eq_mul_inv]
    have hstep : N * (L ^ ((1 : ℝ) / 4) * (N ^ ((1 : ℝ) / 4))⁻¹)
        = (N * N ^ (-(1 : ℝ) / 4)) * L ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_neg hNnonneg ((1 : ℝ) / 4)]
      ring_nf
    rw [hstep, hNpow]
  rw [inv_le_iff_one_le_mul₀' hNpos, hprod]
  have h1 : (1 : ℝ) ≤ N ^ ((3 : ℝ) / 4) := Real.one_le_rpow hN1 (by norm_num)
  have h2 : (1 : ℝ) ≤ L ^ ((1 : ℝ) / 4) := Real.one_le_rpow hL (by norm_num)
  calc (1 : ℝ) = 1 * 1 := by ring_nf
    _ ≤ N ^ ((3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) :=
        mul_le_mul h1 h2 (by norm_num) (Real.rpow_nonneg (le_of_lt hNpos) _)

/-- For `d ≥ 3`, `N⁻¹ ≤ Q^{1/d}` as soon as `N ≥ 1` and `log(n+2) ≥ 1`. -/
private lemma rate_inv_le_higher {d : ℕ} (hd : 3 ≤ d) {n : ℕ} (hn : 1 ≤ n)
    (hL : 1 ≤ Real.log (n + 2)) :
    (((n : ℝ) ^ ((1 : ℝ) / (d + 1)))⁻¹)
      ≤ ((Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
          ^ ((1 : ℝ) / d) := by
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hNdef
  set L : ℝ := Real.log (n + 2) with hLdef
  set Q : ℝ := (L / N) ^ ((d : ℝ) / (2 * d - 1)) with hQdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < N := by rw [hNdef]; exact Real.rpow_pos_of_pos hn0 _
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  have hNnonneg : 0 ≤ N := le_of_lt hNpos
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNdef]
    exact Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  have hden : (2 * (d : ℝ) - 1) ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hdpos : (0 : ℝ) < d := by linarith [show (3 : ℝ) ≤ d by exact_mod_cast hd]
  have hbase_nonneg : 0 ≤ L / N := div_nonneg hLnonneg hNnonneg
  have hQpow : Q ^ ((1 : ℝ) / d) = (L / N) ^ ((1 : ℝ) / (2 * d - 1)) := by
    rw [hQdef, ← Real.rpow_mul hbase_nonneg]
    congr 1
    field_simp [hden, hdpos.ne']
  have hexp : (1 : ℝ) + -(1 / (2 * (d : ℝ) - 1))
      = (2 * (d : ℝ) - 2) / (2 * (d : ℝ) - 1) := by
    field_simp [hden]
    ring_nf
  have hNpow : N * N ^ (-(1 : ℝ) / (2 * d - 1))
      = N ^ ((2 * (d : ℝ) - 2) / (2 * d - 1)) := by
    nth_rewrite 1 [← Real.rpow_one N]
    rw [← Real.rpow_add hNpos]
    congr 1
    rw [show (-(1 : ℝ) / (2 * d - 1)) = -(1 / (2 * (d : ℝ) - 1)) by ring_nf]
    exact hexp
  have hprod : N * Q ^ ((1 : ℝ) / d)
      = N ^ ((2 * (d : ℝ) - 2) / (2 * d - 1)) * L ^ ((1 : ℝ) / (2 * d - 1)) := by
    rw [hQpow, Real.div_rpow hLnonneg hNnonneg, div_eq_mul_inv]
    have hstep : N * (L ^ ((1 : ℝ) / (2 * d - 1)) * (N ^ ((1 : ℝ) / (2 * d - 1)))⁻¹)
        = (N * N ^ (-(1 : ℝ) / (2 * d - 1))) * L ^ ((1 : ℝ) / (2 * d - 1)) := by
      rw [show (N ^ ((1 : ℝ) / (2 * d - 1)))⁻¹ = N ^ (-(1 : ℝ) / (2 * d - 1)) by
        rw [show (-(1 : ℝ) / (2 * d - 1)) = -((1 : ℝ) / (2 * d - 1)) by ring_nf]
        exact (Real.rpow_neg hNnonneg ((1 : ℝ) / (2 * d - 1))).symm]
      ring_nf
    rw [hstep, hNpow]
  rw [inv_le_iff_one_le_mul₀' hNpos, hprod]
  have h1 : (1 : ℝ) ≤ N ^ ((2 * (d : ℝ) - 2) / (2 * d - 1)) :=
    Real.one_le_rpow hN1 (by
      apply div_nonneg
      · linarith [show (3 : ℝ) ≤ d by exact_mod_cast hd]
      · linarith [show (3 : ℝ) ≤ d by exact_mod_cast hd])
  have h2 : (1 : ℝ) ≤ L ^ ((1 : ℝ) / (2 * d - 1)) :=
    Real.one_le_rpow hL (by
      apply div_nonneg (by norm_num)
      linarith [show (3 : ℝ) ≤ d by exact_mod_cast hd])
  calc (1 : ℝ) = 1 * 1 := by ring_nf
    _ ≤ N ^ ((2 * (d : ℝ) - 2) / (2 * d - 1)) * L ^ ((1 : ℝ) / (2 * d - 1)) :=
        mul_le_mul h1 h2 (by norm_num) (Real.rpow_nonneg (le_of_lt hNpos) _)

/-- The inverse scale is dominated by the rate power `Q^{1/d}`. -/
private lemma rate_inv_le {d : ℕ} (hd : 2 ≤ d) {n : ℕ} (hn : 1 ≤ n)
    (hL : 1 ≤ Real.log (n + 2)) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1)))⁻¹
      ≤ (if d = 2 then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
          else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
        ^ ((1 : ℝ) / d) := by
  by_cases h2 : d = 2
  · subst d
    simp only [if_true]
    norm_num
    exact rate_inv_le_planar hn hL
  · have hd3 : 3 ≤ d := by omega
    simp only [if_neg h2]
    exact rate_inv_le_higher hd3 hn hL

/-- The normalizing constant `a` of the fluctuation theorem is positive. -/
private lemma a_pos {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    0 < ((d + 1) / (2 * d * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal))
      ^ ((1 : ℝ) / (d + 1)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hvol : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal := by
    have hpos : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      Metric.measure_ball_pos volume 0 zero_lt_one
    have hne : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ (⊤ : ENNReal) :=
      measure_ball_ne_top
    exact ENNReal.toReal_pos hpos.ne' hne
  have hbase : 0 < (d + 1) / (2 * d * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal) := by positivity
  exact Real.rpow_pos_of_pos hbase _

/-- The eventual facts of the fluctuation scale: the cover threshold is below `a`, and the
scale, log and rate are at least one. -/
private lemma eventually_scale_facts {d : ℕ} (hd : 2 ≤ d) {C a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      C * (if d = 2 then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
          else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
        + 2 * Real.sqrt d / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) < a ∧
      (if d = 2 then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
          else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
            ^ ((d : ℝ) / (2 * d - 1))) ≤ 1 ∧
      (1 : ℝ) ≤ Real.log (n + 2) ∧
      (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  have hQ : Tendsto (fun n : ℕ => if d = 2
      then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
      else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
      atTop (𝓝 0) := tendsto_rate_zero hd
  have hN : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (d + 1))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < (1 : ℝ) / (d + 1))).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ ((1 : ℝ) / (d + 1)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hN
  have hsum : Tendsto (fun n : ℕ => C * (if d = 2
        then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
        else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
        + 2 * Real.sqrt d * ((n : ℝ) ^ ((1 : ℝ) / (d + 1)))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => C * (if d = 2
        then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
        else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1))))
        atTop (𝓝 (C * 0)) := hQ.const_mul C
    have h2 : Tendsto (fun n : ℕ => 2 * Real.sqrt d * ((n : ℝ) ^ ((1 : ℝ) / (d + 1)))⁻¹)
        atTop (𝓝 (2 * Real.sqrt d * 0)) := hinv.const_mul (2 * Real.sqrt d)
    simpa using h1.add h2
  have hE1 : ∀ᶠ n : ℕ in atTop, C * (if d = 2
        then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
        else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((d : ℝ) / (2 * d - 1)))
        + 2 * Real.sqrt d / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) < a :=
    (hsum.eventually (isOpen_Iio.mem_nhds ha)).mono fun n hn =>
      by simpa only [div_eq_mul_inv] using hn
  have hE2 : ∀ᶠ n : ℕ in atTop, (if d = 2
        then (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ ((1 : ℝ) / 2)
        else (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
          ^ ((d : ℝ) / (2 * d - 1))) ≤ 1 :=
    (hQ.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun n hn => le_of_lt hn
  have hE3 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n + 2) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hE4 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
    hN.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hE1, hE2, hE3, hE4] with n hn1 hn2 hn3 hn4
  exact ⟨hn1, hn2, hn3, hn4⟩

/-- Radial projection to radius `r` does not increase the norm below `r`: the scaled point
`(min ‖y‖ r / ‖y‖) • y` has norm `min ‖y‖ r`. -/
private lemma norm_smul_min_div (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    ‖(min ‖y‖ r / ‖y‖) • y‖ = min ‖y‖ r := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [norm_zero, min_eq_left hr.le, zero_div, zero_smul, norm_zero]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy)]
    exact div_nonneg (le_min (norm_nonneg _) hr.le) (norm_nonneg _)

/-- The distance from `y` to its radial projection `(min ‖y‖ r / ‖y‖) • y` is
`max (‖y‖ - r) 0`. -/
private lemma norm_sub_smul_min_div (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hr : 0 < r) :
    ‖y - (min ‖y‖ r / ‖y‖) • y‖ = max (‖y‖ - r) 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [norm_zero, min_eq_left hr.le, zero_div, zero_smul, sub_zero, norm_zero, zero_sub]
    rw [max_eq_right (by linarith : -r ≤ 0)]
  · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hsub : y - (min ‖y‖ r / ‖y‖) • y = (1 - min ‖y‖ r / ‖y‖) • y := by
      module
    rw [hsub, norm_smul, Real.norm_eq_abs]
    by_cases h : ‖y‖ ≤ r
    · rw [min_eq_left h, div_self (ne_of_gt hyn), sub_self, abs_zero, zero_mul,
        max_eq_right (by linarith)]
    · rw [min_eq_right (le_of_lt (not_le.mp h)),
        abs_of_nonneg (sub_nonneg.mpr ((div_le_one hyn).mpr (le_of_lt (not_le.mp h)))),
        sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hyn),
        max_eq_left (by linarith [not_le.mp h])]

/-- A point within `a + c` of the origin is within `c` of the closed ball of radius `a`. -/
private lemma exists_closedBall_near {d : ℕ} {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (z : EuclideanSpace ℝ (Fin d)) (hz : ‖z‖ < a + c) :
    ∃ w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) a,
      edist z w ≤ ENNReal.ofReal c := by
  by_cases hza : ‖z‖ ≤ a
  · refine ⟨z, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hza
    · rw [edist_dist, dist_self]
      exact ENNReal.ofReal_le_ofReal hc
  · rw [not_le] at hza
    have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (le_of_lt ha) hza
    have hznz : ‖z‖ ≠ 0 := ne_of_gt hzpos
    have hdiv_lt : a / ‖z‖ < 1 := (div_lt_one hzpos).mpr hza
    have hdiv_nonneg : 0 ≤ a / ‖z‖ := div_nonneg (le_of_lt ha) (norm_nonneg _)
    refine ⟨(a / ‖z‖) • z, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hdiv_nonneg, div_mul_cancel₀ _ hznz]
    · rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      have hsub : z - (a / ‖z‖) • z = (1 - a / ‖z‖) • z := by module
      rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt hdiv_lt))]
      calc (1 - a / ‖z‖) * ‖z‖ = ‖z‖ - a := by
            rw [sub_mul, one_mul, div_mul_cancel₀ _ hznz]
        _ ≤ c := le_of_lt (by linarith)

/-- Every point of the closed ball of radius `a` is within `C Q + 2√d/N` of a rescaled cell
center from the departure range, provided the inner threshold `(a - C Q) N` is contained in
the departure range. -/
private lemma exists_departure_near {d : ℕ} (hd : 1 ≤ d) {Y : ℕ → Site d} {n : ℕ}
    {a C Q N r : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hrdef : r = a - C * Q - Real.sqrt d / N)
    (hCQ : 0 ≤ C * Q + Real.sqrt d / N)
    (hin : {x : Site d | euclidNorm x < (a - C * Q) * N} ⊆ ↑(departureRange Y n))
    (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ a) :
    ∃ x ∈ departureRange Y n,
      edist y (N⁻¹ • toSpace x) ≤ ENNReal.ofReal (C * Q + 2 * Real.sqrt d / N) := by
  set y' : EuclideanSpace ℝ (Fin d) := (min ‖y‖ r / ‖y‖) • y with hy'def
  have hy'norm : ‖y'‖ = min ‖y‖ r := by rw [hy'def]; exact norm_smul_min_div d y hr
  have hysub : ‖y - y'‖ = max (‖y‖ - r) 0 := by
    rw [hy'def]; exact norm_sub_smul_min_div d y hr
  have har : a - r = C * Q + Real.sqrt d / N := by linarith [hrdef]
  have hysub_le : ‖y - y'‖ ≤ a - r := by
    rw [hysub]
    apply max_le
    · linarith
    · rw [har]; exact hCQ
  set x : Site d := cellCenter (N • y') with hxdef
  have hxcell : N • y' ∈ cell x := by rw [hxdef]; exact mem_cell_cellCenter _
  have hxclose : ‖N • y' - toSpace x‖ ≤ Real.sqrt d / 2 :=
    CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hxcell
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < d by omega))
  have hxbound : euclidNorm x < (a - C * Q) * N := by
    have h2 : ‖N • y'‖ = N * min ‖y‖ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hN), hy'norm]
    have h3 : N * min ‖y‖ r ≤ N * r :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hN)
    have h4 : N * r + Real.sqrt d / 2 = (a - C * Q) * N - Real.sqrt d / 2 := by
      rw [hrdef]; field_simp; ring_nf
    rw [← norm_toSpace x]
    have ht : ‖toSpace x‖ ≤ ‖N • y'‖ + ‖N • y' - toSpace x‖ := by
      have h := norm_le_norm_add_norm_sub' (toSpace x) (N • y')
      rwa [norm_sub_rev] at h
    calc ‖toSpace x‖ ≤ ‖N • y'‖ + ‖N • y' - toSpace x‖ := ht
      _ ≤ N * r + Real.sqrt d / 2 := by linarith
      _ = (a - C * Q) * N - Real.sqrt d / 2 := h4
      _ < (a - C * Q) * N := by linarith
  refine ⟨x, hin hxbound, ?_⟩
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  have h1 : dist y (N⁻¹ • toSpace x) ≤ dist y y' + dist y' (N⁻¹ • toSpace x) :=
    dist_triangle y y' _
  have h2 : dist y y' ≤ a - r := by rw [dist_eq_norm]; exact hysub_le
  have h3 : dist y' (N⁻¹ • toSpace x) ≤ N⁻¹ * (Real.sqrt d / 2) := by
    have hmod : y' - N⁻¹ • toSpace x = N⁻¹ • (N • y' - toSpace x) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hN.ne', one_smul]
    rw [dist_eq_norm, hmod, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (inv_pos.mpr hN))]
    exact mul_le_mul_of_nonneg_left hxclose (le_of_lt (inv_pos.mpr hN))
  calc dist y (N⁻¹ • toSpace x) ≤ dist y y' + dist y' (N⁻¹ • toSpace x) := h1
    _ ≤ (a - r) + N⁻¹ * (Real.sqrt d / 2) := add_le_add h2 h3
    _ = C * Q + Real.sqrt d / N + Real.sqrt d / (2 * N) := by
        rw [har]; ring_nf
    _ ≤ C * Q + 2 * Real.sqrt d / N := by
        have hsd : 0 ≤ Real.sqrt d := le_of_lt hsqrt
        have hle : Real.sqrt d / (2 * N) ≤ Real.sqrt d / N := by
          rw [div_le_div_iff₀ (by positivity) hN]
          nlinarith [hsd, hN]
        have h2' : (2 : ℝ) * Real.sqrt d / N = Real.sqrt d / N + Real.sqrt d / N := by
          ring_nf
        rw [h2']
        linarith

/-- `eq:hausdorff` and the planar inner inclusion, deterministically on the fluctuation event:
there are `C'` and `n₀` such that for every path `Y` and every `n ≥ n₀` on which
`fluctGood d ε C Y n` holds, both bounds hold. -/
theorem hausdorff_of_good (hd : 2 ≤ d) {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ C' : ℝ, ∃ n₀ : ℕ, 0 < C' ∧ ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n → fluctGood d ε C Y n →
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      Metric.hausdorffEDist ((fun x => N⁻¹ • toSpace x) '' ↑(visitedRange Y n))
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) a)
        ≤ ENNReal.ofReal (C' * (if d = 2 then (n : ℝ) ^ (-(1 : ℝ) / 12) * L ^ ((5 : ℝ) / 4)
            else (n : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
              * L ^ ((2 * d : ℝ) / (2 * d - 1)))) ∧
      (d = 2 → {x : Site d | euclidNorm x < a * N - C' * (n : ℝ) ^ ((1 : ℝ) / 6)
          * Real.sqrt L} ⊆ ↑(departureRange Y n)) := by
  dsimp only
  have ha0 : 0 < ((d + 1) / (2 * d * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^ ((1 : ℝ) / (d + 1)) :=
    a_pos hd hε
  have hev := eventually_scale_facts (d := d) hd (C := C) (a := ((d + 1) / (2 * d * ε *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^ ((1 : ℝ) / (d + 1))) ha0
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  let C' : ℝ := 2 * C + 2 * Real.sqrt d + 1
  have hC'pos : 0 < C' := by
    dsimp [C']
    linarith [Real.sqrt_nonneg d]
  have hC'ge : C ≤ C' := by
    dsimp [C']
    linarith [Real.sqrt_nonneg d]
  refine ⟨C', max n₀ 1, hC'pos, ?_⟩
  intro Y n hn hgood
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hn₀ n hn₀'
  obtain ⟨hin, hAV, hout, hvol, hprof⟩ := hgood
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hNdef
  set L : ℝ := Real.log (n + 2) with hLdef
  set Q : ℝ := (if d = 2 then (L / N) ^ ((1 : ℝ) / 2)
      else (L / N) ^ ((d : ℝ) / (2 * d - 1))) with hQdef
  let AA : ℝ := ((d + 1) / (2 * d * ε *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^ ((1 : ℝ) / (d + 1))
  clear hvol hprof
  have hQnonneg : 0 ≤ Q := by
    rw [hQdef]
    exact rate_nonneg d n
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hE4
  have hQp_nonneg : 0 ≤ Q ^ ((1 : ℝ) / d) := Real.rpow_nonneg hQnonneg _
  have hQpL_nonneg : 0 ≤ Q ^ ((1 : ℝ) / d) * L := mul_nonneg hQp_nonneg hLnonneg
  have hE5 : N⁻¹ ≤ Q ^ ((1 : ℝ) / d) := by
    rw [hQdef]
    exact rate_inv_le hd hn1 hE3
  have hQ_le : Q ≤ Q ^ ((1 : ℝ) / d) * L := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have h1 : Q ≤ Q ^ ((1 : ℝ) / d) := by
      have hQd : Q ^ (d : ℝ) ≤ Q :=
        Real.rpow_le_self_of_le_one hQnonneg hE2 (by exact_mod_cast (show 1 ≤ d by omega))
      have := (Real.le_rpow_inv_iff_of_pos hQnonneg hQnonneg hdpos).mpr hQd
      simpa only [one_div] using this
    calc Q ≤ Q ^ ((1 : ℝ) / d) := h1
      _ ≤ Q ^ ((1 : ℝ) / d) * L := le_mul_of_one_le_right hQp_nonneg hE3
  have hCQ_nonneg : 0 ≤ C * Q + Real.sqrt d / N := by
    have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
    positivity
  have hr : 0 < ((d + 1) / (2 * d * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^ ((1 : ℝ) / (d + 1))
      - C * Q - Real.sqrt d / N := by
    have h2 : (2 : ℝ) * Real.sqrt d / N = Real.sqrt d / N + Real.sqrt d / N := by ring_nf
    rw [h2] at hE1
    have hsdpos : 0 < Real.sqrt d / N :=
      div_pos (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < d by omega))) hNpos
    linarith [hE1, hsdpos]
  have hcov : C * Q + 2 * Real.sqrt d / N ≤ C' * (Q ^ ((1 : ℝ) / d) * L) := by
    rw [div_eq_mul_inv]
    have h1 : C * Q ≤ C * (Q ^ ((1 : ℝ) / d) * L) :=
      mul_le_mul_of_nonneg_left hQ_le hC
    have h2 : 2 * Real.sqrt d * N⁻¹ ≤ 2 * Real.sqrt d * (Q ^ ((1 : ℝ) / d) * L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hE5.trans (le_mul_of_one_le_right hQp_nonneg hE3)
    calc C * Q + 2 * Real.sqrt d * N⁻¹
        ≤ C * (Q ^ ((1 : ℝ) / d) * L) + 2 * Real.sqrt d * (Q ^ ((1 : ℝ) / d) * L) :=
          add_le_add h1 h2
      _ = (C + 2 * Real.sqrt d) * (Q ^ ((1 : ℝ) / d) * L) := by ring_nf
      _ ≤ C' * (Q ^ ((1 : ℝ) / d) * L) := by
          apply mul_le_mul_of_nonneg_right _ hQpL_nonneg
          linarith
  have hED : Metric.hausdorffEDist ((fun x => N⁻¹ • toSpace x) '' ↑(visitedRange Y n))
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) AA)
      ≤ ENNReal.ofReal (C' * (Q ^ ((1 : ℝ) / d) * L)) := by
    refine Metric.hausdorffEDist_le_of_mem_edist ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hxnorm : euclidNorm x < (AA + C * Q ^ ((1 : ℝ) / d) * L) * N := hout hx
      have hz : ‖N⁻¹ • toSpace x‖ < AA + C * Q ^ ((1 : ℝ) / d) * L := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hNpos)),
          norm_toSpace]
        have hmul : N⁻¹ * ((AA + C * Q ^ ((1 : ℝ) / d) * L) * N)
            = AA + C * Q ^ ((1 : ℝ) / d) * L := by
          field_simp [hNpos.ne']
        calc N⁻¹ * euclidNorm x < N⁻¹ * ((AA + C * Q ^ ((1 : ℝ) / d) * L) * N) :=
              mul_lt_mul_of_pos_left hxnorm (inv_pos.mpr hNpos)
          _ = AA + C * Q ^ ((1 : ℝ) / d) * L := hmul
      obtain ⟨w, hw, hwe⟩ := exists_closedBall_near ha0 (mul_nonneg (mul_nonneg hC hQp_nonneg)
        hLnonneg) _ hz
      exact ⟨w, hw, le_trans hwe (ENNReal.ofReal_le_ofReal (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hC'ge hQpL_nonneg))⟩
    · intro y hy
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      obtain ⟨x, hx, hxe⟩ := exists_departure_near (d := d) (show 1 ≤ d by omega)
        (Y := Y) (n := n) hNpos hr rfl hCQ_nonneg hin y hy
      refine ⟨N⁻¹ • toSpace x, ⟨x, hAV hx, rfl⟩, ?_⟩
      exact le_trans hxe (ENNReal.ofReal_le_ofReal hcov)
  have hrate : Q ^ ((1 : ℝ) / d) * L = (if d = 2 then
        (n : ℝ) ^ (-(1 : ℝ) / 12) * L ^ ((5 : ℝ) / 4)
      else (n : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
        * L ^ ((2 * d : ℝ) / (2 * d - 1))) := by
    rw [hQdef]
    by_cases h2 : d = 2
    · rw [h2] at hNdef ⊢
      simp only [if_true]
      rw [hNdef]
      convert planar_excess_rate (n := (n : ℝ)) (L := L)
        (by exact_mod_cast (show 0 < n by omega)) hLpos using 1
      norm_num
    · simp only [if_neg h2]
      rw [hNdef]
      convert excess_rate (d := d) (n := (n : ℝ)) (L := L)
        (by omega) (by exact_mod_cast (show 0 < n by omega)) hLpos using 1
  refine ⟨?_, ?_⟩
  · rw [← hrate]
    exact hED
  · intro h2
    subst d
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    apply hin
    have hQN : Q * N = (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt L := by
      rw [hQdef]
      simp only [if_true]
      rw [mul_comm]
      rw [hNdef]
      convert planar_inner_rate (n := (n : ℝ)) (L := L)
        (by exact_mod_cast (show 0 < n by omega)) hLpos using 1
      norm_num
    have hQN' : C * Q * N = C * ((n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt L) := by
      rw [mul_assoc, hQN]
    have hs : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt L :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.sqrt_nonneg _)
    have hkey : C * Q * N ≤ C' * (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt L := by
      rw [hQN']
      nlinarith [hC'ge, hs]
    let E : ℝ := (((2 : ℝ) + 1) / (2 * (2 : ℝ) * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal))
      ^ ((1 : ℝ) / ((2 : ℝ) + 1))
    have hle : E * N - C' * (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt L ≤ (E - C * Q) * N := by
      rw [sub_mul]
      linarith [hkey]
    exact lt_of_lt_of_le hx hle

end CERW.Support.Main
