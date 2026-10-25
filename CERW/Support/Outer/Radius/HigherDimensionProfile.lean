module

public import CERW.Support.Outer.Radius.PlanarRadius

@[expose] public section

/-!
# Higher Dimension Profile

The inner estimate and higher-dimensional outer-radius bound control the local-time profile
uniformly in space. The error has order the square root of the product of the radius and the
logarithm.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- Theorem `thm:fluctuations` (iii), `d ≥ 3`, deterministically. -/
theorem local_core_high (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (C₀ C₁ Cin Cout : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hCin : 0 < Cin) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      LocalPathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n →
      maxRadius Y n ≤ radius d ε n + Cout * Real.log n ^ ((d : ℝ) + 1) →
      ∀ x : Site d, |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
        C * Real.sqrt (radius d ε n * Real.log n) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  obtain ⟨a, ha, hra⟩ := tk_radius_eq hd1 hε
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1
    (((tk_log_pow_le hd1 hε (A := (d : ℝ) + 1) (by positivity) 1 (s := 1 / 2)
        (by norm_num)).and
      (tk_log_pow_le hd1 hε (A := 1) zero_le_one (2 * Cin) (s := 1) one_pos)).and
      (tk_log_pow_le hd1 hε (A := 1) zero_le_one 1 (s := 1) one_pos))
  set Cδ : ℝ := C₁ * (Real.sqrt (2 * C₀ / a) + 2) with hCδ
  set Cw : ℝ := Cin + max Cout 0 + 2 * Real.sqrt d with hCw
  set C : ℝ := Cδ + 2 * d * ε * (Cw + Cin + Real.sqrt d) with hC
  have hCpos : 0 < C := by rw [hC, hCδ, hCw]; positivity
  refine ⟨C, hCpos, max n₁ 3, ?_⟩
  intro Y n hn hP hI hout x
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨⟨h1, h2⟩, h3⟩ := hn₁ n hn1
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  have hlg1 : 1 ≤ lg := by
    rw [hlg_def, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact this.le.trans (by exact_mod_cast hn3)
  have hlg0 : 0 < lg := by linarith
  simp only [Real.rpow_one, one_mul] at h2 h3
  rw [one_mul] at h1
  have hb0 := innerRadius_nonneg Y n
  have hbR := innerRadius_le hd1 Y n
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  have hrq := radius_mul_qrate hd1 hε (by omega : 1 ≤ n)
  rw [if_neg (by omega : d ≠ 2)] at hrq
  have hbr : |b - r| ≤ Cin * lg := by
    have := hI.1
    calc |b - r| ≤ Cin * r * qrate d ε n := this
      _ = Cin * (r * qrate d ε n) := by ring
      _ = Cin * lg := by rw [hrq]
  have hbr1 := abs_le.mp hbr
  have hbpos : 0 < b := by nlinarith
  have hpow1 : lg ≤ lg ^ ((d : ℝ) + 1) := by
    calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ lg ^ ((d : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le hlg1 (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  set P := lg ^ ((d : ℝ) + 1) with hP_def
  have hS : P ≤ Real.sqrt (r * lg) := by
    calc P ≤ r ^ ((1 : ℝ) / 2) := h1
      _ = Real.sqrt r := (Real.sqrt_eq_rpow r).symm
      _ ≤ Real.sqrt (r * lg) := Real.sqrt_le_sqrt (le_mul_of_one_le_right hr.le hlg1)
  set S := Real.sqrt (r * lg) with hS_def
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hlgS : lg ≤ S := hpow1.trans hS
  have hw0 : 0 < R - b + 2 * Real.sqrt d := by linarith
  have hwP : R - b + 2 * Real.sqrt d ≤ Cw * P := by
    have hout' : R ≤ r + Cout * P := hout
    have hc : Cout * P ≤ max Cout 0 * P :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    have h4 : Cin * lg ≤ Cin * P := mul_le_mul_of_nonneg_left hpow1 hCin.le
    have h5 : 2 * Real.sqrt d ≤ 2 * Real.sqrt d * P :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have h6 : Cw * P = Cin * P + max Cout 0 * P + 2 * Real.sqrt d * P := by rw [hCw]; ring
    rw [h6]
    linarith [hbr1.1]
  have hD := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDb : Bornology.IsBounded (cellSet Y n) :=
    Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)
  have hE : MeasurableSet (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    hD.diff Metric.isOpen_ball.measurableSet
  have hpath : ∀ j, euclidNorm (Y j) ≤ j :=
    CERW.Support.Occupation.euclidNorm_le_of_steps Y hP.start hP.step
  have hRn : R ≤ n := co_maxRadius_le hpath
  have hCS : 0 ≤ 2 * d * ε := by positivity
  by_cases hxR : euclidNorm x ≤ R
  · -- inside the ball of radius R
    have hy : ‖toSpace x‖ ≤ 2 * n := by
      rw [norm_toSpace]
      have : (R : ℝ) ≤ n := hRn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hg := hP.glob (toSpace x) hy
    rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell x), if_neg (by omega : d ≠ 2)] at hg
    have hsplit := potential_split hd2 ε hD hDb hbpos (ball_innerRadius_subset hd1 Y n)
      (toSpace x)
    have hann := annulus_potential_le hd2 hε hw0 hE (sdiff_subset_annulus hd1 Y n) (toSpace x)
    rw [norm_toSpace] at hsplit
    have hM : (maxLocalTime Y n : ℝ) ≤ C₀ * (r / a) := by
      have h1 := hP.maxLoc
      have h2 : r / a = (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
        rw [hr_def, hra n]; field_simp
      rw [h2]; exact h1
    have hL' : Real.log ((n : ℝ) + 2) ≤ 2 * lg := co_log_add_two_le hn2
    have hL'0 : 0 ≤ Real.log ((n : ℝ) + 2) := mono_log_nonneg n
    have hM0 : (0 : ℝ) ≤ (maxLocalTime Y n : ℝ) := Nat.cast_nonneg _
    have hsq : Real.sqrt ((maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2)) ≤
        Real.sqrt (2 * C₀ / a) * S := by
      rw [hS_def, ← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      calc (maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2) ≤ (C₀ * (r / a)) * (2 * lg) :=
            mul_le_mul hM hL' hL'0 (by positivity)
        _ = 2 * C₀ / a * (r * lg) := by ring
    have hδ : C₁ * (Real.sqrt ((maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2)) +
        Real.log ((n : ℝ) + 2)) ≤ Cδ * S := by
      rw [hCδ]
      have : Real.sqrt ((maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2)) +
          Real.log ((n : ℝ) + 2) ≤ (Real.sqrt (2 * C₀ / a) + 2) * S := by
        rw [add_mul]; linarith
      exact mul_le_mul_of_nonneg_left this hC₁.le |>.trans_eq (by ring)
    have hcone : |max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0| ≤ Cin * lg := by
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      have : (b - euclidNorm x) - (r - euclidNorm x) = b - r := by ring
      rw [this]; exact hbr
    have hCwP : 2 * d * ε * (Cw * P) ≤ 2 * d * ε * (Cw * S) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS (by rw [hCw]; positivity)) hCS
    have hCinlg : 2 * d * ε * (Cin * lg) ≤ 2 * d * ε * (Cin * S) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlgS hCin.le) hCS
    have hann' : |potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x)| ≤
        2 * d * ε * (Cw * P) :=
      hann.trans (mul_le_mul_of_nonneg_left hwP hCS)
    have hconeb : 2 * d * ε * |max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0| ≤
        2 * d * ε * (Cin * lg) := mul_le_mul_of_nonneg_left hcone hCS
    have hfinal : |(localTime Y n x : ℝ) - 2 * d * ε * max (r - euclidNorm x) 0| ≤
        Cδ * S + 2 * d * ε * (Cin * lg) + 2 * d * ε * (Cw * P) := by
      have e1 : (localTime Y n x : ℝ) - 2 * d * ε * max (r - euclidNorm x) 0 =
          ((localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)) +
            (2 * d * ε * (max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0) +
              potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x)) := by
        rw [hsplit]; ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      have h2 := (abs_add_le (2 * d * ε * (max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0))
        (potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x)))
      rw [abs_mul, abs_of_nonneg hCS] at h2
      linarith
    have hCS' : 0 ≤ Cδ * S := by rw [hCδ]; positivity
    calc _ ≤ Cδ * S + 2 * d * ε * (Cin * lg) + 2 * d * ε * (Cw * P) := hfinal
      _ ≤ Cδ * S + 2 * d * ε * (Cin * S) + 2 * d * ε * (Cw * S) := by linarith
      _ ≤ C * S := by
        have h8 : C * S = Cδ * S + 2 * d * ε * (Cin * S) + 2 * d * ε * (Cw * S) +
            2 * d * ε * (Real.sqrt d * S) := by rw [hC]; ring
        have h9 : 0 ≤ 2 * d * ε * (Real.sqrt d * S) := by positivity
        rw [h8]
        linarith
  · -- outside the ball of radius R
    rw [not_le] at hxR
    rw [co_localTime_eq_zero hxR]
    have hrR : r - euclidNorm x ≤ (Cin + Real.sqrt d) * S := by
      have h1 : r - R ≤ r - b + Real.sqrt d / 2 := by linarith
      have h2 : r - b ≤ Cin * lg := by linarith [hbr1.1]
      have h3 : Real.sqrt d / 2 ≤ Real.sqrt d * S := by
        calc Real.sqrt d / 2 ≤ Real.sqrt d * 1 := by linarith
          _ ≤ Real.sqrt d * S := mul_le_mul_of_nonneg_left (hlg1.trans hlgS) hsd.le
      have h4 : Cin * lg ≤ Cin * S := mul_le_mul_of_nonneg_left hlgS hCin.le
      have h5 : (Cin + Real.sqrt d) * S = Cin * S + Real.sqrt d * S := by ring
      rw [h5]
      linarith
    have hmax : max (r - euclidNorm x) 0 ≤ (Cin + Real.sqrt d) * S :=
      max_le hrR (by positivity)
    simp only [Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    calc 2 * d * ε * max (r - euclidNorm x) 0 ≤ 2 * d * ε * ((Cin + Real.sqrt d) * S) :=
          mul_le_mul_of_nonneg_left hmax hCS
      _ ≤ C * S := by
        rw [hC]
        have : 0 ≤ Cδ * S := by rw [hCδ]; positivity
        have h6 : 2 * d * ε * (Cw + Cin + Real.sqrt d) * S =
            2 * d * ε * ((Cin + Real.sqrt d) * S) + 2 * d * ε * (Cw * S) := by ring
        have h7 : 0 ≤ 2 * d * ε * (Cw * S) := by rw [hCw]; positivity
        have h8 : C * S = Cδ * S + 2 * d * ε * (Cw + Cin + Real.sqrt d) * S := by rw [hC]; ring
        rw [h8, h6]
        linarith

end CERW.Support.Outer.Radius
