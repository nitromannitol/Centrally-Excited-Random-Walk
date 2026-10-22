import CERW.Support.Outer.Radius.HigherDimensionRadius

/-!
# Planar Radius

The planar exterior and crossing estimates bound the outer radius. Positivity of the inner-ball
potential controls the remaining annular terms.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The planar absorption: from `w ≤ K₁ lg (1 + L)` and `L ≤ C₂ (t √w + t²)` with `t⁴ = r lg`. -/
lemma co_planar_arith {K₁ C₂ lg r w L : ℝ} (hK₁ : 0 ≤ K₁) (hC₂ : 0 ≤ C₂)
    (hlg : 1 ≤ lg) (hr : 1 ≤ r) (hw : 0 ≤ w)
    (h1 : w ≤ K₁ * lg * (1 + L))
    (h2 : L ≤ C₂ * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg))) :
    w ≤ (2 * K₁ + (K₁ * C₂) ^ 2 + 2 * K₁ * C₂) * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by
  have hr0 : 0 ≤ r := by linarith
  have hlg0 : 0 < lg := by linarith
  set t : ℝ := (r * lg) ^ ((1 : ℝ) / 4) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have ht2 : t ^ 2 = Real.sqrt r * lg ^ ((1 : ℝ) / 2) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [show ((1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = 1 / 2 by push_cast; ring,
      Real.mul_rpow hr0 hlg0.le, Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (r * lg) = t ^ 2 := by
    rw [ht2, Real.sqrt_mul hr0, Real.sqrt_eq_rpow lg]
  set u : ℝ := Real.sqrt w with hu
  have hu2 : u ^ 2 = w := Real.sq_sqrt hw
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  rw [hsq] at h2
  have h3 : w ≤ K₁ * lg + K₁ * C₂ * lg * t * u + K₁ * C₂ * lg * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ K₁ * lg)
    nlinarith
  have hamgm : K₁ * C₂ * lg * t * u ≤ w / 2 + (K₁ * C₂ * lg * t) ^ 2 / 2 := by
    have := two_mul_le_add_sq u (K₁ * C₂ * lg * t)
    rw [hu2] at this
    nlinarith
  have h4 : w ≤ 2 * K₁ * lg + (K₁ * C₂) ^ 2 * lg ^ 2 * t ^ 2 + 2 * K₁ * C₂ * lg * t ^ 2 := by
    nlinarith
  have hl1 : lg ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    have h5 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
    have h6 : lg ≤ lg ^ ((5 : ℝ) / 2) := by
      calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ lg ^ ((5 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hlg (by norm_num)
    calc lg ≤ lg ^ ((5 : ℝ) / 2) := h6
      _ = 1 * lg ^ ((5 : ℝ) / 2) := (one_mul _).symm
      _ ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hlg0.le _)
  have h52 : lg ^ 2 * t ^ 2 = Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    rw [ht2, show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add hlg0, Real.rpow_two]
    ring
  have h32 : lg * t ^ 2 ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    rw [← h52, sq lg]
    have h7 : lg * t ^ 2 * 1 ≤ lg * t ^ 2 * lg :=
      mul_le_mul_of_nonneg_left hlg (by positivity)
    calc lg * t ^ 2 = lg * t ^ 2 * 1 := (mul_one _).symm
      _ ≤ lg * t ^ 2 * lg := h7
      _ = lg * lg * t ^ 2 := by ring
  have hK : 0 ≤ K₁ * C₂ := mul_nonneg hK₁ hC₂
  have e1 : 2 * K₁ * lg ≤ 2 * K₁ * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hl1 (by positivity)
  have e2 : (K₁ * C₂) ^ 2 * (lg ^ 2 * t ^ 2) =
      (K₁ * C₂) ^ 2 * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by
    rw [h52]
  have e3 : 2 * K₁ * C₂ * (lg * t ^ 2) ≤
      2 * K₁ * C₂ * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left h32 (by positivity)
  have e4 : (2 * K₁ + (K₁ * C₂) ^ 2 + 2 * K₁ * C₂) * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) =
      2 * K₁ * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) +
        (K₁ * C₂) ^ 2 * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) +
        2 * K₁ * C₂ * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by ring
  have e5 : (K₁ * C₂) ^ 2 * lg ^ 2 * t ^ 2 = (K₁ * C₂) ^ 2 * (lg ^ 2 * t ^ 2) := by ring
  have e6 : 2 * K₁ * C₂ * lg * t ^ 2 = 2 * K₁ * C₂ * (lg * t ^ 2) := by ring
  rw [e4]
  rw [e5, e6] at h4
  linarith

/-- The potential of a set outside the ball of radius `b` is nonnegative inside that ball. -/
lemma co_potential_nonneg_inside (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) {b : ℝ}
    (hsub : E ⊆ {v | b ≤ ‖v‖}) {y : EuclideanSpace ℝ (Fin d)} (hy : ‖y‖ ≤ b) :
    0 ≤ potential d ε E y := by
  unfold potential
  refine mul_nonneg (by have := unitBallVolume_pos d; positivity) ?_
  refine setIntegral_nonneg hE fun v hv => ?_
  by_cases hvy : v = y
  · rw [hvy]; simp
  · have h1 := CERW.Support.Contact.rpow_le_inner_unitDir_div hd (hy.trans (hsub hv)) hvy
    exact le_trans (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (norm_nonneg _) _)) h1

/-- The potential is at most its positive part. -/
lemma co_potential_le_positive (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (y : EuclideanSpace ℝ (Fin d)) : potential d ε E y ≤ positivePotential d ε E y := by
  unfold potential positivePotential
  refine mul_le_mul_of_nonneg_left ?_ (by have := unitBallVolume_pos d; positivity)
  have hint := CERW.Support.Geometry.integrableOn_potentialIntegrand hd hE
    hEb.measure_lt_top.ne y
  exact integral_mono hint hint.pos_part fun v => le_max_left _ _

/-- Proposition `prop:stronger-outer`, `d = 2`, deterministically. -/
theorem outer_core_planar (hd : d = 2) (hnear : near_far) {ε : ℝ}
    (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Ccr : ℝ) (hCin : 0 < Cin)
    (hCcr : 0 < Ccr) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      LocalPathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → CrossOK d Ccr Y n →
      maxRadius Y n ≤
        radius d ε n + C * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Cp, hCp, np, hpl⟩ := planar_exterior hd hnear hε hεd C₀ C₁ Cin
    (Cin * (1 + d * unitBallVolume d))
  set K₁ : ℝ := Ccr + 2 * Real.sqrt d / Real.log 2 with hK₁
  have hK₁pos : 0 < K₁ := by positivity
  set Mc : ℝ := (2 * d * ε + 1) * Cin with hMc
  set B : ℝ := K₁ * (1 + Mc) with hB
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((tk_small hd2 hε B).and
    ((tk_qrate_le_one hd1 hε).and (tk_log_pow_le hd1 hε (A := 0) le_rfl 1 (s := 1) one_pos)))
  set Kw : ℝ := 2 * K₁ + (K₁ * (2 * Cp)) ^ 2 + 2 * K₁ * (2 * Cp) with hKw
  refine ⟨Cin + Kw, by positivity, max (max n₁ np) 3, ?_⟩
  intro Y n hn hP hI hC
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hnp : np ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  obtain ⟨hsm, hq1, hr1⟩ := hn₁ n hn1
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  have hlg1 : 1 ≤ lg := by
    rw [hlg_def, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact this.le.trans (by exact_mod_cast hn3)
  have hlg2 : Real.log 2 ≤ lg := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hlg0 : 0 < lg := by linarith
  simp only [Real.rpow_zero, mul_one, Real.rpow_one] at hr1
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  set w := R - b + 2 * Real.sqrt d with hw_def
  have hbR := innerRadius_le hd1 Y n
  have hw0 : 0 < w := by rw [hw_def]; linarith
  have hb0 := innerRadius_nonneg Y n
  have hpath : ∀ j, euclidNorm (Y j) ≤ j :=
    CERW.Support.Occupation.euclidNorm_le_of_steps Y hP.start hP.step
  have hRn : R ≤ n := co_maxRadius_le hpath
  have hrq := radius_mul_qrate hd1 hε (by omega : 1 ≤ n)
  rw [if_pos hd] at hrq
  have hbr : |b - r| ≤ Cin * Real.sqrt (r * lg) := by
    have := hI.1
    calc |b - r| ≤ Cin * r * qrate d ε n := this
      _ = Cin * (r * qrate d ε n) := by ring
      _ = Cin * Real.sqrt (r * lg) := by rw [hrq]
  -- the maximal local time
  have hX0 : 0 ≤ r * qrate d ε n ^ ((1 : ℝ) / d) := by
    have := co_qrate_pos hd1 hε hn2
    positivity
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  have hM0 : 0 ≤ Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) := mul_nonneg hMc0 hX0
  have hL : (outerMax Y n b : ℝ) ≤ Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) := by
    refine co_outerMax_le hM0 fun z _ hz => ?_
    exact co_local_le hd1 hε hCin hn2 hI hq1 hz
  have hcr := hC b hb0
  have hL0 : (0 : ℝ) ≤ (outerMax Y n b : ℝ) := Nat.cast_nonneg _
  have hw1 : w ≤ K₁ * lg * (1 + (outerMax Y n b : ℝ)) := by
    have h2 : 2 * Real.sqrt d ≤ (2 * Real.sqrt d / Real.log 2) * lg := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      exact mul_le_mul_of_nonneg_left hlg2 (by positivity)
    have h3 : (2 * Real.sqrt d / Real.log 2) * lg ≤
        (2 * Real.sqrt d / Real.log 2) * lg * (1 + (outerMax Y n b : ℝ)) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have h4 : Ccr * (1 + (outerMax Y n b : ℝ)) * lg =
        Ccr * lg * (1 + (outerMax Y n b : ℝ)) := by ring
    have h5 : K₁ * lg * (1 + (outerMax Y n b : ℝ)) =
        Ccr * lg * (1 + (outerMax Y n b : ℝ)) +
          (2 * Real.sqrt d / Real.log 2) * lg * (1 + (outerMax Y n b : ℝ)) := by
      rw [hK₁]; ring
    rw [hw_def, h5]
    linarith
  have hw2 : w ≤ K₁ * lg * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) :=
    hw1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hpowcast : lg ^ ((d : ℝ) + 1) = lg ^ (d + 1) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  have hwr : w ≤ r / lg := by
    rw [le_div_iff₀ hlg0]
    have hsm' : B * lg ^ (d + 1) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) ≤ r := by
      rw [← hpowcast]; exact hsm
    have hlg2' : lg ^ 2 ≤ lg ^ (d + 1) := pow_le_pow_right₀ hlg1 (by omega)
    calc w * lg ≤ K₁ * lg * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) * lg :=
          mul_le_mul_of_nonneg_right hw2 hlg0.le
      _ = K₁ * lg ^ 2 * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) := by ring
      _ ≤ K₁ * lg ^ (d + 1) * ((1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d))) := by
          have h1 : 1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) ≤
              (1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) := by
            have h2 : (1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) =
                1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) +
                  (r * qrate d ε n ^ ((1 : ℝ) / d) + Mc) := by ring
            rw [h2]
            linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hlg2' hK₁pos.le) h1 (by positivity)
            (by positivity)
      _ = B * lg ^ (d + 1) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) := by rw [hB]; ring
      _ ≤ r := hsm'
  have hmass := mass_of_inner hd2 hε hCin.le Y (by omega : 1 ≤ n) hI
  obtain ⟨hpt, hpos⟩ := hpl Y n hnp hP hI hmass (by rw [← hr_def]; exact hwr)
  have hE : MeasurableSet (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    (CERW.Support.Occupation.measurableSet_cellSet Y n).diff Metric.isOpen_ball.measurableSet
  have hEb : Bornology.IsBounded (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)).subset Set.sdiff_subset
  have hL2 : (outerMax Y n b : ℝ) ≤ (2 * Cp) * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w +
      Real.sqrt (r * lg)) := by
    have hbound0 : 0 ≤ (2 * Cp) * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w +
        Real.sqrt (r * lg)) := by positivity
    refine co_outerMax_le hbound0 fun z hz hbz => ?_
    have hzR : euclidNorm z ≤ R :=
      LatticeProb.mem_ballFinset_iff.mp
        (CERW.Support.Occupation.departureRange_subset_ballFinset Y n hz)
    have hRn' : (R : ℝ) ≤ n := hRn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : |(localTime Y n z : ℝ) - potential d ε (cellSet Y n \ Metric.ball 0 b)
        (toSpace z)| ≤ Cp * Real.sqrt (r * lg) := hpt z hbz (by linarith)
    have h2 : positivePotential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace z) ≤
        Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) :=
      hpos (toSpace z) (by rw [norm_toSpace]; exact hbz) (by rw [norm_toSpace]; linarith)
    have h3 := co_potential_le_positive hd1 hε.le hE hEb (toSpace z)
    have h4 := (abs_le.mp h1).2
    have hA : 0 ≤ Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w) := by positivity
    linarith
  have hw3 := co_planar_arith (K₁ := K₁) (C₂ := 2 * Cp) hK₁pos.le (by positivity) hlg1 hr1
    hw0.le hw1 hL2
  have hT : Real.sqrt (r * lg) ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) := by
    have h5 : Real.sqrt lg ≤ lg ^ ((5 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hlg1 (by norm_num)
    rw [Real.sqrt_mul hr.le]
    exact mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)
  have hRb : R ≤ b + w := by rw [hw_def]; linarith
  have hb2 := (abs_le.mp hbr).2
  have hZ0 : 0 ≤ Real.sqrt r * lg ^ ((5 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlg0.le _)
  have h6 : Cin * Real.sqrt (r * lg) ≤ Cin * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hT hCin.le
  have h7 : (Cin + Kw) * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) =
      Cin * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) + Kw * (Real.sqrt r * lg ^ ((5 : ℝ) / 2)) := by
    ring
  rw [h7]
  linarith

end CERW.Support.Outer.Radius
