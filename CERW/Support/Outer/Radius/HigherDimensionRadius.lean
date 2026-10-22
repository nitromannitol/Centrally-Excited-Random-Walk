import CERW.Support.Outer.Radius.RadiusAsymptotics

/-!
# Higher Dimension Radius

The higher-dimensional exterior and crossing estimates bound the outer radius. Elementary local-time
bounds supply the inputs at large times.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- For `n ≥ 2`, `log (n + 2) ≤ 2 log n`. -/
lemma co_log_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith) (by nlinarith)
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- The path stays within distance `n` of the origin. -/
lemma co_maxRadius_le {Y : ℕ → Site d} {n : ℕ} (hpath : ∀ j, euclidNorm (Y j) ≤ j) :
    maxRadius Y n ≤ n := by
  unfold maxRadius
  refine Finset.sup'_le _ _ fun j hj => (hpath j).trans ?_
  exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

/-- A visited site lies within the maximal radius, so off that ball the local time vanishes. -/
lemma co_localTime_eq_zero {Y : ℕ → Site d} {n : ℕ} {x : Site d}
    (hx : maxRadius Y n < euclidNorm x) : localTime Y n x = 0 := by
  by_contra h
  have h1 : x ∈ departureRange Y n := mem_departureRange_iff.mpr (Nat.pos_of_ne_zero h)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h1
  exact absurd (euclidNorm_le_maxRadius Y (Finset.mem_range.mp hj).le) (not_le.mpr hx)

/-- The maximal local time over the sites beyond a radius is bounded by a bound on each one. -/
lemma co_outerMax_le {Y : ℕ → Site d} {n : ℕ} {b M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z ∈ departureRange Y n, b ≤ euclidNorm z → (localTime Y n z : ℝ) ≤ M) :
    (outerMax Y n b : ℝ) ≤ M := by
  have h1 : outerMax Y n b ≤ ⌊M⌋₊ := by
    refine Finset.sup_le fun z hz => ?_
    rw [Finset.mem_filter] at hz
    exact Nat.le_floor (h z hz.1 hz.2)
  exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hM)

/-- The rate `q_n` is positive for `n ≥ 2`. -/
lemma co_qrate_pos (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    0 < qrate d ε n := by
  rw [tk_qrate_eq hd hε hn]
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Real.rpow_pos_of_pos (div_pos hlog hr) _

/-- Beyond the inner radius the local times are at most `C r q^{1/d}` (from the profile clause
of Proposition `prop:inner` and the inner radius clause). -/
lemma co_local_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {Cin : ℝ} (hCin : 0 < Cin)
    {Y : ℕ → Site d} {n : ℕ} (hn : 2 ≤ n) (hI : InnerOK d ε Cin Y n)
    (hq : qrate d ε n ≤ 1) {z : Site d} (hz : innerRadius Y n ≤ euclidNorm z) :
    (localTime Y n z : ℝ) ≤
      (2 * d * ε + 1) * Cin * (radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) := by
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hq0 := co_qrate_pos hd hε hn
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨i1, -, i3⟩ := hI
  have h3 := i3 (toSpace z)
  rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell z), norm_toSpace] at h3
  have hb := (abs_le.mp i1).1
  have hmax : max (radius d ε n - euclidNorm z) 0 ≤ Cin * radius d ε n * qrate d ε n := by
    refine max_le (by linarith) (by positivity)
  have hqq : qrate d ε n ≤ qrate d ε n ^ ((1 : ℝ) / d) := by
    have h1 : (1 : ℝ) / d ≤ 1 := by
      rw [div_le_one hd0]; exact_mod_cast hd
    calc qrate d ε n = qrate d ε n ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ qrate d ε n ^ ((1 : ℝ) / d) :=
          Real.rpow_le_rpow_of_exponent_ge hq0 hq h1
  have hqd : 0 ≤ qrate d ε n ^ ((1 : ℝ) / d) := Real.rpow_nonneg hq0.le _
  have h4 := (abs_le.mp h3).2
  have h5 : 2 * d * ε * max (radius d ε n - euclidNorm z) 0 ≤
      2 * d * ε * (Cin * radius d ε n * qrate d ε n) :=
    mul_le_mul_of_nonneg_left hmax (by positivity)
  have h6 : Cin * radius d ε n * qrate d ε n ≤ Cin * radius d ε n * qrate d ε n ^ ((1 : ℝ) / d) :=
    mul_le_mul_of_nonneg_left hqq (by positivity)
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * d * ε) hCin.le) hr.le]

/-- Proposition `prop:stronger-outer`, `d ≥ 3`, deterministically. -/
theorem outer_core_high (hd : 3 ≤ d) (hN : NewtonConv d) (hnear : near_far) {ε : ℝ}
    (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Ccr : ℝ) (hCin : 0 < Cin)
    (hCcr : 0 < Ccr) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      LocalPathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n → CrossOK d Ccr Y n →
      maxRadius Y n ≤ radius d ε n + C * Real.log n ^ ((d : ℝ) + 1) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Kh, hKh, nh, hhx⟩ := high_exterior hd hN hnear hε hεd C₀ C₁ Cin
    (Cin * (1 + d * unitBallVolume d))
  set K₁ : ℝ := Ccr + 2 * Real.sqrt d / Real.log 2 with hK₁
  have hK₁pos : 0 < K₁ := by positivity
  obtain ⟨Ka, hKa, harith⟩ := arith_high hd K₁ Kh Kh hK₁pos hKh hKh
  set Mc : ℝ := (2 * d * ε + 1) * Cin with hMc
  set B : ℝ := max Ka 8 * (K₁ * (1 + Mc)) with hB
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((tk_small hd2 hε B).and (tk_qrate_le_one hd1 hε))
  refine ⟨Cin + Ka, by positivity, max (max n₁ nh) 3, ?_⟩
  intro Y n hn hP hI hC
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hnh : nh ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  obtain ⟨hsm, hq1⟩ := hn₁ n hn1
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  have hlg1 : 1 ≤ lg := by
    rw [hlg_def, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact this.le.trans (by exact_mod_cast hn3)
  have hlg2 : Real.log 2 ≤ lg := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  set w := R - b + 2 * Real.sqrt d with hw_def
  have hbR := innerRadius_le hd1 Y n
  have hw0 : 0 < w := by rw [hw_def]; linarith
  have hb0 := innerRadius_nonneg Y n
  -- the maximal local time
  have hM0 : 0 ≤ Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) := by
    have := co_qrate_pos hd1 hε hn2
    positivity
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
  -- smallness of the width
  have hw2 : w ≤ K₁ * lg * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) := by
    refine hw1.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hlgd : 1 ≤ lg ^ d := one_le_pow₀ hlg1
  have hsm' : B * lg ^ ((d : ℝ) + 1) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) ≤ r := hsm
  have hX0 : 0 ≤ r * qrate d ε n ^ ((1 : ℝ) / d) := by
    have := co_qrate_pos hd1 hε hn2
    positivity
  have hMc0 : 0 ≤ Mc := by rw [hMc]; positivity
  have hmax0 : 0 ≤ max Ka 8 := le_trans (by norm_num) (le_max_right _ _)
  have hpowcast : lg ^ ((d : ℝ) + 1) = lg ^ (d + 1) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  have hw3 : max Ka 8 * lg ^ d * w ≤ r := by
    calc max Ka 8 * lg ^ d * w ≤ max Ka 8 * lg ^ d * (K₁ * lg * (1 + Mc *
          (r * qrate d ε n ^ ((1 : ℝ) / d)))) :=
          mul_le_mul_of_nonneg_left hw2 (by positivity)
      _ = max Ka 8 * K₁ * lg ^ (d + 1) * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d))) := by
          rw [pow_succ]; ring
      _ ≤ B * lg ^ ((d : ℝ) + 1) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) := by
          rw [hpowcast, hB]
          have h1 : 1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) ≤
              (1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) := by
            have h2 : (1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d)) =
                1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)) +
                  (r * qrate d ε n ^ ((1 : ℝ) / d) + Mc) := by ring
            rw [h2]
            linarith
          calc max Ka 8 * K₁ * lg ^ (d + 1) * (1 + Mc * (r * qrate d ε n ^ ((1 : ℝ) / d)))
              ≤ max Ka 8 * K₁ * lg ^ (d + 1) * ((1 + Mc) * (1 + r * qrate d ε n ^ ((1 : ℝ) / d))) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = _ := by ring
      _ ≤ r := hsm'
  have hw4 : w ≤ r / 8 := by
    have h8 : 8 * w ≤ max Ka 8 * lg ^ d * w := by
      refine mul_le_mul_of_nonneg_right ?_ hw0.le
      calc (8 : ℝ) = 8 * 1 := by norm_num
        _ ≤ max Ka 8 * lg ^ d := mul_le_mul (le_max_right _ _) hlgd zero_le_one hmax0
    linarith
  have hw5 : Ka * lg ^ d * w ≤ r := by
    refine le_trans ?_ hw3
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)) hw0.le
  have hmass := mass_of_inner hd2 hε hCin.le Y (by omega : 1 ≤ n) hI
  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ := hhx Y n hnh hP hI hmass (by rw [← hr_def]; exact hw4)
  have hfin := harith lg r w (outerMax Y n b : ℝ) Θ hlg1 hr hw0.le hL0 hw1 hΘ3 hΘ1 hΘ2 hw5
  have hbr : b ≤ r + Cin * lg := by
    have h1 := (abs_le.mp hI.1).2
    have h2 := radius_mul_qrate hd1 hε (by omega : 1 ≤ n)
    rw [if_neg (by omega : d ≠ 2)] at h2
    have h3 : Cin * r * qrate d ε n = Cin * (r * qrate d ε n) := by ring
    rw [h3, h2] at h1
    linarith
  have hlgle : lg ≤ lg ^ ((d : ℝ) + 1) := by
    calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ lg ^ ((d : ℝ) + 1) :=
          Real.rpow_le_rpow_of_exponent_le hlg1 (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
  have hpow0 : 0 ≤ lg ^ ((d : ℝ) + 1) := Real.rpow_nonneg (by linarith) _
  have hRw : R ≤ b + w := by rw [hw_def]; linarith
  rw [hpowcast] at hlgle hpow0 ⊢
  calc R ≤ b + w := hRw
    _ ≤ r + Cin * lg + Ka * lg ^ (d + 1) := by linarith
    _ ≤ r + (Cin + Ka) * lg ^ (d + 1) := by
        have h1 := mul_le_mul_of_nonneg_left hlgle hCin.le
        have h2 : (Cin + Ka) * lg ^ (d + 1) = Cin * lg ^ (d + 1) + Ka * lg ^ (d + 1) := by ring
        rw [h2]
        linarith

end CERW.Support.Outer.Radius
