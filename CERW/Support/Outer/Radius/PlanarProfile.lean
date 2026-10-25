module

public import CERW.Support.Outer.Radius.PlanarProfileBounds

@[expose] public section

/-!
# Planar Profile

The planar inner and outer estimates give a uniform local-time profile. The error is bounded by the
square root of the radius times the three-halves power of the logarithm.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- Theorem `thm:fluctuations` (iii), `d = 2`, deterministically. -/
theorem local_core_planar (hd : d = 2) (hnear : near_far) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Cout : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hCin : 0 < Cin) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      LocalPathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n →
      maxRadius Y n ≤
        radius d ε n + Cout * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) →
      ∀ x : Site d, |(localTime Y n x : ℝ) - 2 * d * ε * max (radius d ε n - euclidNorm x) 0| ≤
        C * (Real.sqrt (radius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  obtain ⟨a, ha, hra⟩ := tk_radius_eq hd1 hε
  obtain ⟨Cp, hCp, np, hpl⟩ := planar_exterior hd hnear hε hεd C₀ C₁ Cin
    (Cin * (1 + d * unitBallVolume d))
  set Kw : ℝ := Cin + max Cout 0 + 2 * Real.sqrt d with hKw
  have hKw0 : 0 < Kw := by rw [hKw]; positivity
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1
    ((tk_log_pow_le hd1 hε (A := (7 : ℝ) / 2) (by norm_num) Kw (s := 1 / 2) (by norm_num)).and
      ((tk_log_pow_le hd1 hε (A := (1 : ℝ) / 2) (by norm_num) (2 * Cin) (s := 1 / 2)
        (by norm_num)).and
      (tk_log_pow_le hd1 hε (A := 0) le_rfl 1 (s := 1) one_pos)))
  set Cδ : ℝ := C₁ * (2 * Real.sqrt (C₀ / a) + 2) with hCδ
  set Cbd : ℝ := Cp * (Real.sqrt Kw + 1) with hCbd
  set C : ℝ := Cδ + 2 * d * ε * (Cin + Real.sqrt d) + Cbd with hC
  have hCpos : 0 < C := by rw [hC, hCδ, hCbd]; positivity
  refine ⟨C, hCpos, max (max n₁ np) 3, ?_⟩
  intro Y n hn hP hI hout x
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by omega
  have hnp : np ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  obtain ⟨h1, h2, h3⟩ := hn₁ n hn1
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  set r := radius d ε n with hr_def
  set lg := Real.log n with hlg_def
  have hlg1 : 1 ≤ lg := by
    rw [hlg_def, Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    exact this.le.trans (by exact_mod_cast hn3)
  have hlg0 : 0 < lg := by linarith
  simp only [Real.rpow_zero, mul_one, Real.rpow_one] at h3
  set b := innerRadius Y n with hb_def
  set R := maxRadius Y n with hR_def
  set w := R - b + 2 * Real.sqrt d with hw_def
  have hbR := innerRadius_le hd1 Y n
  have hb0 := innerRadius_nonneg Y n
  have hw0 : 0 < w := by rw [hw_def]; linarith
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
  have hbr1 := abs_le.mp hbr
  obtain ⟨hwb, hwr, hbhalf⟩ := co_planar_width (Kw := Kw) hCin hsd hKw h3 hlg1 h1 h2 hbr hout
  have hbpos : 0 < b := by linarith
  have hmass := mass_of_inner hd2 hε hCin.le Y (by omega : 1 ≤ n) hI
  obtain ⟨-, hpos⟩ := hpl Y n hnp hP hI hmass (by rw [← hr_def]; exact hwr)
  have hD := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDb : Bornology.IsBounded (cellSet Y n) :=
    Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 Y n)
  have hE : MeasurableSet (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    hD.diff Metric.isOpen_ball.measurableSet
  have hEb : Bornology.IsBounded (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) :=
    hDb.subset Set.sdiff_subset
  have hsubE : cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ {v | b ≤ ‖v‖} := by
    intro v hv
    have h := hv.2
    rw [Metric.mem_ball, dist_zero_right, not_lt] at h
    exact h
  set Z : ℝ := Real.sqrt r * lg ^ ((3 : ℝ) / 2) with hZ
  have hlg32 : lg ≤ lg ^ ((3 : ℝ) / 2) := by
    calc lg = lg ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ lg ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hlg1 (by norm_num)
  have hlg12 : Real.sqrt lg ≤ lg ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlg1 (by norm_num)
  have hsr1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr h3
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hT : Real.sqrt (r * lg) ≤ Z := by
    rw [Real.sqrt_mul hr.le, hZ]
    exact mul_le_mul_of_nonneg_left hlg12 (Real.sqrt_nonneg _)
  have hlgZ : lg ≤ Z := by
    calc lg ≤ 1 * lg ^ ((3 : ℝ) / 2) := by rw [one_mul]; exact hlg32
      _ ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hsr1 (Real.rpow_nonneg hlg0.le _)
  have hbd1 := co_planar_bd hKw0.le hlg1 h3 hwb
  have hBd : Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) ≤ Cbd * Z := by
    have : (r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg) ≤
        (Real.sqrt Kw + 1) * Z := by
      rw [add_mul, one_mul]; exact add_le_add hbd1 hT
    rw [hCbd, mul_assoc]
    exact mul_le_mul_of_nonneg_left this hCp.le
  have hposy : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ R + 2 * Real.sqrt d →
      positivePotential d ε (cellSet Y n \ Metric.ball 0 b) y ≤
        Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) :=
    fun y h1 h2 => hpos y h1 h2
  have hM : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = b → potential d ε
      (cellSet Y n \ Metric.ball 0 b) y ≤
        Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) := fun y hy =>
    (co_potential_le_positive hd1 hε.le hE hEb y).trans
      (hposy y hy.ge (by rw [hy]; linarith))
  have hmp := planar_max_principle hd hε hE hEb hbpos hsubE hM
  have hCS : 0 ≤ 2 * d * ε := by positivity
  set Bd : ℝ := Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) with hBd_def
  have hBd0 : 0 ≤ Bd := by rw [hBd_def]; positivity
  have hCδZ : 0 ≤ Cδ * Z := by rw [hCδ]; positivity
  have hCbdZ : 0 ≤ Cbd * Z := by rw [hCbd]; positivity
  by_cases hxR : euclidNorm x ≤ R
  · have hy : ‖toSpace x‖ ≤ 2 * n := by
      rw [norm_toSpace]
      have : (R : ℝ) ≤ n := hRn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hg := hP.glob (toSpace x) hy
    rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell x), if_pos hd] at hg
    have hsplit := potential_split hd2 ε hD hDb hbpos (ball_innerRadius_subset hd1 Y n)
      (toSpace x)
    rw [norm_toSpace] at hsplit
    have hM' : (maxLocalTime Y n : ℝ) ≤ C₀ * (r / a) := by
      have h1 := hP.maxLoc
      have h2 : r / a = (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
        rw [hr_def, hra n]; field_simp
      rw [h2]; exact h1
    have hδ : C₁ * (Real.sqrt (maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2) +
        Real.log ((n : ℝ) + 2)) ≤ Cδ * Z := by
      rw [hCδ, hZ]
      exact co_planar_delta hC₀.le hC₁ ha h3 hlg1 hM' (mono_log_nonneg n)
        (co_log_add_two_le hn2)
    have hcone : |max (b - euclidNorm x) 0 - max (r - euclidNorm x) 0| ≤
        Cin * Real.sqrt (r * lg) := by
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      have : (b - euclidNorm x) - (r - euclidNorm x) = b - r := by ring
      rw [this]; exact hbr
    have hCZ : Cδ * Z + 2 * d * ε * (Cin * Z) + Cbd * Z ≤ C * Z := by
      have h8 : C * Z = Cδ * Z + 2 * d * ε * (Cin * Z) + 2 * d * ε * (Real.sqrt d * Z) +
          Cbd * Z := by rw [hC]; ring
      have h9 : 0 ≤ 2 * d * ε * (Real.sqrt d * Z) := by positivity
      rw [h8]; linarith
    have hCin0 := hCin.le
    by_cases hxb : euclidNorm x ≤ b
    · -- inside the inner ball
      have hUE0 := co_potential_nonneg_inside hd2 hε.le hE hsubE
        (y := toSpace x) (by rw [norm_toSpace]; exact hxb)
      have hUEM : potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x) ≤ Bd :=
        hmp (toSpace x) (by rw [norm_toSpace]; exact hxb)
      have hdiff : |2 * d * ε * max (b - euclidNorm x) 0 - 2 * d * ε * max (r - euclidNorm x) 0| ≤
          2 * d * ε * (Cin * Real.sqrt (r * lg)) := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hCS]
        exact mul_le_mul_of_nonneg_left hcone hCS
      exact co_planar_inside hCS hg hsplit hdiff hUE0 hUEM hδ hBd hT hCin0 hCZ
    · -- between the inner ball and the outer radius
      rw [not_le] at hxb
      have hUE : potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x) ≤ Bd :=
        (co_potential_le_positive hd1 hε.le hE hEb _).trans
          (hposy (toSpace x) (by rw [norm_toSpace]; exact hxb.le)
            (by rw [norm_toSpace]; linarith))
      have hU0 : 2 * d * ε * max (b - euclidNorm x) 0 = 0 := by
        rw [max_eq_right (by linarith)]; ring
      have hlow : (localTime Y n x : ℝ) ≤ Cδ * Z +
          potential d ε (cellSet Y n \ Metric.ball 0 b) (toSpace x) := by
        have h1 := (abs_le.mp hg).2
        rw [hsplit, hU0] at h1
        linarith
      have hconeN : 2 * d * ε * max (r - euclidNorm x) 0 ≤
          2 * d * ε * (Cin * Real.sqrt (r * lg)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCS
        refine max_le ?_ (by positivity)
        linarith [hbr1.1]
      exact co_planar_between hCS (Nat.cast_nonneg _) (by positivity) hlow hUE hconeN hBd hT
        hCin0 hZ0 hCZ
  · rw [not_le] at hxR
    rw [co_localTime_eq_zero hxR]
    simp only [Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    have h8 : C * Z = Cδ * Z + 2 * d * ε * ((Cin + Real.sqrt d) * Z) + Cbd * Z := by
      rw [hC]; ring
    exact co_planar_outside hCS hCin hsd hlg1 hlgZ hT hbr hbR hxR h8 hCδZ hCbdZ

/-! ### Proposition `prop:stronger-outer` -/

end CERW.Support.Outer.Radius
