import CERW.Support.Outer.SourceDisplays
import CERW.Support.Outer.NearFar
import CERW.Support.Lower.SeparatedBracketsEvent
import CERW.Frozen.InnerRadius

/-!
# The real-point profile of the plane and the displays on the seven-estimate event

This module proves the assertions of the last subsection of the outer-radius section that the
lattice statements of the proofs do not state, and composes the full displays with the literal
event of Section 5.1.

* `hasGradientAt_log_norm_sub` is the identity `(v - y)|v - y|^{-2} = -∇_y log |v - y|`, as a
  statement about the gradient, for `y ≠ v`; `harmonicAt_neg_gradient_log_coordinate` combines it
  with the harmonicity of the coordinates of the Newton field.
* `PlanarRealProfile` collects the real-point displays of the uniform bound on the local times
  for `d = 2`: the estimate `U_E(y) ≤ C √r_n (log n)^{3/2}` of the excess potential at every real
  `y` with `|y| ≤ b + w` (and its real supremum, `planar_real_profile_sup`), the two-region
  estimates of `ℓ~_n(y) - 2dε (r_n - |y|)_+` for `|y| ≤ b` and `|y| ≥ b`, and the uniform bound.
  `planar_real_profile_prob` proves it with probability at least `1 - C n^{-p}`.
* `planar_displays_on_E7` and `envelope_high_on_E7` compose the planar displays and the full
  higher-dimensional envelope with the event `E7` of the seven estimates, at every legal sample
  point and at every sample point of the legal carrier, with constants and thresholds chosen
  before the probability space, the walk, the sample point and the time.
* `volume_cellSet_diff_ball_innerRadius_pos` shows that the excess set `D_n ∖ B(0, R_in(n))` has
  positive area (`d ≥ 2`), so that the maximum principle is applied to a genuine set.
  `planar_potential_le_of_circle` and `planar_potential_nonneg_inside` are the two inputs of the
  maximum principle as used in the source, and `planar_potential_annulus_maximum_principle` consumes
  them for a set of positive area.
* `exists_realization_planar_on_E7` and `exists_realization_envelope_high_on_E7` consume the
  displays at an actual walk: a sample point of the event, legal, with real interior and exterior
  points that are not lattice sites, and `planar_newton_gradient_at_real_point` consumes the
  gradient identity at a real nonsingular point.

No display is assumed. The producers are the proved event of Sections 3-5, the proved clauses of
`prop:inner` and `prop:stronger-outer`, the maximum principle for the planar potential, the bound
on the positive potential in the annulus and the seven estimates of the event.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.PlanarReal

open CERW CERW.Support.Statements CERW.Support.Outer.SourceDisplays
  CERW.Support.Norm.ContactEvent CERW.Support.Norm.Section5Localization
open private PathFacts PathFacts.mk InnerOK radius qrate planar_exterior planar_max_principle
  co_potential_nonneg_inside co_potential_le_positive potential_split co_planar_width
  co_planar_bd co_planar_delta co_maxRadius_le co_log_add_two_le mono_log_nonneg mass_of_inner
  tk_log_pow_le tk_radius_eq innerRadius_le innerRadius_nonneg ball_innerRadius_subset
  radius_pos radius_mul_qrate exists_pathFacts_prob measure_le_union_three
  one_le_ofReal_mul_rpow gd_maxRadius_nonneg ev_braSum_eq braSum
  from CERW.Support.Outer.OuterRadius
open private pathFacts_of_estimates7 crossOK_of_estimates7 outer_bound innerOK_of_innerConclusion
  from CERW.Support.Lower.SeparatedBracketsEvent

variable {d : ℕ}

/-! ## The planar Newton field as a negative gradient -/

/-- **The Newton field is the negative gradient of the logarithm.** For `v ≠ y` in a real inner
product space, `y' ↦ log |v - y'|` has gradient `-(v - y) / |v - y|²` at `y`. -/
theorem hasGradientAt_log_norm_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (v y : E) (hvy : y ≠ v) :
    HasGradientAt (fun y' : E => Real.log ‖v - y'‖) (-((‖v - y‖ ^ 2)⁻¹ • (v - y))) y := by
  have hne : v - y ≠ 0 := sub_ne_zero.mpr hvy.symm
  have hn2 : ‖v - y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have hu : HasFDerivAt (fun y' : E => v - y') (-(ContinuousLinearMap.id ℝ E)) y :=
    (hasFDerivAt_id y).const_sub v
  have h1 : HasFDerivAt (fun y' : E => ‖v - y'‖ ^ 2)
      ((2 • innerSL ℝ (v - y)).comp (-(ContinuousLinearMap.id ℝ E))) y :=
    (hasStrictFDerivAt_norm_sq (v - y)).hasFDerivAt.comp y hu
  have h2 := (h1.log hn2).const_mul (1 / 2 : ℝ)
  have hfun : (fun y' : E => Real.log ‖v - y'‖) =
      fun y' => (1 / 2 : ℝ) * Real.log (‖v - y'‖ ^ 2) := by
    funext y'
    rw [Real.log_pow]
    push_cast
    ring
  rw [hasGradientAt_iff_hasFDerivAt, hfun]
  refine h2.congr_fderiv ?_
  ext z
  simp only [InnerProductSpace.toDual_apply_apply, smul_apply,
    ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, inner_neg_left, inner_neg_right, real_inner_smul_left, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The identity `(v - y)|v - y|^{-2} = -∇_y log |v - y|`** in the plane, for `y ≠ v`. -/
theorem planar_newton_field_eq_neg_gradient_log (v y : EuclideanSpace ℝ (Fin 2)) (hvy : y ≠ v) :
    (‖v - y‖ ^ 2)⁻¹ • (v - y) =
      -gradient (fun y' : EuclideanSpace ℝ (Fin 2) => Real.log ‖v - y'‖) y := by
  rw [(hasGradientAt_log_norm_sub v y hvy).gradient, neg_neg]

/-- **Each coordinate of `-∇_y log |v - y|` is harmonic in `y ≠ v`** (the sentence of the source
that precedes the maximum principle): the coordinates of the gradient of the logarithm agree
near `y` with the coordinates of the Newton field, which are harmonic. -/
theorem harmonicAt_neg_gradient_log_coordinate (v y : EuclideanSpace ℝ (Fin 2)) (hvy : y ≠ v)
    (i : Fin 2) :
    InnerProductSpace.HarmonicAt
      (fun y' : EuclideanSpace ℝ (Fin 2) =>
        (-gradient (fun z : EuclideanSpace ℝ (Fin 2) => Real.log ‖v - z‖) y') i) y := by
  have hev : ∀ᶠ y' in 𝓝 y, y' ≠ v := isOpen_ne.mem_nhds hvy
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp (harmonicAt_planar_newton_field v y hvy i)
  filter_upwards [hev] with y' hy'
  rw [← planar_newton_field_eq_neg_gradient_log v y' hy']
  simp [div_eq_inv_mul]


/-! ## The real-point profile of the plane -/

/-- **The real-point displays of the uniform bound on the local times in the plane**
(Section 7, last subsection). For a path `Y`, a time `n` and a constant `C`, with `b = R_in(n)`,
`w = R_out(n) - b + 2√d`, `E = D_n ∖ B(0,b)`, `r = r_n` and `Z = √r_n (log n)^{3/2}`:

* the excess potential satisfies `U_E(y) ≤ C Z` at every real `y` with `|y| ≤ b + w`;
* at every real `y` with `|y| ≤ b`, `|ℓ~_n(y) - 2dε (r - |y|)_+| ≤ C (Z + |b - r|)`;
* at every real `y` with `|y| ≥ b`, `|ℓ~_n(y) - 2dε (r - |y|)_+|` is at most the larger of the
  nonnegative numbers `ℓ~_n(y)` and `2dε (r - |y|)_+`; `2dε (r - |y|)_+ ≤ 2dε |b - r|`;
  if `|y| ≤ b + w` then `ℓ~_n(y) ≤ U_E(y) + C √r_n log n`; and if `|y| > b + w` then
  `ℓ~_n(y) = 0`;
* at every real `y`, `|ℓ~_n(y) - 2dε (r - |y|)_+| ≤ C Z`. -/
def PlanarRealProfile (d : ℕ) (ε C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  (∀ y : EuclideanSpace ℝ (Fin d),
      ‖y‖ ≤ innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) →
      potential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y ≤
        C * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2))) ∧
  (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ innerRadius Y n →
      |cellLocalTime Y n y - 2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0| ≤
        C * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2) +
          |innerRadius Y n - sourceRadius d ε n|)) ∧
  (∀ y : EuclideanSpace ℝ (Fin d), innerRadius Y n ≤ ‖y‖ →
      |cellLocalTime Y n y - 2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0| ≤
        max (cellLocalTime Y n y) (2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0) ∧
      2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0 ≤
        2 * d * ε * |innerRadius Y n - sourceRadius d ε n| ∧
      (‖y‖ ≤ innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) →
        cellLocalTime Y n y ≤
          potential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y +
            C * (Real.sqrt (sourceRadius d ε n) * Real.log n)) ∧
      (innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) < ‖y‖ →
        cellLocalTime Y n y = 0)) ∧
  (∀ y : EuclideanSpace ℝ (Fin d),
      |cellLocalTime Y n y - 2 * d * ε * max (sourceRadius d ε n - ‖y‖) 0| ≤
        C * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2)))

/-- The real supremum of the excess potential over the disc `|y| ≤ b + w` is attained below
`C Z`: the range is bounded above and the supremum is at most `C Z`. -/
theorem planar_real_profile_sup {d : ℕ} {ε C : ℝ} {Y : ℕ → Site d} {n : ℕ}
    (h : PlanarRealProfile d ε C Y n) :
    BddAbove (Set.range fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
        (innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d)) =>
      potential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y) ∧
    (⨆ y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
        (innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d)),
      potential d ε (cellSet Y n \ Metric.ball 0 (innerRadius Y n)) y) ≤
      C * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2)) := by
  have h1 := h.1
  refine ⟨⟨C * (Real.sqrt (sourceRadius d ε n) * Real.log n ^ ((3 : ℝ) / 2)), ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact h1 y (mem_closedBall_zero_iff.mp y.2)
  · have h2 : 0 ≤ innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) := by
      have h3 := gd_maxRadius_nonneg Y n
      have h4 := Real.sqrt_nonneg (d : ℝ)
      linarith
    haveI : Nonempty (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
        (innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d))) :=
      ⟨⟨0, Metric.mem_closedBall_self h2⟩⟩
    exact ciSup_le fun y => h1 y (mem_closedBall_zero_iff.mp y.2)

/-! ### Scalar arithmetic of the real-point profile -/

/-- For nonnegative `a`, `b`, `|a - b| ≤ max a b`. -/
private lemma abs_sub_le_max_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : |a - b| ≤ max a b :=
  abs_le.mpr ⟨by linarith [le_max_right a b], by linarith [le_max_left a b]⟩

/-- Inside the inner ball the local time is within `C (Z + β)` of the cone. -/
private lemma real_inside_arith {ℓ U Ub UE cone δ Bd Cδ Cbd Z β D C : ℝ}
    (hg : |ℓ - U| ≤ δ) (hU : U = Ub + UE) (hdiff : |Ub - cone| ≤ D * β) (hUE0 : 0 ≤ UE)
    (hUE : UE ≤ Bd) (hδ : δ ≤ Cδ * Z) (hBd : Bd ≤ Cbd * Z) (hZ : 0 ≤ Z) (hβ : 0 ≤ β)
    (hC1 : Cδ + Cbd ≤ C) (hC2 : D ≤ C) : |ℓ - cone| ≤ C * (Z + β) := by
  have h2 : ℓ - cone = (ℓ - U) + (Ub - cone) + UE := by rw [hU]; ring
  rw [h2]
  have h3 := abs_add_le ((ℓ - U) + (Ub - cone)) UE
  have h4 := abs_add_le (ℓ - U) (Ub - cone)
  rw [abs_of_nonneg hUE0] at h3
  have h5 : Cδ * Z + Cbd * Z ≤ C * Z := by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right hC1 hZ
  have h6 : D * β ≤ C * β := mul_le_mul_of_nonneg_right hC2 hβ
  have h7 : C * (Z + β) = C * Z + C * β := by ring
  rw [h7]
  linarith


/-! ### The deterministic core -/

/-- A point outside the cell set has local time zero. -/
private lemma cellLocalTime_eq_zero_of_not_mem (Y : ℕ → Site d) (n : ℕ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∉ cellSet Y n) : cellLocalTime Y n y = 0 := by
  by_contra hne
  have hpos : 0 < localTime Y n (cellCenter y) := by
    have h : cellLocalTime Y n y = (localTime Y n (cellCenter y) : ℝ) := rfl
    rw [h] at hne
    exact Nat.pos_of_ne_zero (by intro h0; apply hne; simp [h0])
  exact hy (Set.mem_iUnion₂.mpr ⟨cellCenter y, mem_departureRange_iff.mpr hpos,
    mem_cell_cellCenter y⟩)

/-- **The real-point displays, deterministically.** Let `d = 2` and `0 < ε < 1/2`. For the constants
of the path facts and of the inner and outer radius estimates there are `C` and `n₀` such that every
path with the path facts, the clauses of `prop:inner` and the outer radius bound at a time
`n ≥ n₀` has `PlanarRealProfile`. The near-far lemma, the maximum principle for the potential, the
bound on the positive potential in the annulus and the global approximation at the exact scale are
produced by existing proved terms. -/
private theorem planar_real_profile_core (hd : d = 2) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (C₀ C₁ Cin Cout : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hCin : 0 < Cin) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      PathFacts d ε C₀ C₁ Y n → InnerOK d ε Cin Y n →
      maxRadius Y n ≤
        radius d ε n + Cout * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) →
      PlanarRealProfile d ε C Y n := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  obtain ⟨a, ha, hra⟩ := tk_radius_eq hd1 hε
  obtain ⟨Cp, hCp, np, hpl⟩ := planar_exterior hd CERW.Support.Outer.near_far_holds hε hεd C₀ C₁
    Cin (Cin * (1 + d * unitBallVolume d))
  obtain ⟨Cg, hCg, ng, hglobal⟩ := global_approximation_scale hd2 hε C₀ C₁
  set Kw : ℝ := Cin + max Cout 0 + 2 * Real.sqrt d with hKw
  have hKw0 : 0 < Kw := by rw [hKw]; positivity
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1
    ((tk_log_pow_le hd1 hε (A := (7 : ℝ) / 2) (by norm_num) Kw (s := 1 / 2) (by norm_num)).and
      ((tk_log_pow_le hd1 hε (A := (1 : ℝ) / 2) (by norm_num) (2 * Cin) (s := 1 / 2)
        (by norm_num)).and
      (tk_log_pow_le hd1 hε (A := 0) le_rfl 1 (s := 1) one_pos)))
  set Cδ : ℝ := C₁ * (2 * Real.sqrt (C₀ / a) + 2) with hCδ
  set Cbd : ℝ := Cp * (Real.sqrt Kw + 1) with hCbd
  set C0 : ℝ := Cδ + Cbd + 2 * d * ε + Cg with hC0
  set C : ℝ := C0 * (1 + Cin) + 1 with hC
  have hCδ0 : 0 ≤ Cδ := by rw [hCδ]; positivity
  have hCbd0 : 0 ≤ Cbd := by rw [hCbd]; positivity
  have hdε0 : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hC00 : 0 ≤ C0 := by rw [hC0]; linarith [hCg.le]
  have hCpos : 0 < C := by rw [hC, mul_add, mul_one]; linarith [mul_nonneg hC00 hCin.le]
  have hC0C : C0 ≤ C := by rw [hC, mul_add, mul_one]; linarith [mul_nonneg hC00 hCin.le]
  have hCuni : C0 * (1 + Cin) ≤ C := by rw [hC]; linarith
  refine ⟨C, hCpos, max (max (max n₁ np) (max ng ⌈2 * Real.sqrt d⌉₊)) 3, ?_⟩
  intro Y n hn hP hI hout
  simp only [max_le_iff] at hn
  obtain ⟨⟨⟨hn1, hnp⟩, hng, hceil⟩, hn3⟩ := hn
  have hn2 : 2 ≤ n := by omega
  have h2sd : 2 * Real.sqrt d ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  obtain ⟨h1, h2, h3⟩ := hn₁ n hn1
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  have hP' := hP
  obtain ⟨hstart, hstep, hmaxloc, -, hglob, -, -⟩ := hP'
  unfold PlanarRealProfile
  rw [show sourceRadius d ε n = radius d ε n from rfl]
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
    CERW.Support.Occupation.euclidNorm_le_of_steps Y hstart hstep
  have hRn : R ≤ n := co_maxRadius_le hpath
  have hR0 := gd_maxRadius_nonneg Y n
  have hbw : b + w = R + 2 * Real.sqrt d := by rw [hw_def]; ring
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
  have hrlgZ : Real.sqrt r * lg ≤ Z := by
    rw [hZ]
    exact mul_le_mul_of_nonneg_left hlg32 (Real.sqrt_nonneg _)
  have hlgZ : lg ≤ Z := by
    calc lg ≤ 1 * lg ^ ((3 : ℝ) / 2) := by rw [one_mul]; exact hlg32
      _ ≤ Real.sqrt r * lg ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hsr1 (Real.rpow_nonneg hlg0.le _)
  have hbrZ : |b - r| ≤ Cin * Z := hbr.trans (mul_le_mul_of_nonneg_left hT hCin.le)
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
  set Bd : ℝ := Cp * ((r * lg) ^ ((1 : ℝ) / 4) * Real.sqrt w + Real.sqrt (r * lg)) with hBd_def
  have hCbdC' : Cbd ≤ C := by linarith [hC0C, hC0, hCδ0, hdε0, hCg.le]
  have hCgC : Cg ≤ C := by linarith [hC0C, hC0, hCδ0, hCbd0, hdε0]
  have hdεC0 : 2 * (d : ℝ) * ε ≤ C0 := by linarith [hC0, hCδ0, hCbd0, hCg.le]
  -- every point of the disc `|y| ≤ b + w` is within the range of the global approximation
  have hb2n : b + w ≤ 2 * n := by rw [hbw]; linarith
  have hUE : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ b + w →
      potential d ε (cellSet Y n \ Metric.ball 0 b) y ≤ Bd := by
    intro y hy
    by_cases hyb : ‖y‖ ≤ b
    · exact hmp y hyb
    · push Not at hyb
      exact (co_potential_le_positive hd1 hε.le hE hEb y).trans
        (hposy y hyb.le (by rw [← hbw]; exact hy))
  have hM' : (maxLocalTime Y n : ℝ) ≤ C₀ * (r / a) := by
    have h1 := hmaxloc
    have h2 : r / a = (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
      rw [hr_def, hra n]; field_simp
    rw [h2]; exact h1
  have hδ : C₁ * (Real.sqrt (maxLocalTime Y n : ℝ) * Real.log ((n : ℝ) + 2) +
      Real.log ((n : ℝ) + 2)) ≤ Cδ * Z := by
    rw [hCδ, hZ]
    exact co_planar_delta hC₀.le hC₁ ha h3 hlg1 hM' (mono_log_nonneg n) (co_log_add_two_le hn2)
  have hglob2 : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ b + w →
      |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ Cδ * Z := by
    intro y hy
    have hg := hglob y (hy.trans hb2n)
    rw [if_pos hd] at hg
    exact hg.trans hδ
  have hsplit : ∀ y : EuclideanSpace ℝ (Fin d), potential d ε (cellSet Y n) y =
      2 * d * ε * max (b - ‖y‖) 0 + potential d ε (cellSet Y n \ Metric.ball 0 b) y :=
    fun y => potential_split hd2 ε hD hDb hbpos (ball_innerRadius_subset hd1 Y n) y
  have hcone : ∀ y : EuclideanSpace ℝ (Fin d), |max (b - ‖y‖) 0 - max (r - ‖y‖) 0| ≤ |b - r| := by
    intro y
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have : (b - ‖y‖) - (r - ‖y‖) = b - r := by ring
    rw [this]
  have hconeb : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ →
      max (r - ‖y‖) 0 ≤ |b - r| := by
    intro y hy
    refine max_le ?_ (abs_nonneg _)
    have h5 : r - b ≤ |b - r| := by rw [← abs_neg, neg_sub]; exact le_abs_self _
    linarith
  have hfar : ∀ y : EuclideanSpace ℝ (Fin d), b + w < ‖y‖ → cellLocalTime Y n y = 0 := by
    intro y hy
    refine cellLocalTime_eq_zero_of_not_mem Y n fun hmem => ?_
    have := CERW.Support.Occupation.norm_le_of_mem_cellSet Y n hmem
    rw [hbw] at hy
    linarith
  have hinside : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ b →
      |cellLocalTime Y n y - 2 * d * ε * max (r - ‖y‖) 0| ≤ C0 * (Z + |b - r|) := by
    intro y hy
    have hyw : ‖y‖ ≤ b + w := by linarith
    have hUE0 := co_potential_nonneg_inside hd2 hε.le hE hsubE (y := y) hy
    have hdiff : |2 * d * ε * max (b - ‖y‖) 0 - 2 * d * ε * max (r - ‖y‖) 0| ≤
        2 * d * ε * |b - r| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hdε0]
      exact mul_le_mul_of_nonneg_left (hcone y) hdε0
    exact real_inside_arith (hglob2 y hyw) (hsplit y) hdiff hUE0 (hUE y hyw) le_rfl hBd hZ0
      (abs_nonneg _) (by linarith [hdε0, hCg.le]) hdεC0
  have hcone_le : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ →
      2 * d * ε * max (r - ‖y‖) 0 ≤ C * Z := by
    intro y hy
    have e1 : 2 * (d : ℝ) * ε * (Cin * Z) ≤ C0 * (Cin * Z) :=
      mul_le_mul_of_nonneg_right hdεC0 (mul_nonneg hCin.le hZ0)
    have e2 : C0 * (Cin * Z) ≤ C0 * ((1 + Cin) * Z) :=
      mul_le_mul_of_nonneg_left (by rw [add_mul, one_mul]; linarith [hZ0]) hC00
    have e3 : C0 * ((1 + Cin) * Z) ≤ C * Z := by
      calc C0 * ((1 + Cin) * Z) = (C0 * (1 + Cin)) * Z := by ring
        _ ≤ C * Z := mul_le_mul_of_nonneg_right hCuni hZ0
    calc 2 * d * ε * max (r - ‖y‖) 0 ≤ 2 * d * ε * |b - r| :=
          mul_le_mul_of_nonneg_left (hconeb y hy) hdε0
      _ ≤ 2 * d * ε * (Cin * Z) := mul_le_mul_of_nonneg_left hbrZ hdε0
      _ ≤ C * Z := by linarith
  have hell : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
      cellLocalTime Y n y ≤
        potential d ε (cellSet Y n \ Metric.ball 0 b) y + Cg * (Real.sqrt r * lg) := by
    intro y hyb hyw
    have hg := hglobal Y n hng hmaxloc hglob y (hyw.trans hb2n)
    rw [if_pos hd] at hg
    have hg' : |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ Cg * (Real.sqrt r * lg) :=
      hg
    have hU0 : 2 * d * ε * max (b - ‖y‖) 0 = 0 := by
      rw [max_eq_right (by linarith)]; ring
    have h5 := (abs_le.mp hg').2
    rw [hsplit y, hU0] at h5
    linarith
  have hell_le : ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
      cellLocalTime Y n y ≤ C * Z := by
    intro y hyb hyw
    have h5 := hell y hyb hyw
    have h6 := hUE y hyw
    have h7 : Cg * (Real.sqrt r * lg) ≤ Cg * Z := mul_le_mul_of_nonneg_left hrlgZ hCg.le
    have h8 : Cbd * Z + Cg * Z ≤ C0 * Z := by
      rw [hC0, add_mul, add_mul, add_mul]
      have : 0 ≤ Cδ * Z := mul_nonneg hCδ0 hZ0
      have : 0 ≤ 2 * (d : ℝ) * ε * Z := mul_nonneg hdε0 hZ0
      linarith
    have h9 : C0 * Z ≤ C * Z := mul_le_mul_of_nonneg_right hC0C hZ0
    linarith
  refine ⟨fun y hy => (hUE y hy).trans (hBd.trans (mul_le_mul_of_nonneg_right hCbdC' hZ0)),
    fun y hy => (hinside y hy).trans (mul_le_mul_of_nonneg_right hC0C
      (add_nonneg hZ0 (abs_nonneg _))),
    fun y hyb => ⟨abs_sub_le_max_of_nonneg (cellLocalTime_nonneg Y n y) (by positivity),
      mul_le_mul_of_nonneg_left (hconeb y hyb) hdε0, fun hyw => ?_, hfar y⟩, fun y => ?_⟩
  · have h5 := hell y hyb hyw
    have h7 : Cg * (Real.sqrt r * lg) ≤ C * (Real.sqrt r * lg) :=
      mul_le_mul_of_nonneg_right hCgC (by positivity)
    linarith
  · by_cases hyb : ‖y‖ ≤ b
    · refine (hinside y hyb).trans ?_
      calc C0 * (Z + |b - r|) ≤ C0 * (Z + Cin * Z) :=
            mul_le_mul_of_nonneg_left (add_le_add_right hbrZ Z) hC00
        _ = (C0 * (1 + Cin)) * Z := by ring
        _ ≤ C * Z := mul_le_mul_of_nonneg_right hCuni hZ0
    · push Not at hyb
      by_cases hyw : ‖y‖ ≤ b + w
      · refine (abs_sub_le_max_of_nonneg (cellLocalTime_nonneg Y n y) (by positivity)).trans
          (max_le (hell_le y hyb.le hyw) (hcone_le y hyb.le))
      · push Not at hyw
        rw [hfar y hyw, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
        exact hcone_le y hyb.le


/-! ### The real-point displays with high probability -/

/-- **The real-point displays of the uniform bound on the local times in the plane, with high
probability.** For `d = 2`, `0 < ε < 1/2` and `p > 0` there are constants `C`, `Cp`, chosen before
the probability space, the walk and `n`, such that for every centrally excited random walk and every
`n ≥ 2`, with probability at least `1 - Cp n^{-p}` the walk has `PlanarRealProfile` with constant
`C`. The event of Sections 3-5, the clauses of the proved `prop:inner` and the proved outer radius
bound of `prop:stronger-outer` are the producers; nothing about the profile is assumed. -/
theorem planar_real_profile_prob (hd : d = 2) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C Cp : ℝ, 0 < C ∧ 0 < Cp ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ PlanarRealProfile d ε C (fun j => X j ω) n} ≤
          ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨C₀, C₁, Cf, hC₀, hC₁, hCf, hfl⟩ := exists_pathFacts_prob hd2 hε hεd hp
  obtain ⟨Cin, hCin, hin⟩ := CERW.Frozen.inner_radius hd2 ε hε hεd p hp
  obtain ⟨Co, hCo, hout⟩ := (CERW.Support.Outer.outer_radius_of @CERW.Frozen.inner_radius.{u}
    CERW.Support.Outer.near_far_holds CERW.Support.Norm.outer_crossing_holds) hd2 ε hε hεd p hp
  obtain ⟨C, hC, n₀, hcore⟩ := planar_real_profile_core hd hε hεd C₀ C₁ Cin Co hC₀ hC₁ hCin
  have hn₀p : 0 < ((n₀ : ℝ) + 1) ^ p := Real.rpow_pos_of_pos (by positivity) p
  refine ⟨C, Cf + Cin + Co + ((n₀ : ℝ) + 1) ^ p, hC, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn2
  have hnp0 : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  by_cases hnb : n₀ ≤ n
  · have h1 : μ {ω | ¬ PathFacts d ε C₀ C₁ (fun j => X j ω) n} ≤ _ := hfl μ X hX n hn2
    have h2 : μ {ω | ¬ InnerOK d ε Cin (fun j => X j ω) n} ≤ _ := hin μ X hX n hn2
    have h3 := hout μ X hX n hn2
    refine measure_le_union_three (hS := ?_) h1 h2 h3 (mul_nonneg hCf.le hnp0)
      (mul_nonneg hCin.le hnp0) ?_ (mul_nonneg hCo.le hnp0)
    · intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      obtain ⟨⟨hA, hB⟩, hD⟩ := hcon
      apply hω
      have hD' : maxRadius (fun j => X j ω) n ≤ radius d ε n +
          Co * (Real.sqrt (radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)) := by
        have := hD
        rw [if_pos hd] at this
        exact this
      exact hcore _ n hnb hA hB hD'
    · calc Cf * (n : ℝ) ^ (-p) + Cin * (n : ℝ) ^ (-p) + Co * (n : ℝ) ^ (-p)
          = (Cf + Cin + Co) * (n : ℝ) ^ (-p) := by ring
        _ ≤ (Cf + Cin + Co + ((n₀ : ℝ) + 1) ^ p) * (n : ℝ) ^ (-p) :=
          mul_le_mul_of_nonneg_right (by linarith) hnp0
  · exact (prob_le_one).trans (one_le_ofReal_mul_rpow hp (by omega) (not_le.mp hnb)
      (by linarith))


/-! ## The displays on the literal seven-estimate event -/

/-- **The planar source displays at a path.** The planar envelope at every point, the local time at
every site, and `PlanarRealProfile`, with constants `Ce`, `Cs`, `Cr`. -/
def PlanarSourceDisplays (d : ℕ) (ε Ce Cs Cr : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  (∀ y : EuclideanSpace ℝ (Fin d), cellLocalTime Y n y ≤
      2 * d * ε * max (innerRadius Y n - ‖y‖) 0 +
        Ce * (sourceRadius d ε n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4))) ∧
  (∀ x : Site d, (localTime Y n x : ℝ) ≤
      2 * d * ε * max (innerRadius Y n - euclidNorm x) 0 +
        Cs * (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt d) +
        Cs * (Real.sqrt (sourceRadius d ε n) * Real.log n)) ∧
  PlanarRealProfile d ε Cr Y n

/-- **The planar source displays on the seven estimates of Section 5.1.** Let `0 < ε < 1/2` and
`p > 0`. There are constants `K` of the event `E7`, `Ce`, `Cs`, `Cr`, `Cp` and a threshold `n₀`,
chosen before the field `ξ`, the probability space, the walk, the time and the sample point, such
that for every field `ξ` of subgradients of the Euclidean norm with `ξ 0 = 0`, every walk `X` with
drift field `ξ` and every `n ≥ n₀`:

* the complement of `E7` has probability at most `Cp n^{-p}`, `E7` belongs to the `σ`-algebra
  generated by `X_0, …, X_n`, and the sample points at which the path is not a nearest-neighbour
  path from the origin have probability zero;
* at every legal sample point of `E7` the walk has `PlanarSourceDisplays`;
* the same holds at every sample point of the event `E7` of the legal carrier of `X`, a walk with
  the same drift field that coincides with `X` almost surely and is legal at every sample point,
  with the same bound on the complement.

The displays are consequences of the seven estimates; they are not extra clauses of the event, and
no legality is added to `E7`. -/
theorem planar_displays_on_E7 {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ)) {p : ℝ}
    (hp : 0 < p) :
    ∃ (K : EventConstants) (Ce Cs Cr Cp : ℝ) (n₀ : ℕ), 0 < Ce ∧ 0 < Cs ∧ 0 < Cr ∧ 0 < Cp ∧
      ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2) (hX : IsDriftCERW μ ε ξ X), ∀ n : ℕ, n₀ ≤ n →
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε ξ K X n)ᶜ ≤
            ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) ∧
          MeasurableSet[CERW.Support.Law.pathFiltration hX.measurable n]
            (E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε ξ K X n) ∧
          μ (legalSet X)ᶜ = 0 ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε ξ K X n, ω ∈ legalSet X →
            PlanarSourceDisplays 2 ε Ce Cs Cr (fun j => X j ω) n) ∧
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε ξ K
            (legalCarrier (by norm_num : 1 ≤ 2) X) n)ᶜ ≤ ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε ξ K
              (legalCarrier (by norm_num : 1 ≤ 2) X) n,
            PlanarSourceDisplays 2 ε Ce Cs Cr
              (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n) := by
  obtain ⟨K, Cc, Cin0, hCc, hCin0, n₀, hn₀, hmain⟩ :=
    section5_euclid_localization.{u} (d := 2) (by norm_num) hε hεd hp
  obtain ⟨C₀, C₁, hC₀, hC₁, hPF⟩ := pathFacts_of_estimates7 (d := 2) (by norm_num) hε K
  obtain ⟨Cin, hCin, nin, hIn⟩ := inner_of_estimates7 (d := 2) (by norm_num) hε K hCc
  obtain ⟨Ccr, hCcr, hCr⟩ := crossOK_of_estimates7 (d := 2) (by norm_num) hε hεd K
  obtain ⟨Co, hCo, no, hOut⟩ := outer_bound (d := 2) (by norm_num) hε hεd C₀ C₁ Cin Ccr hCin hCcr
  obtain ⟨Ce, hCe, ne, hdetE⟩ := planar_envelope_all_points (d := 2) rfl hε Cin
  obtain ⟨Cs, hCs, ns, hdetS⟩ := planar_localtime_all_sites (d := 2) rfl hε C₀ C₁
  obtain ⟨Cr, hCr0, nr, hcore⟩ :=
    planar_real_profile_core (d := 2) rfl hε hεd C₀ C₁ Cin Co hC₀ hC₁ hCin
  set N : ℕ := max (max (max nin no) (max ne ns)) (max nr 3) with hN
  have hdet : ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (P : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (Y : ℕ → Site 2) (n : ℕ),
        N ≤ n → PathTyping 2 Y →
        Estimates7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε ξ K P Y n →
        ContactBound 2 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε Cc Y n →
        PlanarSourceDisplays 2 ε Ce Cs Cr Y n := by
    intro ξ hξ hξ0 P Y n hn hty hE hct
    simp only [hN, max_le_iff] at hn
    obtain ⟨⟨⟨hnin, hno⟩, hne, hns⟩, hnr, hn3⟩ := hn
    have hP := hPF ξ hξ hξ0 P Y n (by omega) hty hE
    have hI := innerOK_of_innerConclusion (hIn ξ hξ hξ0 P Y n hnin hty hE hct)
    have hC' := hCr ξ hξ hξ0 P Y n (by omega) hty hE
    have hmax := hOut Y n hno hP hI hC'
    rw [if_pos rfl] at hmax
    have hP' := hP
    obtain ⟨hstart, hstep, hmaxloc, -, hglob, -, -⟩ := hP'
    have hYn := CERW.Support.Occupation.euclidNorm_le_of_steps Y hstart hstep
    refine ⟨hdetE Y n hne hI.1 hI.2.2, hdetS Y n hns hYn hmaxloc ?_,
      hcore Y n hnr hP hI hmax⟩
    intro y hy
    have := hglob y hy
    rw [if_pos rfl] at this
    exact this
  refine ⟨K, Ce, Cs, Cr, Cc, max n₀ N, hCe, hCs, hCr0, hCc, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hn₀n : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hNn : N ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨⟨hprob, hE⟩, hleg, -, -, htyp, hprobc, hEc⟩ := hmain ξ hξ hξ0 μ X hX n hn₀n
  refine ⟨⟨hprob, measurableSet_E7_filtration hX.measurable _ ε ξ K n, hleg,
    fun ω hω hL => ?_⟩, hprobc, fun ω hω => ?_⟩
  · exact hdet ξ hξ hξ0 (projectionAt (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε n)
      (fun j => X j ω) n hNn hL hω (hE ω hω hL).1
  · exact hdet ξ hξ hξ0 (projectionAt (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε n)
      (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n hNn (htyp ω) hω (hEc ω hω).1


/-- The bracket of the source is the bracket sum over the times `j < n`. -/
private lemma bracketSum_eq (Y : ℕ → Site d) (n : ℕ) (y : Site d) :
    bracketSum d Y n y = braSum Y n y := by
  rw [ev_braSum_eq Y n (Finset.Subset.refl _) y]
  rfl

/-- **The displays `eq:potential-convolution` and `eq:envelopehigh` on the seven estimates of
Section 5.1.** Let `d ≥ 3`, `0 < ε < 1/d` and `p > 0`. There are constants `K` of the event `E7`,
`Cpc`, `Ce`, `Cp` and a threshold `n₀`, chosen before the field `ξ`, the probability space, the
walk, the time and the sample point, such that for every field `ξ` of subgradients of the Euclidean
norm with `ξ 0 = 0`, every walk `X` with drift field `ξ` and every `n ≥ n₀`: the complement of `E7`
has probability at most `Cp n^{-p}`, `E7` belongs to the `σ`-algebra generated by `X_0, …, X_n`,
the illegal sample points have probability zero, and at every legal sample point of `E7`, and at
every sample point of the `E7` of the legal carrier, the displays hold at every point `y ∈ ℝ^d`
with `b = R_in(n)`. -/
theorem envelope_high_on_E7 (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) {p : ℝ}
    (hp : 0 < p) :
    ∃ (K : EventConstants) (Cpc Ce Cp : ℝ) (n₀ : ℕ), 0 < Cpc ∧ 0 < Ce ∧ 0 < Cp ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X), ∀ n : ℕ, n₀ ≤ n →
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n)ᶜ ≤
            ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) ∧
          MeasurableSet[CERW.Support.Law.pathFiltration hX.measurable n]
            (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n) ∧
          μ (legalSet X)ᶜ = 0 ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n, ω ∈ legalSet X →
            EnvelopeHighDisplays d ε Cpc Ce (fun j => X j ω) n) ∧
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K
            (legalCarrier (by omega : 1 ≤ d) X) n)ᶜ ≤ ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K
              (legalCarrier (by omega : 1 ≤ d) X) n,
            EnvelopeHighDisplays d ε Cpc Ce
              (fun j => legalCarrier (by omega : 1 ≤ d) X j ω) n) := by
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  obtain ⟨K, Cc, Cin0, hCc, hCin0, n₀, hn₀, hmain⟩ :=
    section5_euclid_localization.{u} hd2 hε hεd hp
  obtain ⟨C₀, C₁, hC₀, hC₁, hPF⟩ := pathFacts_of_estimates7 hd2 hε K
  obtain ⟨Ce, hCe, ne, henv⟩ := envelope_high_full hd hε C₁
  obtain ⟨Cpc, hCpc, npc, hpcs⟩ := potential_convolution_cellSet hd hε
  set N : ℕ := max (max ne npc) 2 with hN
  have hdet : ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Y : ℕ → Site d) (n : ℕ),
        N ≤ n → PathTyping d Y →
        Estimates7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K P Y n →
        EnvelopeHighDisplays d ε Cpc Ce Y n := by
    intro ξ hξ hξ0 P Y n hn hty hE
    simp only [hN, max_le_iff] at hn
    obtain ⟨⟨hne, hnpc⟩, hn2⟩ := hn
    have hP := hPF ξ hξ hξ0 P Y n hn2 hty hE
    obtain ⟨hstart, hstep, -, -, -, hpoint, -⟩ := hP
    have hYn := CERW.Support.Occupation.euclidNorm_le_of_steps Y hstart hstep
    have hfine : ∀ x : Site d, euclidNorm x ≤ 3 * n →
        |(localTime Y n x : ℝ) - potential d ε (cellSet Y n) (toSpace x)| ≤
          C₁ * (Real.sqrt (bracketSum d Y n x * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2)) := by
      intro x hx
      rw [bracketSum_eq]
      exact hpoint x hx
    intro y
    exact ⟨hpcs Y n hnpc hYn _ (innerRadius_nonneg Y n) (ball_innerRadius_subset hd1 Y n) y,
      henv Y n hne hYn hfine _ (innerRadius_nonneg Y n) (ball_innerRadius_subset hd1 Y n) y⟩
  refine ⟨K, Cpc, Ce, Cc, max n₀ N, hCpc, hCe, hCc, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hn₀n : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hNn : N ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨⟨hprob, hE⟩, hleg, -, -, htyp, hprobc, hEc⟩ := hmain ξ hξ hξ0 μ X hX n hn₀n
  refine ⟨⟨hprob, measurableSet_E7_filtration hX.measurable _ ε ξ K n, hleg,
    fun ω hω hL => ?_⟩, hprobc, fun ω hω => ?_⟩
  · exact hdet ξ hξ hξ0 (projectionAt (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n)
      (fun j => X j ω) n hNn hL hω
  · exact hdet ξ hξ hξ0 (projectionAt (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n)
      (fun j => legalCarrier (by omega : 1 ≤ d) X j ω) n hNn (htyp ω) hω

/-- **The displays of the full higher-dimensional envelope on the event, for the centrally excited
random walk.** The two parts of `envelope_high_on_E7` for a process `X` with `IsCERW μ ε X`, whose
drift field is `x ↦ u_x = x / |x|`: at the legal sample points of `E7` of `X`, and at every sample
point of the `E7` of the legal carrier of `X`. -/
theorem envelope_high_on_E7_of_isCERW (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ (K : EventConstants) (Cpc Ce Cp : ℝ) (n₀ : ℕ), 0 < Cpc ∧ 0 < Ce ∧ 0 < Cp ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n)ᶜ ≤
            ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) ∧
          μ (legalSet X)ᶜ = 0 ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n,
            ω ∈ legalSet X → EnvelopeHighDisplays d ε Cpc Ce (fun j => X j ω) n) ∧
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε (fun z => unitDir (toSpace z)) K
            (legalCarrier (by omega : 1 ≤ d) X) n)ᶜ ≤ ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε (fun z => unitDir (toSpace z)) K
              (legalCarrier (by omega : 1 ≤ d) X) n,
            EnvelopeHighDisplays d ε Cpc Ce
              (fun j => legalCarrier (by omega : 1 ≤ d) X j ω) n) := by
  obtain ⟨K, Cpc, Ce, Cp, n₀, hCpc, hCe, hCp, h⟩ := envelope_high_on_E7.{u} hd hε hεd hp
  obtain ⟨-, hsub, hξ0, -⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := d) hεd
  refine ⟨K, Cpc, Ce, Cp, n₀, hCpc, hCe, hCp, fun μ _ X hX n hn => ?_⟩
  obtain ⟨h1, h2⟩ := h _ hsub hξ0 μ X
    ((CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).1 hX) n hn
  exact ⟨⟨h1.1, h1.2.2.1, h1.2.2.2⟩, h2⟩

/-- **The planar source displays on the event, for the centrally excited random walk.** The two
parts of `planar_displays_on_E7` for a process `X` with `IsCERW μ ε X`: at the legal sample points
of `E7` of `X`, and at every sample point of the `E7` of the legal carrier of `X`. -/
theorem planar_displays_on_E7_of_isCERW {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ (K : EventConstants) (Ce Cs Cr Cp : ℝ) (n₀ : ℕ), 0 < Ce ∧ 0 < Cs ∧ 0 < Cr ∧ 0 < Cp ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n)ᶜ ≤
            ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) ∧
          μ (legalSet X)ᶜ = 0 ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n,
            ω ∈ legalSet X → PlanarSourceDisplays 2 ε Ce Cs Cr (fun j => X j ω) n) ∧
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K
            (legalCarrier (by norm_num : 1 ≤ 2) X) n)ᶜ ≤ ENNReal.ofReal (Cp * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K
              (legalCarrier (by norm_num : 1 ≤ 2) X) n,
            PlanarSourceDisplays 2 ε Ce Cs Cr
              (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n) := by
  obtain ⟨K, Ce, Cs, Cr, Cp, n₀, hCe, hCs, hCr, hCp, h⟩ :=
    planar_displays_on_E7.{u} hε hεd hp
  obtain ⟨-, hsub, hξ0, -⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := 2) hεd
  refine ⟨K, Ce, Cs, Cr, Cp, n₀, hCe, hCs, hCr, hCp, fun μ _ X hX n hn => ?_⟩
  obtain ⟨h1, h2⟩ := h _ hsub hξ0 μ X
    ((CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).1 hX) n hn
  exact ⟨⟨h1.1, h1.2.2.1, h1.2.2.2⟩, h2⟩


/-! ## The excess set has positive area -/

/-- Each coordinate function of Euclidean space is continuous. -/
private lemma continuous_coord (i : Fin d) :
    Continuous fun v : EuclideanSpace ℝ (Fin d) => v i :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous

/-- A point of the open box of a cell of `D_n` that lies outside the closed ball of radius `b`
gives positive area to `D_n ∖ B(0,b)`: the open box intersected with `{|v| > b}` is a nonempty
open subset of the excess set. -/
private lemma volume_pos_of_box_point {Y : ℕ → Site d} {n : ℕ} {x : Site d}
    (hx : x ∈ departureRange Y n) {b : ℝ} {q : EuclideanSpace ℝ (Fin d)}
    (hq : ∀ i, ((x i : ℤ) : ℝ) - 1 / 2 < q i ∧ q i < ((x i : ℤ) : ℝ) + 1 / 2)
    (hqb : b < ‖q‖) :
    0 < volume (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) := by
  have hopen : IsOpen {v : EuclideanSpace ℝ (Fin d) |
      (∀ i, ((x i : ℤ) : ℝ) - 1 / 2 < v i ∧ v i < ((x i : ℤ) : ℝ) + 1 / 2) ∧ b < ‖v‖} := by
    rw [Set.setOf_and, Set.setOf_forall]
    refine (isOpen_iInter_of_finite fun i => ?_).inter (isOpen_lt continuous_const continuous_norm)
    rw [Set.setOf_and]
    exact (isOpen_lt continuous_const (continuous_coord i)).inter
      (isOpen_lt (continuous_coord i) continuous_const)
  have hsub : {v : EuclideanSpace ℝ (Fin d) |
      (∀ i, ((x i : ℤ) : ℝ) - 1 / 2 < v i ∧ v i < ((x i : ℤ) : ℝ) + 1 / 2) ∧ b < ‖v‖} ⊆
      cellSet Y n \ Metric.ball 0 b := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨Set.mem_iUnion₂.mpr ⟨x, hx, fun i => ⟨(hv1 i).1.le, (hv1 i).2⟩⟩, ?_⟩
    rw [mem_ball_zero_iff, not_lt]
    exact hv2.le
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨q, hq, hqb⟩) (measure_mono hsub)

/-- **The excess set `D_n ∖ B(0, R_in(n))` has positive area** (`d ≥ 2`, a path from the origin,
`n ≥ 1`). The ball `B(0, b)` lies in `D_n`; the point `b e₀` of its boundary lies in the closure of
one cell, with every other coordinate in the interior of the side of that cell; moving it inside
the open box of the cell in a direction that increases the norm (along `e₀`, or, if `b e₀` is on the
outer face, slightly inward and along `e₁`) produces a point of the open box of the cell outside
`B(0,b)`, and that point has a neighbourhood in the excess set. -/
theorem volume_cellSet_diff_ball_innerRadius_pos (hd : 2 ≤ d) (Y : ℕ → Site d) (n : ℕ)
    (hn : 1 ≤ n) (h0 : Y 0 = 0) :
    0 < volume (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius Y n)) := by
  set b := innerRadius Y n with hb
  have hb2 : 1 / 2 ≤ b := half_le_innerRadius (by omega) Y n hn h0
  have hbpos : 0 < b := by linarith
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ⊆ cellSet Y n :=
    ball_innerRadius_subset (by omega : 1 ≤ d) Y n
  obtain ⟨i0, i1, h01⟩ : ∃ i0 i1 : Fin d, i1 ≠ i0 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  set p : EuclideanSpace ℝ (Fin d) := b • EuclideanSpace.single i0 (1 : ℝ) with hp
  have hpi : ∀ i, p i = if i = i0 then b else 0 := by
    intro i
    simp [hp, PiLp.single_apply]
  have hpn : ‖p‖ = b := by
    simp [hp, norm_smul, abs_of_pos hbpos]
  have hpcl : p ∈ closure (cellSet Y n) := by
    have h1 : p ∈ closure (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b) := by
      rw [closure_ball _ hbpos.ne']
      exact mem_closedBall_zero_iff.mpr hpn.le
    exact closure_mono hball h1
  have hpcl' : p ∈ closure (⋃ x ∈ departureRange Y n, cell x) := hpcl
  rw [Finset.closure_biUnion] at hpcl'
  obtain ⟨x, hx, hpx⟩ := Set.mem_iUnion₂.mp hpcl'
  have hbox : ∀ i, ((x i : ℤ) : ℝ) - 1 / 2 ≤ p i ∧ p i ≤ ((x i : ℤ) : ℝ) + 1 / 2 := by
    have hclosed : IsClosed {v : EuclideanSpace ℝ (Fin d) |
        ∀ i, ((x i : ℤ) : ℝ) - 1 / 2 ≤ v i ∧ v i ≤ ((x i : ℤ) : ℝ) + 1 / 2} := by
      rw [Set.setOf_forall]
      refine isClosed_iInter fun i => ?_
      rw [Set.setOf_and]
      exact (isClosed_le continuous_const (continuous_coord i)).inter
        (isClosed_le (continuous_coord i) continuous_const)
    exact closure_minimal (fun v hv i => ⟨(hv i).1, (hv i).2.le⟩) hclosed hpx
  have hx0 : ∀ i, i ≠ i0 → x i = 0 := by
    intro i hi
    have h := hbox i
    rw [hpi i, if_neg hi] at h
    have h1 : ((x i : ℤ) : ℝ) < 1 := by linarith [h.1]
    have h2 : (-1 : ℝ) < ((x i : ℤ) : ℝ) := by linarith [h.2]
    have h1' : x i < 1 := by exact_mod_cast h1
    have h2' : -1 < x i := by exact_mod_cast h2
    omega
  have key : ∃ a t : ℝ, ((x i0 : ℤ) : ℝ) - 1 / 2 < a ∧ a < ((x i0 : ℤ) : ℝ) + 1 / 2 ∧
      |t| < 1 / 2 ∧ b ^ 2 < a ^ 2 + t ^ 2 := by
    have h := hbox i0
    rw [hpi i0, if_pos rfl] at h
    by_cases hlt : b < ((x i0 : ℤ) : ℝ) + 1 / 2
    · set δ : ℝ := (((x i0 : ℤ) : ℝ) + 1 / 2 - b) / 2 with hδ
      have hδ0 : 0 < δ := by rw [hδ]; linarith
      refine ⟨b + δ, 0, by linarith [h.1], by rw [hδ]; linarith, by simp, ?_⟩
      nlinarith [mul_pos hbpos hδ0, sq_nonneg δ]
    · have heq : b = ((x i0 : ℤ) : ℝ) + 1 / 2 := le_antisymm h.2 (not_lt.mp hlt)
      set s : ℝ := 1 / (64 * b) with hs
      have hs0 : 0 < s := by rw [hs]; positivity
      have hs1 : s ≤ 1 / 32 := by
        rw [hs, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have hbs : b * s = 1 / 64 := by rw [hs]; field_simp
      refine ⟨b - s, 1 / 4, by linarith, by linarith, by rw [abs_of_pos (by norm_num)]; norm_num,
        ?_⟩
      nlinarith [sq_nonneg s]
  obtain ⟨a, t, ha1, ha2, ht, habt⟩ := key
  set q : EuclideanSpace ℝ (Fin d) :=
    a • EuclideanSpace.single i0 (1 : ℝ) + t • EuclideanSpace.single i1 (1 : ℝ) with hq
  have hqi : ∀ i, q i = (if i = i0 then a else 0) + (if i = i1 then t else 0) := by
    intro i
    simp [hq, PiLp.single_apply]
  have hq0 : q i0 = a := by rw [hqi, if_pos rfl, if_neg h01.symm, add_zero]
  have hq1 : q i1 = t := by rw [hqi, if_neg h01, if_pos rfl, zero_add]
  have hqbox : ∀ i, ((x i : ℤ) : ℝ) - 1 / 2 < q i ∧ q i < ((x i : ℤ) : ℝ) + 1 / 2 := by
    intro i
    by_cases hi : i = i0
    · rw [hi, hq0]
      exact ⟨ha1, ha2⟩
    · rw [hx0 i hi, Int.cast_zero]
      by_cases hi1 : i = i1
      · rw [hi1, hq1]
        constructor <;> linarith [abs_lt.mp ht]
      · rw [hqi i, if_neg hi, if_neg hi1]
        constructor <;> norm_num
  have hsq : a ^ 2 + t ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => q i ^ 2)
      (Finset.subset_univ ({i0, i1} : Finset (Fin d))) (fun i _ _ => sq_nonneg _)
    simpa only [Finset.sum_pair h01.symm, hq0, hq1] using this
  have hqn : b < ‖q‖ := by
    by_contra hcon
    push Not at hcon
    have := pow_le_pow_left₀ (norm_nonneg q) hcon 2
    linarith
  exact volume_pos_of_box_point hx hqbox hqn

/-! ## Consumers at an actual walk and at real points -/

/-- **The Newton field at a real, nonsingular point.** In the plane, `v = e₁` and the real point
`y = e₁/4`, which is not a lattice site, differ; `y' ↦ log |e₁ - y'|` has the gradient
`-(e₁ - y)/|e₁ - y|²` at `y`, the identity `(v - y)|v - y|^{-2} = -∇_y log |v - y|` holds there,
and both coordinates of `-∇_{y'} log |e₁ - y'|` are harmonic at `y`. -/
theorem planar_newton_gradient_at_real_point :
    (1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ≠
        EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∧
      (∀ x : Site 2, toSpace x ≠ (1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) ∧
      HasGradientAt (fun y' : EuclideanSpace ℝ (Fin 2) =>
        Real.log ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ) - y'‖)
        (-((‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ) -
            (1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ^ 2)⁻¹ •
          (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) -
            (1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))
        ((1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) ∧
      (∀ i : Fin 2, InnerProductSpace.HarmonicAt
        (fun y' : EuclideanSpace ℝ (Fin 2) =>
          (-gradient (fun z : EuclideanSpace ℝ (Fin 2) =>
            Real.log ‖EuclideanSpace.single (0 : Fin 2) (1 : ℝ) - z‖) y') i)
        ((1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) := by
  have hne : (1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ≠
      EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
    intro h
    have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
    simp at this
  refine ⟨hne, fun x h => ?_, hasGradientAt_log_norm_sub _ _ hne, fun i =>
    harmonicAt_neg_gradient_log_coordinate _ _ hne i⟩
  have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
  simp only [CERW.toSpace, PiLp.smul_apply, PiLp.single_apply, if_true,
    smul_eq_mul, mul_one] at this
  have h4 : ((4 * x 0 : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h5 : 4 * x 0 = 1 := by exact_mod_cast h4
  omega


/-- The norm of a multiple of a coordinate vector is the absolute value of the multiple. -/
private lemma norm_smul_single (c : ℝ) (i : Fin d) :
    ‖c • EuclideanSpace.single i (1 : ℝ)‖ = |c| := by
  simp [norm_smul]

/-- **The maximum principle for the planar potential** (Section 7, last subsection): for a bounded
measurable set `E` outside the disc `B(0,b)`, a bound `M` of `U_E` on the circle `|y| = b` bounds
`U_E` on the closed disc. -/
theorem planar_potential_le_of_circle {ε : ℝ} (hε : 0 < ε)
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    {b M : ℝ} (hb : 0 < b) (hsub : E ⊆ {v | b ≤ ‖v‖})
    (hcircle : ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ = b → potential 2 ε E y ≤ M) :
    ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ ≤ b → potential 2 ε E y ≤ M :=
  planar_max_principle rfl hε hE hEb hb hsub hcircle

/-- **The potential of a set outside a disc is nonnegative inside the disc**: `u_v·(v - y) ≥ 0`
when `|v| ≥ b ≥ |y|`. -/
theorem planar_potential_nonneg_inside {ε : ℝ} (hε : 0 ≤ ε)
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E) {b : ℝ}
    (hsub : E ⊆ {v | b ≤ ‖v‖}) {y : EuclideanSpace ℝ (Fin 2)} (hy : ‖y‖ ≤ b) :
    0 ≤ potential 2 ε E y :=
  co_potential_nonneg_inside (by norm_num) hε hE hsub hy

/-- **Consumer of the maximum principle with an excess set of positive area.** The annulus
`{1 ≤ |v| ≤ 2}` has positive area, its potential is nonnegative on the closed unit disc, and at
every point of the disc it is at most its supremum over the unit circle. -/
theorem planar_potential_annulus_maximum_principle (ε : ℝ) (hε : 0 < ε) :
    0 < volume {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} ∧
      ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ ≤ 1 →
        0 ≤ potential 2 ε {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} y ∧
          potential 2 ε {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} y ≤
            ⨆ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
              potential 2 ε {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} z := by
  set A : Set (EuclideanSpace ℝ (Fin 2)) := {v | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} with hA
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hAb : Bornology.IsBounded A := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := 2)).subset ?_
    intro v hv
    exact mem_closedBall_zero_iff.mpr hv.2
  have hsub : A ⊆ {v | (1 : ℝ) ≤ ‖v‖} := fun v hv => hv.1
  have hvol : 0 < volume A := by
    have hopen : IsOpen {v : EuclideanSpace ℝ (Fin 2) | 1 < ‖v‖ ∧ ‖v‖ < 2} := by
      rw [Set.setOf_and]
      exact (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hne : ({v : EuclideanSpace ℝ (Fin 2) | 1 < ‖v‖ ∧ ‖v‖ < 2} : Set _).Nonempty := by
      refine ⟨(3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_⟩
      rw [Set.mem_setOf_eq, norm_smul_single, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      constructor <;> norm_num
    exact lt_of_lt_of_le (hopen.measure_pos volume hne)
      (measure_mono fun v hv => ⟨hv.1.le, hv.2.le⟩)
  refine ⟨hvol, fun y hy => ⟨?_, ?_⟩⟩
  · exact planar_potential_nonneg_inside hε.le hAm hsub hy
  · have hbdd : BddAbove (Set.range fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 =>
        potential 2 ε A z) := by
      refine ⟨supAbsPotential 2 ε A, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact (le_abs_self _).trans (abs_potential_le_supAbs (by norm_num) hε.le hAm hAb z)
    exact planar_potential_le_of_circle hε hAm hAb one_pos hsub
      (fun z hz => le_ciSup hbdd ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩) y hy

/-- A vector with a non-integral coordinate is not an embedded lattice site. -/
private lemma toSpace_ne_of_not_int {x : Site d} {y : EuclideanSpace ℝ (Fin d)} (i : Fin d)
    (hy : ∀ m : ℤ, y i ≠ (m : ℝ)) : toSpace x ≠ y := fun h =>
  hy (x i) (by rw [← h]; rfl)

/-- `1/4` is not an integer. -/
private lemma quarter_ne_int (m : ℤ) : (1 / 4 : ℝ) ≠ (m : ℝ) := by
  intro h
  have h4 : ((4 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h5 : 4 * m = 1 := by exact_mod_cast h4
  omega

/-- For a bound `Cp n^{-1}` that tends to zero, a time at least `n₀` and at least `2` at which the
bound is below one. -/
private lemma exists_nat_rate_lt_one (Cp : ℝ) (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ 2 ≤ n ∧ Cp * (n : ℝ) ^ (-(1 : ℝ)) < 1 := by
  have hn2 : 2 ≤ max n₀ (⌈Cp⌉₊ + 2) := le_trans (by omega) (le_max_right _ _)
  refine ⟨max n₀ (⌈Cp⌉₊ + 2), le_max_left _ _, hn2, ?_⟩
  have hnpos : (0 : ℝ) < (max n₀ (⌈Cp⌉₊ + 2) : ℕ) := by exact_mod_cast (by omega : 0 < _)
  rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_lt_one hnpos]
  have h1 := Nat.le_ceil Cp
  have h2 : ((⌈Cp⌉₊ + 2 : ℕ) : ℝ) ≤ (max n₀ (⌈Cp⌉₊ + 2) : ℕ) := by
    exact_mod_cast le_max_right _ _
  have h3 : ((⌈Cp⌉₊ + 2 : ℕ) : ℝ) = (⌈Cp⌉₊ : ℝ) + 2 := by push_cast; ring
  linarith

/-- A set whose complement has probability at most `c < 1` meets every set whose complement is
null. -/
private lemma exists_mem_inter_of_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A B : Set Ω} {c : ℝ} (hA : μ Aᶜ ≤ ENNReal.ofReal c) (hc : c < 1)
    (hB : μ Bᶜ = 0) : ∃ ω, ω ∈ A ∧ ω ∈ B := by
  by_contra hno
  push Not at hno
  have hsub : (Set.univ : Set Ω) ⊆ Aᶜ ∪ Bᶜ := by
    intro ω _
    by_cases hω : ω ∈ A
    · exact Or.inr (hno ω hω)
    · exact Or.inl hω
  have h1 := (measure_mono (μ := μ) hsub).trans (measure_union_le _ _)
  rw [measure_univ, hB, add_zero] at h1
  exact absurd (h1.trans_lt (hA.trans_lt (by rw [ENNReal.ofReal_lt_one]; exact hc)))
    (lt_irrefl _)

/-- **The coefficient of the cone in the plane**: `2 d ε = 4 ε` for `d = 2`. -/
theorem planar_cone_coefficient (ε : ℝ) : 2 * ((2 : ℕ) : ℝ) * ε = 4 * ε := by
  norm_num

/-- **Consumer of the displays on the seven estimates at an actual planar walk.** There are a
probability space carrying centrally excited random walk with `ε = 1/4`, constants, a time `n` and
a sample point `ω` that is legal and belongs to the literal event `E7`, at which the planar source
displays hold; the walk has inner radius at least `1/2`, the excess set `D_n ∖ B(0, R_in(n))` has
positive area, and the real excess potential has a bounded range on the closed disc with the
supremum at most `C Z`. The real point `y₁ = e₁/4`, which is not a lattice site, lies in
`B(0,b)` and satisfies the inner estimate; the real point `y₂ = (b + w + 1/3) e₁ + e₂/4`, which is
not a lattice site, lies beyond the support, where the local time vanishes and the profile is
bounded by `C Z`. -/
theorem exists_realization_planar_on_E7 :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), IsCERW μ (1 / 4 : ℝ) X ∧
      ∃ (K : EventConstants) (Ce Cs Cr : ℝ), 0 < Ce ∧ 0 < Cs ∧ 0 < Cr ∧
        ∃ (n : ℕ) (ω : Ω), 2 ≤ n ∧
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (1 / 4 : ℝ)
            (fun z => unitDir (toSpace z)) K X n ∧ ω ∈ legalSet X ∧ X 0 ω = 0 ∧
          PlanarSourceDisplays 2 (1 / 4 : ℝ) Ce Cs Cr (fun j => X j ω) n ∧
          1 / 2 ≤ innerRadius (fun j => X j ω) n ∧
          0 < volume (cellSet (fun j => X j ω) n \
            Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius (fun j => X j ω) n)) ∧
          BddAbove (Set.range fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2))
              (innerRadius (fun j => X j ω) n + (maxRadius (fun j => X j ω) n -
                innerRadius (fun j => X j ω) n + 2 * Real.sqrt (2 : ℕ))) =>
            potential 2 (1 / 4 : ℝ) (cellSet (fun j => X j ω) n \
              Metric.ball 0 (innerRadius (fun j => X j ω) n)) y) ∧
          (⨆ y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2))
              (innerRadius (fun j => X j ω) n + (maxRadius (fun j => X j ω) n -
                innerRadius (fun j => X j ω) n + 2 * Real.sqrt (2 : ℕ))),
            potential 2 (1 / 4 : ℝ) (cellSet (fun j => X j ω) n \
              Metric.ball 0 (innerRadius (fun j => X j ω) n)) y) ≤
            Cr * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2)) ∧
          (∃ y₁ : EuclideanSpace ℝ (Fin 2), ‖y₁‖ < innerRadius (fun j => X j ω) n ∧
            (∀ x : Site 2, toSpace x ≠ y₁) ∧
            |cellLocalTime (fun j => X j ω) n y₁ -
                2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₁‖) 0| ≤
              Cr * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2) +
                |innerRadius (fun j => X j ω) n - sourceRadius 2 (1 / 4 : ℝ) n|)) ∧
          (∃ y₂ : EuclideanSpace ℝ (Fin 2),
            innerRadius (fun j => X j ω) n + (maxRadius (fun j => X j ω) n -
              innerRadius (fun j => X j ω) n + 2 * Real.sqrt (2 : ℕ)) < ‖y₂‖ ∧
            (∀ x : Site 2, toSpace x ≠ y₂) ∧
            cellLocalTime (fun j => X j ω) n y₂ = 0 ∧
            |cellLocalTime (fun j => X j ω) n y₂ -
                2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₂‖) 0| ≤
              Cr * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2))) ∧
          ∃ ω' : Ω, ω' ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (1 / 4 : ℝ)
              (fun z => unitDir (toSpace z)) K (legalCarrier (by norm_num : 1 ≤ 2) X) n ∧
            PlanarSourceDisplays 2 (1 / 4 : ℝ) Ce Cs Cr
              (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω') n := by
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hεd : (1 / 4 : ℝ) < 1 / ((2 : ℕ) : ℝ) := by norm_num
  obtain ⟨Ω, hΩ, μ, hμ, X, hX⟩ := CERW.Support.Law.exists_isCERW (d := 2) (by omega) hε.le hεd
  obtain ⟨K, Ce, Cs, Cr, Cp, n₀, hCe, hCs, hCr, hCp, h⟩ :=
    planar_displays_on_E7_of_isCERW.{0} hε hεd (p := 1) one_pos
  refine ⟨Ω, hΩ, μ, hμ, X, hX, K, Ce, Cs, Cr, hCe, hCs, hCr, ?_⟩
  obtain ⟨n, hn0, hn2, hCn⟩ := exists_nat_rate_lt_one Cp n₀
  obtain ⟨⟨hE, hleg, himp⟩, hEc, himpc⟩ := h μ X hX n hn0
  obtain ⟨ω, hωE, hωL⟩ := exists_mem_inter_of_prob μ hE hCn hleg
  have hD := himp ω hωE hωL
  have h0 : X 0 ω = 0 := hωL.1
  have hb := half_le_innerRadius (by omega : 1 ≤ 2) (fun j => X j ω) n (by omega) h0
  obtain ⟨hsup1, hsup2⟩ := planar_real_profile_sup hD.2.2
  have hvol := volume_cellSet_diff_ball_innerRadius_pos (d := 2) le_rfl (fun j => X j ω) n
    (by omega) h0
  refine ⟨n, ω, hn2, hωE, hωL, h0, hD, hb, hvol, hsup1, hsup2, ?_, ?_, ?_⟩
  · refine ⟨(1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_, ?_, ?_⟩
    · rw [norm_smul_single, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith
    · intro x
      refine toSpace_ne_of_not_int (0 : Fin 2) fun m => ?_
      have h10 : ((1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 = 1 / 4 := by
        simp
      rw [h10]
      exact quarter_ne_int m
    · refine hD.2.2.2.1 _ ?_
      rw [norm_smul_single, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith
  · obtain ⟨y₂, hy20, hy21⟩ : ∃ y : EuclideanSpace ℝ (Fin 2),
        y 0 = max (innerRadius (fun j => X j ω) n) (innerRadius (fun j => X j ω) n +
          (maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n +
            2 * Real.sqrt (2 : ℕ))) + 1 / 3 ∧ y 1 = 1 / 4 :=
      ⟨(max (innerRadius (fun j => X j ω) n) (innerRadius (fun j => X j ω) n +
          (maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n +
            2 * Real.sqrt (2 : ℕ))) + 1 / 3) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (1 / 4 : ℝ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ), by simp, by simp⟩
    have hy2 : y₂ 0 ≤ ‖y₂‖ := (Real.le_norm_self (y₂ 0)).trans (PiLp.norm_apply_le y₂ 0)
    rw [hy20] at hy2
    have hfar : innerRadius (fun j => X j ω) n + (maxRadius (fun j => X j ω) n -
        innerRadius (fun j => X j ω) n + 2 * Real.sqrt (2 : ℕ)) < ‖y₂‖ :=
      lt_of_le_of_lt (le_max_right _ _)
        (lt_of_lt_of_le (lt_add_of_pos_right _ (by norm_num)) hy2)
    have hbn : innerRadius (fun j => X j ω) n ≤ ‖y₂‖ :=
      le_trans (le_max_left _ _) (le_trans (le_add_of_nonneg_right (by norm_num)) hy2)
    refine ⟨y₂, hfar, fun x => toSpace_ne_of_not_int (1 : Fin 2) fun m => ?_,
      (hD.2.2.2.2.1 y₂ hbn).2.2.2 hfar, hD.2.2.2.2.2 y₂⟩
    rw [hy21]
    exact quarter_ne_int m
  · obtain ⟨ω', hω', -⟩ := exists_mem_inter_of_prob μ hEc hCn (B := Set.univ) (by simp)
    exact ⟨ω', hω', himpc ω' hω'⟩

/-- **Consumer of the displays of the full higher-dimensional envelope on the seven estimates.**
For `d ≥ 3` and `0 < ε < 1/d` there are a probability space carrying centrally excited random walk,
constants, a time `n ≥ 2` and a sample point `ω` that is legal and belongs to the literal event
`E7`, at which the displays hold at every real point, the inner radius is at least `1/2`, and the
excess set `D_n ∖ B(0, R_in(n))` has positive volume. -/
theorem exists_realization_envelope_high_on_E7 (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site d), IsCERW μ ε X ∧
      ∃ (K : EventConstants) (Cpc Ce : ℝ), 0 < Cpc ∧ 0 < Ce ∧
        ∃ (n : ℕ) (ω : Ω), 2 ≤ n ∧
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n ∧
          ω ∈ legalSet X ∧ X 0 ω = 0 ∧
          EnvelopeHighDisplays d ε Cpc Ce (fun j => X j ω) n ∧
          1 / 2 ≤ innerRadius (fun j => X j ω) n ∧
          0 < volume (cellSet (fun j => X j ω) n \
            Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (innerRadius (fun j => X j ω) n)) := by
  obtain ⟨Ω, hΩ, μ, hμ, X, hX⟩ := CERW.Support.Law.exists_isCERW (by omega : 1 ≤ d) hε.le hεd
  obtain ⟨K, Cpc, Ce, Cp, n₀, hCpc, hCe, hCp, h⟩ :=
    envelope_high_on_E7_of_isCERW.{0} hd hε hεd (p := 1) one_pos
  refine ⟨Ω, hΩ, μ, hμ, X, hX, K, Cpc, Ce, hCpc, hCe, ?_⟩
  obtain ⟨n, hn0, hn2, hCn⟩ := exists_nat_rate_lt_one Cp n₀
  obtain ⟨⟨hE, hleg, himp⟩, -⟩ := h μ X hX n hn0
  obtain ⟨ω, hωE, hωL⟩ := exists_mem_inter_of_prob μ hE hCn hleg
  have h0 : X 0 ω = 0 := hωL.1
  exact ⟨n, ω, hn2, hωE, hωL, h0, himp ω hωE hωL,
    half_le_innerRadius (by omega : 1 ≤ d) (fun j => X j ω) n (by omega) h0,
    volume_cellSet_diff_ball_innerRadius_pos (by omega : 2 ≤ d) (fun j => X j ω) n (by omega) h0⟩

end CERW.Support.Outer.PlanarReal
