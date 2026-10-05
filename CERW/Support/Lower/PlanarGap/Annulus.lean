import CERW.Generic.Newton.Polar
import CERW.Support.Occupation.CellDirection
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The direction-free planar annulus bound

Let `A ⊂ ℤ²` be a finite set that contains the lattice disk `{|x| < ρ}` and lies in `{|x| ≤ R}`.
Then, in every direction at once,
`|∑_{x ∈ A} u_x| ≤ R² - ρ² + C (R + 1)`, with an absolute constant `C` and leading coefficient
exactly one. (A coordinatewise bound has the same leading coefficient only for one coordinate;
the norm of a vector in a coordinate frame costs a factor `√2`.)

The proof has three parts, all deterministic.

* The inner disk cancels: the lattice disk `{|x| < ρ}` is invariant under `x ↦ -x`, which negates
  `u_x`. Pairing the sum with a unit vector `e` in the direction of the sum leaves a sum of
  `⟪e, u_x⟫` over the sites with `ρ ≤ |x| ≤ R`, which is at most the sum of the positive parts.
* The angular constant. In polar coordinates `∫ h(|v|) (⟪e, v⟫/|v|)₊ dv` factors as
  `(∫_{S¹} (⟪e, θ⟫)₊ dσ) · ∫_0^∞ r h(r) dr`, and the angular factor is exactly `2` for every unit
  vector `e`: a reflection carries `e` to the first coordinate vector, and
  `∫_{B(0,1)} (v₀)₊ dv = 2/3`.
* The cell comparison. On the unit cell of a site `x ≠ 0` the profile `(⟪e, u_v⟫)₊` moves by at
  most `2/|x|`, so the lattice sum is at most the integral over the annulus
  `{ρ - 1 < |v| ≤ R + 1}` plus `4σ(R+1)` where `σ` is the total mass of the sphere measure, because
  `1/|x| ≤ 2/|v|` on the cell.

No shape, local-time or provider hypothesis enters: the statements concern an arbitrary finite
set of lattice sites.
-/

namespace CERW.Support.Lower.PlanarGap

open MeasureTheory CERW LatticeProb CERW.Support.Occupation

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ### The angular profile -/

/-- The angular profile `v ↦ (⟪e, v⟫/|v|)₊` is unchanged by a positive scaling of `v`. -/
private lemma angular_smul (e v : E2) {r : ℝ} (hr : 0 < r) :
    max (inner ℝ e (r • v) / ‖r • v‖) 0 = max (inner ℝ e v / ‖v‖) 0 := by
  rw [real_inner_smul_right, norm_smul, Real.norm_of_nonneg hr.le, mul_div_mul_left _ _ hr.ne']

/-- The angular profile is nonnegative. -/
private lemma angular_nonneg (e v : E2) : 0 ≤ max (inner ℝ e v / ‖v‖) 0 := le_max_right _ _

/-- The angular profile of a vector of norm at most one is at most one. -/
private lemma angular_le_one {e : E2} (he : ‖e‖ ≤ 1) (v : E2) :
    max (inner ℝ e v / ‖v‖) 0 ≤ 1 := by
  refine max_le ?_ zero_le_one
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [div_le_one (norm_pos_iff.mpr hv)]
    calc inner ℝ e v ≤ ‖e‖ * ‖v‖ := real_inner_le_norm e v
      _ ≤ 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := one_mul _

/-- The angular profile is measurable. -/
private lemma measurable_angular (e : E2) :
    Measurable (fun v : E2 => max (inner ℝ e v / ‖v‖) 0) :=
  ((measurable_const.inner measurable_id).div measurable_norm).max measurable_const

/-- The angular profile at a vector, through the direction map `u_v = v/|v|`. -/
private lemma angular_eq_unitDir (e v : E2) :
    max (inner ℝ e v / ‖v‖) 0 = max (inner ℝ e (unitDir v)) 0 := by
  simp [unitDir, real_inner_smul_right, div_eq_inv_mul]

/-- The angular profile is integrable over every set of finite volume. -/
private lemma integrableOn_angular {e : E2} (he : ‖e‖ = 1) {S : Set E2} (hS : volume S ≠ ⊤) :
    IntegrableOn (fun v : E2 => max (inner ℝ e v / ‖v‖) 0) S := by
  refine Measure.integrableOn_of_bounded (M := 1) hS (measurable_angular e).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun v => by
    rw [Real.norm_of_nonneg (angular_nonneg e v)]
    exact angular_le_one he.le v

/-! ### Polar coordinates with a separated integrand -/

/-- Polar coordinates for an integrand `h(|v|) ψ(v)` with `ψ` homogeneous of degree zero and `h`
bounded with bounded support: the integral is the product of the sphere integral of `ψ` and the
radial integral `∫_0^∞ r h(r) dr`. -/
private lemma integral_polar_sep (ψ : E2 → ℝ) (hψm : Measurable ψ) (hψb : ∀ v, |ψ v| ≤ 1)
    (hψh : ∀ r : ℝ, 0 < r → ∀ v : E2, ψ (r • v) = ψ v) (h : ℝ → ℝ) (hm : Measurable h)
    {M T : ℝ} (hb : ∀ r, |h r| ≤ M) (hs : ∀ r, T < r → h r = 0) :
    ∫ v : E2, h ‖v‖ * ψ v =
      (∫ θ : Metric.sphere (0 : E2) 1, ψ (θ : E2) ∂(volume : Measure E2).toSphere) *
        ∫ r in Set.Ioi (0 : ℝ), r * h r := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  have hint : Integrable (fun v : E2 => h ‖v‖ * ψ v) := by
    have hbd : ∀ v : E2, ‖h ‖v‖ * ψ v‖ ≤
        (Metric.closedBall (0 : E2) T).indicator (fun _ => M) v := by
      intro v
      by_cases hv : ‖v‖ ≤ T
      · rw [Set.indicator_of_mem (by simpa using hv)]
        calc ‖h ‖v‖ * ψ v‖ = |h ‖v‖| * |ψ v| := by rw [Real.norm_eq_abs, abs_mul]
          _ ≤ M * 1 := mul_le_mul (hb _) (hψb v) (abs_nonneg _) hM
          _ = M := mul_one M
      · rw [not_le] at hv
        rw [hs _ hv, zero_mul, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => hM) v
    refine Integrable.mono' ?_ ((hm.comp measurable_norm).mul hψm).aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    exact integrableOn_const (measure_closedBall_lt_top).ne
  rw [CERW.Generic.Newton.integral_eq_integral_Ioi_sphere (d := 2) (by norm_num) hint,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  have hinner : ∀ θ : Metric.sphere (0 : E2) 1,
      h ‖r • (θ : E2)‖ * ψ (r • (θ : E2)) = h r * ψ (θ : E2) := by
    intro θ
    have hθ : ‖(θ : E2)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
    rw [norm_smul, Real.norm_of_nonneg hr'.le, hθ, mul_one, hψh r hr']
  simp only [hinner]
  rw [integral_const_mul]
  simp only [Nat.reduceSub, pow_one]
  ring

/-! ### The angular constant -/

/-- An elementary integral: `∫_0^1 2x√(1-x²) dx = 2/3`. -/
private lemma integral_x_sqrt : ∫ x in (0 : ℝ)..1, 2 * x * Real.sqrt (1 - x ^ 2) = 2 / 3 := by
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => -(2 / 3) * ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2)))
        (2 * x * Real.sqrt (1 - x ^ 2)) x := by
    intro x hx
    have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr hx2
    have hss : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hx2.le
    have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub 1
    have h2 : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
        (-(2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x := h1.sqrt hx2.ne'
    have h3 := (h1.mul h2).const_mul (-(2 / 3) : ℝ)
    have hs2 : 1 - x ^ 2 = Real.sqrt (1 - x ^ 2) ^ 2 := hss.symm
    refine h3.congr_deriv ?_
    generalize Real.sqrt (1 - x ^ 2) = s at hs hs2 ⊢
    rw [hs2]
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => -(2 / 3) * ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2)))
      (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    fun_prop
  have hint : IntervalIntegrable (fun x : ℝ => 2 * x * Real.sqrt (1 - x ^ 2)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  norm_num

/-- A point of the plane lies in the open unit disk iff the sum of the squares of its coordinates
is below one. -/
private lemma norm_lt_one_iff (y : E2) : ‖y‖ < 1 ↔ y 0 ^ 2 + y 1 ^ 2 < 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs, Real.sqrt_lt' one_pos, one_pow]

/-- The integral of the positive part of the first coordinate over the unit disk, in
coordinates. -/
private lemma integral_ball_coord :
    ∫ y in Metric.ball (0 : E2) 1, max (y 0) 0 = 2 / 3 := by
  let φ : E2 ≃ᵐ ℝ × ℝ := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
    MeasurableEquiv.finTwoArrow
  have hφ : MeasurePreserving φ volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  set G : ℝ × ℝ → ℝ := fun p => if p.1 ^ 2 + p.2 ^ 2 < 1 then max p.1 0 else 0 with hG
  have h1 : ∫ y in Metric.ball (0 : E2) 1, max (y 0) 0 = ∫ y : E2, G (φ y) := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hφy : φ y = (y 0, y 1) := rfl
    simp [Set.indicator, hG, hφy, norm_lt_one_iff]
  have hGm : Measurable G := by
    refine Measurable.ite ?_ (measurable_fst.max measurable_const) measurable_const
    exact measurableSet_lt (by fun_prop) measurable_const
  have hGint : Integrable G (volume : Measure (ℝ × ℝ)) := by
    have hbd : ∀ p : ℝ × ℝ,
        ‖G p‖ ≤ (Metric.closedBall (0 : ℝ × ℝ) 1).indicator (fun _ => (1 : ℝ)) p := by
      intro p
      by_cases hp : p.1 ^ 2 + p.2 ^ 2 < 1
      · have h1' : |p.1| ≤ 1 := by
          rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg p.2]
        have h2' : |p.2| ≤ 1 := by
          rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg p.1]
        have hmem : p ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
          rw [mem_closedBall_zero_iff, Prod.norm_def]
          exact max_le (by simpa using h1') (by simpa using h2')
        rw [Set.indicator_of_mem hmem]
        simp only [hG, hp, if_true]
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (abs_le.mp h1').2 zero_le_one
      · simp only [hG, hp, if_false, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) p
    refine Integrable.mono' ?_ hGm.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    exact integrableOn_const (measure_closedBall_lt_top).ne
  rw [h1, hφ.integral_comp φ.measurableEmbedding G]
  have hGint' : Integrable G ((volume : Measure ℝ).prod (volume : Measure ℝ)) := hGint
  have hprod : ∫ z : ℝ × ℝ, G z = ∫ x : ℝ, ∫ y : ℝ, G (x, y) := integral_prod G hGint'
  rw [hprod]
  have hinner : ∀ x : ℝ, ∫ y : ℝ, G (x, y) =
      (Set.Ioo (0 : ℝ) 1).indicator (fun x => 2 * x * Real.sqrt (1 - x ^ 2)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
    · have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      rw [Set.indicator_of_mem hx]
      generalize hs_def : Real.sqrt (1 - x ^ 2) = s
      have hs : 0 < s := hs_def ▸ Real.sqrt_pos.mpr hx2
      have hset : ∀ y : ℝ, y ∈ Set.Ioo (-s) s ↔ x ^ 2 + y ^ 2 < 1 := by
        intro y
        rw [Set.mem_Ioo, ← abs_lt, ← hs_def, Real.lt_sqrt (abs_nonneg y), sq_abs]
        constructor <;> intro h <;> linarith
      have hfun : (fun y : ℝ => G (x, y)) = (Set.Ioo (-s) s).indicator (fun _ => x) := by
        funext y
        by_cases hy : y ∈ Set.Ioo (-s) s
        · have hc : x ^ 2 + y ^ 2 < 1 := (hset y).mp hy
          simp [hG, hc, hy, max_eq_left hx.1.le]
        · have hc : ¬ (x ^ 2 + y ^ 2 < 1) := fun hc => hy ((hset y).mpr hc)
          simp [hG, hc, hy]
      rw [hfun, integral_indicator measurableSet_Ioo, setIntegral_const]
      simp only [measureReal_def, Real.volume_Ioo, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by linarith)]
      ring
    · have hzero : ∀ y : ℝ, G (x, y) = 0 := by
        intro y
        by_cases hx1 : x ≤ 0
        · simp [hG, max_eq_right hx1]
        · have hx2 : 1 ≤ x := by
            by_contra h
            exact hx ⟨by linarith [not_le.mp hx1], by linarith [not_le.mp h]⟩
          have hc : ¬ (x ^ 2 + y ^ 2 < 1) := by nlinarith [sq_nonneg y]
          simp [hG, hc]
      simp only [hzero, integral_zero, Set.indicator_of_notMem hx]
  simp_rw [hinner]
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  exact integral_x_sqrt

/-- The first moment of the positive part of a linear form over the unit disk is `2/3` for
every unit vector, by a rotation to the first coordinate. -/
private lemma integral_ball_angular {e : E2} (he : ‖e‖ = 1) :
    ∫ v in Metric.ball (0 : E2) 1, max (inner ℝ e v) 0 = 2 / 3 := by
  set e₀ : E2 := EuclideanSpace.single 0 1 with he₀
  have hne : ‖e‖ = ‖e₀‖ := by simp [he₀, he]
  set A := Submodule.reflection (ℝ ∙ (e - e₀))ᗮ
  have hAe : A e = e₀ := Submodule.reflection_sub hne
  have hmp := (LinearIsometryEquiv.measurePreserving A).setIntegral_preimage_emb
    A.toMeasurableEquiv.measurableEmbedding (fun w : E2 => max (inner ℝ e₀ w) 0)
    (Metric.ball 0 1)
  rw [LinearIsometryEquiv.preimage_ball, A.symm.map_zero] at hmp
  calc ∫ v in Metric.ball (0 : E2) 1, max (inner ℝ e v) 0
      = ∫ x in Metric.ball (0 : E2) 1, max (inner ℝ e₀ (A x)) 0 := by
        refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
        rw [← hAe, A.inner_map_map]
    _ = ∫ y in Metric.ball (0 : E2) 1, max (inner ℝ e₀ y) 0 := hmp
    _ = ∫ y in Metric.ball (0 : E2) 1, max (y 0) 0 := by
        refine setIntegral_congr_fun measurableSet_ball fun y _ => ?_
        simp [he₀, EuclideanSpace.inner_single_left]
    _ = 2 / 3 := integral_ball_coord

/-- The angular constant: the sphere integral of the positive part of `⟪e, θ⟫` is `2`. -/
private lemma angular_const {e : E2} (he : ‖e‖ = 1) :
    ∫ θ : Metric.sphere (0 : E2) 1, max (inner ℝ e (θ : E2) / ‖(θ : E2)‖) 0
      ∂(volume : Measure E2).toSphere = 2 := by
  have hh : ∀ r : ℝ, |(Set.Ioo (0 : ℝ) 1).indicator (fun r => r) r| ≤ 1 := by
    intro r
    by_cases hr : r ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hr, abs_of_pos hr.1]; exact hr.2.le
    · rw [Set.indicator_of_notMem hr]; simp
  have hs : ∀ r : ℝ, 1 < r → (Set.Ioo (0 : ℝ) 1).indicator (fun r => r) r = 0 := by
    intro r hr
    exact Set.indicator_of_notMem (fun h => by linarith [h.2]) _
  have hpolar := integral_polar_sep (fun v : E2 => max (inner ℝ e v / ‖v‖) 0)
    (measurable_angular e)
    (fun v => by rw [abs_of_nonneg (angular_nonneg e v)]; exact angular_le_one he.le v)
    (fun r hr v => angular_smul e v hr)
    ((Set.Ioo (0 : ℝ) 1).indicator (fun r => r)) (measurable_id'.indicator measurableSet_Ioo)
    (M := 1) (T := 1) hh hs
  have hLHS : ∫ v : E2, (Set.Ioo (0 : ℝ) 1).indicator (fun r => r) ‖v‖ *
        max (inner ℝ e v / ‖v‖) 0 = ∫ v in Metric.ball (0 : E2) 1, max (inner ℝ e v) 0 := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    by_cases h0 : v = 0
    · subst h0; simp
    · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr h0
      by_cases h1 : ‖v‖ < 1
      · have hv : v ∈ Metric.ball (0 : E2) 1 := by simpa using h1
        rw [Set.indicator_of_mem hv,
          Set.indicator_of_mem (show ‖v‖ ∈ Set.Ioo (0 : ℝ) 1 from ⟨hpos, h1⟩),
          mul_max_of_nonneg _ _ hpos.le]
        have : ‖v‖ * (inner ℝ e v / ‖v‖) = inner ℝ e v := by field_simp
        rw [this, mul_zero]
      · have hv : v ∉ Metric.ball (0 : E2) 1 := by simpa using h1
        rw [Set.indicator_of_notMem hv,
          Set.indicator_of_notMem (show ‖v‖ ∉ Set.Ioo (0 : ℝ) 1 from fun h => h1 h.2)]
        simp
  have hrad : ∫ r in Set.Ioi (0 : ℝ), r * (Set.Ioo (0 : ℝ) 1).indicator (fun r => r) r
      = 1 / 3 := by
    have hpt : ∀ r : ℝ, r * (Set.Ioo (0 : ℝ) 1).indicator (fun r => r) r =
        (Set.Ioo (0 : ℝ) 1).indicator (fun r => r ^ 2) r := by
      intro r
      by_cases hr : r ∈ Set.Ioo (0 : ℝ) 1 <;> simp [hr, sq]
    simp_rw [hpt]
    have hsub : Set.Ioi (0 : ℝ) ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 :=
      Set.inter_eq_right.mpr (fun r hr => hr.1)
    rw [setIntegral_indicator measurableSet_Ioo, hsub,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    norm_num
  rw [hLHS, integral_ball_angular he, hrad] at hpolar
  linarith

/-- The integral of the angular profile times a radial indicator over the plane, in terms of
the radial integral `∫_a^b r dr`: for `0 ≤ a ≤ b` it is `b² - a²`. -/
private lemma integral_annulus_angular {e : E2} (he : ‖e‖ = 1) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∫ v : E2, (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) ‖v‖ * max (inner ℝ e v / ‖v‖) 0 =
      b ^ 2 - a ^ 2 := by
  have hh : ∀ r : ℝ, |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) r| ≤ 1 := by
    intro r
    by_cases hr : r ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hr]; simp
    · rw [Set.indicator_of_notMem hr]; simp
  have hs : ∀ r : ℝ, b < r → (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) r = 0 := by
    intro r hr
    exact Set.indicator_of_notMem (fun h => by linarith [h.2]) _
  rw [integral_polar_sep (fun v : E2 => max (inner ℝ e v / ‖v‖) 0) (measurable_angular e)
    (fun v => by rw [abs_of_nonneg (angular_nonneg e v)]; exact angular_le_one he.le v)
    (fun r hr v => angular_smul e v hr)
    ((Set.Ioc a b).indicator (fun _ => (1 : ℝ))) (measurable_const.indicator measurableSet_Ioc)
    (M := 1) (T := b) hh hs]
  rw [angular_const he]
  have hrad : ∫ r in Set.Ioi (0 : ℝ), r * (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) r =
      (b ^ 2 - a ^ 2) / 2 := by
    have hpt : ∀ r : ℝ, r * (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) r =
        (Set.Ioc a b).indicator (fun r => r) r := by
      intro r
      by_cases hr : r ∈ Set.Ioc a b <;> simp [hr]
    simp_rw [hpt]
    have hsub : Set.Ioi (0 : ℝ) ∩ Set.Ioc a b = Set.Ioc a b :=
      Set.inter_eq_right.mpr (fun r hr => lt_of_le_of_lt ha hr.1)
    rw [setIntegral_indicator measurableSet_Ioc, hsub,
      ← intervalIntegral.integral_of_le hab, integral_id]
  rw [hrad]
  ring

/-- The integral of `1/|v|` over an annulus is the total mass of the sphere times its width:
for `0 < a ≤ b`. -/
private lemma integral_annulus_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ v : E2, (Set.Ioc a b).indicator (fun r : ℝ => r⁻¹) ‖v‖ =
      ((volume : Measure E2).toSphere Set.univ).toReal * (b - a) := by
  have hh : ∀ r : ℝ, |(Set.Ioc a b).indicator (fun r : ℝ => r⁻¹) r| ≤ a⁻¹ := by
    intro r
    by_cases hr : r ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hr, abs_of_pos (inv_pos.mpr (ha.trans hr.1))]
      exact (inv_le_inv₀ (ha.trans hr.1) ha).mpr hr.1.le
    · rw [Set.indicator_of_notMem hr]; simp [ha.le]
  have hs : ∀ r : ℝ, b < r → (Set.Ioc a b).indicator (fun r : ℝ => r⁻¹) r = 0 := by
    intro r hr
    exact Set.indicator_of_notMem (fun h => by linarith [h.2]) _
  have hpol := integral_polar_sep (fun _ : E2 => (1 : ℝ)) measurable_const (fun _ => by simp)
    (fun _ _ _ => rfl) ((Set.Ioc a b).indicator (fun r : ℝ => r⁻¹))
    (measurable_inv.indicator measurableSet_Ioc) (M := a⁻¹) (T := b) hh hs
  simp only [mul_one] at hpol
  rw [hpol]
  have hrad : ∫ r in Set.Ioi (0 : ℝ), r * (Set.Ioc a b).indicator (fun r : ℝ => r⁻¹) r = b - a := by
    have hpt : ∀ r : ℝ, r * (Set.Ioc a b).indicator (fun r : ℝ => r⁻¹) r =
        (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) r := by
      intro r
      by_cases hr : r ∈ Set.Ioc a b
      · simp only [Set.indicator_of_mem hr]
        exact mul_inv_cancel₀ (ha.trans hr.1).ne'
      · simp [hr]
    simp_rw [hpt]
    have hsub : Set.Ioi (0 : ℝ) ∩ Set.Ioc a b = Set.Ioc a b :=
      Set.inter_eq_right.mpr (fun r hr => ha.trans hr.1)
    rw [setIntegral_indicator measurableSet_Ioc, hsub, setIntegral_const]
    simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hrad, integral_const]
  simp [measureReal_def]

/-! ### Lattice facts -/

/-- The Euclidean norm of a planar site is invariant under `x ↦ -x`. -/
private lemma euclidNorm_neg (x : Site 2) : euclidNorm (-x) = euclidNorm x := by
  simp [LatticeProb.euclidNorm]

/-- The embedding of the lattice commutes with negation. -/
private lemma toSpace_neg' (x : Site 2) : toSpace (-x) = -toSpace x := by
  ext i
  simp

/-- The direction map is odd. -/
private lemma unitDir_neg' (v : E2) : unitDir (-v) = -unitDir v := by
  simp [unitDir]

/-- The Euclidean norm of a planar site in coordinates. -/
private lemma euclidNorm_two (x : Site 2) :
    euclidNorm x = Real.sqrt (((x 0 : ℤ) : ℝ) ^ 2 + ((x 1 : ℤ) : ℝ) ^ 2) := by
  simp [LatticeProb.euclidNorm, Fin.sum_univ_two]

/-- A nonzero site embeds to a nonzero vector. -/
private lemma toSpace_ne_zero {x : Site 2} (hx : x ≠ 0) : toSpace x ≠ 0 := by
  intro h
  apply hx
  funext i
  have := congrArg (fun v : E2 => v i) h
  simpa using this

/-- A nonzero lattice site has Euclidean norm at least one. -/
private lemma one_le_norm_toSpace {x : Site 2} (hx : x ≠ 0) : 1 ≤ ‖toSpace x‖ := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    apply hx
    funext i
    by_contra hne
    exact hcon ⟨i, hne⟩
  have h1 : (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi
  calc (1 : ℝ) ≤ |((x i : ℤ) : ℝ)| := h1
    _ = ‖(toSpace x) i‖ := by simp
    _ ≤ ‖toSpace x‖ := PiLp.norm_apply_le _ i

/-- `√2/2 ≤ 3/4`. -/
private lemma sqrt_two_div_two_le : Real.sqrt ((2 : ℕ) : ℝ) / 2 ≤ 3 / 4 := by
  have h : Real.sqrt ((2 : ℕ) : ℝ) ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  linarith

/-- A point of the unit cell of a site is within `3/4` of the site. -/
private lemma norm_sub_le_of_mem_cell {x : Site 2} {v : E2} (hv : v ∈ cell x) :
    ‖v - toSpace x‖ ≤ 3 / 4 :=
  (norm_sub_toSpace_le_of_mem_cell hv).trans sqrt_two_div_two_le

/-- The integral of a constant over a unit cell. -/
private lemma setIntegral_const_cell (x : Site 2) (c : ℝ) : ∫ _v in cell x, c = c := by
  rw [setIntegral_const, measureReal_def, volume_cell]
  simp

/-- Comparison of the profile at a site with the profile at a point of its cell. -/
private lemma cell_compare {e : E2} (he : ‖e‖ = 1) {x : Site 2} (hx : x ≠ 0) {v : E2}
    (hv : v ∈ cell x) :
    max (inner ℝ e (unitDir (toSpace x))) 0 ≤
      max (inner ℝ e v / ‖v‖) 0 + 2 / ‖toSpace x‖ := by
  rw [angular_eq_unitDir]
  have hsub : ‖unitDir (toSpace x) - unitDir v‖ ≤ 2 / ‖toSpace x‖ := by
    refine (norm_unitDir_sub_le (toSpace_ne_zero hx)).trans ?_
    have hc : ‖toSpace x - v‖ ≤ 1 := by
      rw [norm_sub_rev]; linarith [norm_sub_le_of_mem_cell hv]
    calc 2 * ‖toSpace x - v‖ / ‖toSpace x‖ ≤ 2 * 1 / ‖toSpace x‖ := by gcongr
      _ = 2 / ‖toSpace x‖ := by ring
  have habs : |max (inner ℝ e (unitDir (toSpace x))) 0 - max (inner ℝ e (unitDir v)) 0| ≤
      ‖unitDir (toSpace x) - unitDir v‖ := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [← inner_sub_right]
    calc |inner ℝ e (unitDir (toSpace x) - unitDir v)|
        ≤ ‖e‖ * ‖unitDir (toSpace x) - unitDir v‖ := abs_real_inner_le_norm _ _
      _ = ‖unitDir (toSpace x) - unitDir v‖ := by rw [he, one_mul]
  have := (le_abs_self _).trans habs
  linarith

/-- The sum of the directions over a finite set of sites that is invariant under negation
vanishes. -/
private lemma sum_unitDir_neg_invariant (L : Finset (Site 2)) (hL : ∀ x ∈ L, -x ∈ L) :
    ∑ x ∈ L, unitDir (toSpace x) = 0 := by
  have h : ∑ x ∈ L, unitDir (toSpace x) = ∑ x ∈ L, unitDir (toSpace (-x)) :=
    Finset.sum_nbij' (fun x => -x) (fun x => -x) hL hL (fun x _ => neg_neg x)
      (fun x _ => neg_neg x) (fun x _ => by simp [neg_neg])
  simp only [toSpace_neg', unitDir_neg', Finset.sum_neg_distrib] at h
  have h2 : (2 : ℝ) • ∑ x ∈ L, unitDir (toSpace x) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-! ### The lattice sum against the angular profile -/

/-- The sum over a finite set of nonzero lattice sites of the positive part of `⟪e, u_x⟫` is at
most the annular integral plus the cell error. -/
private lemma sum_angular_le {e : E2} (he : ‖e‖ = 1) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R)
    (hρR : ρ ≤ R + 1) (H : Finset (Site 2))
    (hH : ∀ x ∈ H, x ≠ 0 ∧ ρ ≤ euclidNorm x ∧ euclidNorm x ≤ R) :
    ∑ x ∈ H, max (inner ℝ e (unitDir (toSpace x))) 0 ≤
      R ^ 2 - ρ ^ 2 +
        (4 + 4 * ((volume : Measure E2).toSphere Set.univ).toReal) * (R + 1) := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = ((volume : Measure E2).toSphere Set.univ).toReal := ⟨_, rfl⟩
  rw [← hσ]
  have hσ0 : 0 ≤ σ := by rw [hσ]; exact ENNReal.toReal_nonneg
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = max (ρ - 1) 0 := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = R + 1 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha_def]; exact le_max_right _ _
  have hab : a ≤ b := by rw [ha_def, hb_def]; exact max_le (by linarith) (by linarith)
  have hone : ∀ x ∈ H, 1 ≤ ‖toSpace x‖ := fun x hx => one_le_norm_toSpace (hH x hx).1
  have hFn : ∀ x : Site 2, ‖toSpace x‖ = euclidNorm x := fun x => norm_toSpace x
  -- the geometry of the cells
  have hcell_lo : ∀ x ∈ H, ∀ v ∈ cell x, 1 / 4 ≤ ‖v‖ ∧ euclidNorm x - 3 / 4 ≤ ‖v‖ := by
    intro x hx v hv
    have h1 := norm_sub_le_of_mem_cell hv
    have h2 : ‖toSpace x‖ - ‖v‖ ≤ ‖v - toSpace x‖ := by
      have := norm_sub_norm_le (toSpace x) v
      rwa [norm_sub_rev] at this
    have h3 := hone x hx
    have h4 := hFn x
    exact ⟨by linarith, by linarith⟩
  have hcell_hi : ∀ x ∈ H, ∀ v ∈ cell x, ‖v‖ ≤ euclidNorm x + 3 / 4 ∧
      ‖v‖ ≤ 2 * ‖toSpace x‖ := by
    intro x hx v hv
    have h1 := norm_sub_le_of_mem_cell hv
    have h2 : ‖v‖ - ‖toSpace x‖ ≤ ‖v - toSpace x‖ := norm_sub_norm_le v (toSpace x)
    have h3 := hone x hx
    have h4 := hFn x
    exact ⟨by linarith, by linarith⟩
  have hvolball : ∀ r : ℝ, volume (Metric.closedBall (0 : E2) r) ≠ ⊤ :=
    fun r => (measure_closedBall_lt_top).ne
  obtain ⟨Ann₁, hAnn₁⟩ : ∃ S : Set E2, S = (fun v : E2 => ‖v‖) ⁻¹' Set.Ioc a b := ⟨_, rfl⟩
  obtain ⟨Ann₂, hAnn₂⟩ : ∃ S : Set E2, S = (fun v : E2 => ‖v‖) ⁻¹' Set.Ioc (1 / 8) b := ⟨_, rfl⟩
  have hmem₁ : ∀ v : E2, v ∈ Ann₁ ↔ a < ‖v‖ ∧ ‖v‖ ≤ b := by
    intro v; rw [hAnn₁]; exact Iff.rfl
  have hmem₂ : ∀ v : E2, v ∈ Ann₂ ↔ 1 / 8 < ‖v‖ ∧ ‖v‖ ≤ b := by
    intro v; rw [hAnn₂]; exact Iff.rfl
  have hAnn₁m : MeasurableSet Ann₁ := by
    rw [hAnn₁]; exact measurable_norm measurableSet_Ioc
  have hAnn₂m : MeasurableSet Ann₂ := by
    rw [hAnn₂]; exact measurable_norm measurableSet_Ioc
  have hvol₁ : volume Ann₁ ≠ ⊤ :=
    ne_top_of_le_ne_top (hvolball b) (measure_mono (fun v hv =>
      mem_closedBall_zero_iff.mpr ((hmem₁ v).mp hv).2))
  have hvol₂ : volume Ann₂ ≠ ⊤ :=
    ne_top_of_le_ne_top (hvolball b) (measure_mono (fun v hv =>
      mem_closedBall_zero_iff.mpr ((hmem₂ v).mp hv).2))
  have hsub₁ : ∀ x ∈ H, cell x ⊆ Ann₁ := by
    intro x hx v hv
    obtain ⟨hlo1, hlo2⟩ := hcell_lo x hx v hv
    obtain ⟨hhi1, -⟩ := hcell_hi x hx v hv
    obtain ⟨-, hρx, hxR⟩ := hH x hx
    refine (hmem₁ v).mpr ⟨?_, by linarith⟩
    rw [ha_def]
    exact max_lt (by linarith) (by linarith)
  have hsub₂ : ∀ x ∈ H, cell x ⊆ Ann₂ := by
    intro x hx v hv
    obtain ⟨hlo1, -⟩ := hcell_lo x hx v hv
    obtain ⟨hhi1, -⟩ := hcell_hi x hx v hv
    obtain ⟨-, -, hxR⟩ := hH x hx
    exact (hmem₂ v).mpr ⟨by linarith, by linarith⟩
  have hcellvol : ∀ x : Site 2, volume (cell x) ≠ ⊤ := fun x => by
    rw [volume_cell]; exact ENNReal.one_ne_top
  have hFint : ∀ S : Set E2, volume S ≠ ⊤ →
      IntegrableOn (fun v : E2 => max (inner ℝ e v / ‖v‖) 0) S :=
    fun S hS => integrableOn_angular he hS
  -- (1) the comparison on each cell
  have hmain : ∀ x ∈ H, max (inner ℝ e (unitDir (toSpace x))) 0 ≤
      (∫ v in cell x, max (inner ℝ e v / ‖v‖) 0) + 2 / ‖toSpace x‖ := by
    intro x hx
    have hx0 := (hH x hx).1
    have hle : ∫ _v in cell x, (max (inner ℝ e (unitDir (toSpace x))) 0 - 2 / ‖toSpace x‖) ≤
        ∫ v in cell x, max (inner ℝ e v / ‖v‖) 0 := by
      refine setIntegral_mono_on (integrableOn_const (hcellvol x)) (hFint _ (hcellvol x))
        (measurableSet_cell x) fun v hv => ?_
      have := cell_compare he hx0 hv
      linarith
    rw [setIntegral_const_cell] at hle
    linarith
  have hsum1 : ∑ x ∈ H, max (inner ℝ e (unitDir (toSpace x))) 0 ≤
      (∑ x ∈ H, ∫ v in cell x, max (inner ℝ e v / ‖v‖) 0) + ∑ x ∈ H, 2 / ‖toSpace x‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hmain
  -- (2) the cell integrals add up to at most the annular integral
  have hbig : ∑ x ∈ H, ∫ v in cell x, max (inner ℝ e v / ‖v‖) 0 ≤ b ^ 2 - a ^ 2 := by
    rw [← integral_biUnion_finset H (fun x _ => measurableSet_cell x)
      (fun x _ y _ hxy => cell_disjoint hxy) (fun x _ => hFint _ (hcellvol x))]
    calc ∫ v in ⋃ x ∈ H, cell x, max (inner ℝ e v / ‖v‖) 0
        ≤ ∫ v in Ann₁, max (inner ℝ e v / ‖v‖) 0 := by
          refine setIntegral_mono_set (hFint _ hvol₁)
            (Filter.Eventually.of_forall fun v => angular_nonneg e v) ?_
          exact (Set.iUnion₂_subset hsub₁).eventuallyLE
      _ = ∫ v : E2, (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) ‖v‖ *
            max (inner ℝ e v / ‖v‖) 0 := by
          rw [← integral_indicator hAnn₁m]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          dsimp only
          by_cases hv : ‖v‖ ∈ Set.Ioc a b
          · have hv' : v ∈ Ann₁ := (hmem₁ v).mpr hv
            rw [Set.indicator_of_mem hv', Set.indicator_of_mem hv, one_mul]
          · have hv' : v ∉ Ann₁ := fun h => hv ((hmem₁ v).mp h)
            rw [Set.indicator_of_notMem hv', Set.indicator_of_notMem hv, zero_mul]
      _ = b ^ 2 - a ^ 2 := integral_annulus_angular he ha0 hab
  -- (3) the error terms
  have herr : ∑ x ∈ H, 2 / ‖toSpace x‖ ≤ 4 * σ * b := by
    have hinteg : ∀ x ∈ H, IntegrableOn (fun v : E2 => 4 * ‖v‖⁻¹) (cell x) := by
      intro x hx
      refine Measure.integrableOn_of_bounded (M := 16) (hcellvol x) ?_ ?_
      · exact (measurable_const.mul measurable_norm.inv).aestronglyMeasurable
      · refine (ae_restrict_iff' (measurableSet_cell x)).2
          (Filter.Eventually.of_forall fun v hv => ?_)
        have h1 := (hcell_lo x hx v hv).1
        have h2 : ‖v‖⁻¹ ≤ 4 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        rw [Real.norm_of_nonneg (by positivity)]
        linarith
    have hpt : ∀ x ∈ H, 2 / ‖toSpace x‖ ≤ ∫ v in cell x, 4 * ‖v‖⁻¹ := by
      intro x hx
      have hle : ∫ _v in cell x, 2 / ‖toSpace x‖ ≤ ∫ v in cell x, 4 * ‖v‖⁻¹ := by
        refine setIntegral_mono_on (integrableOn_const (hcellvol x)) (hinteg x hx)
          (measurableSet_cell x) fun v hv => ?_
        have hv2 := (hcell_hi x hx v hv).2
        have hv1 : 0 < ‖v‖ := by linarith [(hcell_lo x hx v hv).1]
        have hx1 : 0 < ‖toSpace x‖ := by linarith [hone x hx]
        have h4 : 4 * ‖v‖⁻¹ = 4 / ‖v‖ := by ring
        rw [h4, div_le_div_iff₀ hx1 hv1]
        linarith
      rwa [setIntegral_const_cell] at hle
    have hint₂ : IntegrableOn (fun v : E2 => 4 * ‖v‖⁻¹) Ann₂ := by
      refine Measure.integrableOn_of_bounded (M := 32) hvol₂ ?_ ?_
      · exact (measurable_const.mul measurable_norm.inv).aestronglyMeasurable
      · refine (ae_restrict_iff' hAnn₂m).2 (Filter.Eventually.of_forall fun v hv => ?_)
        have h1 : 1 / 8 < ‖v‖ := ((hmem₂ v).mp hv).1
        have h2 : ‖v‖⁻¹ ≤ 8 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        rw [Real.norm_of_nonneg (by positivity)]
        linarith
    calc ∑ x ∈ H, 2 / ‖toSpace x‖ ≤ ∑ x ∈ H, ∫ v in cell x, 4 * ‖v‖⁻¹ :=
          Finset.sum_le_sum hpt
      _ = ∫ v in ⋃ x ∈ H, cell x, 4 * ‖v‖⁻¹ :=
          (integral_biUnion_finset H (fun x _ => measurableSet_cell x)
            (fun x _ y _ hxy => cell_disjoint hxy) hinteg).symm
      _ ≤ ∫ v in Ann₂, 4 * ‖v‖⁻¹ := by
          refine setIntegral_mono_set hint₂
            (Filter.Eventually.of_forall fun v => by simp only [Pi.zero_apply]; positivity) ?_
          exact (Set.iUnion₂_subset hsub₂).eventuallyLE
      _ = 4 * ∫ v : E2, (Set.Ioc (1 / 8 : ℝ) b).indicator (fun r : ℝ => r⁻¹) ‖v‖ := by
          rw [← integral_indicator hAnn₂m, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          dsimp only
          by_cases hv : ‖v‖ ∈ Set.Ioc (1 / 8 : ℝ) b
          · have hv' : v ∈ Ann₂ := (hmem₂ v).mpr hv
            rw [Set.indicator_of_mem hv', Set.indicator_of_mem hv]
          · have hv' : v ∉ Ann₂ := fun h => hv ((hmem₂ v).mp h)
            rw [Set.indicator_of_notMem hv', Set.indicator_of_notMem hv, mul_zero]
      _ = 4 * (σ * (b - 1 / 8)) := by
          rw [integral_annulus_inv (a := 1 / 8) (b := b) (by norm_num) (by linarith), hσ]
      _ ≤ 4 * σ * b := by nlinarith
  have harith : b ^ 2 - a ^ 2 ≤ R ^ 2 - ρ ^ 2 + 4 * (R + 1) := by
    rcases le_total (ρ - 1) 0 with h | h
    · rw [ha_def, hb_def, max_eq_right h]; nlinarith
    · rw [ha_def, hb_def, max_eq_left h]; nlinarith
  calc ∑ x ∈ H, max (inner ℝ e (unitDir (toSpace x))) 0
      ≤ (b ^ 2 - a ^ 2) + 4 * σ * b := hsum1.trans (add_le_add hbig herr)
    _ ≤ R ^ 2 - ρ ^ 2 + 4 * (R + 1) + 4 * σ * (R + 1) := by
        have hbσ : 4 * σ * b = 4 * σ * (R + 1) := by rw [hb_def]
        linarith [harith, hbσ]
    _ = R ^ 2 - ρ ^ 2 + (4 + 4 * σ) * (R + 1) := by ring

/-- Every vector of the plane has a unit vector whose inner product with it is its norm. -/
private lemma exists_unit_inner_eq_norm (V : E2) : ∃ e : E2, ‖e‖ = 1 ∧ inner ℝ e V = ‖V‖ := by
  by_cases hV0 : V = 0
  · exact ⟨EuclideanSpace.single 0 1, by simp, by simp [hV0]⟩
  · have hn : ‖V‖ ≠ 0 := norm_ne_zero_iff.mpr hV0
    refine ⟨‖V‖⁻¹ • V, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp

/-! ### The annulus bound -/

/-- **The direction-free annulus bound, directional form.** For a finite set `A` of planar lattice
sites that contains the lattice disk `{|x| < ρ}` and lies in `{|x| ≤ R}`, the sum of the directions
`u_x = x/|x|` satisfies `⟪e, ∑_{x ∈ A} u_x⟫ ≤ R² - ρ² + C (R + 1)` for every unit vector `e`, with
one absolute constant `C` independent of `A`, `ρ`, `R` and `e`. -/
theorem inner_sum_unitDir_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Site 2)) {ρ R : ℝ}, 0 ≤ ρ → 0 ≤ R →
      (∀ x : Site 2, euclidNorm x < ρ → x ∈ A) → (∀ x ∈ A, euclidNorm x ≤ R) →
      ∀ e : E2, ‖e‖ = 1 →
        inner ℝ e (∑ x ∈ A, unitDir (toSpace x)) ≤ R ^ 2 - ρ ^ 2 + C * (R + 1) := by
  classical
  refine ⟨4 + 4 * ((volume : Measure E2).toSphere Set.univ).toReal, by positivity, ?_⟩
  intro A ρ R hρ hR hin hout e he
  have hρR : ρ ≤ R + 1 := by
    by_contra hlt
    rw [not_le] at hlt
    set s : Site 2 := ![((⌊R⌋₊ : ℕ) : ℤ) + 1, 0] with hs
    have hsn : euclidNorm s = (⌊R⌋₊ : ℝ) + 1 := by
      rw [euclidNorm_two]
      simp only [hs, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      rw [show (((⌊R⌋₊ : ℕ) : ℝ) + 1) ^ 2 + (0 : ℝ) ^ 2 = (((⌊R⌋₊ : ℕ) : ℝ) + 1) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    have h1 : euclidNorm s < ρ := by linarith [Nat.floor_le hR]
    have h2 := hout s (hin s h1)
    linarith [Nat.lt_floor_add_one R]
  -- the inner disk cancels
  have hsplit := Finset.sum_filter_add_sum_filter_not A (fun x => euclidNorm x < ρ)
    (fun x => unitDir (toSpace x))
  have hlow : ∑ x ∈ A.filter (fun x => euclidNorm x < ρ), unitDir (toSpace x) = 0 := by
    refine sum_unitDir_neg_invariant _ fun x hx => ?_
    rw [Finset.mem_filter] at hx ⊢
    have : euclidNorm (-x) < ρ := by rw [euclidNorm_neg]; exact hx.2
    exact ⟨hin _ this, this⟩
  rw [← hsplit, hlow, zero_add, inner_sum]
  -- the remaining sites lie in the lattice annulus
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : Finset (Site 2), H₀ =
      ((LatticeProb.ballFinset 2 R).filter (fun x => ρ ≤ euclidNorm x)).filter
        (fun x => x ≠ 0) := ⟨_, rfl⟩
  have hmemH : ∀ x : Site 2, x ∈ H₀ ↔ (euclidNorm x ≤ R ∧ ρ ≤ euclidNorm x) ∧ x ≠ 0 := by
    intro x
    rw [hH₀, Finset.mem_filter, Finset.mem_filter, LatticeProb.mem_ballFinset_iff]
  have hH : ∀ x ∈ H₀, x ≠ 0 ∧ ρ ≤ euclidNorm x ∧ euclidNorm x ≤ R := by
    intro x hx
    have := (hmemH x).mp hx
    exact ⟨this.2, this.1.2, this.1.1⟩
  have hzero : ∀ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ),
      max (inner ℝ e (unitDir (toSpace x))) 0 ≠ 0 → x ≠ 0 := by
    intro x _ hne hx0
    apply hne
    have : toSpace (0 : Site 2) = 0 := by ext i; simp
    simp [hx0, this]
  have hsub : (A.filter (fun x => ¬ euclidNorm x < ρ)).filter (fun x => x ≠ 0) ⊆ H₀ := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_filter] at hx
    exact (hmemH x).mpr ⟨⟨hout x hx.1.1, not_lt.mp hx.1.2⟩, hx.2⟩
  calc ∑ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ), inner ℝ e (unitDir (toSpace x))
      ≤ ∑ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ),
          max (inner ℝ e (unitDir (toSpace x))) 0 :=
        Finset.sum_le_sum fun x _ => le_max_left _ _
    _ = ∑ x ∈ (A.filter (fun x => ¬ euclidNorm x < ρ)).filter (fun x => x ≠ 0),
          max (inner ℝ e (unitDir (toSpace x))) 0 :=
        (Finset.sum_filter_of_ne hzero).symm
    _ ≤ ∑ x ∈ H₀, max (inner ℝ e (unitDir (toSpace x))) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => le_max_right _ _
    _ ≤ _ := sum_angular_le he hρ hR hρR H₀ hH

/-- **The direction-free annulus bound.** For a finite set `A` of planar lattice sites that
contains the lattice disk `{|x| < ρ}` and lies in `{|x| ≤ R}`,
`‖∑_{x ∈ A} u_x‖ ≤ R² - ρ² + C (R + 1)`, with one absolute constant `C` independent of `A`, `ρ`
and `R`. The leading coefficient is one. -/
theorem norm_sum_unitDir_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Site 2)) {ρ R : ℝ}, 0 ≤ ρ → 0 ≤ R →
      (∀ x : Site 2, euclidNorm x < ρ → x ∈ A) → (∀ x ∈ A, euclidNorm x ≤ R) →
        ‖∑ x ∈ A, unitDir (toSpace x)‖ ≤ R ^ 2 - ρ ^ 2 + C * (R + 1) := by
  obtain ⟨C, hC, h⟩ := inner_sum_unitDir_le
  refine ⟨C, hC, fun A ρ R hρ hR hin hout => ?_⟩
  obtain ⟨e, he, hVe⟩ := exists_unit_inner_eq_norm (∑ x ∈ A, unitDir (toSpace x))
  rw [← hVe]
  exact h A hρ hR hin hout e he

end CERW.Support.Lower.PlanarGap
