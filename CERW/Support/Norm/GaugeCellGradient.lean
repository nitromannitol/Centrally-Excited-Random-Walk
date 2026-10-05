import CERW.Support.Norm.GaugeLaplacian
import CERW.Support.Norm.GaugePotential
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume
import CERW.Support.Drift
import CERW.Support.LocalTime
import CERW.Support.Geometry
import CERW.Generic.Lattice.Packing

/-!
# The gradient of the gauge of a convex body on a cell

Lemma `lem:cell` of the paper for the literal Minkowski functional `ψ_K = gauge K` of a compact
convex set `K ⊆ ℝ^d` with the origin in its interior, which is convex and positively homogeneous but
need not be even: for every choice of subgradients `ξ(x) ∈ ∂ψ_K(x)` at the lattice sites (and
`ξ(0) = 0`) and every locally finite measure `m` that is the distributional Laplacian of `ψ_K`
(`GaugeLaplacian`), the cell `C_x` satisfies `∫_{C_x} |∇ψ_K - ξ(x)| ≤ C m(B(x, 6 √d))`, with `C`
depending only on the dimension.

The proof is that of the symmetric case. The recentred function `ψ_K(x + u) - ψ_K(x) - ξ · u` is
nonnegative, convex along rays through the origin, and its integral against a radial profile is
bounded by the mass of `m` on a ball (the weak mass bound); at a point of differentiability the
gradient differs from a subgradient by at most the sum of the excesses at the `2d` neighbours.
Convexity, continuity, the subgradient property of the gradient and almost-everywhere
differentiability (all in `GaugeModel`) replace the properties of a norm.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeCellGradient

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugeLaplacian

section CellLemma

open scoped ContDiff

/-- A smooth radial cut-off profile: values in `[0, 1]`, equal to `1` up to `a ^ 2` and
vanishing from `r ^ 2` on. -/
private structure Cutoff (a r : ℝ) (b : ℝ → ℝ) : Prop where
  /-- The profile is smooth. -/
  smooth : ContDiff ℝ ∞ b
  /-- The profile is nonnegative. -/
  nonneg : ∀ s, 0 ≤ b s
  /-- The profile is at most one. -/
  le_one : ∀ s, b s ≤ 1
  /-- The profile equals one up to `a ^ 2`. -/
  eq_one : ∀ s, s ≤ a ^ 2 → b s = 1
  /-- The profile vanishes from `r ^ 2` on. -/
  eq_zero : ∀ s, r ^ 2 ≤ s → b s = 0

/-- For `0 ≤ a < r` there is a smooth cut-off profile. -/
private lemma exists_cutoff {a r : ℝ} (ha : 0 ≤ a) (h : a < r) : ∃ b, Cutoff a r b := by
  have hpos : 0 < r ^ 2 - a ^ 2 := by nlinarith
  have hsm : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition ((r ^ 2 - s) / (r ^ 2 - a ^ 2))) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  refine ⟨fun s => Real.smoothTransition ((r ^ 2 - s) / (r ^ 2 - a ^ 2)), hsm, ?_, ?_, ?_, ?_⟩
  · intro s
    exact Real.smoothTransition.nonneg _
  · intro s
    exact Real.smoothTransition.le_one _
  · intro s hs
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hpos]
    linarith
  · intro s hs
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le

/-- The primitive `E(s) = ∫_0^s b`. -/
private noncomputable def prim (b : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, b t

/-- The primitive of a continuous function has the function as derivative. -/
private lemma hasDerivAt_prim {b : ℝ → ℝ} (hb : Continuous b) (s : ℝ) :
    HasDerivAt (prim b) (b s) s :=
  (hb.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- The primitive of a smooth function is smooth. -/
private lemma contDiff_prim {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (prim b) := by
  rw [contDiff_infty_iff_deriv]
  have hd : deriv (prim b) = b := funext fun s => (hasDerivAt_prim hb.continuous s).deriv
  exact ⟨fun s => (hasDerivAt_prim hb.continuous s).differentiableAt, by rw [hd]; exact hb⟩

variable {d : ℕ}

/-- The radial test function `φ(v) = (E(r²) - E(|v - x|²)) / 2`. -/
private noncomputable def testFn (b : ℝ → ℝ) (r : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2) * (prim b (r ^ 2) - prim b (‖v - x‖ ^ 2))

/-- The derivative of the radial test function is `-b(|v - x|²) (v - x)`. -/
private lemma hasFDerivAt_testFn {b : ℝ → ℝ} (hb : Continuous b) (r : ℝ)
    (x v : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (testFn b r x) ((-b (‖v - x‖ ^ 2)) • innerSL ℝ (v - x)) v := by
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => ‖w - x‖ ^ 2)
      (2 • innerSL ℝ (v - x)) v := by
    have := (hasStrictFDerivAt_norm_sq (v - x)).hasFDerivAt.comp v
      ((hasFDerivAt_id v).sub_const x)
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have h2 := (hasDerivAt_prim hb (‖v - x‖ ^ 2)).comp_hasFDerivAt v h1
  have h3 := ((hasFDerivAt_const (prim b (r ^ 2)) v).sub h2).const_mul (1 / 2 : ℝ)
  refine HasFDerivAt.congr_fderiv (h3 : HasFDerivAt (testFn b r x) _ v) ?_
  ext w
  simp
  ring

/-- The derivative of the gradient field `w ↦ -b(|w - x|²) (w - x)` of the radial test function. -/
private lemma hasFDerivAt_gradField {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b)
    (x v : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => (-b (‖w - x‖ ^ 2)) • innerSL ℝ (w - x))
      ((-b (‖v - x‖ ^ 2)) • (innerSL ℝ (E := EuclideanSpace ℝ (Fin d))) +
        (-(deriv b (‖v - x‖ ^ 2) • (2 • innerSL ℝ (v - x)))).smulRight (innerSL ℝ (v - x))) v := by
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => ‖w - x‖ ^ 2)
      (2 • innerSL ℝ (v - x)) v := by
    have := (hasStrictFDerivAt_norm_sq (v - x)).hasFDerivAt.comp v
      ((hasFDerivAt_id v).sub_const x)
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have hb' : HasDerivAt b (deriv b (‖v - x‖ ^ 2)) (‖v - x‖ ^ 2) :=
    (hb.differentiable (by simp) _).hasDerivAt
  have hc := (hb'.comp_hasFDerivAt v h1).neg
  have hf : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => innerSL ℝ (w - x))
      (innerSL ℝ (E := EuclideanSpace ℝ (Fin d))) v := by
    have := (innerSL ℝ (E := EuclideanSpace ℝ (Fin d))).hasFDerivAt.comp v
      ((hasFDerivAt_id v).sub_const x)
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  exact hc.smul hf

/-- The Laplacian of the radial test function:
`Δφ(v) = -d b(|v - x|²) - 2 b'(|v - x|²) |v - x|²`. -/
private lemma laplacian_testFn {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (r : ℝ)
    (x v : EuclideanSpace ℝ (Fin d)) :
    Laplacian.laplacian (testFn b r x) v =
      -(d : ℝ) * b (‖v - x‖ ^ 2) - 2 * deriv b (‖v - x‖ ^ 2) * ‖v - x‖ ^ 2 := by
  have hfd : fderiv ℝ (testFn b r x) =
      fun w => (-b (‖w - x‖ ^ 2)) • innerSL ℝ (w - x) :=
    funext fun w => (hasFDerivAt_testFn hb.continuous r x w).fderiv
  have hkey : ∀ e e' : EuclideanSpace ℝ (Fin d),
      fderiv ℝ (fderiv ℝ (testFn b r x)) v e e' = -b (‖v - x‖ ^ 2) * inner ℝ e e' -
        deriv b (‖v - x‖ ^ 2) * (2 * inner ℝ (v - x) e) * inner ℝ (v - x) e' := by
    intro e e'
    rw [hfd, (hasFDerivAt_gradField hb x v).fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, neg_apply,
      smul_eq_mul, innerSL_apply_apply]
    erw [innerSL_apply_apply]
    ring
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (testFn b r x)
    (EuclideanSpace.basisFun (Fin d) ℝ)) v]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hkey,
    EuclideanSpace.basisFun_apply]
  have hsq : ‖v - x‖ ^ 2 = ∑ i, (v i - x i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have hterm : ∀ i : Fin d,
      -b (‖v - x‖ ^ 2) * inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ)) -
        deriv b (‖v - x‖ ^ 2) * (2 * inner ℝ (v - x) (EuclideanSpace.single i (1 : ℝ))) *
          inner ℝ (v - x) (EuclideanSpace.single i (1 : ℝ)) =
      -b (‖v - x‖ ^ 2) - 2 * deriv b (‖v - x‖ ^ 2) * (v i - x i) ^ 2 := by
    intro i
    simp [EuclideanSpace.inner_single_right]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hsq]
  simp

/-- Beyond `r ^ 2` the primitive of a cut-off profile is constant. -/
private lemma prim_eq_of_le {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) {s : ℝ} (hs : r ^ 2 ≤ s) :
    prim b s = prim b (r ^ 2) := by
  have hint : ∀ t u : ℝ, IntervalIntegrable b volume t u := fun t u =>
    (hb.smooth.continuous.intervalIntegrable t u)
  have h := intervalIntegral.integral_interval_sub_left (hint 0 s) (hint 0 (r ^ 2))
  have h0 : ∫ t in (r ^ 2)..s, b t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hs] at ht
      exact hb.eq_zero t ht.1
  rw [h0] at h
  unfold prim
  linarith

/-- The primitive of a cut-off profile drops by between `0` and `r ^ 2` from any `s ≥ 0` to
`r ^ 2`. -/
private lemma prim_sub_bounds {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ prim b (r ^ 2) - prim b s ∧ prim b (r ^ 2) - prim b s ≤ r ^ 2 := by
  rcases le_total s (r ^ 2) with h | h
  · have hint : ∀ t u : ℝ, IntervalIntegrable b volume t u := fun t u =>
      (hb.smooth.continuous.intervalIntegrable t u)
    have hsub := intervalIntegral.integral_interval_sub_left (hint 0 (r ^ 2)) (hint 0 s)
    have hrs : prim b (r ^ 2) - prim b s = ∫ t in s..(r ^ 2), b t := hsub
    rw [hrs]
    refine ⟨intervalIntegral.integral_nonneg h fun t _ => hb.nonneg t, ?_⟩
    calc ∫ t in s..(r ^ 2), b t ≤ ∫ _ in s..(r ^ 2), (1 : ℝ) :=
          intervalIntegral.integral_mono_on h (hint _ _) (by simp)
            fun t _ => hb.le_one t
      _ = r ^ 2 - s := by simp
      _ ≤ r ^ 2 := by linarith
  · rw [prim_eq_of_le hb h]
    have : 0 ≤ r ^ 2 := sq_nonneg r
    constructor <;> simp [this]

/-- The radial test function is smooth. -/
private lemma contDiff_testFn {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ContDiff ℝ ∞ (testFn b r x) := by
  unfold testFn
  have h1 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin d) => ‖v - x‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  exact contDiff_const.mul (contDiff_const.sub ((contDiff_prim hb).comp h1))

/-- The radial test function vanishes outside the ball of radius `r`. -/
private lemma testFn_eq_zero {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b)
    {x v : EuclideanSpace ℝ (Fin d)} (hv : r ≤ ‖v - x‖) (hr : 0 ≤ r) : testFn b r x v = 0 := by
  unfold testFn
  have : r ^ 2 ≤ ‖v - x‖ ^ 2 := by nlinarith
  rw [prim_eq_of_le hb this]
  ring

/-- The radial test function is nonnegative and at most `r ^ 2 / 2`. -/
private lemma testFn_bounds {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b)
    (x v : EuclideanSpace ℝ (Fin d)) : 0 ≤ testFn b r x v ∧ testFn b r x v ≤ r ^ 2 / 2 := by
  have h := prim_sub_bounds hb (sq_nonneg ‖v - x‖)
  unfold testFn
  constructor <;> nlinarith [h.1, h.2]

/-- The radial test function has compact support. -/
private lemma hasCompactSupport_testFn {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    (x : EuclideanSpace ℝ (Fin d)) : HasCompactSupport (testFn b r x) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x r) ?_
  intro v hv
  by_contra hnot
  rw [Metric.mem_closedBall, dist_eq_norm] at hnot
  exact hv (testFn_eq_zero hb (le_of_lt (not_le.mp hnot)) hr)

/-- The derivative of a cut-off profile is continuous. -/
private lemma continuous_deriv_cutoff {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) :
    Continuous (deriv b) :=
  hb.smooth.continuous_deriv (by exact_mod_cast le_top)

/-- The derivative of a cut-off profile vanishes beyond `r ^ 2`. -/
private lemma deriv_eq_zero_of_lt {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) {t : ℝ}
    (ht : r ^ 2 < t) : deriv b t = 0 := by
  have h : b =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs using hb.eq_zero s (le_of_lt hs)
  rw [h.deriv_eq]
  simp

/-- The derivative of a cut-off profile vanishes below `a ^ 2`. -/
private lemma deriv_eq_zero_of_gt {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) {t : ℝ}
    (ht : t < a ^ 2) : deriv b t = 0 := by
  have h : b =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs using hb.eq_one s (le_of_lt hs)
  rw [h.deriv_eq]
  simp

/-- The derivative of a cut-off profile is bounded. -/
private lemma exists_bound_deriv {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) :
    ∃ M, ∀ t, |deriv b t| ≤ M := by
  have hsupp : HasCompactSupport (deriv b) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a ^ 2) (b := r ^ 2))
      ?_
    intro t ht
    by_contra hnot
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
    rcases hnot with h | h
    · exact ht (deriv_eq_zero_of_gt hb h)
    · exact ht (deriv_eq_zero_of_lt hb h)
  obtain ⟨M, hM⟩ := (continuous_deriv_cutoff hb).bounded_above_of_compact_support hsupp
  exact ⟨M, fun t => by simpa using hM t⟩

/-- Differentiating the dilated profile under the integral sign at scale one. -/
private lemma hasDerivAt_dilation {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    {H : EuclideanSpace ℝ (Fin d) → ℝ} (hH : Continuous H) :
    HasDerivAt (fun s : ℝ => ∫ u, H u * b (s ^ 2 * ‖u‖ ^ 2))
      (∫ u, H u * (deriv b (‖u‖ ^ 2) * (2 * ‖u‖ ^ 2))) 1 := by
  obtain ⟨M, hM⟩ := exists_bound_deriv hb
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  set K : ℝ := M * (3 * (2 * r) ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  let F : ℝ → EuclideanSpace ℝ (Fin d) → ℝ := fun s u => H u * b (s ^ 2 * ‖u‖ ^ 2)
  let F' : ℝ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun s u => H u * (deriv b (s ^ 2 * ‖u‖ ^ 2) * (2 * s * ‖u‖ ^ 2))
  let bound : EuclideanSpace ℝ (Fin d) → ℝ :=
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 * r)).indicator fun u => |H u| * K
  have hbc := hb.smooth.continuous
  have hFc : ∀ s, Continuous (F s) := fun s => hH.mul (hbc.comp (by fun_prop))
  have hF'c : ∀ s, Continuous (F' s) := fun s =>
    hH.mul (((continuous_deriv_cutoff hb).comp (by fun_prop)).mul (by fun_prop))
  have hFint : Integrable (F 1) volume := by
    refine (hFc 1).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 r) ?_
    intro u hu
    by_contra hnot
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hnot
    apply hu
    have : r ^ 2 ≤ 1 ^ 2 * ‖u‖ ^ 2 := by nlinarith
    simp only [F, hb.eq_zero _ this, mul_zero]
  have hbound_int : Integrable bound volume := by
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    exact (hH.abs.mul continuous_const).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 (2 * r))
  have hbound : ∀ᵐ u ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ∀ s ∈ Metric.ball (1 : ℝ) (1 / 2), ‖F' s u‖ ≤ bound u := by
    refine Eventually.of_forall fun u s hs => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    by_cases hu : u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 * r)
    · have hu' : ‖u‖ ≤ 2 * r := mem_closedBall_zero_iff.1 hu
      have hb1 : bound u = |H u| * K := Set.indicator_of_mem hu _
      rw [hb1]
      have hs0 : 0 < s := by linarith
      have hu2 : ‖u‖ ^ 2 ≤ (2 * r) ^ 2 := by gcongr
      have h1 : 2 * s * ‖u‖ ^ 2 ≤ 3 * (2 * r) ^ 2 :=
        mul_le_mul (by linarith) hu2 (by positivity) (by norm_num)
      have hab : |2 * s * ‖u‖ ^ 2| = 2 * s * ‖u‖ ^ 2 := abs_of_nonneg (by positivity)
      calc ‖F' s u‖
          = |H u| * (|deriv b (s ^ 2 * ‖u‖ ^ 2)| * (2 * s * ‖u‖ ^ 2)) := by
            rw [Real.norm_eq_abs]
            simp only [F']
            rw [abs_mul, abs_mul, hab]
        _ ≤ |H u| * (M * (3 * (2 * r) ^ 2)) := by
            gcongr
            exact hM _
        _ = |H u| * K := by rw [hK]
    · have hu' : 2 * r < ‖u‖ := by
        rw [mem_closedBall_zero_iff, not_le] at hu
        exact hu
      have hs2 : 1 / 4 < s ^ 2 := by nlinarith
      have hu2 : 4 * r ^ 2 < ‖u‖ ^ 2 := by nlinarith
      have ht : r ^ 2 < s ^ 2 * ‖u‖ ^ 2 := by
        have hpos : 0 < ‖u‖ ^ 2 := by nlinarith [sq_nonneg r]
        nlinarith [mul_lt_mul_of_pos_right hs2 hpos]
      have hb0 : bound u = 0 := Set.indicator_of_notMem hu _
      rw [hb0]
      simp only [F', deriv_eq_zero_of_lt hb ht]
      simp
  have hdiff : ∀ᵐ u ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ∀ s ∈ Metric.ball (1 : ℝ) (1 / 2), HasDerivAt (fun t => F t u) (F' s u) s := by
    refine Eventually.of_forall fun u s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 * ‖u‖ ^ 2) (2 * s * ‖u‖ ^ 2) s := by
      simpa using (hasDerivAt_pow 2 s).mul_const (‖u‖ ^ 2)
    have h2 : HasDerivAt b (deriv b (s ^ 2 * ‖u‖ ^ 2)) (s ^ 2 * ‖u‖ ^ 2) :=
      (hb.smooth.differentiable (by simp) _).hasDerivAt
    exact (h2.comp s h1).const_mul (H u)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F)
    (F' := F') (x₀ := 1) (bound := bound) (s := Metric.ball (1 : ℝ) (1 / 2))
    (Metric.ball_mem_nhds 1 (by norm_num))
    (Eventually.of_forall fun s => (hFc s).aestronglyMeasurable)
    hFint (hF'c 1).aestronglyMeasurable hbound hbound_int hdiff
  simpa [F, F'] using key.2

/-- A function differentiable at `1` whose value at `1` dominates its values on `[1, ∞)` has
nonpositive derivative there. -/
private lemma deriv_nonpos_of_le_right {L : ℝ → ℝ} {L' : ℝ} (h : HasDerivAt L L' 1)
    (hle : ∀ s, 1 ≤ s → L s ≤ L 1) : L' ≤ 0 := by
  have hlim := h.tendsto_slope_zero_right
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have := hle (1 + t) (by linarith)
  rw [smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht'.le) (by linarith)

/-- Substituting `w = s u` in the integral of a function times the dilated profile. -/
private lemma integral_dilate (b : ℝ → ℝ) (Φ : EuclideanSpace ℝ (Fin d) → ℝ) {s : ℝ}
    (hs : 0 < s) :
    ∫ u, Φ u * b (s ^ 2 * ‖u‖ ^ 2) =
      (s ^ d)⁻¹ * ∫ w, Φ (s⁻¹ • w) * b (‖w‖ ^ 2) := by
  have h := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (fun w => Φ (s⁻¹ • w) * b (‖w‖ ^ 2)) s
  rw [finrank_euclideanSpace_fin, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hs.le _)),
    smul_eq_mul] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [inv_smul_smul₀ hs.ne', norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow]

/-- A continuous function vanishing outside a ball is integrable. -/
private lemma integrable_of_zero_outside {r : ℝ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) (h : ∀ u, r < ‖u‖ → f u = 0) : Integrable f volume := by
  refine hf.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 r) ?_
  intro u hu
  by_contra hnot
  rw [mem_closedBall_zero_iff, not_le] at hnot
  exact hu (h u hnot)

/-- A continuous function times the profile of the squared norm is integrable. -/
private lemma integrable_mul_profile {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    {G : EuclideanSpace ℝ (Fin d) → ℝ} (hG : Continuous G) :
    Integrable (fun u => G u * b (‖u‖ ^ 2)) volume := by
  refine integrable_of_zero_outside (r := r) (hG.mul (hb.smooth.continuous.comp (by fun_prop)))
    fun u hu => ?_
  have : r ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith
  rw [hb.eq_zero _ this, mul_zero]

/-- A continuous function times the derivative term of the profile is integrable. -/
private lemma integrable_mul_deriv {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    {G : EuclideanSpace ℝ (Fin d) → ℝ} (hG : Continuous G) :
    Integrable (fun u => G u * (deriv b (‖u‖ ^ 2) * (2 * ‖u‖ ^ 2))) volume := by
  refine integrable_of_zero_outside (r := r)
    (hG.mul (((continuous_deriv_cutoff hb).comp (by fun_prop)).mul (by fun_prop))) fun u hu => ?_
  have : r ^ 2 < ‖u‖ ^ 2 := by nlinarith
  rw [deriv_eq_zero_of_lt hb this, zero_mul, mul_zero]

/-- The Laplacian of the radial test function integrates to zero. -/
private lemma integral_laplacian_profile {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b)
    (hr : 0 ≤ r) :
    ∫ u : EuclideanSpace ℝ (Fin d), (-(d : ℝ) * b (‖u‖ ^ 2) - 2 * deriv b (‖u‖ ^ 2) * ‖u‖ ^ 2) =
      0 := by
  have hd := hasDerivAt_dilation hb hr (H := fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ))
    continuous_const
  have hc : HasDerivAt (fun s : ℝ => ∫ u : EuclideanSpace ℝ (Fin d), 1 * b (s ^ 2 * ‖u‖ ^ 2))
      (-(d : ℝ) * ∫ w : EuclideanSpace ℝ (Fin d), 1 * b (‖w‖ ^ 2)) 1 := by
    have h0 : HasDerivAt (fun s : ℝ => (s ^ d)⁻¹ * ∫ w : EuclideanSpace ℝ (Fin d), 1 * b (‖w‖ ^ 2))
        (-(d : ℝ) * ∫ w : EuclideanSpace ℝ (Fin d), 1 * b (‖w‖ ^ 2)) 1 := by
      have := ((hasDerivAt_pow d (1 : ℝ)).inv (by simp)).mul_const
        (∫ w : EuclideanSpace ℝ (Fin d), 1 * b (‖w‖ ^ 2))
      simpa using this
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    simpa using integral_dilate b (fun _ => (1 : ℝ)) hs
  have huniq := hd.unique hc
  have h1 := integrable_mul_profile (d := d) hb hr (G := fun _ => -(d : ℝ)) continuous_const
  have h2 := integrable_mul_deriv (d := d) hb hr (G := fun _ => (1 : ℝ)) continuous_const
  have h3 : ∫ u : EuclideanSpace ℝ (Fin d), (-(d : ℝ) * b (‖u‖ ^ 2)) =
      -(d : ℝ) * ∫ w : EuclideanSpace ℝ (Fin d), 1 * b (‖w‖ ^ 2) := by
    rw [integral_const_mul]
    simp only [one_mul]
  have h4 : ∫ u : EuclideanSpace ℝ (Fin d), 2 * deriv b (‖u‖ ^ 2) * ‖u‖ ^ 2 =
      ∫ u : EuclideanSpace ℝ (Fin d), 1 * (deriv b (‖u‖ ^ 2) * (2 * ‖u‖ ^ 2)) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    ring
  have h5 : Integrable (fun u : EuclideanSpace ℝ (Fin d) => 2 * deriv b (‖u‖ ^ 2) * ‖u‖ ^ 2)
      volume := by
    refine h2.congr (Eventually.of_forall fun u => ?_)
    simp only
    ring
  rw [integral_sub h1 h5, h3, h4, huniq]
  ring

/-- The dilation inequality: for a continuous `H` with `H(t u) ≤ t H(u)` for `t ∈ [0, 1]`,
`∫ H(u) ((d + 1) b(|u|²) + 2 b'(|u|²) |u|²) du ≤ 0`. -/
private lemma dilation_ineq {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    {H : EuclideanSpace ℝ (Fin d) → ℝ} (hH : Continuous H)
    (hconv : ∀ (t : ℝ) (u : EuclideanSpace ℝ (Fin d)), 0 ≤ t → t ≤ 1 → H (t • u) ≤ t * H u) :
    ∫ u, H u * (((d : ℝ) + 1) * b (‖u‖ ^ 2) + 2 * deriv b (‖u‖ ^ 2) * ‖u‖ ^ 2) ≤ 0 := by
  set c : ℝ := ∫ u, H u * b (‖u‖ ^ 2) with hc
  have hK := hasDerivAt_dilation hb hr hH
  have hle : ∀ s : ℝ, 1 ≤ s →
      (∫ u, H u * b (s ^ 2 * ‖u‖ ^ 2)) ≤ (s ^ (d + 1))⁻¹ * c := by
    intro s hs
    have hs0 : 0 < s := by linarith
    rw [integral_dilate b H hs0]
    have hmono : ∫ w, H (s⁻¹ • w) * b (‖w‖ ^ 2) ≤ ∫ w, (s⁻¹ * H w) * b (‖w‖ ^ 2) := by
      refine integral_mono (integrable_mul_profile hb hr (by fun_prop))
        (integrable_mul_profile hb hr (by fun_prop)) fun w => ?_
      have hs1 : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
      exact mul_le_mul_of_nonneg_right (hconv s⁻¹ w (inv_nonneg.2 hs0.le) hs1) (hb.nonneg _)
    have hpull : ∫ w, (s⁻¹ * H w) * b (‖w‖ ^ 2) = s⁻¹ * c := by
      rw [hc, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      ring
    calc (s ^ d)⁻¹ * ∫ w, H (s⁻¹ • w) * b (‖w‖ ^ 2)
        ≤ (s ^ d)⁻¹ * (s⁻¹ * c) :=
          mul_le_mul_of_nonneg_left (hmono.trans hpull.le) (inv_nonneg.2 (pow_nonneg hs0.le _))
      _ = (s ^ (d + 1))⁻¹ * c := by
          rw [pow_succ, mul_inv]
          ring
  have hinv : HasDerivAt (fun s : ℝ => (s ^ (d + 1))⁻¹ * c) (-((d : ℝ) + 1) * c) 1 := by
    have := ((hasDerivAt_pow (d + 1) (1 : ℝ)).inv (by simp)).mul_const c
    simpa using this
  have hL := hK.sub hinv
  have hnonpos := deriv_nonpos_of_le_right hL (fun s hs => by
    have := hle s hs
    simp only [Pi.sub_apply, one_pow, inv_one, one_mul]
    linarith)
  have hint1 := integrable_mul_profile hb hr hH
  have hint2 := integrable_mul_deriv hb hr hH
  have hsplit : ∫ u, H u * (((d : ℝ) + 1) * b (‖u‖ ^ 2) + 2 * deriv b (‖u‖ ^ 2) * ‖u‖ ^ 2) =
      ((d : ℝ) + 1) * c + ∫ u, H u * (deriv b (‖u‖ ^ 2) * (2 * ‖u‖ ^ 2)) := by
    rw [hc, ← integral_const_mul, ← integral_add (hint1.const_mul _) hint2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    ring
  rw [hsplit]
  linarith

/-- The profile `-d b(|u|²) - 2 b'(|u|²) |u|²` of the Laplacian of the radial test function. -/
private noncomputable def lapProfile (b : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(d : ℝ) * b (‖u‖ ^ 2) - 2 * deriv b (‖u‖ ^ 2) * ‖u‖ ^ 2

/-- The Laplacian profile is continuous. -/
private lemma continuous_lapProfile {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) :
    Continuous (lapProfile (d := d) b) := by
  unfold lapProfile
  have h1 := hb.smooth.continuous
  have h2 := continuous_deriv_cutoff hb
  fun_prop

/-- The Laplacian profile vanishes outside the ball of radius `r`. -/
private lemma lapProfile_eq_zero {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    {u : EuclideanSpace ℝ (Fin d)} (hu : r < ‖u‖) : lapProfile b u = 0 := by
  have h : r ^ 2 < ‖u‖ ^ 2 := by nlinarith
  unfold lapProfile
  rw [hb.eq_zero _ h.le, deriv_eq_zero_of_lt hb h]
  ring

/-- The Laplacian profile is even. -/
private lemma lapProfile_neg (b : ℝ → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    lapProfile b (-u) = lapProfile b u := by
  simp [lapProfile]

/-- A continuous function times the Laplacian profile is integrable. -/
private lemma integrable_mul_lapProfile {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    {G : EuclideanSpace ℝ (Fin d) → ℝ} (hG : Continuous G) :
    Integrable (fun u => G u * lapProfile b u) volume := by
  refine integrable_of_zero_outside (r := r) (hG.mul (continuous_lapProfile hb)) fun u hu => ?_
  rw [lapProfile_eq_zero hb hr hu, mul_zero]

/-- A linear function times the Laplacian profile integrates to zero, by symmetry. -/
private lemma integral_inner_mul_lapProfile (b : ℝ → ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ u, inner ℝ ξ u * lapProfile b u = 0 := by
  have h := integral_neg_eq_self (fun u : EuclideanSpace ℝ (Fin d) => inner ℝ ξ u * lapProfile b u)
    volume
  simp only [inner_neg_right, lapProfile_neg, neg_mul, integral_neg] at h
  linarith


/-- A convex function is convex along segments. -/
private lemma norm_segment_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : ConvexOn ℝ Set.univ Ψ)
    (x y : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ψ ((1 - t) • x + t • y) ≤ (1 - t) * Ψ x + t * Ψ y := by
  have h := hΨ.2 (Set.mem_univ x) (Set.mem_univ y) (sub_nonneg.mpr ht1) ht0 (by ring)
  simpa only [smul_eq_mul] using h

/-- A convex function recentred at a subgradient, `H(u) = Ψ(x + u) - Ψ(x) - ξ · u`, is convex along
rays through the origin: `H(t u) ≤ t H(u)` for `t ∈ [0, 1]`. -/
private lemma recentred_ray_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : ConvexOn ℝ Set.univ Ψ)
    (x ξ u : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ψ (x + t • u) - Ψ x - inner ℝ ξ (t • u) ≤ t * (Ψ (x + u) - Ψ x - inner ℝ ξ u) := by
  have h := norm_segment_le hΨ x (x + u) ht0 ht1
  have hx : (1 - t) • x + t • (x + u) = x + t • u := by module
  rw [hx] at h
  rw [real_inner_smul_right]
  nlinarith

/-- The weak mass bound: for a continuous convex function `Ψ` with distributional Laplacian `m`, a
vector `ξ` and a smooth cut-off profile `b`,
`∫ (Ψ(x + u) - Ψ(x) - ξ · u) b(|u|²) du ≤ ∫ φ dm`. -/
private lemma weak_mass_bound {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨc : Continuous Ψ)
    (hΨ : ConvexOn ℝ Set.univ Ψ)
    {x ξ : EuclideanSpace ℝ (Fin d)} {m : Measure (EuclideanSpace ℝ (Fin d))}
    (hm : CERW.IsDistribLaplacian Ψ m) {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r) :
    ∫ u, (Ψ (x + u) - Ψ x - inner ℝ ξ u) * b (‖u‖ ^ 2) ≤ ∫ v, testFn b r x v ∂m := by
  set H : EuclideanSpace ℝ (Fin d) → ℝ := fun u => Ψ (x + u) - Ψ x - inner ℝ ξ u with hH
  have hHc : Continuous H := by
    rw [hH]
    fun_prop
  have hconv : ∀ (t : ℝ) (u : EuclideanSpace ℝ (Fin d)), 0 ≤ t → t ≤ 1 →
      H (t • u) ≤ t * H u := fun t u ht0 ht1 => recentred_ray_le hΨ x ξ u ht0 ht1
  have hdil := dilation_ineq hb hr hHc hconv
  rw [hm (testFn b r x) (contDiff_testFn hb.smooth r x) (hasCompactSupport_testFn hb hr x)]
  have hshift : ∫ v, Ψ v * Laplacian.laplacian (testFn b r x) v =
      ∫ u, Ψ (x + u) * lapProfile b u := by
    rw [← integral_add_left_eq_self (fun v => Ψ v * Laplacian.laplacian (testFn b r x) v) x]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [laplacian_testFn hb.smooth r x (x + u), add_sub_cancel_left, lapProfile]
  have hsplit : ∫ u : EuclideanSpace ℝ (Fin d), Ψ (x + u) * lapProfile b u =
      (∫ u : EuclideanSpace ℝ (Fin d), H u * lapProfile b u) +
        Ψ x * (∫ u : EuclideanSpace ℝ (Fin d), lapProfile b u) +
        (∫ u : EuclideanSpace ℝ (Fin d), inner ℝ ξ u * lapProfile b u) := by
    have hi1 := integrable_mul_lapProfile hb hr hHc
    have hi2 := integrable_mul_lapProfile (d := d) hb hr (G := fun _ => Ψ x) continuous_const
    have hi3 := integrable_mul_lapProfile hb hr
      (G := fun u : EuclideanSpace ℝ (Fin d) => inner ℝ ξ u) (by fun_prop)
    calc ∫ u : EuclideanSpace ℝ (Fin d), Ψ (x + u) * lapProfile b u
        = ∫ u : EuclideanSpace ℝ (Fin d),
            ((H u * lapProfile b u + Ψ x * lapProfile b u) + inner ℝ ξ u * lapProfile b u) := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          simp only [hH]
          ring
      _ = (∫ u : EuclideanSpace ℝ (Fin d), (H u * lapProfile b u + Ψ x * lapProfile b u)) +
            ∫ u : EuclideanSpace ℝ (Fin d), inner ℝ ξ u * lapProfile b u :=
          integral_add (hi1.add hi2) hi3
      _ = _ := by rw [integral_add hi1 hi2, integral_const_mul]
  have hzero : ∫ u : EuclideanSpace ℝ (Fin d), lapProfile b u = 0 :=
    integral_laplacian_profile hb hr
  rw [hshift, hsplit, hzero, integral_inner_mul_lapProfile]
  have hint1 := integrable_mul_profile hb hr hHc
  have hlap : ∫ u : EuclideanSpace ℝ (Fin d), H u * lapProfile b u =
      (∫ u : EuclideanSpace ℝ (Fin d), H u * b (‖u‖ ^ 2)) -
        ∫ u : EuclideanSpace ℝ (Fin d),
          H u * (((d : ℝ) + 1) * b (‖u‖ ^ 2) + 2 * deriv b (‖u‖ ^ 2) * ‖u‖ ^ 2) := by
    have hint2 : Integrable (fun u => H u * (((d : ℝ) + 1) * b (‖u‖ ^ 2) +
        2 * deriv b (‖u‖ ^ 2) * ‖u‖ ^ 2)) volume := by
      have h3 := integrable_mul_deriv hb hr hHc
      have h4 := hint1.const_mul ((d : ℝ) + 1)
      refine (h4.add h3).congr (Eventually.of_forall fun u => ?_)
      simp only [Pi.add_apply]
      ring
    calc ∫ u : EuclideanSpace ℝ (Fin d), H u * lapProfile b u
        = ∫ u : EuclideanSpace ℝ (Fin d), (H u * b (‖u‖ ^ 2) -
            H u * (((d : ℝ) + 1) * b (‖u‖ ^ 2) + 2 * deriv b (‖u‖ ^ 2) * ‖u‖ ^ 2)) := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          simp only [lapProfile]
          ring
      _ = _ := integral_sub hint1 hint2
  rw [hlap]
  linarith

/-- The excess `Ψ(v) - Ψ(x) - ξ · (v - x)` of `Ψ` over its tangent plane at `x` with slope
`ξ`. -/
private noncomputable def excess (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x ξ v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Ψ v - Ψ x - inner ℝ ξ (v - x)

/-- The excess over a tangent plane of a subgradient is nonnegative. -/
private lemma excess_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {x ξ : EuclideanSpace ℝ (Fin d)}
    (hξ : CERW.IsSubgradient Ψ x ξ) (v : EuclideanSpace ℝ (Fin d)) : 0 ≤ excess Ψ x ξ v := by
  have h := hξ v
  unfold excess
  linarith

/-- The excess is continuous when `Ψ` is. -/
private lemma continuous_excess {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : Continuous Ψ)
    (x ξ : EuclideanSpace ℝ (Fin d)) : Continuous (excess Ψ x ξ) := by
  unfold excess
  fun_prop

/-- The Euclidean norm is at most the sum of the absolute values of the coordinates. -/
private lemma norm_le_sum_abs (w : EuclideanSpace ℝ (Fin d)) : ‖w‖ ≤ ∑ i, |w i| := by
  have hw : ∑ i, w i • CERW.coordVec i = w := by
    simpa [CERW.coordVec] using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w
  calc ‖w‖ = ‖∑ i, w i • CERW.coordVec i‖ := by rw [hw]
    _ ≤ ∑ i, ‖w i • CERW.coordVec i‖ := norm_sum_le _ _
    _ = ∑ i, |w i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [CERW.coordVec, norm_smul, PiLp.norm_single]

/-- If the gradient at `v` is a subgradient there, it differs from a subgradient at `x` by at most
the sum of the excesses at the `2d` neighbours of the point. -/
private lemma norm_gradient_sub_le_sum {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {x ξ v : EuclideanSpace ℝ (Fin d)} (hξ : CERW.IsSubgradient Ψ x ξ)
    (hsub : CERW.IsSubgradient Ψ v (gradient Ψ v)) :
    ‖gradient Ψ v - ξ‖ ≤ ∑ i : Fin d, (excess Ψ x ξ (v + CERW.coordVec i) +
      excess Ψ x ξ (v - CERW.coordVec i)) := by
  have hexc := excess_nonneg hξ v
  have key : ∀ (i : Fin d) (σ : ℝ),
      σ * (gradient Ψ v - ξ) i ≤ excess Ψ x ξ (v + σ • CERW.coordVec i) := by
    intro i σ
    have h1 := hsub (v + σ • CERW.coordVec i)
    have hcoord : inner ℝ (gradient Ψ v - ξ) (CERW.coordVec i) = (gradient Ψ v - ξ) i := by
      simp [CERW.coordVec, EuclideanSpace.inner_single_right]
    have h2 : inner ℝ (gradient Ψ v) (σ • CERW.coordVec i) - inner ℝ ξ (σ • CERW.coordVec i) =
        σ * (gradient Ψ v - ξ) i := by
      rw [← inner_sub_left, real_inner_smul_right, hcoord]
    unfold excess at hexc ⊢
    have h3 : inner ℝ ξ (v + σ • CERW.coordVec i - x) =
        inner ℝ ξ (v - x) + inner ℝ ξ (σ • CERW.coordVec i) := by
      rw [← inner_add_right]
      congr 1
      abel
    have h4 : v + σ • CERW.coordVec i - v = σ • CERW.coordVec i := by abel
    rw [h4] at h1
    rw [h3]
    linarith
  refine (norm_le_sum_abs _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hp := key i 1
  have hn := key i (-1)
  have hp0 := excess_nonneg hξ (v + CERW.coordVec i)
  have hn0 := excess_nonneg hξ (v - CERW.coordVec i)
  simp only [one_smul, neg_smul, one_mul, neg_one_mul, ← sub_eq_add_neg] at hp hn
  rw [abs_le]
  constructor <;> linarith

/-- A continuous function is integrable on a bounded set. -/
private lemma integrableOn_of_isBounded {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : Bornology.IsBounded S) :
    IntegrableOn f S volume :=
  (hf.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set subset_closure

/-- For a nonnegative continuous `f` and bounded measurable sets with `S + e ⊆ T`,
`∫_S f(v + e) dv ≤ ∫_T f`. -/
private lemma setIntegral_add_le {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    (hf0 : ∀ v, 0 ≤ f v) {S T : Set (EuclideanSpace ℝ (Fin d))} (e : EuclideanSpace ℝ (Fin d))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hSb : Bornology.IsBounded S)
    (hTb : Bornology.IsBounded T) (hsub : ∀ v ∈ S, v + e ∈ T) :
    ∫ v in S, f (v + e) ≤ ∫ v in T, f v := by
  rw [← integral_indicator hS, ← integral_indicator hT]
  have hTint : Integrable (T.indicator f) volume :=
    (integrable_indicator_iff hT).2 (integrableOn_of_isBounded hf hTb)
  have hSint : Integrable (S.indicator fun v => f (v + e)) volume :=
    (integrable_indicator_iff hS).2
      (integrableOn_of_isBounded (hf.comp (continuous_id.add_const e)) hSb)
  calc ∫ v, S.indicator (fun v => f (v + e)) v ≤ ∫ v, T.indicator f (v + e) := by
        refine integral_mono hSint (hTint.comp_add_right e) fun v => ?_
        by_cases hv : v ∈ S
        · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hsub v hv)]
        · rw [Set.indicator_of_notMem hv]
          exact Set.indicator_nonneg (fun w _ => hf0 w) _
    _ = ∫ v, T.indicator f v := integral_add_right_eq_self (T.indicator f) e

/-- The cell `C_x` is bounded. -/
private lemma isBounded_cell (x : Site d) : Bornology.IsBounded (CERW.cell x) := by
  refine (Metric.isBounded_closedBall (x := CERW.toSpace x) (r := Real.sqrt d / 2)).subset ?_
  intro v hv
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv

/-- The integral of the gradient's distance to a subgradient over a cell is at most `2d` times
the integral of the excess over the ball of radius `2 √d` about the site, for a continuous function
whose gradient is a subgradient wherever it is differentiable, and which is differentiable almost
everywhere. -/
private lemma cell_integral_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨc : Continuous Ψ)
    (hgrad : ∀ v, DifferentiableAt ℝ Ψ v → CERW.IsSubgradient Ψ v (gradient Ψ v))
    (hae : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ Ψ v)
    (hd : 1 ≤ d) {ξ : EuclideanSpace ℝ (Fin d)} (x : Site d)
    (hξ : CERW.IsSubgradient Ψ (CERW.toSpace x) ξ) :
    ∫ v in CERW.cell x, ‖gradient Ψ v - ξ‖ ≤
      2 * d * ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d),
        excess Ψ (CERW.toSpace x) ξ v := by
  set f : EuclideanSpace ℝ (Fin d) → ℝ := excess Ψ (CERW.toSpace x) ξ with hf
  have hfc : Continuous f := continuous_excess hΨc _ _
  have hf0 : ∀ v, 0 ≤ f v := excess_nonneg hξ
  have hS := CERW.Support.Occupation.measurableSet_cell x
  have hSb := isBounded_cell x
  have hTb : Bornology.IsBounded
      (Metric.ball (CERW.toSpace x) (2 * Real.sqrt d)) := Metric.isBounded_ball
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hd
  have hnear : ∀ (e : EuclideanSpace ℝ (Fin d)), ‖e‖ = 1 → ∀ v ∈ CERW.cell x,
      v + e ∈ Metric.ball (CERW.toSpace x) (2 * Real.sqrt d) := by
    intro e he v hv
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hv
    have h2 : ‖v + e - CERW.toSpace x‖ ≤ ‖v - CERW.toSpace x‖ + ‖e‖ := by
      calc ‖v + e - CERW.toSpace x‖ = ‖(v - CERW.toSpace x) + e‖ := by
            congr 1
            abel
        _ ≤ ‖v - CERW.toSpace x‖ + ‖e‖ := norm_add_le _ _
    rw [he] at h2
    linarith
  have hone : ∀ i : Fin d, ‖CERW.coordVec (d := d) i‖ = 1 := by
    intro i
    simp [CERW.coordVec, PiLp.norm_single]
  have hplus : ∀ i : Fin d, ∫ v in CERW.cell x, f (v + CERW.coordVec i) ≤
      ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d), f v := fun i =>
    setIntegral_add_le hfc hf0 _ hS Metric.isOpen_ball.measurableSet hSb hTb
      (hnear _ (hone i))
  have hminus : ∀ i : Fin d, ∫ v in CERW.cell x, f (v - CERW.coordVec i) ≤
      ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d), f v := by
    intro i
    have := setIntegral_add_le hfc hf0 (-CERW.coordVec i) hS Metric.isOpen_ball.measurableSet hSb
      hTb (hnear _ (by rw [norm_neg]; exact hone i))
    simpa [sub_eq_add_neg] using this
  have hint : ∀ e : EuclideanSpace ℝ (Fin d), IntegrableOn (fun v => f (v + e))
      (CERW.cell x) volume := fun e =>
    integrableOn_of_isBounded (hfc.comp (continuous_id.add_const e)) hSb
  have hint' : ∀ e : EuclideanSpace ℝ (Fin d), IntegrableOn (fun v => f (v - e))
      (CERW.cell x) volume := fun e =>
    integrableOn_of_isBounded (hfc.comp (continuous_id.sub continuous_const)) hSb
  have hae : ∀ᵐ v ∂(volume.restrict (CERW.cell x)), ‖gradient Ψ v - ξ‖ ≤
      ∑ i : Fin d, (f (v + CERW.coordVec i) + f (v - CERW.coordVec i)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hae] with v hv
    exact norm_gradient_sub_le_sum hξ (hgrad v hv)
  have hsumint : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      IntegrableOn (fun v => f (v + CERW.coordVec i) + f (v - CERW.coordVec i))
        (CERW.cell x) volume := fun i _ => (hint _).add (hint' _)
  calc ∫ v in CERW.cell x, ‖gradient Ψ v - ξ‖
      ≤ ∫ v in CERW.cell x, ∑ i : Fin d, (f (v + CERW.coordVec i) + f (v - CERW.coordVec i)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
          (integrable_finsetSum _ hsumint) hae
    _ = ∑ i : Fin d, ((∫ v in CERW.cell x, f (v + CERW.coordVec i)) +
          ∫ v in CERW.cell x, f (v - CERW.coordVec i)) := by
        refine (integral_finsetSum Finset.univ hsumint).trans ?_
        exact Finset.sum_congr rfl fun i _ => integral_add (hint _) (hint' _)
    _ ≤ ∑ _i : Fin d, (2 * ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d), f v) := by
        refine Finset.sum_le_sum fun i _ => ?_
        linarith [hplus i, hminus i]
    _ = 2 * d * ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d), f v := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The radial test function integrates against a locally finite measure to at most
`r ^ 2 / 2` times the mass of any ball containing its support. -/
private lemma integral_testFn_le {a r ρ : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r)
    (hrρ : r < ρ) (x : EuclideanSpace ℝ (Fin d)) (m : Measure (EuclideanSpace ℝ (Fin d)))
    [IsLocallyFiniteMeasure m] :
    ∫ v, testFn b r x v ∂m ≤ r ^ 2 / 2 * (m (Metric.ball x ρ)).toReal := by
  have hzero : ∀ v, v ∉ Metric.ball x ρ → testFn b r x v = 0 := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hv
    exact testFn_eq_zero hb (by linarith) hr
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hfin : m (Metric.ball x ρ) < ⊤ := measure_ball_lt_top
  have h := norm_setIntegral_le_of_norm_le_const (μ := m) (s := Metric.ball x ρ)
    (f := testFn b r x) (C := r ^ 2 / 2) hfin fun v _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (testFn_bounds hb x v).1]
      exact (testFn_bounds hb x v).2
  calc ∫ v in Metric.ball x ρ, testFn b r x v ∂m
      ≤ ‖∫ v in Metric.ball x ρ, testFn b r x v ∂m‖ := le_abs_self _
    _ ≤ r ^ 2 / 2 * m.real (Metric.ball x ρ) := h
    _ = r ^ 2 / 2 * (m (Metric.ball x ρ)).toReal := rfl

/-- The integral of the excess of a continuous convex function over a ball is bounded by the mass
of its distributional Laplacian on a larger ball. -/
private lemma ball_excess_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨc : Continuous Ψ)
    (hΨ : ConvexOn ℝ Set.univ Ψ)
    {x ξ : EuclideanSpace ℝ (Fin d)} (hξ : CERW.IsSubgradient Ψ x ξ)
    {m : Measure (EuclideanSpace ℝ (Fin d))} [IsLocallyFiniteMeasure m]
    (hm : CERW.IsDistribLaplacian Ψ m) {a r ρ : ℝ} (ha : 0 ≤ a) (har : a < r) (hrρ : r < ρ) :
    ∫ v in Metric.ball x a, excess Ψ x ξ v ≤ r ^ 2 / 2 * (m (Metric.ball x ρ)).toReal := by
  obtain ⟨b, hb⟩ := exists_cutoff ha har
  have hr : 0 ≤ r := ha.trans har.le
  have hfc : Continuous (excess Ψ x ξ) := continuous_excess hΨc x ξ
  have hf0 := excess_nonneg hξ
  have hshift : ∀ u : EuclideanSpace ℝ (Fin d),
      excess Ψ x ξ (x + u) = Ψ (x + u) - Ψ x - inner ℝ ξ u := by
    intro u
    simp [excess]
  have hH : Continuous (fun u : EuclideanSpace ℝ (Fin d) => excess Ψ x ξ (x + u)) :=
    hfc.comp (continuous_const.add continuous_id)
  have h1 : ∫ v in Metric.ball x a, excess Ψ x ξ v ≤
      ∫ u, excess Ψ x ξ (x + u) * b (‖u‖ ^ 2) := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet]
    rw [← integral_add_left_eq_self ((Metric.ball x a).indicator (excess Ψ x ξ)) x]
    have hint : Integrable ((Metric.ball x a).indicator (excess Ψ x ξ)) volume :=
      (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2
        (integrableOn_of_isBounded hfc Metric.isBounded_ball)
    refine integral_mono (hint.comp_add_left x) (integrable_mul_profile hb hr hH) fun u => ?_
    by_cases hu : x + u ∈ Metric.ball x a
    · rw [Set.indicator_of_mem hu]
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] at hu
      have : ‖u‖ ^ 2 ≤ a ^ 2 := by nlinarith [norm_nonneg u]
      rw [hb.eq_one _ this, mul_one]
    · rw [Set.indicator_of_notMem hu]
      exact mul_nonneg (hf0 _) (hb.nonneg _)
  have h2 := weak_mass_bound (x := x) (ξ := ξ) hΨc hΨ hm hb hr
  have h3 := integral_testFn_le hb hr hrρ x m
  calc ∫ v in Metric.ball x a, excess Ψ x ξ v ≤ ∫ u, excess Ψ x ξ (x + u) * b (‖u‖ ^ 2) := h1
    _ = ∫ u, (Ψ (x + u) - Ψ x - inner ℝ ξ u) * b (‖u‖ ^ 2) := by
        simp only [hshift]
    _ ≤ ∫ v, testFn b r x v ∂m := h2
    _ ≤ _ := h3


/-- **Lemma `lem:cell` for the gauge of a convex body.** There is `C(d) < ∞` such that, for every
compact convex `K` with the origin in its interior, every choice of subgradients `ξ(x) ∈ ∂ψ_K(x)`
at the nonzero sites with `ξ(0) = 0`, every locally finite measure `m` that is the distributional
Laplacian of `ψ_K` and every site `x`,
`∫_{C_x} |∇ψ_K - ξ(x)| ≤ C m(B(x, 6 √d))`. Neither evenness of `K` nor a norm is required. -/
theorem gauge_cell_gradient {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {K : Set (EuclideanSpace ℝ (Fin d))}, IsCompact K → Convex ℝ K →
      (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient (gauge K) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m →
        CERW.IsDistribLaplacian (gauge K) m →
      ∀ x : Site d,
        ENNReal.ofReal (∫ v in CERW.cell x, ‖gradient (gauge K) v - ξ x‖)
          ≤ ENNReal.ofReal C * m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d)) := by
  refine ⟨16 * (d : ℝ) ^ 2, by positivity, ?_⟩
  intro K hK hc h0 ξ hξ hξ0 m hmloc hm x
  haveI := hmloc
  have hd1 : 1 ≤ d := by omega
  have hΨc : Continuous (gauge K) := (lipschitzWith_gauge hK hc h0).continuous
  have hsub : CERW.IsSubgradient (gauge K) (CERW.toSpace x) (ξ x) :=
    isSubgradient_selection hξ hξ0 x
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hd1
  have hcell := cell_integral_le hΨc (fun v hv => gradient_isSubgradient_gauge hc h0 hv)
    (ae_differentiableAt_gauge hK hc h0) hd1 x hsub
  have hball := ball_excess_le hΨc (convexOn_gauge hc h0) hsub hm (a := 2 * Real.sqrt d)
    (r := 4 * Real.sqrt d) (ρ := 6 * Real.sqrt d) (by linarith) (by linarith) (by linarith)
  have hfin : m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d)) < ⊤ := measure_ball_lt_top
  have hsq : (4 * Real.sqrt d) ^ 2 = 16 * (d : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    norm_num
  have hbound : ∫ v in CERW.cell x, ‖gradient (gauge K) v - ξ x‖ ≤
      16 * (d : ℝ) ^ 2 * (m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))).toReal := by
    rw [hsq] at hball
    calc ∫ v in CERW.cell x, ‖gradient (gauge K) v - ξ x‖
        ≤ 2 * d * ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d),
            excess (gauge K) (CERW.toSpace x) (ξ x) v := hcell
      _ ≤ 2 * d * (16 * (d : ℝ) / 2 *
            (m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))).toReal) :=
          mul_le_mul_of_nonneg_left hball (by positivity)
      _ = 16 * (d : ℝ) ^ 2 * (m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))).toReal := by
          ring
  calc ENNReal.ofReal (∫ v in CERW.cell x, ‖gradient (gauge K) v - ξ x‖)
      ≤ ENNReal.ofReal (16 * (d : ℝ) ^ 2 *
          (m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))).toReal) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (16 * (d : ℝ) ^ 2) *
          m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin.ne]


/-! ### The distributional Laplacian of the gauge does not vanish -/

section Nonvanishing

open CERW.Generic.Newton

variable {K : Set (EuclideanSpace ℝ (Fin d))}

/-- Polar coordinates for an integrand `h(|v|) ψ_K(v)` with `h` bounded with bounded support: the
gauge is positively homogeneous of degree one, so the integral is the product of the sphere integral
of `ψ_K` and the radial integral `∫_0^∞ r^d h(r) dr`. -/
private lemma integral_polar_gauge (hd : 1 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (h : ℝ → ℝ) (hm : Measurable h)
    {M T : ℝ} (hT0 : 0 ≤ T) (hb : ∀ r, |h r| ≤ M) (hs : ∀ r, T < r → h r = 0) :
    ∫ v : EuclideanSpace ℝ (Fin d), h ‖v‖ * gauge K v =
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, gauge K (θ : EuclideanSpace ℝ (Fin d))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) *
        ∫ r in Set.Ioi (0 : ℝ), r ^ d * h r := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  have hΛ : 0 ≤ normMax (gauge K) := normMax_gauge_nonneg K
  have hgc : Continuous (gauge K) := (lipschitzWith_gauge hK hc h0).continuous
  have hint : Integrable (fun v : EuclideanSpace ℝ (Fin d) => h ‖v‖ * gauge K v) := by
    have hbd : ∀ v : EuclideanSpace ℝ (Fin d), ‖h ‖v‖ * gauge K v‖ ≤
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) T).indicator
          (fun _ => M * (normMax (gauge K) * T)) v := by
      intro v
      by_cases hv : ‖v‖ ≤ T
      · rw [Set.indicator_of_mem (by simpa using hv)]
        have h1 : gauge K v ≤ normMax (gauge K) * T :=
          (gauge_le_normMax_mul hK h0 v).trans (mul_le_mul_of_nonneg_left hv hΛ)
        calc ‖h ‖v‖ * gauge K v‖ = |h ‖v‖| * |gauge K v| := by rw [Real.norm_eq_abs, abs_mul]
          _ ≤ M * (normMax (gauge K) * T) := by
              rw [abs_of_nonneg (gauge_nonneg v)]
              exact mul_le_mul (hb _) h1 (gauge_nonneg v) hM
      · rw [not_le] at hv
        rw [hs _ hv, zero_mul, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by positivity) v
    refine Integrable.mono' ?_ ((hm.comp measurable_norm).mul hgc.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    exact integrableOn_const (measure_closedBall_lt_top).ne
  rw [integral_eq_integral_Ioi_sphere hd hint, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  have hinner : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      h ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ * gauge K (r • (θ : EuclideanSpace ℝ (Fin d))) =
        (h r * r) * gauge K (θ : EuclideanSpace ℝ (Fin d)) := by
    intro θ
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
    rw [norm_smul, Real.norm_of_nonneg hr'.le, hθ, mul_one, gauge_smul_nonneg K hr'.le]
    ring
  simp only [hinner]
  rw [integral_const_mul]
  have hpow : r ^ (d - 1) * r = r ^ d := by
    rw [← pow_succ]
    congr 1
    omega
  set σint : ℝ := ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
    gauge K (θ : EuclideanSpace ℝ (Fin d)) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
    with hσint
  calc r ^ (d - 1) * ((h r * r) * σint) = (r ^ (d - 1) * r) * h r * σint := by ring
    _ = _ := by rw [hpow]; ring

/-- The cut-off profile is `1` on `[0, a]` and nonnegative, so
`∫_0^r s^d b(s²) ds ≥ a^{d+1}/(d+1)`. -/
private lemma interval_lower_bound {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (ha : 0 ≤ a)
    (har : a < r) :
    a ^ (d + 1) / (d + 1) ≤ ∫ s in (0 : ℝ)..r, s ^ d * b (s ^ 2) := by
  have hbc : Continuous b := hb.smooth.continuous
  have hcontJ : Continuous fun s : ℝ => s ^ d * b (s ^ 2) := by fun_prop
  have hJ0 : ∀ s ∈ Set.uIcc (0 : ℝ) a, s ^ d * b (s ^ 2) = s ^ d := by
    intro s hs
    rw [Set.uIcc_of_le ha] at hs
    rw [hb.eq_one (s ^ 2) (by nlinarith [hs.1, hs.2]), mul_one]
  have hlow : (∫ s in (0 : ℝ)..a, s ^ d * b (s ^ 2)) = a ^ (d + 1) / (d + 1) := by
    have h1 : (∫ s in (0 : ℝ)..a, s ^ d * b (s ^ 2)) = ∫ s in (0 : ℝ)..a, s ^ d :=
      intervalIntegral.integral_congr hJ0
    rw [h1, integral_pow]
    simp
  have hhigh : 0 ≤ ∫ s in a..r, s ^ d * b (s ^ 2) :=
    intervalIntegral.integral_nonneg har.le fun s hs =>
      mul_nonneg (pow_nonneg (ha.trans hs.1) _) (hb.nonneg _)
  have hi1 : IntervalIntegrable (fun s : ℝ => s ^ d * b (s ^ 2)) volume 0 a :=
    hcontJ.intervalIntegrable 0 a
  have hi2 : IntervalIntegrable (fun s : ℝ => s ^ d * b (s ^ 2)) volume a r :=
    hcontJ.intervalIntegrable a r
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  linarith

/-- The radial integral of the Laplacian of the test function `testFn b r 0`:
`∫_0^∞ s^d (-d b(s²) - 2 b'(s²) s²) ds = ∫_0^∞ s^d b(s²) ds`, and it is at least
`a^{d+1}/(d+1)`. -/
private lemma radial_laplacian_integral {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (ha : 0 ≤ a)
    (har : a < r) :
    ∫ s in Set.Ioi (0 : ℝ), s ^ d * (-(d : ℝ) * b (s ^ 2) - 2 * deriv b (s ^ 2) * s ^ 2) =
      ∫ s in (0 : ℝ)..r, s ^ d * b (s ^ 2) ∧
    a ^ (d + 1) / (d + 1) ≤ ∫ s in (0 : ℝ)..r, s ^ d * b (s ^ 2) := by
  have hr0 : 0 ≤ r := ha.trans har.le
  have hbc : Continuous b := hb.smooth.continuous
  have hb'c : Continuous (deriv b) := continuous_deriv_cutoff hb
  -- the integrand vanishes beyond `r`
  have hzero : ∀ s : ℝ, r < s →
      s ^ d * (-(d : ℝ) * b (s ^ 2) - 2 * deriv b (s ^ 2) * s ^ 2) = 0 := by
    intro s hs
    have hs2 : r ^ 2 < s ^ 2 := by nlinarith
    rw [hb.eq_zero (s ^ 2) hs2.le, deriv_eq_zero_of_lt hb hs2]
    ring
  have hcontG : Continuous fun s : ℝ =>
      s ^ d * (-(d : ℝ) * b (s ^ 2) - 2 * deriv b (s ^ 2) * s ^ 2) := by
    have := hbc
    have := hb'c
    fun_prop
  have hcontJ : Continuous fun s : ℝ => s ^ d * b (s ^ 2) := by
    have := hbc
    fun_prop
  -- from the half line to `[0, r]`
  have hIoi : ∫ s in Set.Ioi (0 : ℝ), s ^ d * (-(d : ℝ) * b (s ^ 2) - 2 * deriv b (s ^ 2) * s ^ 2) =
      ∫ s in (0 : ℝ)..r, s ^ d * (-(d : ℝ) * b (s ^ 2) - 2 * deriv b (s ^ 2) * s ^ 2) := by
    rw [intervalIntegral.integral_of_le hr0]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self fun s hs => ?_
    refine hzero s ?_
    by_contra hnot
    exact hs.2 ⟨hs.1, not_lt.mp hnot⟩
  -- integration by parts
  have hu : ∀ s ∈ Set.uIcc (0 : ℝ) r, HasDerivAt (fun s : ℝ => s ^ (d + 1))
      (((d + 1 : ℕ) : ℝ) * s ^ d) s := fun s _ => by
    simpa using hasDerivAt_pow (d + 1) s
  have hv : ∀ s ∈ Set.uIcc (0 : ℝ) r, HasDerivAt (fun s : ℝ => b (s ^ 2))
      (deriv b (s ^ 2) * (2 * s)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    have h2 : HasDerivAt b (deriv b (s ^ 2)) (s ^ 2) :=
      (hb.smooth.differentiable (by simp) _).hasDerivAt
    have h3 : HasDerivAt (b ∘ fun s : ℝ => s ^ 2) (deriv b (s ^ 2) * (2 * s)) s :=
      HasDerivAt.comp (h := fun s : ℝ => s ^ 2) s h2 h1
    exact h3
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    ((by fun_prop : Continuous fun s : ℝ => ((d + 1 : ℕ) : ℝ) * s ^ d).intervalIntegrable _ _)
    ((by have := hb'c; fun_prop :
      Continuous fun s : ℝ => deriv b (s ^ 2) * (2 * s)).intervalIntegrable _ _)
  have hbr : b (r ^ 2) = 0 := hb.eq_zero (r ^ 2) le_rfl
  rw [hbr] at hibp
  have hcont1 : Continuous fun s : ℝ => s ^ (d + 1) * (deriv b (s ^ 2) * (2 * s)) := by
    have := hb'c
    fun_prop
  have hcont2 : Continuous fun s : ℝ => ((d + 1 : ℕ) : ℝ) * s ^ d * b (s ^ 2) := by
    have := hbc
    fun_prop
  have hsplit : ∫ s in (0 : ℝ)..r, s ^ d * (-(d : ℝ) * b (s ^ 2) - 2 * deriv b (s ^ 2) * s ^ 2) =
      ∫ s in (0 : ℝ)..r, s ^ d * b (s ^ 2) := by
    have e1 : ∀ s : ℝ, s ^ d * (-(d : ℝ) * b (s ^ 2) - 2 * deriv b (s ^ 2) * s ^ 2) =
        (-(d : ℝ)) * (s ^ d * b (s ^ 2)) - s ^ (d + 1) * (deriv b (s ^ 2) * (2 * s)) := by
      intro s
      ring
    simp_rw [e1]
    rw [intervalIntegral.integral_sub ((hcontJ.const_mul _).intervalIntegrable _ _)
      (hcont1.intervalIntegrable _ _), intervalIntegral.integral_const_mul, hibp]
    have e2 : ∫ s in (0 : ℝ)..r, ((d + 1 : ℕ) : ℝ) * s ^ d * b (s ^ 2) =
        ((d + 1 : ℕ) : ℝ) * ∫ s in (0 : ℝ)..r, s ^ d * b (s ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    rw [e2]
    simp only [zero_pow (Nat.succ_ne_zero d), mul_zero, sub_zero, zero_mul]
    push_cast
    ring
  exact ⟨hIoi.trans hsplit, interval_lower_bound hb ha har⟩

/-- The sphere integral of the gauge is at least `c_ψ` times the total mass `d ω_d` of the
sphere. -/
private lemma normMin_mul_le_integral_sphere (hd : 1 ≤ d) (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hc : Convex ℝ K) :
    normMin (gauge K) * (d * unitBallVolume d) ≤
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, gauge K (θ : EuclideanSpace ℝ (Fin d))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  obtain ⟨hpos, hle⟩ := normMin_gauge_pos_mul_le hK h0 hd
  have hgc : Continuous (gauge K) := (lipschitzWith_gauge hK hc h0).continuous
  have hΛ : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ‖gauge K (θ : EuclideanSpace ℝ (Fin d))‖ ≤ normMax (gauge K) := by
    intro θ
    have h1 := gauge_le_normMax_mul hK h0 (θ : EuclideanSpace ℝ (Fin d))
    rw [mem_sphere_zero_iff_norm.mp θ.2, mul_one] at h1
    rw [Real.norm_of_nonneg (gauge_nonneg _)]
    exact h1
  have hint : Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      gauge K (θ : EuclideanSpace ℝ (Fin d)))
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) :=
    Integrable.of_bound (C := normMax (gauge K))
      (hgc.comp continuous_subtype_val).aestronglyMeasurable (Filter.Eventually.of_forall hΛ)
  have h1 : ∫ _θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, normMin (gauge K)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere ≤
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, gauge K (θ : EuclideanSpace ℝ (Fin d))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
    refine integral_mono (integrable_const _) hint fun θ => ?_
    have := hle (θ : EuclideanSpace ℝ (Fin d))
    rwa [mem_sphere_zero_iff_norm.mp θ.2, mul_one] at this
  rw [integral_const, smul_eq_mul] at h1
  have h2 : ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).real Set.univ =
      d * unitBallVolume d := CERW.Support.Norm.GaugePotential.toSphere_real_univ_eq d
  rw [h2] at h1
  linarith

/-- **The distributional Laplacian of the gauge charges every ball about the origin.** For every
locally finite measure `m` that is the distributional Laplacian of the gauge of a compact convex
`K` with the origin in its interior, and every `ρ > 0`,
`m(B(0, ρ)) ≥ 8 c_ψ d ω_d / (4^{d+1} (d + 1)) · ρ^{d-1}`, where `c_ψ = min_{|u| = 1} ψ_K(u) > 0`.
This is the lower counterpart of the growth bound `m(B(y, R)) ≤ C Λ_ψ R^{d-1}`, and shows that the
measure is not zero: the radial test function `φ = testFn b r 0` has
`∫ φ dm = ∫ ψ_K Δφ = (∫_{S^{d-1}} ψ_K) ∫_0^∞ s^d b(s²) ds > 0`. -/
theorem measure_ball_ge_gauge (hd : 1 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {m : Measure (EuclideanSpace ℝ (Fin d))} (hmfin : IsLocallyFiniteMeasure m)
    (hlap : CERW.IsDistribLaplacian (gauge K) m) {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (8 * normMin (gauge K) * (d * unitBallVolume d) /
        (4 ^ (d + 1) * ((d : ℝ) + 1)) * ρ ^ (d - 1)) ≤ m (Metric.ball 0 ρ) := by
  haveI := hmfin
  set a : ℝ := ρ / 4 with ha
  set r : ℝ := ρ / 2 with hr
  have ha0 : 0 ≤ a := by positivity
  have har : a < r := by rw [ha, hr]; linarith
  have hrρ : r < ρ := by rw [hr]; linarith
  have hr0 : 0 ≤ r := by positivity
  obtain ⟨b, hb⟩ := exists_cutoff ha0 har
  set φ : EuclideanSpace ℝ (Fin d) → ℝ := testFn b r 0 with hφ
  have hmφ := hlap φ (contDiff_testFn hb.smooth r 0) (hasCompactSupport_testFn hb hr0 0)
  -- the radial profile of the Laplacian
  set H : ℝ → ℝ := fun s => -(d : ℝ) * b (s ^ 2) - 2 * deriv b (s ^ 2) * s ^ 2 with hH
  have hHc : Continuous H := by
    have := hb.smooth.continuous
    have := continuous_deriv_cutoff hb
    rw [hH]
    fun_prop
  have hHzero : ∀ s : ℝ, r < |s| → H s = 0 := by
    intro s hs
    have hs2 : r ^ 2 < s ^ 2 := by
      have : r ^ 2 < |s| ^ 2 := by nlinarith
      rwa [sq_abs] at this
    simp only [hH]
    rw [hb.eq_zero (s ^ 2) hs2.le, deriv_eq_zero_of_lt hb hs2]
    ring
  obtain ⟨M', hM'⟩ := exists_bound_deriv hb
  have hHb : ∀ s, |H s| ≤ (d : ℝ) + 2 * M' * r ^ 2 := by
    intro s
    by_cases hs : r < |s|
    · rw [hHzero s hs, abs_zero]
      have : 0 ≤ M' := (abs_nonneg _).trans (hM' 0)
      positivity
    · rw [not_lt] at hs
      have hs2 : s ^ 2 ≤ r ^ 2 := by
        have : |s| ^ 2 ≤ r ^ 2 := by nlinarith [abs_nonneg s]
        rwa [sq_abs] at this
      have hM0 : 0 ≤ M' := (abs_nonneg _).trans (hM' 0)
      have h1 : |(-(d : ℝ)) * b (s ^ 2)| ≤ d := by
        rw [abs_mul, abs_neg, Nat.abs_cast, abs_of_nonneg (hb.nonneg _)]
        exact mul_le_of_le_one_right (Nat.cast_nonneg d) (hb.le_one _)
      have h2 : |2 * deriv b (s ^ 2) * s ^ 2| ≤ 2 * M' * r ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg s), abs_two]
        have h4 := hM' (s ^ 2)
        have h3 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
        exact mul_le_mul (mul_le_mul_of_nonneg_left h4 (by norm_num)) hs2 h3 (by positivity)
      have h5 := abs_sub ((-(d : ℝ)) * b (s ^ 2)) (2 * deriv b (s ^ 2) * s ^ 2)
      have hHs : H s = (-(d : ℝ)) * b (s ^ 2) - 2 * deriv b (s ^ 2) * s ^ 2 := rfl
      rw [hHs]
      linarith
  -- the Laplacian of the test function in polar form
  have hlapφ : ∀ v, Laplacian.laplacian φ v = H ‖v‖ := by
    intro v
    simp only [hφ, hH]
    rw [laplacian_testFn hb.smooth r 0 v]
    simp
  have hpolar := integral_polar_gauge hd hK hc h0 H hHc.measurable (T := r) hr0 hHb
    (fun s hs => hHzero s (by rwa [abs_of_pos (hr0.trans_lt hs)]))
  obtain ⟨hradial, hlower⟩ := radial_laplacian_integral (d := d) hb ha0 har
  have hint1 : ∫ v, gauge K v * Laplacian.laplacian φ v =
      ∫ v : EuclideanSpace ℝ (Fin d), H ‖v‖ * gauge K v := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hlapφ, mul_comm]
  have hrad' : ∫ s in Set.Ioi (0 : ℝ), s ^ d * H s = ∫ s in (0 : ℝ)..r, s ^ d * b (s ^ 2) :=
    hradial
  have hsph := normMin_mul_le_integral_sphere hd hK h0 hc
  have hωpos : 0 < unitBallVolume d := unitBallVolume_pos d
  obtain ⟨hcpos, -⟩ := normMin_gauge_pos_mul_le hK h0 hd
  have hmain : normMin (gauge K) * (d * unitBallVolume d) * (a ^ (d + 1) / (d + 1)) ≤
      ∫ v, φ v ∂m := by
    rw [hmφ, hint1, hpolar, hrad']
    have hJpos : 0 ≤ a ^ (d + 1) / (d + 1) := by positivity
    exact mul_le_mul hsph hlower hJpos (by
      have := hsph
      have hd0 : (0 : ℝ) ≤ normMin (gauge K) * (d * unitBallVolume d) := by positivity
      exact hd0.trans hsph)
  have hup := integral_testFn_le hb hr0 hrρ 0 m
  have hfin : m (Metric.ball 0 ρ) < ⊤ := measure_ball_lt_top
  rw [ENNReal.ofReal_le_iff_le_toReal hfin.ne]
  have hr2 : 0 < r ^ 2 := by positivity
  have hlow := hmain.trans hup
  have hρd : (0 : ℝ) < ρ := hρ
  have hkey : 8 * normMin (gauge K) * (d * unitBallVolume d) /
        (4 ^ (d + 1) * ((d : ℝ) + 1)) * ρ ^ (d - 1) =
      normMin (gauge K) * (d * unitBallVolume d) * (a ^ (d + 1) / (d + 1)) / (r ^ 2 / 2) := by
    rw [ha, hr, div_pow]
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  rw [hkey, div_le_iff₀ (by positivity)]
  calc normMin (gauge K) * (d * unitBallVolume d) * (a ^ (d + 1) / (d + 1))
      ≤ r ^ 2 / 2 * (m (Metric.ball 0 ρ)).toReal := hlow
    _ = (m (Metric.ball 0 ρ)).toReal * (r ^ 2 / 2) := by ring

end Nonvanishing

end CellLemma

/-! ### The weighted summation of the cell estimate -/

section DirectionReplacement

open MeasureTheory Filter Topology LatticeProb CERW CERW.Support.Occupation CERW.Generic.Kernel
open scoped ENNReal Classical

section FarSum

variable {d : ℕ}

/-- The number of lattice sites within `r` of a point is at most `(r + √d)^d ω_d`: their unit cells
are disjoint and lie in the ball of radius `r + √d`. -/
private lemma card_filter_ball_le (hd : 1 ≤ d) (T : Finset (Site d))
    (z : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r) :
    ((T.filter fun x => z ∈ Metric.ball (toSpace x) r).card : ℝ≥0∞) ≤
      ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d) := by
  set T' := T.filter fun x => z ∈ Metric.ball (toSpace x) r with hT'
  have hδ : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hsub : (⋃ x ∈ T', cell x) ⊆ Metric.ball z (r + Real.sqrt d) := by
    intro v hv
    obtain ⟨x, hx, hvx⟩ := Set.mem_iUnion₂.mp hv
    have hxz : z ∈ Metric.ball (toSpace x) r := (Finset.mem_filter.mp hx).2
    rw [Metric.mem_ball, dist_eq_norm] at hxz ⊢
    have h1 := norm_sub_toSpace_le_of_mem_cell hvx
    calc ‖v - z‖ = ‖(v - toSpace x) + (toSpace x - z)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖v - toSpace x‖ + ‖toSpace x - z‖ := norm_add_le _ _
      _ = ‖v - toSpace x‖ + ‖z - toSpace x‖ := by rw [norm_sub_rev (toSpace x) z]
      _ < r + Real.sqrt d := by linarith
  calc (T'.card : ℝ≥0∞) = volume (⋃ x ∈ T', cell x) := (volume_biUnion_cell T').symm
    _ ≤ volume (Metric.ball z (r + Real.sqrt d)) := measure_mono hsub
    _ = ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d) := by
        rw [Measure.addHaar_ball_of_pos volume z (by positivity), finrank_euclideanSpace_fin,
          unitBallVolume, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal measure_ball_lt_top.ne]

/-- A multiplicity bound: the balls `B(x, r)` around distinct lattice sites of a finite set `T` have
total measure at most `(r + √d)^d ω_d` times the measure of a set containing all of them. -/
private lemma sum_measure_ball_le (hd : 1 ≤ d) {m : Measure (EuclideanSpace ℝ (Fin d))}
    (T : Finset (Site d)) {r : ℝ} (hr : 0 ≤ r) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hUm : MeasurableSet U) (hU : ∀ x ∈ T, Metric.ball (toSpace x) r ⊆ U) :
    ∑ x ∈ T, m (Metric.ball (toSpace x) r) ≤
      ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d) * m U := by
  have hmeas : ∀ x ∈ T, Measurable ((Metric.ball (toSpace x) r).indicator
      (fun _ => (1 : ℝ≥0∞))) := fun x _ =>
    measurable_const.indicator Metric.isOpen_ball.measurableSet
  calc ∑ x ∈ T, m (Metric.ball (toSpace x) r)
      = ∑ x ∈ T, ∫⁻ z, (Metric.ball (toSpace x) r).indicator (fun _ => (1 : ℝ≥0∞)) z ∂m := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet, one_mul]
    _ = ∫⁻ z, ∑ x ∈ T, (Metric.ball (toSpace x) r).indicator (fun _ => (1 : ℝ≥0∞)) z ∂m :=
        (lintegral_finsetSum _ hmeas).symm
    _ ≤ ∫⁻ z, U.indicator
          (fun _ => ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d)) z ∂m := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ U
        · rw [Set.indicator_of_mem hz]
          have := card_filter_ball_le hd T z hr
          calc ∑ x ∈ T, (Metric.ball (toSpace x) r).indicator (fun _ => (1 : ℝ≥0∞)) z
              = ((T.filter fun x => z ∈ Metric.ball (toSpace x) r).card : ℝ≥0∞) := by
                push_cast [Finset.card_filter, Set.indicator_apply]
                rfl
            _ ≤ _ := this
        · rw [Set.indicator_of_notMem hz]
          refine le_of_eq (Finset.sum_eq_zero fun x hx => ?_)
          rw [Set.indicator_of_notMem]
          exact fun h => hz (hU x hx h)
    _ = ENNReal.ofReal ((r + Real.sqrt d) ^ d * unitBallVolume d) * m U := by
        rw [lintegral_indicator_const hUm, mul_comm]

/-- Dyadic shells: a site `x` with `8 √d < |x - y| ≤ R'` lies in the shell `2^k ≤ |x - y| < 2^{k+1}`
with `k = ⌊log₂ ⌊|x - y|⌋⌋ ≤ ⌊log₂ ⌈R'⌉⌋`, and the ball `B(x, 6 √d)` lies in `B(y, 2^{k+2})`. -/
private lemma dyadic_shell {y x : Site d} {R' : ℝ} (hd : 1 ≤ d)
    (hx : 8 * Real.sqrt d < euclidNorm (x - y) ∧ euclidNorm (x - y) ≤ R') :
    Nat.log 2 ⌊euclidNorm (x - y)⌋₊ ≤ Nat.log 2 ⌈R'⌉₊ ∧
      (2 : ℝ) ^ Nat.log 2 ⌊euclidNorm (x - y)⌋₊ ≤ euclidNorm (x - y) ∧
      euclidNorm (x - y) < 2 ^ (Nat.log 2 ⌊euclidNorm (x - y)⌋₊ + 1) := by
  have hδ : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  set ρ := euclidNorm (x - y) with hρ
  have hρ1 : 1 ≤ ρ := by linarith [hx.1]
  have hfl : ⌊ρ⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊ρ⌋₊ := Nat.le_floor (by simpa using hρ1)
    omega
  refine ⟨Nat.log_mono_right ?_, ?_, ?_⟩
  · exact (Nat.floor_le_floor hx.2).trans (Nat.floor_le_ceil R')
  · have h1 : 2 ^ Nat.log 2 ⌊ρ⌋₊ ≤ ⌊ρ⌋₊ := Nat.pow_log_le_self 2 hfl
    calc (2 : ℝ) ^ Nat.log 2 ⌊ρ⌋₊ ≤ ((⌊ρ⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ρ := Nat.floor_le (by linarith)
  · have h1 : ⌊ρ⌋₊ < 2 ^ (Nat.log 2 ⌊ρ⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    calc ρ < (⌊ρ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ρ
      _ ≤ ((2 ^ (Nat.log 2 ⌊ρ⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = 2 ^ (Nat.log 2 ⌊ρ⌋₊ + 1) := by push_cast; ring

/-- The far sum in `ℝ≥0∞`: if `m (B(y, R)) ≤ Kg R^{d-1}` for every `R`, then
`Σ_x |x - y|^{-(d-1)} m(B(x, 6√d))` over sites with `8 √d < |x - y| ≤ R'` is at most
`(⌊log₂ ⌈R'⌉⌋ + 1) (7√d)^d ω_d Kg 4^{d-1}`. -/
private lemma sum_far_le (hd : 2 ≤ d) {m : Measure (EuclideanSpace ℝ (Fin d))} {Kg : ℝ}
    (hKg : 0 ≤ Kg) (y : Site d)
    (hgrowth : ∀ {R : ℝ}, 0 < R → m (Metric.ball (toSpace y) R) ≤ ENNReal.ofReal (Kg * R ^ (d - 1)))
    (F : Finset (Site d)) {R' : ℝ}
    (hF : ∀ x ∈ F, 8 * Real.sqrt d < euclidNorm (x - y) ∧ euclidNorm (x - y) ≤ R') :
    ∑ x ∈ F, ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
        m (Metric.ball (toSpace x) (6 * Real.sqrt d)) ≤
      ((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          ((6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d * Kg * 4 ^ (d - 1)) := by
  have hd1 : 1 ≤ d := by omega
  have hδ : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd1)
  set K := Nat.log 2 ⌈R'⌉₊ with hK
  set k : Site d → ℕ := fun x => Nat.log 2 ⌊euclidNorm (x - y)⌋₊ with hk
  set Nr : ℝ := (6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d with hNr
  have hmaps : ∀ x ∈ F, k x ∈ Finset.range (K + 1) := fun x hx =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (dyadic_shell hd1 (hF x hx)).1)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ Finset.range (K + 1),
      ∑ x ∈ F.filter (fun x => k x = j), ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
        m (Metric.ball (toSpace x) (6 * Real.sqrt d)) ≤
      ENNReal.ofReal (Nr * Kg * 4 ^ (d - 1)) := by
    intro j _
    set Fj := F.filter (fun x => k x = j) with hFj
    have hmem : ∀ x ∈ Fj, x ∈ F ∧ k x = j := fun x hx => Finset.mem_filter.mp hx
    have hshell : ∀ x ∈ Fj,
        (2 : ℝ) ^ j ≤ euclidNorm (x - y) ∧ euclidNorm (x - y) < 2 ^ (j + 1) := by
      intro x hx
      obtain ⟨hxF, hxj⟩ := hmem x hx
      have h := dyadic_shell hd1 (hF x hxF)
      have hxj' : Nat.log 2 ⌊euclidNorm (x - y)⌋₊ = j := hxj
      rw [hxj'] at h
      exact ⟨h.2.1, h.2.2⟩
    have hsub : ∀ x ∈ Fj, Metric.ball (toSpace x) (6 * Real.sqrt d) ⊆
        Metric.ball (toSpace y) (2 ^ (j + 2)) := by
      intro x hx z hz
      obtain ⟨hxF, -⟩ := hmem x hx
      obtain ⟨-, h2⟩ := hshell x hx
      have h8 := (hF x hxF).1
      rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
      have hxy : ‖toSpace x - toSpace y‖ = euclidNorm (x - y) := by rw [← toSpace_sub, norm_toSpace]
      calc ‖z - toSpace y‖ = ‖(z - toSpace x) + (toSpace x - toSpace y)‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ ‖z - toSpace x‖ + ‖toSpace x - toSpace y‖ := norm_add_le _ _
        _ < 6 * Real.sqrt d + euclidNorm (x - y) := by rw [hxy]; linarith
        _ ≤ 2 ^ (j + 2) := by
            have : (2 : ℝ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
            rw [this]
            linarith
    have hinv : ∀ x ∈ Fj, ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) ≤
        ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) := by
      intro x hx
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := (hshell x hx).1
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 _)
    calc ∑ x ∈ Fj, ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
          m (Metric.ball (toSpace x) (6 * Real.sqrt d))
        ≤ ∑ x ∈ Fj, ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) *
          m (Metric.ball (toSpace x) (6 * Real.sqrt d)) :=
          Finset.sum_le_sum fun x hx => mul_le_mul' (hinv x hx) le_rfl
      _ = ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) *
          ∑ x ∈ Fj, m (Metric.ball (toSpace x) (6 * Real.sqrt d)) := (Finset.mul_sum _ _ _).symm
      _ ≤ ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) *
          (ENNReal.ofReal Nr * m (Metric.ball (toSpace y) (2 ^ (j + 2)))) :=
          by
            gcongr
            exact sum_measure_ball_le hd1 Fj (r := 6 * Real.sqrt d) (by positivity)
              Metric.isOpen_ball.measurableSet hsub
      _ ≤ ENNReal.ofReal ((((2 : ℝ) ^ j) ^ (d - 1))⁻¹) *
          (ENNReal.ofReal Nr * ENNReal.ofReal (Kg * ((2 : ℝ) ^ (j + 2)) ^ (d - 1))) :=
          by
            gcongr
            exact hgrowth (by positivity)
      _ = ENNReal.ofReal (Nr * Kg * 4 ^ (d - 1)) := by
          have hNr0 : 0 ≤ Nr := by
            have := unitBallVolume_pos d
            rw [hNr]
            positivity
          have ha0 : 0 ≤ (((2 : ℝ) ^ j) ^ (d - 1))⁻¹ := by positivity
          have hb0 : 0 ≤ Kg * ((2 : ℝ) ^ (j + 2)) ^ (d - 1) := by positivity
          rw [← ENNReal.ofReal_mul hNr0, ← ENNReal.ofReal_mul ha0]
          congr 1
          have h2 : ((2 : ℝ) ^ (j + 2)) ^ (d - 1) = ((2 : ℝ) ^ j) ^ (d - 1) * 4 ^ (d - 1) := by
            rw [← mul_pow, pow_add]
            norm_num
          rw [h2]
          have h3 : (0 : ℝ) < ((2 : ℝ) ^ j) ^ (d - 1) := by positivity
          field_simp
  calc ∑ j ∈ Finset.range (K + 1), ∑ x ∈ F.filter (fun x => k x = j),
        ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
          m (Metric.ball (toSpace x) (6 * Real.sqrt d))
      ≤ ∑ _j ∈ Finset.range (K + 1), ENNReal.ofReal (Nr * Kg * 4 ^ (d - 1)) :=
        Finset.sum_le_sum hfib
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end FarSum

section Direction

variable {d : ℕ}

/-- For `t > 0`, `t^{1-d} = (t^{d-1})⁻¹`. -/
private lemma rpow_one_sub_eq_inv_pow {t : ℝ} (ht : 0 < t) (hd : 1 ≤ d) :
    t ^ (1 - (d : ℝ)) = (t ^ (d - 1))⁻¹ := by
  have : (1 - (d : ℝ)) = -((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd]
    ring
  rw [this, Real.rpow_neg ht.le, Real.rpow_natCast]

/-- A bound for the integral of the kernel against a measurable bounded field on a set of finite
volume: if `‖g v‖ ‖v - z‖^{1-d} ≤ h v` on `D` then `|∫_D ⟨g, K(· - z)⟩| ≤ ∫_D h`. -/
private lemma abs_setIntegral_inner_newtonField_le (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (z : EuclideanSpace ℝ (Fin d)) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : IntegrableOn h D) (hpt : ∀ v ∈ D, ‖g v‖ * ‖v - z‖ ^ (1 - (d : ℝ)) ≤ h v) :
    |∫ v in D, inner ℝ (g v) (newtonField (v - z))| ≤ ∫ v in D, h v := by
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hh ?_
  refine (ae_restrict_iff' hD).mpr (Eventually.of_forall fun v hv => ?_)
  calc ‖inner ℝ (g v) (newtonField (v - z))‖ ≤ ‖g v‖ * ‖newtonField (v - z)‖ :=
        norm_inner_le_norm _ _
    _ = ‖g v‖ * ‖v - z‖ ^ (1 - (d : ℝ)) := by rw [norm_newtonField hd]
    _ ≤ h v := hpt v hv

/-- The logarithmic count of dyadic levels: `⌊log₂ ⌈R'⌉⌋ + 1 ≤ (1 + 1/log 2) log (R' + 2)`. -/
private lemma natLog_ceil_add_one_le {R' : ℝ} (hR' : 1 ≤ R') :
    ((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ) ≤ (1 + 1 / Real.log 2) * Real.log (R' + 2) := by
  have hL : 1 ≤ Real.log (R' + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : (0 : ℝ) < (⌈R'⌉₊ : ℝ) := by
    have : 0 < ⌈R'⌉₊ := Nat.ceil_pos.mpr (by linarith)
    exact_mod_cast this
  have h1 : (Nat.log 2 ⌈R'⌉₊ : ℝ) ≤ Real.logb 2 (⌈R'⌉₊ : ℝ) := Real.natLog_le_logb _ _
  have h2 : Real.log (⌈R'⌉₊ : ℝ) ≤ Real.log (R' + 2) :=
    Real.log_le_log hceil (by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ R')])
  have h3 : (Nat.log 2 ⌈R'⌉₊ : ℝ) ≤ Real.log (R' + 2) / Real.log 2 := by
    refine h1.trans ?_
    rw [Real.logb]
    exact div_le_div_of_nonneg_right h2 hlog2.le
  push_cast
  calc (Nat.log 2 ⌈R'⌉₊ : ℝ) + 1 ≤ Real.log (R' + 2) / Real.log 2 + 1 := by linarith
    _ ≤ (1 + 1 / Real.log 2) * Real.log (R' + 2) := by
        have : Real.log (R' + 2) / Real.log 2 = 1 / Real.log 2 * Real.log (R' + 2) := by ring
        rw [this]
        nlinarith

/-- The far sum in `ℝ`, for a locally finite measure. -/
private lemma sum_far_real_le (hd : 2 ≤ d) {m : Measure (EuclideanSpace ℝ (Fin d))}
    (hmfin : IsLocallyFiniteMeasure m) {Kg : ℝ}
    (hKg : 0 ≤ Kg) (y : Site d)
    (hgrowth : ∀ {R : ℝ}, 0 < R → m (Metric.ball (toSpace y) R) ≤ ENNReal.ofReal (Kg * R ^ (d - 1)))
    (F : Finset (Site d)) {R' : ℝ}
    (hF : ∀ x ∈ F, 8 * Real.sqrt d < euclidNorm (x - y) ∧ euclidNorm (x - y) ≤ R') :
    ∑ x ∈ F, (euclidNorm (x - y) ^ (d - 1))⁻¹ *
        (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal ≤
      ((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ) *
        ((6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d * Kg * 4 ^ (d - 1)) := by
  have h := sum_far_le hd hKg y hgrowth F hF
  have hfin : ∀ x ∈ F, ENNReal.ofReal ((euclidNorm (x - y) ^ (d - 1))⁻¹) *
      m (Metric.ball (toSpace x) (6 * Real.sqrt d)) ≠ ⊤ := fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  have hT : ((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal
        ((6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d * Kg * 4 ^ (d - 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono hT h
  rw [ENNReal.toReal_sum hfin] at h2
  have hω := unitBallVolume_pos d
  have hT0 : 0 ≤ (6 * Real.sqrt d + Real.sqrt d) ^ d * unitBallVolume d * Kg * 4 ^ (d - 1) := by
    positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hT0] at h2
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_)) h2
  have hx0 : 0 ≤ (euclidNorm (x - y) ^ (d - 1))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (euclidNorm_nonneg _) _)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hx0]

/-- **The weighted summation of the cell estimate** for the gauge of a convex body: replacing the
lattice drift `ξ(x)` by the gradient `∇ψ_K(v)` on the cells costs `O(log(R' + 2))` in the source
sum, given the cell estimate of `lem:cell` (with constant `Cc` and a measure `m`) and the growth
`m(B(y, R)) ≤ Kg R^{d-1}` of the distributional Laplacian at the centre `y`. -/
theorem gauge_sum_abs_setIntegral_sub_gradient_le (hd : 2 ≤ d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hcvx : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {m : Measure (EuclideanSpace ℝ (Fin d))} (hmfin : IsLocallyFiniteMeasure m)
    {Cc Kg : ℝ} (hCc : 0 ≤ Cc) (hKg : 0 ≤ Kg) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)), (∀ x, ‖ξ x‖ ≤ normMax (gauge K)) →
      (∀ x : Site d, ENNReal.ofReal (∫ v in cell x, ‖gradient (gauge K) v - ξ x‖) ≤
        ENNReal.ofReal Cc * m (Metric.ball (toSpace x) (6 * Real.sqrt d))) →
      ∀ (F : Finset (Site d)) (y : Site d) (R' : ℝ), 1 ≤ R' →
        (∀ x ∈ F, euclidNorm (x - y) ≤ R') →
        (∀ {R : ℝ}, 0 < R →
          m (Metric.ball (toSpace y) R) ≤ ENNReal.ofReal (Kg * R ^ (d - 1))) →
        ∑ x ∈ F, |∫ v in cell x, inner ℝ (ξ x - gradient (gauge K) v) (newtonField (v - toSpace y))|
          ≤ C * Real.log (R' + 2) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hdR
  have hω := unitBallVolume_pos d
  have hΛ : 0 ≤ normMax (gauge K) := normMax_gauge_nonneg K
  set Λ := normMax (gauge K) with hΛdef
  set ω := unitBallVolume d with hωdef
  set Nr : ℝ := (6 * Real.sqrt d + Real.sqrt d) ^ d * ω with hNr
  have hNr0 : 0 ≤ Nr := by rw [hNr]; positivity
  set Cn : ℝ := 2 * Λ * (d * ω * (9 * Real.sqrt d)) with hCn
  set Cf : ℝ := 2 ^ (d - 1) * Cc * (Nr * Kg * 4 ^ (d - 1)) * (1 + 1 / Real.log 2) with hCf
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCn0 : 0 ≤ Cn := by rw [hCn]; positivity
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  refine ⟨Cn + Cf, add_nonneg hCn0 hCf0, ?_⟩
  intro ξ hξ hcell F y R' hR' hF hgrowth
  have hL : 1 ≤ Real.log (R' + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  set c := toSpace y with hc
  rw [← Finset.sum_filter_add_sum_filter_not F (fun x => euclidNorm (x - y) ≤ 8 * Real.sqrt d)]
  -- the field `ξ x - ∇(gauge K)` is bounded by `2 Λ`
  have hgb : ∀ x v, ‖ξ x - gradient (gauge K) v‖ ≤ 2 * Λ := fun x v =>
    (norm_sub_le _ _).trans (by linarith [hξ x, norm_gradient_gauge_le hK hcvx h0 v])
  have hgmeas : ∀ x, Measurable fun v => ‖gradient (gauge K) v - ξ x‖ := fun x =>
    continuous_norm.measurable.comp ((measurable_gradient (gauge K)).sub_const _)
  have hcellfin : ∀ x : Site d, volume (cell x) ≠ ⊤ := fun x => by
    rw [volume_cell]
    exact ENNReal.one_ne_top
  have hkernel : ∀ x : Site d, IntegrableOn (fun v => ‖v - c‖ ^ (1 - (d : ℝ))) (cell x) :=
    fun x => (integrableOn_and_setIntegral_le hd1 (measurableSet_cell x) (hcellfin x) c).1
  -- the near terms
  have hnear : ∑ x ∈ F.filter (fun x => euclidNorm (x - y) ≤ 8 * Real.sqrt d),
      |∫ v in cell x, inner ℝ (ξ x - gradient (gauge K) v) (newtonField (v - c))| ≤ Cn := by
    set Fn := F.filter (fun x => euclidNorm (x - y) ≤ 8 * Real.sqrt d) with hFn
    have hterm : ∀ x ∈ Fn,
        |∫ v in cell x, inner ℝ (ξ x - gradient (gauge K) v) (newtonField (v - c))| ≤
          ∫ v in cell x, 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)) := by
      intro x _
      refine abs_setIntegral_inner_newtonField_le hd (measurableSet_cell x) c
        ((hkernel x).const_mul _) fun v _ => ?_
      exact mul_le_mul_of_nonneg_right (hgb x v) (Real.rpow_nonneg (norm_nonneg _) _)
    have hball : IntegrableOn (fun v => 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)))
        (Metric.ball c (9 * Real.sqrt d)) :=
      (integrableOn_ball_and_integral_eq hd1 c
        (by positivity : (0 : ℝ) < 9 * Real.sqrt d)).1.const_mul _
    have hsub : (⋃ x ∈ Fn, cell x) ⊆ Metric.ball c (9 * Real.sqrt d) := by
      intro v hv
      obtain ⟨x, hx, hvx⟩ := Set.mem_iUnion₂.mp hv
      have hxn : euclidNorm (x - y) ≤ 8 * Real.sqrt d := (Finset.mem_filter.mp hx).2
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 := norm_sub_toSpace_le_of_mem_cell hvx
      have hxy : ‖toSpace x - c‖ = euclidNorm (x - y) := by rw [hc, ← toSpace_sub, norm_toSpace]
      calc ‖v - c‖ = ‖(v - toSpace x) + (toSpace x - c)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖v - toSpace x‖ + ‖toSpace x - c‖ := norm_add_le _ _
        _ < 9 * Real.sqrt d := by rw [hxy]; linarith
    calc ∑ x ∈ Fn, |∫ v in cell x, inner ℝ (ξ x - gradient (gauge K) v) (newtonField (v - c))|
        ≤ ∑ x ∈ Fn, ∫ v in cell x, 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)) := Finset.sum_le_sum hterm
      _ = ∫ v in ⋃ x ∈ Fn, cell x, 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)) :=
          (integral_biUnion_finset Fn (fun x _ => measurableSet_cell x)
            (fun x _ y _ hxy => cell_disjoint hxy) (fun x _ => (hkernel x).const_mul _)).symm
      _ ≤ ∫ v in Metric.ball c (9 * Real.sqrt d), 2 * Λ * ‖v - c‖ ^ (1 - (d : ℝ)) :=
          setIntegral_mono_set hball
            (Eventually.of_forall fun v =>
              mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _))
            hsub.eventuallyLE
      _ = Cn := by
          rw [integral_const_mul,
            (integrableOn_ball_and_integral_eq hd1 c (by positivity : (0 : ℝ) < 9 * Real.sqrt d)).2]
  -- the far terms
  have hfar : ∑ x ∈ F.filter (fun x => ¬ euclidNorm (x - y) ≤ 8 * Real.sqrt d),
      |∫ v in cell x, inner ℝ (ξ x - gradient (gauge K) v) (newtonField (v - c))| ≤
        Cf * Real.log (R' + 2) := by
    set Ff := F.filter (fun x => ¬ euclidNorm (x - y) ≤ 8 * Real.sqrt d) with hFf
    have hFf' : ∀ x ∈ Ff, 8 * Real.sqrt d < euclidNorm (x - y) ∧ euclidNorm (x - y) ≤ R' := by
      intro x hx
      obtain ⟨hxF, hxn⟩ := Finset.mem_filter.mp hx
      exact ⟨not_le.mp hxn, hF x hxF⟩
    have hterm : ∀ x ∈ Ff,
        |∫ v in cell x, inner ℝ (ξ x - gradient (gauge K) v) (newtonField (v - c))| ≤
          2 ^ (d - 1) * Cc * ((euclidNorm (x - y) ^ (d - 1))⁻¹ *
            (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal) := by
      intro x hx
      obtain ⟨h8, hR⟩ := hFf' x hx
      have hρ : 0 < euclidNorm (x - y) := by linarith
      set ρ := euclidNorm (x - y) with hρdef
      have hK : (0 : ℝ) ≤ 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ := by positivity
      have hpt : ∀ v ∈ cell x, ‖ξ x - gradient (gauge K) v‖ * ‖v - c‖ ^ (1 - (d : ℝ)) ≤
          (2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹) * ‖gradient (gauge K) v - ξ x‖ := by
        intro v hv
        have hvx := norm_sub_toSpace_le_of_mem_cell hv
        have hxy : ‖toSpace x - c‖ = ρ := by rw [hc, ← toSpace_sub, norm_toSpace]
        have hvc : ρ / 2 ≤ ‖v - c‖ := by
          have h1 : ‖toSpace x - c‖ ≤ ‖toSpace x - v‖ + ‖v - c‖ := by
            calc ‖toSpace x - c‖ = ‖(toSpace x - v) + (v - c)‖ := by rw [sub_add_sub_cancel]
              _ ≤ _ := norm_add_le _ _
          rw [norm_sub_rev (toSpace x) v] at h1
          linarith
        have hvcpos : 0 < ‖v - c‖ := by linarith
        rw [rpow_one_sub_eq_inv_pow hvcpos hd1, norm_sub_rev (ξ x)]
        have h2 : (‖v - c‖ ^ (d - 1))⁻¹ ≤ 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ := by
          have h3 : (ρ / 2) ^ (d - 1) ≤ ‖v - c‖ ^ (d - 1) := pow_le_pow_left₀ (by positivity) hvc _
          calc (‖v - c‖ ^ (d - 1))⁻¹ ≤ ((ρ / 2) ^ (d - 1))⁻¹ := inv_anti₀ (by positivity) h3
            _ = 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ := by
                rw [div_pow, inv_div, div_eq_mul_inv]
        calc ‖gradient (gauge K) v - ξ x‖ * (‖v - c‖ ^ (d - 1))⁻¹
            ≤ ‖gradient (gauge K) v - ξ x‖ * (2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = _ := by ring
      have hI : IntegrableOn
          (fun v => (2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹) * ‖gradient (gauge K) v - ξ x‖)
          (cell x) := by
        refine Integrable.const_mul ?_ _
        refine IntegrableOn.of_bound (hcellfin x).lt_top (hgmeas x).aestronglyMeasurable (2 * Λ) ?_
        refine (ae_restrict_iff' (measurableSet_cell x)).mpr (Eventually.of_forall fun v _ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_sub_rev]
        exact hgb x v
      have habs := abs_setIntegral_inner_newtonField_le hd (measurableSet_cell x) c hI hpt
      rw [integral_const_mul] at habs
      have hIx : ∫ v in cell x, ‖gradient (gauge K) v - ξ x‖ ≤
          Cc * (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal := by
        have h := (ENNReal.ofReal_le_iff_le_toReal
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)).mp (hcell x)
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCc] at h
      refine habs.trans ?_
      calc 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ * ∫ v in cell x, ‖gradient (gauge K) v - ξ x‖
          ≤ 2 ^ (d - 1) * (ρ ^ (d - 1))⁻¹ *
            (Cc * (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal) :=
            mul_le_mul_of_nonneg_left hIx hK
        _ = _ := by ring
    have hsum := sum_far_real_le hd hmfin hKg y hgrowth Ff hFf'
    have hlogc := natLog_ceil_add_one_le hR'
    calc ∑ x ∈ Ff, |∫ v in cell x, inner ℝ (ξ x - gradient (gauge K) v) (newtonField (v - c))|
        ≤ ∑ x ∈ Ff, 2 ^ (d - 1) * Cc * ((euclidNorm (x - y) ^ (d - 1))⁻¹ *
            (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal) := Finset.sum_le_sum hterm
      _ = 2 ^ (d - 1) * Cc * ∑ x ∈ Ff, (euclidNorm (x - y) ^ (d - 1))⁻¹ *
            (m (Metric.ball (toSpace x) (6 * Real.sqrt d))).toReal := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 ^ (d - 1) * Cc * (((Nat.log 2 ⌈R'⌉₊ + 1 : ℕ) : ℝ) * (Nr * Kg * 4 ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 2 ^ (d - 1) * Cc *
          (((1 + 1 / Real.log 2) * Real.log (R' + 2)) * (Nr * Kg * 4 ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlogc (by positivity)) (by positivity)
      _ = Cf * Real.log (R' + 2) := by rw [hCf]; ring
  calc _ ≤ Cn + Cf * Real.log (R' + 2) := add_le_add hnear hfar
    _ ≤ (Cn + Cf) * Real.log (R' + 2) := by nlinarith

end Direction

end DirectionReplacement

/-! ### The discretization of the potential -/

section SourceSum

open MeasureTheory LatticeProb CERW CERW.Support.Law CERW.Generic.Kernel CERW.Support.Occupation
open CERW.Support.LocalTime CERW.Generic.Lattice

variable {d : ℕ}

/-- For a measurable field `g` with `‖g‖ ≤ Λ`, `v ↦ ⟪g v, K(v - z)⟫` is integrable on a measurable
set of finite volume. -/
private lemma integrableOn_inner_field_newtonField (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hgb : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (z : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (g v) (newtonField (v - z))) D volume := by
  have hbase : IntegrableOn (fun v => ‖v - z‖ ^ (1 - (d : ℝ))) D volume :=
    (integrableOn_and_setIntegral_le (d := d) (by omega : 1 ≤ d) hD hDfin z).1
  have hmeas : Measurable
      (fun v : EuclideanSpace ℝ (Fin d) => inner ℝ (g v) (newtonField (v - z))) :=
    hg.inner (measurable_newtonField.comp (measurable_id.sub measurable_const))
  refine (hbase.const_mul Λ).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with v
  calc ‖inner ℝ (g v) (newtonField (v - z))‖ ≤ ‖g v‖ * ‖newtonField (v - z)‖ :=
        norm_inner_le_norm _ _
    _ = ‖g v‖ * ‖v - z‖ ^ (1 - (d : ℝ)) := by rw [norm_newtonField hd]
    _ ≤ Λ * ‖v - z‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (hgb v) (Real.rpow_nonneg (norm_nonneg _) _)

/-- **The discretization of the potential.** The source sum of `eq:dynkin` for the walk with drift
field `ξ`, a choice of subgradients of the gauge `ψ_K`, differs from the potential `U_D(y)` of the
cell set `D` by `O(ε log(R' + 2))`: the gradient is replaced by the Newtonian field, the kernel
value by its cell integral, and the lattice drift `ξ(x)` by the gradient `∇ψ_K(v)` on the cell
(`lem:cell` for the gauge, `gauge_cell_gradient`, with the growth of its distributional
Laplacian). -/
theorem gauge_abs_source_sum_sub_normPotential_le (hd : 2 ≤ d) {b : Site d → ℝ}
    {Ca R Cg : ℝ}
    (hR : 1 ≤ R)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ) (y : Site d) (R' : ℝ), 1 ≤ R' →
      (∀ x ∈ departureRange X n, euclidNorm (x - y) ≤ R') →
        |ε * ∑ x ∈ departureRange X n, inner ℝ (ξ x) (centralDiff b (x - y)) -
            normPotential d ε (gauge K) (cellSet X n) (toSpace y)| ≤ C * ε * Real.log (R' + 2) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Ca', hCa'_nonneg, hCa⟩ :=
    exists_sum_norm_centralDiff_sub_newtonField_le (d := d) hd hR hgradA hgrad
  obtain ⟨Cb, hCb_nonneg, hCb⟩ := exists_sum_abs_newtonField_sub_setIntegral_le (d := d) hd
  obtain ⟨Cc, hCc0, hcellC⟩ := gauge_cell_gradient hd
  obtain ⟨m, hmfin, hlap⟩ := exists_isDistribLaplacian_gauge hK hc h0
  obtain ⟨Kgen, hKgen, hgrowth⟩ := measure_ball_le_gauge hd1
  have hΛ : 0 ≤ normMax (gauge K) := normMax_gauge_nonneg K
  set Λ := normMax (gauge K) with hΛdef
  obtain ⟨Cdir, hCdir0, hCdir⟩ := gauge_sum_abs_setIntegral_sub_gradient_le hd hK hc h0 hmfin
    (Cc := Cc) (Kg := Kgen * Λ) hCc0.le (mul_nonneg hKgen hΛ)
  have hω := unitBallVolume_pos d
  have hcoef : 0 ≤ 2 / unitBallVolume d := le_of_lt (div_pos (by norm_num) hω)
  refine ⟨Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir), ?_, ?_⟩
  · positivity
  · intro ε hε ξ hξ hξ0 X n y R' hR' hcellR
    have hξΛ := norm_selection_le hK h0 hξ hξ0
    have hcellξ : ∀ x : Site d, ENNReal.ofReal (∫ v in cell x, ‖gradient (gauge K) v - ξ x‖) ≤
        ENNReal.ofReal Cc * m (Metric.ball (toSpace x) (6 * Real.sqrt d)) :=
      hcellC hK hc h0 ξ hξ hξ0 m hmfin hlap
    set S0 : ℝ := ∑ x ∈ departureRange X n, inner ℝ (ξ x) (centralDiff b (x - y)) with hS0
    set S1 : ℝ := ∑ x ∈ departureRange X n,
      inner ℝ (ξ x) (newtonField (toSpace x - toSpace y)) with hS1
    set S2 : ℝ := ∑ x ∈ departureRange X n,
      ∫ v in cell x, inner ℝ (ξ x) (newtonField (v - toSpace y)) with hS2
    set S3 : ℝ := ∑ x ∈ departureRange X n,
      ∫ v in cell x, inner ℝ (gradient (gauge K) v) (newtonField (v - toSpace y)) with hS3
    have hcellmeas : ∀ x : Site d, MeasurableSet (cell x) := measurableSet_cell
    have hcellfin : ∀ x : Site d, volume (cell x) ≠ ⊤ := fun x => by
      rw [volume_cell]
      exact ENNReal.one_ne_top
    have hint_xi : ∀ x : Site d, IntegrableOn
        (fun v => inner ℝ (ξ x) (newtonField (v - toSpace y))) (cell x) volume := fun x =>
      integrableOn_inner_field_newtonField hd (g := fun _ => ξ x) measurable_const
        (fun _ => hξΛ x) (hcellmeas x) (hcellfin x) (toSpace y)
    have hint_grad : ∀ x : Site d, IntegrableOn
        (fun v => inner ℝ (gradient (gauge K) v) (newtonField (v - toSpace y))) (cell x) volume :=
      fun x => (CERW.Support.Norm.GaugePotential.integrableOn_potentialIntegrand_gauge hd1 hK hc
        h0 (hcellmeas x) (hcellfin x) (toSpace y)).congr_fun
        (fun v _ => (inner_newtonField (gradient (gauge K) v) (v - toSpace y)).symm)
        (hcellmeas x)
    have h1 : |S0 - (2 / unitBallVolume d) * S1| ≤ Λ * Ca' * Real.log (R' + 2) := by
      have hsum := hCa (departureRange X n) y R' hR' hcellR
      have hrew : S0 - (2 / unitBallVolume d) * S1 =
          ∑ x ∈ departureRange X n, inner ℝ (ξ x)
            (centralDiff b (x - y) -
              (2 / unitBallVolume d) • newtonField (toSpace (x - y))) := by
        rw [hS0, hS1, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [inner_sub_right, inner_smul_right, toSpace_sub]
      rw [hrew]
      calc |∑ x ∈ departureRange X n, inner ℝ (ξ x)
              (centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace (x - y)))|
          ≤ ∑ x ∈ departureRange X n, ‖inner ℝ (ξ x)
              (centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace (x - y)))‖ :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x ∈ departureRange X n, Λ *
              ‖centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖ := by
            apply Finset.sum_le_sum
            intro x _
            calc ‖inner ℝ (ξ x)
                    (centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace (x - y)))‖
                ≤ ‖ξ x‖ * ‖centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖ :=
                  norm_inner_le_norm _ _
              _ ≤ Λ * ‖centralDiff b (x - y) -
                      (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖ :=
                  mul_le_mul_of_nonneg_right (hξΛ x) (norm_nonneg _)
        _ = Λ * ∑ x ∈ departureRange X n,
              ‖centralDiff b (x - y) -
                (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖ := by
            rw [Finset.mul_sum]
        _ ≤ Λ * (Ca' * Real.log (R' + 2)) := mul_le_mul_of_nonneg_left hsum hΛ
        _ = Λ * Ca' * Real.log (R' + 2) := by ring
    have h2 : |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| ≤
        (2 / unitBallVolume d) * ((Λ + 1) * Cb) * Real.log (R' + 2) := by
      have hΛ1 : 0 < Λ + 1 := by linarith
      have hsum := hCb (departureRange X n) (fun x => (Λ + 1)⁻¹ • ξ x) y R' hR'
        (fun x => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ1)]
          calc (Λ + 1)⁻¹ * ‖ξ x‖ ≤ (Λ + 1)⁻¹ * (Λ + 1) :=
                mul_le_mul_of_nonneg_left ((hξΛ x).trans (by linarith)) (inv_pos.mpr hΛ1).le
            _ = 1 := inv_mul_cancel₀ hΛ1.ne')
        hcellR
      have hterm : ∀ x ∈ departureRange X n,
          |inner ℝ (ξ x) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ (ξ x) (newtonField (v - toSpace y))| =
            (Λ + 1) * |inner ℝ ((Λ + 1)⁻¹ • ξ x) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ ((Λ + 1)⁻¹ • ξ x) (newtonField (v - toSpace y))| := by
        intro x _
        simp_rw [inner_smul_left, RCLike.conj_to_real]
        rw [integral_const_mul, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hΛ1), ← mul_assoc,
          mul_inv_cancel₀ hΛ1.ne', one_mul]
      have hrew : S1 - S2 =
          ∑ x ∈ departureRange X n,
            (inner ℝ (ξ x) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ (ξ x) (newtonField (v - toSpace y))) := by
        rw [hS1, hS2, ← Finset.sum_sub_distrib]
      have htri : |S1 - S2| ≤
          (Λ + 1) * ∑ x ∈ departureRange X n,
            |inner ℝ ((Λ + 1)⁻¹ • ξ x) (newtonField (toSpace x - toSpace y)) -
              ∫ v in cell x, inner ℝ ((Λ + 1)⁻¹ • ξ x) (newtonField (v - toSpace y))| := by
        rw [hrew, Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl hterm
      calc |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2|
          = (2 / unitBallVolume d) * |S1 - S2| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hcoef]
        _ ≤ (2 / unitBallVolume d) * ((Λ + 1) * (Cb * Real.log (R' + 2))) :=
            mul_le_mul_of_nonneg_left (htri.trans (mul_le_mul_of_nonneg_left hsum hΛ1.le)) hcoef
        _ = (2 / unitBallVolume d) * ((Λ + 1) * Cb) * Real.log (R' + 2) := by ring
    have h3 : |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| ≤
        (2 / unitBallVolume d) * Cdir * Real.log (R' + 2) := by
      have hsum := hCdir ξ hξΛ hcellξ (departureRange X n) y R' hR' hcellR
        (fun {R} hR => by
          simpa [hΛdef] using hgrowth hK hc h0 hmfin hlap (toSpace y) hR)
      have hrew : S2 - S3 =
          ∑ x ∈ departureRange X n,
            ∫ v in cell x,
              inner ℝ (ξ x - gradient (gauge K) v) (newtonField (v - toSpace y)) := by
        rw [hS2, hS3, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        rw [← integral_sub (hint_xi x) (hint_grad x)]
        exact setIntegral_congr_fun (hcellmeas x) (fun v _ => by rw [inner_sub_left])
      have htri : |S2 - S3| ≤
          ∑ x ∈ departureRange X n,
            |∫ v in cell x,
              inner ℝ (ξ x - gradient (gauge K) v) (newtonField (v - toSpace y))| := by
        rw [hrew]
        exact Finset.abs_sum_le_sum_abs _ _
      calc |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3|
          = (2 / unitBallVolume d) * |S2 - S3| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hcoef]
        _ ≤ (2 / unitBallVolume d) * (Cdir * Real.log (R' + 2)) :=
            mul_le_mul_of_nonneg_left (htri.trans hsum) hcoef
        _ = (2 / unitBallVolume d) * Cdir * Real.log (R' + 2) := by ring
    have hmain : |S0 - (2 / unitBallVolume d) * S3| ≤
        (Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir)) * Real.log (R' + 2) := by
      have htri : |S0 - (2 / unitBallVolume d) * S3| ≤
          |S0 - (2 / unitBallVolume d) * S1| +
            |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| +
              |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| := by
        have heq : S0 - (2 / unitBallVolume d) * S3 =
            (S0 - (2 / unitBallVolume d) * S1) +
              ((2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2) +
                ((2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3) := by ring
        rw [heq]
        calc |(S0 - (2 / unitBallVolume d) * S1) +
                ((2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2) +
                  ((2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3)|
            ≤ |(S0 - (2 / unitBallVolume d) * S1) +
                  ((2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2)| +
                |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| :=
              abs_add_le _ _
          _ ≤ (|S0 - (2 / unitBallVolume d) * S1| +
                  |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2|) +
                |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| :=
              add_le_add (abs_add_le _ _) le_rfl
          _ = _ := by ring
      calc |S0 - (2 / unitBallVolume d) * S3|
          ≤ |S0 - (2 / unitBallVolume d) * S1| +
              |(2 / unitBallVolume d) * S1 - (2 / unitBallVolume d) * S2| +
                |(2 / unitBallVolume d) * S2 - (2 / unitBallVolume d) * S3| := htri
        _ ≤ Λ * Ca' * Real.log (R' + 2) +
              (2 / unitBallVolume d) * ((Λ + 1) * Cb) * Real.log (R' + 2) +
                (2 / unitBallVolume d) * Cdir * Real.log (R' + 2) :=
            add_le_add (add_le_add h1 h2) h3
        _ = (Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir)) * Real.log (R' + 2) := by
            ring
    have hpot : normPotential d ε (gauge K) (cellSet X n) (toSpace y) =
        ε * ((2 / unitBallVolume d) * S3) := by
      have hD3 : ∫ v in cellSet X n, inner ℝ (gradient (gauge K) v) (newtonField (v - toSpace y))
          = S3 := by
        rw [hS3, cellSet]
        exact integral_biUnion_finset (departureRange X n) (fun x _ => hcellmeas x)
          (fun x _ y _ hxy => cell_disjoint hxy) (fun x _ => hint_grad x)
      have hcongr : ∫ v in cellSet X n,
            inner ℝ (gradient (gauge K) v) (v - toSpace y) / ‖v - toSpace y‖ ^ d
          = ∫ v in cellSet X n,
            inner ℝ (gradient (gauge K) v) (newtonField (v - toSpace y)) := by
        exact setIntegral_congr_fun (measurableSet_cellSet X n)
          (fun v _ => (inner_newtonField (gradient (gauge K) v) (v - toSpace y)).symm)
      rw [normPotential, hcongr, hD3]
      ring
    calc |ε * S0 - normPotential d ε (gauge K) (cellSet X n) (toSpace y)|
        = |ε * S0 - ε * ((2 / unitBallVolume d) * S3)| := by rw [hpot]
      _ = ε * |S0 - (2 / unitBallVolume d) * S3| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hε]
      _ ≤ ε * ((Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir)) *
            Real.log (R' + 2)) := mul_le_mul_of_nonneg_left hmain hε
      _ = (Λ * Ca' + (2 / unitBallVolume d) * ((Λ + 1) * Cb + Cdir)) * ε *
            Real.log (R' + 2) := by ring


end SourceSum

/-! ### Consumption at bodies that are not symmetric -/

section Consumption

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- **The cell estimate and the Laplacian measure of a convex body, together.** For a compact convex
`K ⊆ ℝ^d`, `d ≥ 2`, with the origin in its interior there is a locally finite measure `m` that is
the distributional Laplacian of `ψ_K`, charges every ball about the origin, has the growth
`m(B(y, R)) ≤ Kg R^{d-1}` at every site, and satisfies the cell estimate
`∫_{C_x} |∇ψ_K - ξ(x)| ≤ C m(B(x, 6 √d))` for every choice of subgradients. -/
theorem gauge_laplacian_cell_package (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m ∧
      CERW.IsDistribLaplacian (gauge K) m ∧
      (∀ {ρ : ℝ}, 0 < ρ → 0 < m (Metric.ball 0 ρ)) ∧
      (∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (y : Site d) {R : ℝ}, 0 < R →
        m (Metric.ball (CERW.toSpace y) R) ≤ ENNReal.ofReal (Kg * R ^ (d - 1))) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient (gauge K) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ x : Site d,
          ENNReal.ofReal (∫ v in CERW.cell x, ‖gradient (gauge K) v - ξ x‖)
            ≤ ENNReal.ofReal C * m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨m, hm, hlap, Kg, hKg, hgrowth⟩ := exists_isDistribLaplacian_gauge_growth hd1 hK hc h0
  obtain ⟨C, hC, hcell⟩ := gauge_cell_gradient hd
  refine ⟨m, hm, hlap, fun {ρ} hρ => ?_, ⟨Kg, hKg, hgrowth⟩, C, hC,
    fun ξ hξ hξ0 x => hcell hK hc h0 ξ hξ hξ0 m hm hlap x⟩
  have hlow := measure_ball_ge_gauge hd1 hK hc h0 hm hlap hρ
  refine lt_of_lt_of_le (ENNReal.ofReal_pos.mpr ?_) hlow
  obtain ⟨hcpos, -⟩ := normMin_gauge_pos_mul_le hK h0 hd1
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  positivity


/-- **Consumption at the non-even planar body `cutDisc`.** The gauge of `cutDisc` is not a norm; its
distributional Laplacian is a locally finite measure that charges every ball about the origin and
satisfies the cell estimate for every choice of subgradients. -/
theorem cutDisc_laplacian_cell :
    ¬ CERW.IsNorm (gauge cutDisc) ∧
    ∃ m : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m ∧
      CERW.IsDistribLaplacian (gauge cutDisc) m ∧
      (∀ {ρ : ℝ}, 0 < ρ → 0 < m (Metric.ball 0 ρ)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 → CERW.IsSubgradient (gauge cutDisc) (CERW.toSpace x) (ξ x)) →
          ξ 0 = 0 → ∀ x : Site 2,
          ENNReal.ofReal (∫ v in CERW.cell x, ‖gradient (gauge cutDisc) v - ξ x‖)
            ≤ ENNReal.ofReal C *
              m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt ((2 : ℕ) : ℝ))) := by
  obtain ⟨m, hm, hlap, hpos, -, C, hC, hcell⟩ := gauge_laplacian_cell_package (d := 2) (le_refl 2)
    isCompact_cutDisc convex_cutDisc zero_mem_interior_cutDisc
  exact ⟨not_isNorm_gauge_cutDisc, m, hm, hlap, hpos, C, hC, hcell⟩

/-- **Consumption at a body with corners.** The gauge of the triangle `cornerTriangle` with vertices
`(-1,-1)`, `(2,-1)`, `(-1,2)` is not differentiable at the vertex direction `(-1,-1)`, so its
gradient exists only almost everywhere, and it is not even; its distributional Laplacian is a
locally finite measure that charges every ball about the origin and satisfies the cell estimate for
every choice of subgradients. -/
theorem cornerTriangle_laplacian_cell :
    ¬ DifferentiableAt ℝ (gauge GaugePotential.cornerTriangle)
        (-CERW.coordVec 0 - CERW.coordVec 1) ∧
    ∃ m : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m ∧
      CERW.IsDistribLaplacian (gauge GaugePotential.cornerTriangle) m ∧
      (∀ {ρ : ℝ}, 0 < ρ → 0 < m (Metric.ball 0 ρ)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 →
          CERW.IsSubgradient (gauge GaugePotential.cornerTriangle) (CERW.toSpace x) (ξ x)) →
          ξ 0 = 0 → ∀ x : Site 2,
          ENNReal.ofReal (∫ v in CERW.cell x,
              ‖gradient (gauge GaugePotential.cornerTriangle) v - ξ x‖)
            ≤ ENNReal.ofReal C *
              m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt ((2 : ℕ) : ℝ))) := by
  obtain ⟨m, hm, hlap, hpos, -, C, hC, hcell⟩ := gauge_laplacian_cell_package (d := 2) (le_refl 2)
    GaugePotential.isCompact_cornerTriangle GaugePotential.convex_cornerTriangle
    GaugePotential.zero_mem_interior_cornerTriangle
  exact ⟨GaugePotential.not_differentiableAt_gauge_cornerTriangle, m, hm, hlap, hpos, C, hC, hcell⟩

end Consumption

end CERW.Support.Norm.GaugeCellGradient
