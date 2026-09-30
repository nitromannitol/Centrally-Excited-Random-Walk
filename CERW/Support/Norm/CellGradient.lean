import CERW.Support.Statements
import CERW.Generic.Norm
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellVolume

/-!
# The gradient of a norm on a cell

Lemma `lem:cell` of the paper: for a norm `Ψ` with distributional Laplacian `m`, a subgradient
`ξ(x)` at the lattice site `x` (and `ξ(0) = 0`), the cell `C_x` satisfies
`∫_{C_x} |∇Ψ - ξ(x)| ≤ C m(B(x, 6 √d))`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal ContDiff
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

open CERW.Support.Statements

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

/-- A norm is convex along segments. -/
private lemma norm_segment_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    (x y : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ψ ((1 - t) • x + t • y) ≤ (1 - t) * Ψ x + t * Ψ y := by
  calc Ψ ((1 - t) • x + t • y) ≤ Ψ ((1 - t) • x) + Ψ (t • y) := hΨ.add_le _ _
    _ = (1 - t) * Ψ x + t * Ψ y := by
        rw [hΨ.smul, hΨ.smul, abs_of_nonneg ht0, abs_of_nonneg (by linarith)]

/-- The norm recentred at a subgradient, `H(u) = Ψ(x + u) - Ψ(x) - ξ · u`, is convex along rays
through the origin: `H(t u) ≤ t H(u)` for `t ∈ [0, 1]`. -/
private lemma recentred_ray_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    (x ξ u : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ψ (x + t • u) - Ψ x - inner ℝ ξ (t • u) ≤ t * (Ψ (x + u) - Ψ x - inner ℝ ξ u) := by
  have h := norm_segment_le hΨ x (x + u) ht0 ht1
  have hx : (1 - t) • x + t • (x + u) = x + t • u := by module
  rw [hx] at h
  rw [real_inner_smul_right]
  nlinarith

/-- The weak mass bound: for a norm `Ψ` with distributional Laplacian `m`, a subgradient `ξ` at
`x` and a smooth cut-off profile `b`,
`∫ (Ψ(x + u) - Ψ(x) - ξ · u) b(|u|²) du ≤ ∫ φ dm`. -/
private lemma weak_mass_bound {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {x ξ : EuclideanSpace ℝ (Fin d)} {m : Measure (EuclideanSpace ℝ (Fin d))}
    (hm : CERW.IsDistribLaplacian Ψ m) {a r : ℝ} {b : ℝ → ℝ} (hb : Cutoff a r b) (hr : 0 ≤ r) :
    ∫ u, (Ψ (x + u) - Ψ x - inner ℝ ξ u) * b (‖u‖ ^ 2) ≤ ∫ v, testFn b r x v ∂m := by
  set H : EuclideanSpace ℝ (Fin d) → ℝ := fun u => Ψ (x + u) - Ψ x - inner ℝ ξ u with hH
  have hΨc : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
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

/-- At a point of differentiability, the gradient of a norm differs from a subgradient at `x` by
at most the sum of the excesses at the `2d` neighbours of the point. -/
private lemma norm_gradient_sub_le_sum {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {x ξ v : EuclideanSpace ℝ (Fin d)} (hξ : CERW.IsSubgradient Ψ x ξ)
    (hv : DifferentiableAt ℝ Ψ v) :
    ‖gradient Ψ v - ξ‖ ≤ ∑ i : Fin d, (excess Ψ x ξ (v + CERW.coordVec i) +
      excess Ψ x ξ (v - CERW.coordVec i)) := by
  have hsub := CERW.Generic.Norm.gradient_isSubgradient hΨ hv
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
the integral of the excess over the ball of radius `2 √d` about the site. -/
private lemma cell_integral_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    (hd : 1 ≤ d) {ξ : EuclideanSpace ℝ (Fin d)} (x : Site d)
    (hξ : CERW.IsSubgradient Ψ (CERW.toSpace x) ξ) :
    ∫ v in CERW.cell x, ‖gradient Ψ v - ξ‖ ≤
      2 * d * ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d),
        excess Ψ (CERW.toSpace x) ξ v := by
  set f : EuclideanSpace ℝ (Fin d) → ℝ := excess Ψ (CERW.toSpace x) ξ with hf
  have hfc : Continuous f := continuous_excess (CERW.Generic.Norm.norm_continuous hΨ) _ _
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
    filter_upwards [CERW.Generic.Norm.ae_differentiableAt hΨ] with v hv
    exact norm_gradient_sub_le_sum hΨ hξ hv
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

/-- The integral of the excess of a norm over a ball is bounded by the mass of its distributional
Laplacian on a larger ball. -/
private lemma ball_excess_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {x ξ : EuclideanSpace ℝ (Fin d)} (hξ : CERW.IsSubgradient Ψ x ξ)
    {m : Measure (EuclideanSpace ℝ (Fin d))} [IsLocallyFiniteMeasure m]
    (hm : CERW.IsDistribLaplacian Ψ m) {a r ρ : ℝ} (ha : 0 ≤ a) (har : a < r) (hrρ : r < ρ) :
    ∫ v in Metric.ball x a, excess Ψ x ξ v ≤ r ^ 2 / 2 * (m (Metric.ball x ρ)).toReal := by
  obtain ⟨b, hb⟩ := exists_cutoff ha har
  have hr : 0 ≤ r := ha.trans har.le
  have hΨc : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
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
  have h2 := weak_mass_bound (x := x) (ξ := ξ) hΨ hm hb hr
  have h3 := integral_testFn_le hb hr hrρ x m
  calc ∫ v in Metric.ball x a, excess Ψ x ξ v ≤ ∫ u, excess Ψ x ξ (x + u) * b (‖u‖ ^ 2) := h1
    _ = ∫ u, (Ψ (x + u) - Ψ x - inner ℝ ξ u) * b (‖u‖ ^ 2) := by
        simp only [hshift]
    _ ≤ ∫ v, testFn b r x v ∂m := h2
    _ ≤ _ := h3

/-- Lemma `lem:cell`: the integral of `|∇Ψ - ξ(x)|` over the cell `C_x` is at most a constant
(depending only on `d`) times the mass of the distributional Laplacian of `Ψ` on `B(x, 6 √d)`. -/
theorem cell_gradient_holds : cell_gradient := by
  intro d hd
  refine ⟨16 * (d : ℝ) ^ 2, by positivity, ?_⟩
  intro Ψ hΨ ξ hξ hξ0 m hmloc hm x
  haveI := hmloc
  have hd1 : 1 ≤ d := by omega
  have hsub : CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x) := by
    by_cases hx : x = 0
    · subst hx
      have h0 : CERW.toSpace (0 : Site d) = 0 := by
        ext i
        simp
      rw [h0, hξ0]
      exact CERW.Generic.Norm.subgradient_zero hΨ
    · exact hξ x hx
  have hsqrt : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hd1
  have hcell := cell_integral_le hΨ hd1 x hsub
  have hball := ball_excess_le hΨ hsub hm (a := 2 * Real.sqrt d) (r := 4 * Real.sqrt d)
    (ρ := 6 * Real.sqrt d) (by linarith) (by linarith) (by linarith)
  have hfin : m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d)) < ⊤ := measure_ball_lt_top
  have hsq : (4 * Real.sqrt d) ^ 2 = 16 * (d : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    norm_num
  have hbound : ∫ v in CERW.cell x, ‖gradient Ψ v - ξ x‖ ≤
      16 * (d : ℝ) ^ 2 * (m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))).toReal := by
    rw [hsq] at hball
    calc ∫ v in CERW.cell x, ‖gradient Ψ v - ξ x‖
        ≤ 2 * d * ∫ v in Metric.ball (CERW.toSpace x) (2 * Real.sqrt d),
            excess Ψ (CERW.toSpace x) (ξ x) v := hcell
      _ ≤ 2 * d * (16 * (d : ℝ) / 2 *
            (m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))).toReal) :=
          mul_le_mul_of_nonneg_left hball (by positivity)
      _ = 16 * (d : ℝ) ^ 2 * (m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))).toReal := by
          ring
  calc ENNReal.ofReal (∫ v in CERW.cell x, ‖gradient Ψ v - ξ x‖)
      ≤ ENNReal.ofReal (16 * (d : ℝ) ^ 2 *
          (m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))).toReal) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (16 * (d : ℝ) ^ 2) *
          m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin.ne]

end CERW.Support.Norm
