import CERW.Support.Norm.GaugeModel
import CERW.Model.Laplacian
import CERW.Model.Potential
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Convex.Cone.Extension

/-!
# The positive distributional Laplacian of the gauge of a convex body

For a compact convex set `K ⊆ ℝ^d` with the origin in its interior, the Minkowski functional
`ψ_K = gauge K` is convex and positively homogeneous but need not be even. The distributional
Laplacian `μ` of `ψ_K`, `∫ φ dμ = ∫ ψ_K Δφ` for smooth compactly supported `φ`, is a positive
locally finite (Radon) measure, and it has the radial growth `μ(B(y, R)) ≤ C Λ_ψ R^{d-1}` used by
the weighted summation of the cell estimate. Here both facts are proved for the literal `gauge K`:

* the functional `φ ↦ ∫ ψ_K Δφ` is nonnegative on nonnegative smooth compactly supported functions,
  because second difference quotients of a convex function are nonnegative; it extends to a
  positive functional on the compactly supported continuous functions (M. Riesz) and is an integral
  against a locally finite measure (Riesz-Markov-Kakutani);
* the growth bound follows by testing against a dilated bump function and subtracting the tangent
  plane at the center, using only that a subgradient exists at every point, that `ψ_K` is
  `Λ_ψ`-Lipschitz and that subgradients have norm at most `Λ_ψ`.

No evenness is used and `IsNorm` does not occur: convexity, continuity, the Lipschitz bound and the
subgradient facts of `GaugeModel` are all that enter. The proofs are those of the symmetric case
(second differences, a Riesz extension, a tangent plane), with continuity and the midpoint
inequality `2 ψ(v) ≤ ψ(v + w) + ψ(v - w)` taking the place of the properties of a norm. The
file is consumed at the non-even planar body `cutDisc` with the walk of drift strength `1/4`.
-/

open Set Metric Topology MeasureTheory Filter
open scoped ContDiff CompactlySupported
open CompactlySupportedContinuousMap

namespace CERW.Support.Norm.GaugeLaplacian

open CERW LatticeProb CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel

variable {d : ℕ}

/-! ### Derivatives of test functions -/

/-- The second directional derivative `D²φ(v)(e, e)`. -/
private noncomputable def hess (φ : EuclideanSpace ℝ (Fin d) → ℝ) (v e : EuclideanSpace ℝ (Fin d)) :
    ℝ :=
  fderiv ℝ (fderiv ℝ φ) v e e

/-- `w ↦ D²φ(w)(e, e)` is continuous for smooth `φ`. -/
private lemma continuous_hess {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : EuclideanSpace ℝ (Fin d)) : Continuous (fun w => hess φ w e) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ φ)) := h1.continuous_fderiv one_ne_zero
  exact (h2.clm_apply continuous_const).clm_apply continuous_const

/-- `w ↦ D²φ(w)(e, e)` has compact support for `φ` of compact support. -/
private lemma hasCompactSupport_hess {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : HasCompactSupport φ) (e : EuclideanSpace ℝ (Fin d)) :
    HasCompactSupport (fun w => hess φ w e) := by
  have h1 := (hc.fderiv (𝕜 := ℝ)).fderiv_apply (𝕜 := ℝ) e
  exact h1.comp_left (g := fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => L e) (by simp)

/-- The Laplacian is the sum of the second derivatives along the standard basis. -/
private lemma laplacian_eq_sum_hess {φ : EuclideanSpace ℝ (Fin d) → ℝ} :
    Laplacian.laplacian φ =
      fun v => ∑ i : Fin d, hess φ v (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  have := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin d) ℝ)
  convert this using 2 with v
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [hess]

/-- A finite sum of compactly supported functions has compact support. -/
private lemma hasCompactSupport_sum {ι : Type*} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin d) → ℝ} (h : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact HasCompactSupport.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The Laplacian of a smooth compactly supported function is continuous. -/
private lemma continuous_laplacian {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (Laplacian.laplacian φ) := by
  rw [laplacian_eq_sum_hess]
  exact continuous_finsetSum _ fun i _ => continuous_hess hφ _

/-- The Laplacian of a compactly supported function has compact support. -/
private lemma hasCompactSupport_laplacian {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : HasCompactSupport φ) : HasCompactSupport (Laplacian.laplacian φ) := by
  rw [laplacian_eq_sum_hess]
  exact hasCompactSupport_sum _ fun i _ => hasCompactSupport_hess hc _

/-- The integral of a directional derivative of a `C¹` compactly supported function vanishes. -/
private lemma integral_fderiv_apply_eq_zero {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (e : EuclideanSpace ℝ (Fin d)) :
    ∫ x, fderiv ℝ ψ x e = 0 := by
  have hcont : Continuous fun x => fderiv ℝ ψ x e :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ)) (g := ψ) (v := e) (by simp)
    (by simpa using Continuous.integrable_of_hasCompactSupport hcont (hc.fderiv_apply (𝕜 := ℝ) e))
    (by simpa using Continuous.integrable_of_hasCompactSupport hψ.continuous hc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hψ.differentiable one_ne_zero) x)
  simpa using this

/-- The derivative of the first derivative `x ↦ Dφ(x) e` in the direction `e` is `D²φ(x)(e, e)`. -/
private lemma hasFDerivAt_fderiv_apply {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun x => fderiv ℝ φ x e)
      ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ φ) x)) x := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero) x
  exact (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp x hdd.hasFDerivAt

/-- An affine function integrates to zero against a second derivative of a compactly supported
function: `∫ (a + ⟨ξ, x⟩) D²φ(x)(e, e) dx = 0`. -/
private lemma integral_affine_mul_hess {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (a : ℝ) (ξ e : EuclideanSpace ℝ (Fin d)) :
    ∫ x, (a + inner ℝ ξ x) * hess φ x e = 0 := by
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => fderiv ℝ φ x e with hg
  have hgc : Continuous g :=
    ((hφ.fderiv_right (m := 1) (by norm_cast)).continuous).clm_apply continuous_const
  have hgs : HasCompactSupport g := hc.fderiv_apply (𝕜 := ℝ) e
  have hgd : ∀ x, HasFDerivAt g
      ((ContinuousLinearMap.apply ℝ ℝ e).comp (fderiv ℝ (fderiv ℝ φ) x)) x :=
    fun x => hasFDerivAt_fderiv_apply hφ e x
  have hf : ∀ x, HasFDerivAt (fun x : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ x)
      (innerSL ℝ ξ) x :=
    fun x => (innerSL ℝ ξ).hasFDerivAt.const_add a
  have hfc : Continuous fun x : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ x := by fun_prop
  have hgd' : ∀ x, fderiv ℝ g x e = hess φ x e := by
    intro x
    rw [(hgd x).fderiv]
    simp [hess]
  have hfd' : ∀ x, fderiv ℝ (fun x : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ x) x e =
      inner ℝ ξ e := by
    intro x
    rw [(hf x).fderiv]
    simp
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun x : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ x) (g := g) (v := e)
    (by
      simp_rw [hfd']
      exact (continuous_const.mul hgc).integrable_of_hasCompactSupport hgs.mul_left)
    (by
      simp_rw [hgd']
      exact (hfc.mul (continuous_hess hφ e)).integrable_of_hasCompactSupport
        (hasCompactSupport_hess hc e).mul_left)
    ((hfc.mul hgc).integrable_of_hasCompactSupport hgs.mul_left)
    (fun x _ => (hf x).differentiableAt) (fun x _ => (hgd x).differentiableAt)
  simp_rw [hgd', hfd'] at hibp
  rw [hibp, integral_const_mul]
  have h0 : ∫ x, g x = 0 := integral_fderiv_apply_eq_zero (hφ.of_le (by norm_cast)) hc e
  rw [h0]
  simp

/-- The derivative of a dilated and translated function. -/
private lemma hasFDerivAt_comp_smul_sub {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : Differentiable ℝ χ) (c : ℝ) (z v : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun v => χ (c • (v - z))) (c • fderiv ℝ χ (c • (v - z))) v := by
  have hA : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin d) => c • (v - z))
      (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) v :=
    ((hasFDerivAt_id v).sub_const z).const_smul c
  have h := (hχ (c • (v - z))).hasFDerivAt.comp v hA
  exact h.congr_fderiv (by ext w; simp)

/-- The second derivative of a dilated and translated function scales by `c²`. -/
private lemma hess_comp_smul_sub {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ContDiff ℝ 2 χ)
    (c : ℝ) (z v e : EuclideanSpace ℝ (Fin d)) :
    hess (fun v => χ (c • (v - z))) v e = c ^ 2 * hess χ (c • (v - z)) e := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ χ) :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : fderiv ℝ (fun v => χ (c • (v - z))) =
      fun v => c • fderiv ℝ χ (c • (v - z)) :=
    funext fun v => (hasFDerivAt_comp_smul_sub hχd c z v).fderiv
  have hA : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin d) => c • (v - z))
      (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) v :=
    ((hasFDerivAt_id v).sub_const z).const_smul c
  have h2 := ((hdd (c • (v - z))).hasFDerivAt.comp v hA).const_smul c
  have h3 : HasFDerivAt (fun v => c • fderiv ℝ χ (c • (v - z)))
      (c • ((fderiv ℝ (fderiv ℝ χ) (c • (v - z))).comp
        (c • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))))) v := h2
  unfold hess
  rw [h1, h3.fderiv]
  simp [pow_two, mul_assoc]

/-- The second derivative vanishes where the function vanishes identically nearby. -/
private lemma hess_eq_zero_of_eventuallyEq {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {w : EuclideanSpace ℝ (Fin d)} (h : φ =ᶠ[𝓝 w] fun _ => 0) (e : EuclideanSpace ℝ (Fin d)) :
    hess φ w e = 0 := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 w] fun _ => (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := by
    filter_upwards [h.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq]
    simp
  have h2 := h1.fderiv_eq (𝕜 := ℝ)
  simp [hess, h2]

/-- The Laplacian of a dilated and translated function. -/
private lemma laplacian_comp_smul_sub {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ContDiff ℝ 2 χ)
    (c : ℝ) (z v : EuclideanSpace ℝ (Fin d)) :
    Laplacian.laplacian (fun v => χ (c • (v - z))) v =
      c ^ 2 * Laplacian.laplacian χ (c • (v - z)) := by
  rw [laplacian_eq_sum_hess, laplacian_eq_sum_hess, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hess_comp_smul_sub hχ c z v _

/-- The fixed smooth bump, equal to `1` on the unit ball and supported in the ball of radius `2`. -/
private noncomputable def bump (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨1, 2, one_pos, by norm_num⟩

/-- The Laplacian of the fixed bump is bounded. -/
private lemma exists_bound_laplacian_bump (d : ℕ) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ w, |Laplacian.laplacian (⇑(bump d)) w| ≤ K₀ := by
  obtain ⟨K₀, hK₀⟩ := (continuous_laplacian (bump d).contDiff).bounded_above_of_compact_support
    (hasCompactSupport_laplacian (bump d).hasCompactSupport)
  refine ⟨K₀, (norm_nonneg _).trans (hK₀ 0), fun w => ?_⟩
  simpa [Real.norm_eq_abs] using hK₀ w

/-- `R ^ d * R * R⁻¹ ^ 2 = R ^ (d - 1)` for `d ≥ 1`. -/
private lemma pow_mul_mul_inv_sq {R : ℝ} (hR : 0 < R) {d : ℕ} (hd : 1 ≤ d) :
    R ^ d * R * R⁻¹ ^ 2 = R ^ (d - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

/-- The test function `φ(v) = χ((v - y)/R)`: smooth, compactly supported, nonnegative, equal to
`1` on `B(y, R)` and zero outside `B(y, 2R)`. -/
private lemma exists_testFunction (d : ℕ) {K₀ : ℝ}
    (hK₀ : ∀ w, |Laplacian.laplacian (⇑(bump d)) w| ≤ K₀) {R : ℝ} (hR : 0 < R)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ v, 0 ≤ φ v) ∧ (∀ v ∈ Metric.closedBall y R, φ v = 1) ∧
      (∀ v, 2 * R < ‖v - y‖ → Laplacian.laplacian φ v = 0) ∧
      ∀ v, |Laplacian.laplacian φ v| ≤ R⁻¹ ^ 2 * K₀ := by
  have hRinv : R⁻¹ ≠ 0 := inv_ne_zero hR.ne'
  refine ⟨fun v => bump d (R⁻¹ • (v - y)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (bump d).contDiff.comp
      (by fun_prop : ContDiff ℝ ∞ fun v : EuclideanSpace ℝ (Fin d) => R⁻¹ • (v - y))
  · exact (bump d).hasCompactSupport.comp_homeomorph
      ((Homeomorph.subRight y).trans (Homeomorph.smulOfNeZero R⁻¹ hRinv))
  · intro v
    exact (bump d).nonneg
  · intro v hv
    refine (bump d).one_of_mem_closedBall ?_
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have h1 : ‖v - y‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hv
      exact hv
    calc R⁻¹ * ‖v - y‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hR).le
      _ = (bump d).rIn := by simp [bump, hR.ne']
  · intro v hv
    rw [laplacian_eq_sum_hess]
    refine Finset.sum_eq_zero fun i _ => hess_eq_zero_of_eventuallyEq ?_ _
    have hopen : IsOpen {w : EuclideanSpace ℝ (Fin d) | 2 * R < ‖w - y‖} :=
      isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    filter_upwards [hopen.mem_nhds hv] with w hw
    have hw' : 2 * R < ‖w - y‖ := hw
    have : R⁻¹ • (w - y) ∉ Function.support (bump d) := by
      rw [(bump d).support_eq, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hR)]
      change ¬ R⁻¹ * ‖w - y‖ < 2
      rw [not_lt]
      calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
        _ ≤ R⁻¹ * ‖w - y‖ := mul_le_mul_of_nonneg_left hw'.le (inv_pos.mpr hR).le
    simpa using this
  · intro v
    rw [laplacian_comp_smul_sub (χ := ⇑(bump d)) ((bump d).contDiff) R⁻¹ y v, abs_mul,
      abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hK₀ _) (by positivity)

/-! ### The tangent-plane growth bound -/

/-- The hessian growth `eq:hessian-growth` for a continuous function that lies between its tangent
plane at `y` and the tangent plane plus `2 L |v - y|`: `m(B(y, R)) ≤ C L R^{d-1}` for every locally
finite measure `m` whose distributional Laplacian is `Δ Ψ`. The constant `C` depends only on the
dimension. -/
private theorem exists_measure_ball_le_of_defect (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}, Continuous Ψ → ∀ {L : ℝ}, 0 ≤ L →
      ∀ {m : Measure (EuclideanSpace ℝ (Fin d))}, IsLocallyFiniteMeasure m →
      CERW.IsDistribLaplacian Ψ m → ∀ {y ξ : EuclideanSpace ℝ (Fin d)},
      (∀ v, 0 ≤ Ψ v - (Ψ y + inner ℝ ξ (v - y)) ∧
        Ψ v - (Ψ y + inner ℝ ξ (v - y)) ≤ 2 * L * ‖v - y‖) → ∀ {R : ℝ}, 0 < R →
        m (Metric.ball y R) ≤ ENNReal.ofReal (K * L * R ^ (d - 1)) := by
  obtain ⟨K₀, hK₀nn, hK₀⟩ := exists_bound_laplacian_bump d
  refine ⟨2 ^ (d + 2) * CERW.unitBallVolume d * K₀, by
    have := CERW.unitBallVolume_pos d
    positivity, ?_⟩
  intro Ψ hΨc L hL m hm hlap y ξ hdef R hR
  obtain ⟨φ, hφs, hφc, hφ0, hφ1, hφz, hφb⟩ := exists_testFunction d hK₀ hR y
  -- the ball is dominated by the test function
  have hint : Integrable φ m := hφs.continuous.integrable_of_hasCompactSupport hφc
  have hball_le : m (Metric.ball y R) ≤ ENNReal.ofReal (∫ v, φ v ∂m) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hφ0)]
    calc m (Metric.ball y R) = ∫⁻ v in Metric.ball y R, ENNReal.ofReal (φ v) ∂m := by
          rw [setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
            (g := fun _ => 1) (fun v hv => by
              rw [hφ1 v (Metric.ball_subset_closedBall hv)]
              simp)]
          simp
      _ ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂m := setLIntegral_le_lintegral _ _
  -- the defining identity of the distributional Laplacian
  have hlap_eq := hlap φ hφs hφc
  -- subtracting the tangent plane does not change the integral
  set a : ℝ := Ψ y - inner ℝ ξ y with ha
  set ℓ : EuclideanSpace ℝ (Fin d) → ℝ := fun v => a + inner ℝ ξ v with hℓ
  have hℓc : Continuous ℓ := by simp only [hℓ]; fun_prop
  have hΔc : Continuous (Laplacian.laplacian φ) := continuous_laplacian hφs
  have hΔs : HasCompactSupport (Laplacian.laplacian φ) := hasCompactSupport_laplacian hφc
  have hiΨ : Integrable (fun v => Ψ v * Laplacian.laplacian φ v) :=
    (hΨc.mul hΔc).integrable_of_hasCompactSupport hΔs.mul_left
  have hiℓ : Integrable (fun v => ℓ v * Laplacian.laplacian φ v) :=
    (hℓc.mul hΔc).integrable_of_hasCompactSupport hΔs.mul_left
  have hzero : ∫ v, ℓ v * Laplacian.laplacian φ v = 0 := by
    simp only [hℓ]
    rw [laplacian_eq_sum_hess]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · exact Finset.sum_eq_zero fun i _ => integral_affine_mul_hess hφs hφc a ξ _
    · intro i _
      exact ((by fun_prop : Continuous fun v : EuclideanSpace ℝ (Fin d) => a + inner ℝ ξ v).mul
        (continuous_hess hφs _)).integrable_of_hasCompactSupport
        (hasCompactSupport_hess hφc _).mul_left
  have hsplit : ∫ v, Ψ v * Laplacian.laplacian φ v =
      ∫ v, (Ψ v - ℓ v) * Laplacian.laplacian φ v := by
    have : ∀ v, (Ψ v - ℓ v) * Laplacian.laplacian φ v =
        Ψ v * Laplacian.laplacian φ v - ℓ v * Laplacian.laplacian φ v := fun v => sub_mul _ _ _
    simp_rw [this]
    rw [integral_sub hiΨ hiℓ, hzero, sub_zero]
  -- the pointwise bound
  set c : ℝ := 4 * L * R * (R⁻¹ ^ 2 * K₀) with hc
  have hpt : ∀ v, ‖(Ψ v - ℓ v) * Laplacian.laplacian φ v‖ ≤
      (Metric.closedBall y (2 * R)).indicator (fun _ => c) v := by
    intro v
    by_cases hv : v ∈ Metric.closedBall y (2 * R)
    · rw [Set.indicator_of_mem hv, Real.norm_eq_abs, abs_mul]
      have hvR : ‖v - y‖ ≤ 2 * R := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hv
        exact hv
      obtain ⟨h0, h1⟩ := hdef v
      have hℓv : Ψ v - ℓ v = Ψ v - (Ψ y + inner ℝ ξ (v - y)) := by
        simp only [hℓ, ha, inner_sub_right]
        ring
      rw [hℓv, abs_of_nonneg h0]
      have h2 : Ψ v - (Ψ y + inner ℝ ξ (v - y)) ≤ 4 * L * R := by
        calc _ ≤ 2 * L * ‖v - y‖ := h1
          _ ≤ 2 * L * (2 * R) :=
              mul_le_mul_of_nonneg_left hvR (by positivity)
          _ = 4 * L * R := by ring
      exact mul_le_mul h2 (hφb v) (abs_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hv, Real.norm_eq_abs, abs_mul]
      have hvR : 2 * R < ‖v - y‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hv
        exact hv
      rw [hφz v hvR]
      simp
  have hvolball : (volume (Metric.closedBall y (2 * R))).toReal =
      (2 * R) ^ d * CERW.unitBallVolume d := by
    have := Measure.addHaar_real_closedBall (volume : Measure (EuclideanSpace ℝ (Fin d))) y
      (by positivity : (0 : ℝ) ≤ 2 * R)
    rw [finrank_euclideanSpace_fin] at this
    simpa [Measure.real_def, CERW.unitBallVolume] using this
  have hint_ind : Integrable ((Metric.closedBall y (2 * R)).indicator fun _ => c) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
      (integrableOn_const measure_closedBall_lt_top.ne)
  have hintegral_le : ∫ v, Ψ v * Laplacian.laplacian φ v ≤
      2 ^ (d + 2) * CERW.unitBallVolume d * K₀ * L * R ^ (d - 1) := by
    rw [hsplit]
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hint_ind (Eventually.of_forall hpt)).trans ?_
    rw [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet, smul_eq_mul,
      Measure.real_def, hvolball, hc]
    have hRd := pow_mul_mul_inv_sq hR hd
    have hω := CERW.unitBallVolume_pos d
    refine le_of_eq ?_
    calc (2 * R) ^ d * CERW.unitBallVolume d * (4 * L * R * (R⁻¹ ^ 2 * K₀))
        = 2 ^ (d + 2) * CERW.unitBallVolume d * K₀ * L * (R ^ d * R * R⁻¹ ^ 2) := by
          rw [mul_pow, pow_add]
          ring
      _ = _ := by rw [hRd]
  calc m (Metric.ball y R) ≤ ENNReal.ofReal (∫ v, φ v ∂m) := hball_le
    _ ≤ ENNReal.ofReal (2 ^ (d + 2) * CERW.unitBallVolume d * K₀ * L *
        R ^ (d - 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hlap_eq]
        exact hintegral_le


/-! ### Positivity of the distributional Laplacian of a convex function -/

/-- One-dimensional second difference: if `a' = g` and `g' = g₂` (derivatives everywhere) and
`|g₂ t - g₂ 0| ≤ η` for `|t| ≤ h`, then `|a h + a (-h) - 2 a 0 - g₂ 0 h²| ≤ 2 η h²`. -/
private lemma abs_secondDiff_sub_le {a g g₂ : ℝ → ℝ} (ha : ∀ t, HasDerivAt a (g t) t)
    (hg : ∀ t, HasDerivAt g (g₂ t) t) {η h : ℝ} (hh : 0 ≤ h)
    (hη : ∀ t, |t| ≤ h → |g₂ t - g₂ 0| ≤ η) :
    |a h + a (-h) - 2 * a 0 - g₂ 0 * h ^ 2| ≤ 2 * η * h ^ 2 := by
  -- m s = g s - g (-s) - 2 g₂ 0 s
  have hm : ∀ s, HasDerivAt (fun s => g s - g (-s) - 2 * g₂ 0 * s)
      (g₂ s + g₂ (-s) - 2 * g₂ 0) s := by
    intro s
    have h1 := hg s
    have h2 := HasDerivAt.comp s (hg (-s)) (hasDerivAt_neg s)
    have h3 := ((h1.sub h2).sub ((hasDerivAt_id s).const_mul (2 * g₂ 0)))
    exact h3.congr_deriv (by ring)
  have hmb : ∀ s, 0 ≤ s → s ≤ h → |g s - g (-s) - 2 * g₂ 0 * s| ≤ 2 * η * s := by
    intro s hs0 hsh
    have hbound : ∀ r ∈ Set.Icc 0 s, ‖g₂ r + g₂ (-r) - 2 * g₂ 0‖ ≤ 2 * η := by
      intro r hr
      have h1 := hη r (by rw [abs_of_nonneg hr.1]; linarith [hr.2])
      have h2 := hη (-r) (by rw [abs_neg, abs_of_nonneg hr.1]; linarith [hr.2])
      rw [Real.norm_eq_abs]
      calc |g₂ r + g₂ (-r) - 2 * g₂ 0| = |(g₂ r - g₂ 0) + (g₂ (-r) - g₂ 0)| := by ring_nf
        _ ≤ |g₂ r - g₂ 0| + |g₂ (-r) - g₂ 0| := abs_add_le _ _
        _ ≤ 2 * η := by linarith
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => g s - g (-s) - 2 * g₂ 0 * s)
      (f' := fun s => g₂ s + g₂ (-s) - 2 * g₂ 0) (C := 2 * η) (s := Set.Icc 0 s)
      (fun r _ => (hm r).hasDerivWithinAt) hbound (convex_Icc 0 s)
      (Set.left_mem_Icc.mpr hs0) (Set.right_mem_Icc.mpr hs0)
    simpa [Real.norm_eq_abs, abs_of_nonneg hs0] using this
  have hk : ∀ s, HasDerivAt (fun s => a s + a (-s) - 2 * a 0 - g₂ 0 * s ^ 2)
      (g s - g (-s) - 2 * g₂ 0 * s) s := by
    intro s
    have h1 := ha s
    have h2 := HasDerivAt.comp s (ha (-s)) (hasDerivAt_neg s)
    have h3 := (h1.add h2).sub_const (2 * a 0)
    have h4 := (((hasDerivAt_id s).pow 2).const_mul (g₂ 0))
    have h5 := h3.sub h4
    exact h5.congr_deriv (by simp only [id, Nat.cast_ofNat]; ring)
  have hkb : ∀ r ∈ Set.Icc 0 h, ‖g r - g (-r) - 2 * g₂ 0 * r‖ ≤ 2 * η * h := by
    intro r hr
    rw [Real.norm_eq_abs]
    refine (hmb r hr.1 hr.2).trans ?_
    have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0 (by simpa using hh))
    exact mul_le_mul_of_nonneg_left hr.2 (by linarith)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => a s + a (-s) - 2 * a 0 - g₂ 0 * s ^ 2)
    (f' := fun s => g s - g (-s) - 2 * g₂ 0 * s) (C := 2 * η * h) (s := Set.Icc 0 h)
    (fun r _ => (hk r).hasDerivWithinAt) hkb (convex_Icc 0 h)
    (Set.left_mem_Icc.mpr hh) (Set.right_mem_Icc.mpr hh)
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hh, neg_zero] at this
  have h0 : a 0 + a 0 - 2 * a 0 - g₂ 0 * 0 ^ 2 = 0 := by ring
  rw [h0] at this
  simpa [sub_zero, abs_of_nonneg hh, mul_assoc, pow_two] using this

/-- The derivative of `t ↦ φ (v + t e)`. -/
private lemma hasDerivAt_line {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (v e : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => φ (v + t • e)) (fderiv ℝ φ (v + t • e) e) t := by
  have hpath : HasDerivAt (fun t : ℝ => v + t • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add v
  have hd : DifferentiableAt ℝ φ (v + t • e) :=
    (hφ.differentiable (by norm_num)) _
  exact hd.hasFDerivAt.comp_hasDerivAt t hpath

/-- The derivative of `t ↦ Dφ(v + t e) e`. -/
private lemma hasDerivAt_line_deriv {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (v e : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => fderiv ℝ φ (v + t • e) e) (hess φ (v + t • e) e) t := by
  have hpath : HasDerivAt (fun t : ℝ => v + t • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add v
  have hdd : DifferentiableAt ℝ (fderiv ℝ φ) (v + t • e) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) _
  have h1 := hdd.hasFDerivAt.comp_hasDerivAt t hpath
  have h2 := (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt t h1
  exact h2.congr_deriv (by simp [hess])

/-- The second difference of a `C²` function along a line, against `D²φ(v)(e,e) h²`. -/
private lemma abs_secondDiff_sub_hess_le {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (v e : EuclideanSpace ℝ (Fin d)) {η h : ℝ} (hh : 0 ≤ h)
    (hη : ∀ t : ℝ, |t| ≤ h → |hess φ (v + t • e) e - hess φ v e| ≤ η) :
    |φ (v + h • e) + φ (v + (-h) • e) - 2 * φ v - hess φ v e * h ^ 2| ≤ 2 * η * h ^ 2 := by
  have := abs_secondDiff_sub_le (a := fun t : ℝ => φ (v + t • e))
    (g := fun t => fderiv ℝ φ (v + t • e) e) (g₂ := fun t => hess φ (v + t • e) e)
    (hasDerivAt_line hφ v e) (hasDerivAt_line_deriv hφ v e) hh (by simpa using hη)
  simpa using this


/-- Convexity gives the midpoint inequality `2 Ψ(v) ≤ Ψ(v + w) + Ψ(v - w)`. -/
private lemma two_mul_le_add_sub {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : ConvexOn ℝ Set.univ Ψ) (v w : EuclideanSpace ℝ (Fin d)) :
    2 * Ψ v ≤ Ψ (v + w) + Ψ (v - w) := by
  have h := hΨ.2 (Set.mem_univ (v + w)) (Set.mem_univ (v - w)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have h2 : (1 / 2 : ℝ) • (v + w) + (1 / 2 : ℝ) • (v - w) = v := by module
  rw [h2] at h
  simp only [smul_eq_mul] at h
  linarith


/-- A product of a continuous function with a compactly supported continuous function is
integrable. -/
private lemma integrable_mul_of_hasCompactSupport {f φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun v => f v * φ v) :=
  Continuous.integrable_of_hasCompactSupport (hf.mul hφ) hc.mul_left

/-- For every `h > 0` the second difference quotient of the test function integrates against a
norm to a nonnegative number. -/
private lemma integral_mul_secondDiff_nonneg {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨc : Continuous Ψ) (hΨ : ConvexOn ℝ Set.univ Ψ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ v, 0 ≤ φ v) (e : EuclideanSpace ℝ (Fin d)) {h : ℝ} (hh : 0 < h) :
    0 ≤ ∫ v, Ψ v * ((φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2) := by
  have hφ1 : Continuous fun v => φ (v + h • e) := hφ.comp (continuous_id.add continuous_const)
  have hφ2 : Continuous fun v => φ (v - h • e) := hφ.comp (continuous_id.sub continuous_const)
  have hc1 : HasCompactSupport fun v => φ (v + h • e) :=
    hc.comp_homeomorph (Homeomorph.addRight (h • e))
  have hc2 : HasCompactSupport fun v => φ (v - h • e) :=
    hc.comp_homeomorph (Homeomorph.subRight (h • e))
  have i1 := integrable_mul_of_hasCompactSupport hΨc hφ1 hc1
  have i2 := integrable_mul_of_hasCompactSupport hΨc hφ2 hc2
  have i0 := integrable_mul_of_hasCompactSupport hΨc hφ hc
  have j1 : Integrable (fun v => Ψ (v - h • e) * φ v) :=
    integrable_mul_of_hasCompactSupport
      (hΨc.comp (continuous_id.sub continuous_const) : Continuous fun v => Ψ (v - h • e)) hφ hc
  have j2 : Integrable (fun v => Ψ (v + h • e) * φ v) :=
    integrable_mul_of_hasCompactSupport
      (hΨc.comp (continuous_id.add continuous_const) : Continuous fun v => Ψ (v + h • e)) hφ hc
  have k1 : Integrable (fun v => Ψ v * φ (v + h • e) + Ψ v * φ (v - h • e)) := i1.add i2
  have k2 : Integrable (fun v => 2 * (Ψ v * φ v)) := i0.const_mul 2
  have k3 : Integrable (fun v => Ψ (v + h • e) * φ v + Ψ (v - h • e) * φ v) := j2.add j1
  have t1 : ∫ v, Ψ v * φ (v + h • e) = ∫ v, Ψ (v - h • e) * φ v := by
    rw [← integral_add_right_eq_self (fun v => Ψ (v - h • e) * φ v) (h • e)]
    simp
  have t2 : ∫ v, Ψ v * φ (v - h • e) = ∫ v, Ψ (v + h • e) * φ v := by
    rw [← integral_sub_right_eq_self (fun v => Ψ (v + h • e) * φ v) (h • e)]
    simp
  have hsum : ∫ v, Ψ v * ((φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2) =
      (∫ v, φ v * (Ψ (v + h • e) + Ψ (v - h • e) - 2 * Ψ v)) / h ^ 2 := by
    have hpt : ∀ v, Ψ v * ((φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2) =
        ((Ψ v * φ (v + h • e) + Ψ v * φ (v - h • e)) - 2 * (Ψ v * φ v)) / h ^ 2 := by
      intro v
      ring
    simp_rw [hpt]
    rw [integral_div, integral_sub k1 k2, integral_add i1 i2, integral_const_mul, t1, t2]
    have hq : ∀ v, φ v * (Ψ (v + h • e) + Ψ (v - h • e) - 2 * Ψ v) =
        (Ψ (v + h • e) * φ v + Ψ (v - h • e) * φ v) - 2 * (Ψ v * φ v) := by
      intro v
      ring
    simp_rw [hq]
    rw [integral_sub k3 k2, integral_add j2 j1, integral_const_mul]
    ring
  rw [hsum]
  refine div_nonneg (integral_nonneg fun v => ?_) (by positivity)
  have := two_mul_le_add_sub hΨ v (h • e)
  exact mul_nonneg (hφ0 v) (by linarith)

/-- Positivity of the distributional Laplacian of a convex function in one direction: for a
nonnegative smooth compactly supported `φ` and `‖e‖ ≤ 1`, `∫ Ψ D²φ(e, e) ≥ 0`. -/
private lemma integral_mul_hess_nonneg {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨc : Continuous Ψ) (hΨ : ConvexOn ℝ Set.univ Ψ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ)
    (hφ0 : ∀ v, 0 ≤ φ v) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ ≤ 1) :
    0 ≤ ∫ v, Ψ v * hess φ v e := by
  have hφc : Continuous φ := hφ.continuous
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 ≤ R ∧
      tsupport φ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R := by
    obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
    exact ⟨max R₀ 0, le_max_right _ _,
      hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hzero : ∀ w : EuclideanSpace ℝ (Fin d), R < ‖w‖ → φ w = 0 := by
    intro w hw
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have := hR h
    rw [mem_closedBall_zero_iff] at this
    linarith
  obtain ⟨M, hM⟩ := (continuous_hess hφ e).bounded_above_of_compact_support
    (hasCompactSupport_hess hc e)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d))
    (R + 1)).exists_bound_of_continuousOn
    hΨc.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp; linarith))
  set S : ℝ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun h v => (φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2 with hS
  -- the pointwise second-difference estimate
  have hest : ∀ v : EuclideanSpace ℝ (Fin d), ∀ {η h : ℝ}, 0 < h →
      (∀ t : ℝ, |t| ≤ h → |hess φ (v + t • e) e - hess φ v e| ≤ η) →
      |S h v - hess φ v e| ≤ 2 * η := by
    intro v η h hh hη
    have h1 := abs_secondDiff_sub_hess_le hφ2 v e hh.le hη
    have h2 : φ (v + (-h) • e) = φ (v - h • e) := by rw [neg_smul, ← sub_eq_add_neg]
    rw [h2] at h1
    simp only [hS]
    have hh2 : 0 < h ^ 2 := by positivity
    have h3 : |(φ (v + h • e) + φ (v - h • e) - 2 * φ v) / h ^ 2 - hess φ v e| =
        |φ (v + h • e) + φ (v - h • e) - 2 * φ v - hess φ v e * h ^ 2| / h ^ 2 := by
      rw [← abs_of_pos hh2, ← abs_div, abs_of_pos hh2]
      congr 1
      field_simp
    rw [h3, div_le_iff₀ hh2]
    nlinarith [h1]
  have hlim : Tendsto (fun h => ∫ v, Ψ v * S h v) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v, Ψ v * hess φ v e)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + 1)).indicator
        (fun _ => B * (5 * M)) v) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun h => ?_
      have : Continuous fun v => Ψ v * S h v := by
        simp only [hS]
        exact hΨc.mul (((hφc.comp (continuous_id.add continuous_const)).add
          (hφc.comp (continuous_id.sub continuous_const))).sub (continuous_const.mul hφc)
          |>.div_const _)
      exact this.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with h hh
      refine Eventually.of_forall fun v => ?_
      by_cases hv : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (R + 1)
      · rw [Set.indicator_of_mem hv]
        have hη : ∀ t : ℝ, |t| ≤ h → |hess φ (v + t • e) e - hess φ v e| ≤ 2 * M := by
          intro t _
          have h1 := hM (v + t • e)
          have h2 := hM v
          rw [Real.norm_eq_abs] at h1 h2
          calc |hess φ (v + t • e) e - hess φ v e|
              ≤ |hess φ (v + t • e) e| + |hess φ v e| := abs_sub _ _
            _ ≤ 2 * M := by linarith
        have h1 := hest v hh.1 hη
        have h2 := hM v
        rw [Real.norm_eq_abs] at h2
        have h3 : |S h v| ≤ 5 * M := by
          have := abs_sub_abs_le_abs_sub (S h v) (hess φ v e)
          linarith
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by simpa using hB v hv) h3 (abs_nonneg _) hB0
      · rw [Set.indicator_of_notMem hv]
        have hv' : R + 1 < ‖v‖ := by
          simpa [mem_closedBall_zero_iff] using hv
        have hT : ∀ w : EuclideanSpace ℝ (Fin d), ‖w - v‖ ≤ 1 → φ w = 0 := by
          intro w hw
          refine hzero w ?_
          have := norm_sub_norm_le v w
          rw [norm_sub_rev] at this
          linarith
        have hs1 : φ (v + h • e) = 0 := hT _ (by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hh.1]
          nlinarith [hh.2, norm_nonneg e])
        have hs2 : φ (v - h • e) = 0 := hT _ (by
          rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh.1]
          nlinarith [hh.2, norm_nonneg e])
        have hs3 : φ v = 0 := hzero v (by linarith)
        simp [hS, hs1, hs2, hs3]
    · exact (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
        (integrableOn_const measure_closedBall_lt_top.ne)
    · refine Eventually.of_forall fun v => ?_
      have hcont : ContinuousAt (fun t : ℝ => hess φ (v + t • e) e) 0 :=
        ((continuous_hess hφ e).comp
          (continuous_const.add (continuous_id.smul continuous_const))).continuousAt
      refine Tendsto.const_mul (Ψ v) ?_
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont (ε / 4) (by positivity)
      refine ⟨δ, hδ, fun h hh hd => ?_⟩
      have hh0 : 0 < h := hh
      have hd' : h < δ := by
        rwa [Real.dist_eq, sub_zero, abs_of_pos hh0] at hd
      have hη : ∀ t : ℝ, |t| ≤ h → |hess φ (v + t • e) e - hess φ v e| ≤ ε / 4 := by
        intro t ht
        have := hδ' (x := t) (by rw [Real.dist_eq, sub_zero]; exact lt_of_le_of_lt ht hd')
        simp only [zero_smul, add_zero, Real.dist_eq] at this
        exact this.le
      have := hest v hh0 hη
      rw [Real.dist_eq]
      linarith
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun h hh =>
    integral_mul_secondDiff_nonneg hΨc hΨ hφc hc hφ0 e hh)

/-- The distributional Laplacian of a convex function is nonnegative. -/
private lemma integral_mul_laplacian_nonneg {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨc : Continuous Ψ) (hΨ : ConvexOn ℝ Set.univ Ψ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ)
    (hφ0 : ∀ v, 0 ≤ φ v) : 0 ≤ ∫ v, Ψ v * Laplacian.laplacian φ v := by
  rw [laplacian_eq_sum_hess]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_nonneg fun i _ => integral_mul_hess_nonneg hΨc hΨ hφ hc hφ0 ?_
    simp
  · intro i _
    exact Continuous.integrable_of_hasCompactSupport
      (hΨc.mul (continuous_hess hφ _)) (hasCompactSupport_hess hc _).mul_left

/-- `Ψ Δφ` is integrable for a smooth compactly supported `φ` and continuous `Ψ`. -/
private lemma integrable_mul_laplacian {Ψ φ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨc : Continuous Ψ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun v => Ψ v * Laplacian.laplacian φ v) := by
  rw [laplacian_eq_sum_hess]
  simp_rw [Finset.mul_sum]
  refine integrable_finsetSum _ fun i _ => ?_
  exact Continuous.integrable_of_hasCompactSupport
    (hΨc.mul (continuous_hess hφ _)) (hasCompactSupport_hess hc _).mul_left

/-! ### Existence of the distributional Laplacian as a measure -/

/-- The smooth functions among the compactly supported continuous functions. -/
private def smoothSubmodule (d : ℕ) : Submodule ℝ C_c(EuclideanSpace ℝ (Fin d), ℝ) where
  carrier := {f | ContDiff ℝ ∞ (f : EuclideanSpace ℝ (Fin d) → ℝ)}
  zero_mem' := by
    change ContDiff ℝ ∞ (⇑(0 : C_c(EuclideanSpace ℝ (Fin d), ℝ)))
    rw [coe_zero]
    exact contDiff_const
  add_mem' := fun {f g} hf hg => by
    change ContDiff ℝ ∞ (⇑(f + g))
    rw [coe_add]
    exact ContDiff.add hf hg
  smul_mem' := fun c f hf => by
    change ContDiff ℝ ∞ (⇑(c • f))
    rw [coe_smul]
    exact ContDiff.const_smul c hf

/-- The functional `φ ↦ ∫ Ψ Δφ` on the smooth compactly supported functions. -/
private noncomputable def lapFunctional (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (hΨc : Continuous Ψ) :
    smoothSubmodule d →ₗ[ℝ] ℝ where
  toFun f := ∫ v, Ψ v * Laplacian.laplacian (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) v
  map_add' := fun f g => by
    have hf : ContDiff ℝ ∞ (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) := f.2
    have hg : ContDiff ℝ ∞ (g.1 : EuclideanSpace ℝ (Fin d) → ℝ) := g.2
    have h1 := integrable_mul_laplacian hΨc hf f.1.hasCompactSupport
    have h2 := integrable_mul_laplacian hΨc hg g.1.hasCompactSupport
    have e : (⇑(f + g : smoothSubmodule d).1 : EuclideanSpace ℝ (Fin d) → ℝ) =
        ⇑f.1 + ⇑g.1 := by
      funext v
      rfl
    show ∫ v, Ψ v * Laplacian.laplacian (⇑(f + g : smoothSubmodule d).1 :
        EuclideanSpace ℝ (Fin d) → ℝ) v = _
    rw [e]
    show _ = (∫ v, Ψ v * Laplacian.laplacian (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) v) +
      ∫ v, Ψ v * Laplacian.laplacian (g.1 : EuclideanSpace ℝ (Fin d) → ℝ) v
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have := ContDiffAt.laplacian_add (x := v) (hf.contDiffAt.of_le (by norm_cast))
      (hg.contDiffAt.of_le (by norm_cast))
    simp only at this ⊢
    rw [this, mul_add]
  map_smul' := fun c f => by
    have hf : ContDiff ℝ ∞ (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) := f.2
    have e : (⇑(c • f : smoothSubmodule d).1 : EuclideanSpace ℝ (Fin d) → ℝ) =
        c • ⇑f.1 := by
      funext v
      rfl
    show ∫ v, Ψ v * Laplacian.laplacian (⇑(c • f : smoothSubmodule d).1 :
        EuclideanSpace ℝ (Fin d) → ℝ) v = c • ∫ v, Ψ v * Laplacian.laplacian
          (f.1 : EuclideanSpace ℝ (Fin d) → ℝ) v
    rw [e, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have := InnerProductSpace.laplacian_smul (x := v) c (hf.contDiffAt.of_le (by norm_cast))
    simp only [smul_eq_mul] at this ⊢
    rw [this]
    ring

/-- A continuous convex function has a distributional Laplacian that is a locally finite measure:
the functional `φ ↦ ∫ Ψ Δφ` is positive on the smooth compactly supported functions, so it extends
to a positive functional on all compactly supported continuous functions (M. Riesz), which is an
integral by the Riesz-Markov-Kakutani theorem. -/
theorem exists_isDistribLaplacian_of_convexOn {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨc : Continuous Ψ) (hΨ : ConvexOn ℝ Set.univ Ψ) :
    ∃ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m ∧
      CERW.IsDistribLaplacian Ψ m := by
  haveI : PosSMulMono ℝ C_c(EuclideanSpace ℝ (Fin d), ℝ) :=
    ⟨fun a ha f g hfg => by
      rw [CompactlySupportedContinuousMap.le_def] at hfg ⊢
      intro v
      simpa using mul_le_mul_of_nonneg_left (hfg v) ha⟩
  let f : C_c(EuclideanSpace ℝ (Fin d), ℝ) →ₗ.[ℝ] ℝ := ⟨smoothSubmodule d, lapFunctional Ψ hΨc⟩
  have nonneg : ∀ x : f.domain, (x : C_c(EuclideanSpace ℝ (Fin d), ℝ)) ∈
      PointedCone.positive ℝ C_c(EuclideanSpace ℝ (Fin d), ℝ) → 0 ≤ f x := by
    intro x hx
    rw [PointedCone.mem_positive, CompactlySupportedContinuousMap.le_def] at hx
    exact integral_mul_laplacian_nonneg hΨc hΨ x.2 x.1.hasCompactSupport fun v => by
      simpa using hx v
  have dense : ∀ y : C_c(EuclideanSpace ℝ (Fin d), ℝ), ∃ x : f.domain,
      (x : C_c(EuclideanSpace ℝ (Fin d), ℝ)) + y ∈
        PointedCone.positive ℝ C_c(EuclideanSpace ℝ (Fin d), ℝ) := by
    intro y
    obtain ⟨R₀, hR₀⟩ := y.hasCompactSupport.isCompact.isBounded.subset_closedBall
      (0 : EuclideanSpace ℝ (Fin d))
    obtain ⟨N, hN⟩ := y.continuous.bounded_above_of_compact_support y.hasCompactSupport
    have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
    let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
      ⟨max R₀ 0 + 1, max R₀ 0 + 2, by positivity, by linarith⟩
    let bc : C_c(EuclideanSpace ℝ (Fin d), ℝ) := ⟨⟨b, b.continuous⟩, b.hasCompactSupport⟩
    refine ⟨⟨N • bc, ?_⟩, ?_⟩
    · change ContDiff ℝ ∞ (⇑(N • bc))
      rw [coe_smul]
      exact ContDiff.const_smul N b.contDiff
    · rw [PointedCone.mem_positive, CompactlySupportedContinuousMap.le_def]
      intro v
      change 0 ≤ N * b v + y v
      by_cases hv : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (max R₀ 0 + 1)
      · rw [b.one_of_mem_closedBall hv]
        have h1 : |y v| ≤ N := by
          have := hN v
          rwa [Real.norm_eq_abs] at this
        linarith [neg_abs_le (y v)]
      · have hy : y v = 0 := by
          refine image_eq_zero_of_notMem_tsupport fun h => hv ?_
          have := hR₀ h
          exact Metric.closedBall_subset_closedBall (by linarith [le_max_left R₀ 0]) this
        rw [hy, add_zero]
        exact mul_nonneg hN0 b.nonneg
  obtain ⟨g, hg, hgpos⟩ := riesz_extension _ f nonneg dense
  let Λ : C_c(EuclideanSpace ℝ (Fin d), ℝ) →ₚ[ℝ] ℝ :=
    ⟨g, fun a b hab => by
      have := hgpos (b - a) (by rw [PointedCone.mem_positive]; exact sub_nonneg.mpr hab)
      rw [map_sub] at this
      exact sub_nonneg.mp this⟩
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, ?_⟩
  intro φ hφ hc
  let φc : C_c(EuclideanSpace ℝ (Fin d), ℝ) := ⟨⟨φ, hφ.continuous⟩, hc⟩
  have h1 := RealRMK.integral_rieszMeasure Λ φc
  have h2 : Λ φc = f ⟨φc, hφ⟩ := hg ⟨φc, hφ⟩
  exact h1.trans h2

/-! ### The gauge of a convex body -/

section Gauge

variable {K : Set (EuclideanSpace ℝ (Fin d))}

/-- The gauge of a compact convex body with the origin in its interior is continuous. -/
private lemma continuous_gauge_body (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) : Continuous (gauge K) :=
  (lipschitzWith_gauge hK hc h0).continuous

/-- **Positivity of the distributional Laplacian of the gauge.** For a nonnegative smooth compactly
supported `φ`, `∫ ψ_K Δφ ≥ 0`. -/
theorem integral_gauge_mul_laplacian_nonneg (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ v, 0 ≤ φ v) :
    0 ≤ ∫ v, gauge K v * Laplacian.laplacian φ v :=
  integral_mul_laplacian_nonneg (continuous_gauge_body hK hc h0) (convexOn_gauge hc h0) hφ hφc hφ0

/-- **The distributional Laplacian of the gauge is a locally finite measure.** For a compact
convex `K` with the origin in its interior, the literal Minkowski functional `gauge K` has a
distributional Laplacian that is a locally finite measure `m`: `∫ φ dm = ∫ gauge K · Δφ` for every
smooth compactly supported `φ`. Evenness of `K` is not required. -/
theorem exists_isDistribLaplacian_gauge (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m ∧
      CERW.IsDistribLaplacian (gauge K) m :=
  exists_isDistribLaplacian_of_convexOn (continuous_gauge_body hK hc h0) (convexOn_gauge hc h0)

/-- The defect of the gauge from a tangent plane at `y` is nonnegative and at most
`2 Λ_ψ |v - y|`. -/
private lemma gauge_defect_le (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {y ξ : EuclideanSpace ℝ (Fin d)}
    (hξ : IsSubgradient (gauge K) y ξ) (v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ gauge K v - (gauge K y + inner ℝ ξ (v - y)) ∧
      gauge K v - (gauge K y + inner ℝ ξ (v - y)) ≤ 2 * normMax (gauge K) * ‖v - y‖ := by
  refine ⟨by linarith [hξ v], ?_⟩
  have h1 : gauge K v - gauge K y ≤ normMax (gauge K) * ‖v - y‖ :=
    (le_abs_self _).trans (abs_gauge_sub_le hK hc h0 v y)
  have h2 : -inner ℝ ξ (v - y) ≤ normMax (gauge K) * ‖v - y‖ := by
    calc -inner ℝ ξ (v - y) ≤ ‖ξ‖ * ‖v - y‖ := by
          have := neg_le_abs (inner ℝ ξ (v - y))
          exact this.trans (abs_real_inner_le_norm _ _)
      _ ≤ normMax (gauge K) * ‖v - y‖ :=
          mul_le_mul_of_nonneg_right (norm_le_normMax_of_isSubgradient hK h0 hξ) (norm_nonneg _)
  linarith

/-- **Radial growth of the distributional Laplacian of the gauge** (`eq:hessian-growth`). There is a
constant `C` depending only on the dimension such that every locally finite measure `m` with
distributional Laplacian `Δ ψ_K` satisfies `m(B(y, R)) ≤ C Λ_ψ R^{d-1}` for every center `y` and
every radius `R > 0`, with `Λ_ψ = max_{|u| = 1} ψ_K(u)`. -/
theorem measure_ball_le_gauge (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : Set (EuclideanSpace ℝ (Fin d))}, IsCompact K → Convex ℝ K →
      (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K →
      ∀ {m : Measure (EuclideanSpace ℝ (Fin d))}, IsLocallyFiniteMeasure m →
      CERW.IsDistribLaplacian (gauge K) m → ∀ (y : EuclideanSpace ℝ (Fin d)) {R : ℝ}, 0 < R →
        m (Metric.ball y R) ≤ ENNReal.ofReal (C * normMax (gauge K) * R ^ (d - 1)) := by
  obtain ⟨C, hC, h⟩ := exists_measure_ball_le_of_defect hd
  refine ⟨C, hC, fun {K} hK hc h0 {m} hm hlap y {R} hR => ?_⟩
  obtain ⟨ξ, hξ⟩ := exists_isSubgradient hc h0 y
  exact h (continuous_gauge_body hK hc h0) (normMax_gauge_nonneg K) hm hlap
    (gauge_defect_le hK hc h0 hξ) hR

/-- **The distributional Laplacian of the gauge with the growth used at lattice sites.** For a
compact convex `K` with the origin in its interior and `d ≥ 1` there are a locally finite measure
`m` with distributional Laplacian `Δ ψ_K` and a constant `Kg ≥ 0` such that for every site `y` of
`ℤ^d` and every `R > 0`, `m(B(y, R)) ≤ Kg R^{d-1}`. This is the hypothesis of the weighted
summation of the cell estimate over the sites of the departure range; `Kg = C Λ_ψ`. -/
theorem exists_isDistribLaplacian_gauge_growth (hd : 1 ≤ d) (hK : IsCompact K)
    (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m ∧
      CERW.IsDistribLaplacian (gauge K) m ∧
      ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (y : Site d) {R : ℝ}, 0 < R →
        m (Metric.ball (toSpace y) R) ≤ ENNReal.ofReal (Kg * R ^ (d - 1)) := by
  obtain ⟨m, hm, hlap⟩ := exists_isDistribLaplacian_gauge hK hc h0
  obtain ⟨C, hC, h⟩ := measure_ball_le_gauge hd
  exact ⟨m, hm, hlap, C * normMax (gauge K), mul_nonneg hC (normMax_gauge_nonneg K),
    fun y {R} hR => h hK hc h0 hm hlap (toSpace y) hR⟩

end Gauge

/-! ### The non-even planar body `cutDisc` at `ε = 1/4` -/

/-- **Consumption at the non-even planar body.** The gauge of `cutDisc` (the disc of radius `2` cut
by `y₀ ≥ -1`) is not a norm and not even, yet it has a locally finite distributional Laplacian
measure with the linear growth `m(B(y, R)) ≤ Kg R` at every site, and the walk of drift strength
`1/4` opposite to a subgradient selection of this gauge exists, with the selection bounded by
`Λ_ψ`. -/
theorem cutDisc_gaugeLaplacian :
    ¬ IsNorm (gauge cutDisc) ∧ gauge cutDisc (-coordVec 0) ≠ gauge cutDisc (coordVec 0) ∧
    ∃ m : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m ∧
      CERW.IsDistribLaplacian (gauge cutDisc) m ∧
      (∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (y : Site 2) {R : ℝ}, 0 < R →
        m (Metric.ball (toSpace y) R) ≤ ENNReal.ofReal (Kg * R ^ (2 - 1))) ∧
      ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cutDisc) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
        (∀ x : Site 2, ‖ξ x‖ ≤ normMax (gauge cutDisc)) ∧
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
          (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4) ξ X := by
  obtain ⟨m, hm, hlap, hgrowth⟩ := exists_isDistribLaplacian_gauge_growth (d := 2) (by norm_num)
    isCompact_cutDisc convex_cutDisc zero_mem_interior_cutDisc
  obtain ⟨ξ, hξ, hξ0, hwalk⟩ := cutDisc_isDriftCERW
  exact ⟨not_isNorm_gauge_cutDisc, gauge_cutDisc_neg_ne, m, hm, hlap, hgrowth, ξ, hξ, hξ0,
    norm_selection_le isCompact_cutDisc zero_mem_interior_cutDisc hξ hξ0, hwalk⟩

end CERW.Support.Norm.GaugeLaplacian
