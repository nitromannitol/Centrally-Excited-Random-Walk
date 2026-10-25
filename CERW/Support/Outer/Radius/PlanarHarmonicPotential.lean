module

public import CERW.Support.Outer.Radius.PlanarExterior

@[expose] public section

/-!
# Planar Harmonic Potential

A complex kernel represents the planar potential as the real part of a holomorphic field. The
maximum principle extends annular potential bounds to the inner ball.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The identification of the complex plane with the Euclidean plane. -/
noncomputable abbrev mp_e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

/-- The complex kernel `u_v / (v - z)` whose real part is the planar potential integrand. -/
noncomputable def mp_kernel (v : EuclideanSpace ℝ (Fin 2)) (z : ℂ) : ℂ :=
  mp_e.symm (unitDir v) * (mp_e.symm v - z)⁻¹

/-- `Re (a / w) = ⟨a, w⟩ / |w|²` for complex numbers seen as vectors of the plane. -/
lemma mp_re_mul_inv (a w : ℂ) :
    (a * w⁻¹).re = inner ℝ (mp_e a) (mp_e w) / ‖mp_e w‖ ^ 2 := by
  rw [LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map, Complex.inner,
    Complex.sq_norm]
  simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The real part of the complex kernel is the integrand of the planar potential. -/
lemma mp_re_kernel (v : EuclideanSpace ℝ (Fin 2)) (z : ℂ) :
    (mp_kernel v z).re = inner ℝ (unitDir v) (v - mp_e z) / ‖v - mp_e z‖ ^ 2 := by
  have h := mp_re_mul_inv (mp_e.symm (unitDir v)) (mp_e.symm v - z)
  rwa [LinearIsometryEquiv.apply_symm_apply, map_sub, LinearIsometryEquiv.apply_symm_apply] at h

/-- A point of norm at least `b` is at distance at least `b - |z|` from `z`. -/
lemma mp_sub_norm_le {b : ℝ} {v : EuclideanSpace ℝ (Fin 2)} (hv : b ≤ ‖v‖) (z : ℂ) :
    b - ‖z‖ ≤ ‖mp_e.symm v - z‖ := by
  calc b - ‖z‖ ≤ ‖mp_e.symm v‖ - ‖z‖ := by rw [LinearIsometryEquiv.norm_map]; linarith
    _ ≤ ‖mp_e.symm v - z‖ := norm_sub_norm_le _ _

/-- The complex kernel is bounded by `1 / (b - |z|)` for `|v| ≥ b > |z|`. -/
lemma mp_norm_kernel_le {b : ℝ} {v : EuclideanSpace ℝ (Fin 2)} (hv : b ≤ ‖v‖) {z : ℂ}
    (hz : ‖z‖ < b) : ‖mp_kernel v z‖ ≤ (b - ‖z‖)⁻¹ := by
  have hpos : 0 < b - ‖z‖ := sub_pos.2 hz
  have hw := mp_sub_norm_le hv z
  rw [mp_kernel, norm_mul, norm_inv, LinearIsometryEquiv.norm_map]
  calc ‖unitDir v‖ * ‖mp_e.symm v - z‖⁻¹ ≤ 1 * (b - ‖z‖)⁻¹ :=
        mul_le_mul (norm_unitDir_le v) (inv_anti₀ hpos hw) (inv_nonneg.2 (norm_nonneg _))
          zero_le_one
    _ = (b - ‖z‖)⁻¹ := one_mul _

/-- The direction `u_v`, seen in the complex plane, is measurable in `v`. -/
lemma mp_measurable_dir :
    Measurable (fun v : EuclideanSpace ℝ (Fin 2) => mp_e.symm (unitDir v)) := by
  have hdir : Measurable (fun v : EuclideanSpace ℝ (Fin 2) => unitDir v) := by
    change Measurable (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖⁻¹ • v)
    fun_prop
  exact mp_e.symm.continuous.measurable.comp hdir

/-- The complex kernel is measurable in `v`. -/
lemma mp_measurable_kernel (z : ℂ) : Measurable (fun v => mp_kernel v z) :=
  mp_measurable_dir.mul ((mp_e.symm.continuous.measurable.sub_const z).inv)

/-- The complex derivative of the kernel in `z`. -/
lemma mp_hasDerivAt_kernel (v : EuclideanSpace ℝ (Fin 2)) {z : ℂ}
    (hz : mp_e.symm v - z ≠ 0) :
    HasDerivAt (fun z => mp_kernel v z) (mp_e.symm (unitDir v) / (mp_e.symm v - z) ^ 2) z := by
  have h1 : HasDerivAt (fun y : ℂ => mp_e.symm v - y) (-1) z := (hasDerivAt_id z).const_sub _
  have h2 : mp_e.symm (unitDir v) / (mp_e.symm v - z) ^ 2 =
      mp_e.symm (unitDir v) * (-(-1) / (mp_e.symm v - z) ^ 2) := by ring
  rw [h2]
  exact (h1.inv hz).const_mul _

/-- The integral `∫_E u_v / (v - z) dv` of the complex kernel. -/
noncomputable def mp_field (E : Set (EuclideanSpace ℝ (Fin 2))) (z : ℂ) : ℂ :=
  ∫ v in E, mp_kernel v z

/-- For `E` bounded outside the disc `B(0,b)`, the kernel is integrable on `E` at every point `z`
of the disc. -/
lemma mp_integrable_kernel {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E)
    (hEb : Bornology.IsBounded E) {b : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖}) {z : ℂ} (hz : ‖z‖ < b) :
    Integrable (fun v => mp_kernel v z) (volume.restrict E) :=
  IntegrableOn.of_bound hEb.measure_lt_top (mp_measurable_kernel z).aestronglyMeasurable
    (b - ‖z‖)⁻¹ (ae_restrict_of_forall_mem hE fun _ hv => mp_norm_kernel_le (hsub hv) hz)

/-- The field `∫_E u_v / (v - z) dv` is complex differentiable on the disc `B(0,b)`. -/
lemma mp_differentiableOn_field {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖}) :
    DifferentiableOn ℂ (mp_field E) (Metric.ball 0 b) := by
  intro z₀ hz₀
  rw [mem_ball_zero_iff] at hz₀
  haveI : IsFiniteMeasure (volume.restrict E) :=
    isFiniteMeasure_restrict.2 hEb.measure_lt_top.ne
  set δ : ℝ := (b - ‖z₀‖) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hnear : ∀ v ∈ E, ∀ z ∈ Metric.ball z₀ δ, δ ≤ ‖mp_e.symm v - z‖ := by
    intro v hv z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := norm_sub_norm_le z z₀
    have h2 := mp_sub_norm_le (hsub hv) z
    linarith
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict E)
    (F := fun z v => mp_kernel v z)
    (F' := fun z v => mp_e.symm (unitDir v) / (mp_e.symm v - z) ^ 2)
    (bound := fun _ => (δ ^ 2)⁻¹) (x₀ := z₀) (Metric.ball_mem_nhds z₀ hδ0)
    (Eventually.of_forall fun z => (mp_measurable_kernel z).aestronglyMeasurable)
    (mp_integrable_kernel hE hEb hsub hz₀)
    (mp_measurable_dir.div
      ((mp_e.symm.continuous.measurable.sub_const z₀).pow_const 2)).aestronglyMeasurable
    (ae_restrict_of_forall_mem hE fun v hv z hz => ?_) (integrable_const _)
    (ae_restrict_of_forall_mem hE fun v hv z hz =>
      mp_hasDerivAt_kernel v (norm_pos_iff.mp (hδ0.trans_le (hnear v hv z hz))))
  · exact hderiv.2.differentiableAt.differentiableWithinAt
  · rw [norm_div, norm_pow, LinearIsometryEquiv.norm_map, ← one_div]
    exact div_le_div₀ zero_le_one (norm_unitDir_le v) (pow_pos hδ0 2)
      (pow_le_pow_left₀ hδ0.le (hnear v hv z hz) 2)

/-- The planar potential is `2ε/ω_2` times the real part of the field inside the disc. -/
lemma mp_potential_eq (ε : ℝ) {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖})
    {z : ℂ} (hz : ‖z‖ < b) :
    potential 2 ε E (mp_e z) = 2 * ε / unitBallVolume 2 * (mp_field E z).re := by
  have h := integral_re (mp_integrable_kernel hE hEb hsub hz)
  simp only [RCLike.re_to_complex, mp_re_kernel] at h
  rw [potential, mp_field, h]

/-- Inside the disc, the exponential of the potential is the modulus of a holomorphic function. -/
lemma mp_exists_holomorphic (ε : ℝ) {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b : ℝ} (hsub : E ⊆ {v | b ≤ ‖v‖}) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (Metric.ball 0 b) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) b, ‖H z‖ = Real.exp (potential 2 ε E (mp_e z)) := by
  refine ⟨fun z => Complex.exp (((2 * ε / unitBallVolume 2 : ℝ) : ℂ) * mp_field E z),
    ((mp_differentiableOn_field hE hEb hsub).const_mul _).cexp, fun z hz => ?_⟩
  rw [Complex.norm_exp, Complex.re_ofReal_mul,
    mp_potential_eq ε hE hEb hsub (mem_ball_zero_iff.mp hz)]

/-- The planar potential of a bounded measurable set is continuous. -/
lemma mp_continuous_potential {ε : ℝ} (hε : 0 < ε) {E : Set (EuclideanSpace ℝ (Fin 2))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) : Continuous (potential 2 ε E) := by
  obtain ⟨C, hC0, hC⟩ := CERW.Support.Geometry.exists_potential_holder (d := 2) le_rfl
  exact CERW.Support.Geometry.continuous_of_holder_half (by positivity)
    (hC ε hε.le E hE hEb.measure_lt_top.ne)

/-- In the plane the potential of a set outside the disc `B(0,b)` is harmonic inside it, so its
supremum over the closed disc is attained on the circle. -/
theorem planar_max_principle (hd : d = 2) {ε : ℝ} (hε : 0 < ε)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    {b M : ℝ} (hb : 0 < b) (hsub : E ⊆ {v | b ≤ ‖v‖})
    (hM : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ = b → potential d ε E y ≤ M) :
    ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ b → potential d ε E y ≤ M := by
  subst hd
  intro y hy
  rcases hy.lt_or_eq with hlt | heq
  swap
  · exact hM y heq
  by_contra hcon
  rw [not_le] at hcon
  have hcont : Continuous (fun z : ℂ => potential 2 ε E (mp_e z)) :=
    (mp_continuous_potential hε hE hEb).comp mp_e.continuous
  obtain ⟨z₀, hz₀K, hmax⟩ := (isCompact_closedBall (0 : ℂ) b).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self hb.le⟩ hcont.continuousOn
  rw [isMaxOn_iff] at hmax
  have hy' : mp_e.symm y ∈ Metric.closedBall (0 : ℂ) b := by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact hy
  have hge : potential 2 ε E y ≤ potential 2 ε E (mp_e z₀) := by
    have h := hmax _ hy'
    simp only [LinearIsometryEquiv.apply_symm_apply] at h
    exact h
  have hz₀ : z₀ ∈ Metric.ball (0 : ℂ) b := by
    rw [mem_closedBall_zero_iff] at hz₀K
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_ne hz₀K fun h => ?_
    have := hM (mp_e z₀) (by rw [LinearIsometryEquiv.norm_map, h])
    linarith
  obtain ⟨H, hHd, hHn⟩ := mp_exists_holomorphic ε hE hEb hsub
  have hHmax : IsMaxOn (norm ∘ H) (Metric.ball 0 b) z₀ := by
    rw [isMaxOn_iff]
    intro z hz
    simp only [Function.comp_apply]
    rw [hHn z hz, hHn z₀ hz₀]
    exact Real.exp_le_exp.2 (hmax z (Metric.ball_subset_closedBall hz))
  have heqOn := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
    (convex_ball (0 : ℂ) b).isPreconnected Metric.isOpen_ball hHd hz₀ hHmax
  have hconst : Set.EqOn (fun z : ℂ => potential 2 ε E (mp_e z))
      (fun _ => potential 2 ε E (mp_e z₀)) (Metric.ball 0 b) := by
    intro z hz
    have h := heqOn hz
    simp only [Function.comp_apply, Function.const_apply] at h
    rw [hHn z hz, hHn z₀ hz₀] at h
    exact Real.exp_injective h
  have hcl := hconst.closure hcont continuous_const
  rw [closure_ball 0 hb.ne'] at hcl
  have hbC : ‖(b : ℂ)‖ = b := Complex.norm_of_nonneg hb.le
  have h1 : potential 2 ε E (mp_e b) = potential 2 ε E (mp_e z₀) :=
    hcl (mem_closedBall_zero_iff.mpr hbC.le)
  have h2 := hM (mp_e b) (by rw [LinearIsometryEquiv.norm_map, hbC])
  linarith
/-! ### The crossing bound for the Euclidean walk -/

end CERW.Support.Outer.Radius
