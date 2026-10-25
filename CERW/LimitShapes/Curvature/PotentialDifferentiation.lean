module

public import CERW.LimitShapes.Curvature.PotentialKernel
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Integration away from the poles of the potential

Uniform separation from the closure of the integration domain gives integrability and
continuity of the actual potential in `eq:potential-intro`.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory Filter Topology

/-- A bounded integration domain with positive separation has an integrable potential kernel. -/
theorem integrable_potentialKernel_of_separation {d : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hEb : Bornology.IsBounded E) {R δ : ℝ} (hδ : 0 < δ)
    (hR : ∀ v ∈ E, ‖v‖ ≤ R) {y : EuclideanSpace ℝ (Fin d)}
    (hsep : ∀ v ∈ E, δ ≤ ‖v - y‖) :
    Integrable (fun v => potentialKernel v y) (volume.restrict E) := by
  exact IntegrableOn.of_bound hEb.measure_lt_top
    (measurable_potentialKernel y).aestronglyMeasurable ((R + ‖y‖) / δ ^ d)
    (ae_restrict_of_forall_mem hE fun v hv =>
      norm_potentialKernel_le hδ (hsep v hv) (hR v hv))

/-- The actual potential kernel is integrable at every point outside the closure of the domain. -/
theorem integrable_potentialKernel {d : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hEb : Bornology.IsBounded E) {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∉ closure E) :
    Integrable (fun v => potentialKernel v y) (volume.restrict E) := by
  obtain ⟨R, _, hR⟩ := hEb.exists_pos_norm_le
  obtain ⟨δ, hδ, hsep⟩ := exists_potential_separation hy
  exact integrable_potentialKernel_of_separation hE hEb hδ hR
    (fun v hv => hsep v hv y (Metric.mem_ball_self hδ))

/-- The integral defining the potential is continuous at every point away from the closed domain. -/
theorem continuousAt_integral_potentialKernel {d : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hEb : Bornology.IsBounded E) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ closure E) :
    ContinuousAt (fun y => ∫ v in E, potentialKernel v y) x := by
  obtain ⟨R, hRpos, hR⟩ := hEb.exists_pos_norm_le
  obtain ⟨δ, hδ, hsep⟩ := exists_potential_separation hx
  letI : IsFiniteMeasure (volume.restrict E) :=
    isFiniteMeasure_restrict.2 hEb.measure_lt_top.ne
  apply continuousAt_of_dominated (bound := fun _ => (R + (‖x‖ + δ)) / δ ^ d)
  · exact Eventually.of_forall fun y => (measurable_potentialKernel y).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
    apply ae_restrict_of_forall_mem hE
    intro v hv
    apply (norm_potentialKernel_le hδ (hsep v hv y hy) (hR v hv)).trans
    have hyx : ‖y - x‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have hnorm : ‖y‖ ≤ ‖x‖ + δ := by
      have := norm_sub_norm_le y x
      linarith
    exact div_le_div_of_nonneg_right (by gcongr) (pow_nonneg hδ.le d)
  · exact integrable_const _
  · apply ae_restrict_of_forall_mem hE
    intro v hv
    have hvx : v ≠ x := by
      intro h
      apply hx
      simpa only [h] using (subset_closure hv)
    exact (contDiffAt_potentialKernel hvx).continuousAt

/-- A continuous integrand on a compact set is integrable on every measurable subset. -/
private theorem integrable_on_compact {d : ℕ} {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {K E : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hE : MeasurableSet E) (hEK : E ⊆ K)
    {f : EuclideanSpace ℝ (Fin d) → A} (hf : ContinuousOn f K) :
    Integrable f (volume.restrict E) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  exact IntegrableOn.of_bound (hK.isBounded.subset hEK).measure_lt_top
    ((hf.mono hEK).aestronglyMeasurable hE) C
    (ae_restrict_of_forall_mem hE fun v hv => hC v (hEK hv))

/-- Smooth compactly parametrized kernels can be differentiated under the set integral. -/
theorem contDiffAt_integral_of_joint_contDiffAt {d : ℕ} (n : ℕ)
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    {K E U : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hE : MeasurableSet E) (hEK : E ⊆ K) (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → A}
    (hF : ∀ x ∈ U, ∀ v ∈ K, ContDiffAt ℝ n (Function.uncurry F) (x, v))
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    ContDiffAt ℝ n (fun y => ∫ v in E, F y v) x := by
  letI : SecondCountableTopology (EuclideanSpace ℝ (Fin d)) := inferInstance
  induction n generalizing A with
  | zero =>
    simp only [Nat.cast_zero, contDiffAt_zero]
    refine ⟨U, hU.mem_nhds hx, ?_⟩
    clear hx x
    intro x hx
    apply ContinuousAt.continuousWithinAt
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
    have hball : Metric.closedBall x (r / 2) ⊆ U := by
      intro y hy
      apply hsub
      have := Metric.mem_closedBall.mp hy
      exact Metric.mem_ball.mpr (by linarith)
    have hc : ContinuousOn (Function.uncurry F) (Metric.closedBall x (r / 2) ×ˢ K) :=
      fun p hp => (hF p.1 (hball hp.1) p.2 hp.2).continuousAt.continuousWithinAt
    have hcompact := (isCompact_closedBall x (r / 2)).prod hK
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc
    letI : IsFiniteMeasure (volume.restrict E) :=
      isFiniteMeasure_restrict.2 (hK.isBounded.subset hEK).measure_lt_top.ne
    apply continuousAt_of_dominated (bound := fun _ => C)
    · filter_upwards [hU.mem_nhds hx] with y hy
      apply ContinuousOn.aestronglyMeasurable _ hE
      intro v hv
      exact ((hF y hy v (hEK hv)).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    · filter_upwards [Metric.ball_mem_nhds x (show 0 < r / 2 by linarith)] with y hy
      exact ae_restrict_of_forall_mem hE fun v hv =>
        hC (y, v) ⟨Metric.ball_subset_closedBall hy, hEK hv⟩
    · exact integrable_const C
    · apply ae_restrict_of_forall_mem hE
      intro v hv
      have hm : ContinuousAt (fun y : EuclideanSpace ℝ (Fin d) => (y, v)) x :=
        continuousAt_id.prodMk continuousAt_const
      exact (hF x hx v (hEK hv)).continuousAt.comp (f := fun y => (y, v)) hm
  | succ n ih =>
    letI : SecondCountableTopologyEither (EuclideanSpace ℝ (Fin d))
        (EuclideanSpace ℝ (Fin d) →L[ℝ] A) := ⟨Or.inl inferInstance⟩
    let D := fun y v => fderiv ℝ (fun z => F z v) y
    have hD : ∀ y ∈ U, ∀ v ∈ K,
        ContDiffAt ℝ n (Function.uncurry D) (y, v) := by
      intro y hy v hv
      have hh : ContDiffAt ℝ (n + 1)
          (fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
            EuclideanSpace ℝ (Fin d) => F p.2 p.1.2) ((y, v), y) :=
        by
          have hm : ContDiffAt ℝ (n + 1)
              (fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
                EuclideanSpace ℝ (Fin d) => (p.2, p.1.2)) ((y, v), y) :=
            contDiffAt_snd.prodMk contDiffAt_fst.snd
          have hh := (hF y hy v hv).comp ((y, v), y) hm
          simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def, Function.uncurry] using hh
      exact hh.fderiv contDiffAt_fst (by simp)
    have hderiv : ∀ y ∈ U, HasFDerivAt (fun z => ∫ v in E, F z v)
        (∫ v in E, D y v) y := by
      intro y hy
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU y hy
      have hball : Metric.closedBall y (r / 2) ⊆ U := by
        intro z hz
        apply hsub
        have := Metric.mem_closedBall.mp hz
        exact Metric.mem_ball.mpr (by linarith)
      have hc : ContinuousOn (Function.uncurry D) (Metric.closedBall y (r / 2) ×ˢ K) :=
        fun p hp => (hD p.1 (hball hp.1) p.2 hp.2).continuousAt.continuousWithinAt
      have hcompact := (isCompact_closedBall y (r / 2)).prod hK
      obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc
      letI : IsFiniteMeasure (volume.restrict E) :=
        isFiniteMeasure_restrict.2 (hK.isBounded.subset hEK).measure_lt_top.ne
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := D) (bound := fun _ => C)
        (Metric.ball_mem_nhds y (show 0 < r / 2 by linarith))
      · filter_upwards [hU.mem_nhds hy] with z hz
        apply ContinuousOn.aestronglyMeasurable _ hE
        intro v hv
        exact ((hF z hz v (hEK hv)).continuousAt.comp
          (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
      · apply integrable_on_compact hK hE hEK
        intro v hv
        exact ((hF y hy v hv).continuousAt.comp
          (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
      · apply ContinuousOn.aestronglyMeasurable _ hE
        intro v hv
        exact ((hD y hy v (hEK hv)).continuousAt.comp
          (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
      · exact ae_restrict_of_forall_mem hE fun v hv z hz =>
          hC (z, v) ⟨Metric.ball_subset_closedBall hz, hEK hv⟩
      · exact integrable_const C
      · apply ae_restrict_of_forall_mem hE
        intro v hv z hz
        have hzU : z ∈ U := hball (Metric.ball_subset_closedBall hz)
        have hh : DifferentiableAt ℝ (fun w => F w v) z :=
          ((hF z hzU v (hEK hv)).comp z
            (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
        exact hh.hasFDerivAt
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun y => ∫ v in E, D y v, ⟨U, hU.mem_nhds hx, hderiv⟩, ?_⟩
    exact ih hD

end CERW.LimitShapes.Curvature
