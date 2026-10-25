module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Differentiation of integrals over bounded sets

Compact bounds on joint derivatives justify differentiation under the curvature integral
in `eq:curvature-improved`.
-/

namespace CERW.LimitShapes.Curvature

open MeasureTheory Filter Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [ProperSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {μ : Measure V} {E K U : Set V} {F : V → V → W}

omit [NormedSpace ℝ V] [SecondCountableTopology V] [NormedSpace ℝ W]
  [CompleteSpace W] in
/-- A jointly continuous integrand has a uniform integrable bound near a compact fiber. -/
lemma integral_compact_local_bound (hK : IsCompact K) (hE : MeasurableSet E)
    (hEK : E ⊆ K) (hfin : μ E ≠ ⊤) (hU : IsOpen U)
    (hc : ∀ y ∈ U, ∀ v ∈ K, ContinuousAt (Function.uncurry F) (y, v))
    {x : V} (hx : x ∈ U) :
    ∃ s ∈ 𝓝 x, s ⊆ U ∧ ∃ C : ℝ, ∀ y ∈ s,
      IntegrableOn (F y) E μ ∧ ∀ v ∈ K, ‖F y v‖ ≤ C := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let s := Metric.closedBall x (r / 2)
  have hsU : s ⊆ U := by
    intro y hy
    apply hrs
    exact lt_of_le_of_lt (show dist y x ≤ r / 2 from hy) (by linarith)
  have hcs : ContinuousOn (Function.uncurry F) (s ×ˢ K) := by
    intro p hp
    exact (hc p.1 (hsU hp.1) p.2 hp.2).continuousWithinAt
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x (r / 2)).prod hK).exists_bound_of_continuousOn hcs
  refine ⟨s, Metric.closedBall_mem_nhds x (by linarith), hsU, C, ?_⟩
  intro y hy
  have hslice : ContinuousOn (F y) K := by
    intro v hv
    exact ((hc y (hsU hy) v hv).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  exact ⟨hslice.integrableOn_of_subset_isCompact hK hE hEK hfin,
    fun v hv => hC (y, v) ⟨hy, hv⟩⟩

omit [NormedSpace ℝ V] [SecondCountableTopology V] [CompleteSpace W] in
/-- Compact domination makes a parameter integral continuous. -/
lemma continuousAt_integral_of_compact (hK : IsCompact K) (hE : MeasurableSet E)
    (hEK : E ⊆ K) (hfin : μ E ≠ ⊤) (hU : IsOpen U)
    (hc : ∀ y ∈ U, ∀ v ∈ K, ContinuousAt (Function.uncurry F) (y, v))
    {x : V} (hx : x ∈ U) : ContinuousAt (fun y => ∫ v in E, F y v ∂μ) x := by
  letI : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hfin.lt_top⟩
  obtain ⟨s, hs, -, C, hC⟩ := integral_compact_local_bound hK hE hEK hfin hU hc hx
  apply continuousAt_of_dominated (bound := fun _ => C)
  · filter_upwards [hs] with y hy using (hC y hy).1.aestronglyMeasurable
  · filter_upwards [hs] with y hy
    exact ae_restrict_of_forall_mem hE (fun v hv => (hC y hy).2 v (hEK hv))
  · exact integrable_const C
  · apply ae_restrict_of_forall_mem hE
    intro v hv
    exact ContinuousAt.comp (g := Function.uncurry F) (f := fun z : V => (z, v))
      (hc x hx v (hEK hv)) (continuousAt_id.prodMk continuousAt_const)

omit [SecondCountableTopology V] [CompleteSpace W] in
/-- Compact domination permits one Fréchet derivative under a set integral. -/
lemma hasFDerivAt_integral_of_compact {F' : V → V → V →L[ℝ] W}
    (hK : IsCompact K) (hE : MeasurableSet E) (hEK : E ⊆ K) (hfin : μ E ≠ ⊤)
    (hU : IsOpen U)
    (hc : ∀ y ∈ U, ∀ v ∈ K, ContinuousAt (Function.uncurry F) (y, v))
    (hc' : ∀ y ∈ U, ∀ v ∈ K, ContinuousAt (Function.uncurry F') (y, v))
    (hd : ∀ y ∈ U, ∀ v ∈ K, HasFDerivAt (fun z => F z v) (F' y v) y)
    {x : V} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ v in E, F y v ∂μ) (∫ v in E, F' x v ∂μ) x := by
  letI : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hfin.lt_top⟩
  obtain ⟨s, hs, hsU, C, hC⟩ := integral_compact_local_bound hK hE hEK hfin hU hc' hx
  obtain ⟨t, ht, -, D, hD⟩ := integral_compact_local_bound hK hE hEK hfin hU hc hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le hs
  · filter_upwards [ht] with y hy using (hD y hy).1.aestronglyMeasurable
  · exact (hD x (mem_of_mem_nhds ht)).1
  · exact (hC x (mem_of_mem_nhds hs)).1.aestronglyMeasurable
  · exact ae_restrict_of_forall_mem hE (fun v hv y hy => (hC y hy).2 v (hEK hv))
  · exact integrable_const C
  · exact ae_restrict_of_forall_mem hE (fun v hv y hy => hd y (hsU hy) v (hEK hv))

omit [SecondCountableTopology V] [CompleteSpace W] in
/-- Two jointly continuous derivative fields give actual C² regularity of the integral. -/
lemma contDiffAt_two_integral_of_compact
    {F' : V → V → V →L[ℝ] W} {F'' : V → V → V →L[ℝ] V →L[ℝ] W}
    (hK : IsCompact K) (hE : MeasurableSet E) (hEK : E ⊆ K) (hfin : μ E ≠ ⊤)
    (hU : IsOpen U)
    (hc : ∀ y ∈ U, ∀ v ∈ K, ContinuousAt (Function.uncurry F) (y, v))
    (hc' : ∀ y ∈ U, ∀ v ∈ K, ContinuousAt (Function.uncurry F') (y, v))
    (hc'' : ∀ y ∈ U, ∀ v ∈ K, ContinuousAt (Function.uncurry F'') (y, v))
    (hd : ∀ y ∈ U, ∀ v ∈ K, HasFDerivAt (fun z => F z v) (F' y v) y)
    (hd' : ∀ y ∈ U, ∀ v ∈ K, HasFDerivAt (fun z => F' z v) (F'' y v) y)
    {x : V} (hx : x ∈ U) : ContDiffAt ℝ 2 (fun y => ∫ v in E, F y v ∂μ) x := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ v in E, F' y v ∂μ, ⟨U, hU.mem_nhds hx, ?_⟩, ?_⟩
  · intro y hy
    exact hasFDerivAt_integral_of_compact hK hE hEK hfin hU hc hc' hd hy
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ v in E, F'' y v ∂μ, ⟨U, hU.mem_nhds hx, ?_⟩, ?_⟩
  · intro y hy
    exact hasFDerivAt_integral_of_compact hK hE hEK hfin hU hc' hc'' hd' hy
  exact contDiffAt_zero.mpr ⟨U, hU.mem_nhds hx, fun y hy =>
    (continuousAt_integral_of_compact hK hE hEK hfin hU hc'' hy).continuousWithinAt⟩


omit [ProperSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [CompleteSpace W] in
/-- Taking a partial derivative lowers joint regularity by one. -/
lemma contDiffAt_partial_fderiv {n : ℕ} {y v : V}
    (hc : ContDiffAt ℝ (n + 1) (Function.uncurry F) (y, v)) :
    ContDiffAt ℝ n (Function.uncurry (fun z w => fderiv ℝ (fun t => F t w) z)) (y, v) := by
  exact (hc.comp ((y, v), y)
    (contDiffAt_snd.prodMk contDiffAt_fst.snd)).fderiv contDiffAt_fst (by norm_num)

end CERW.LimitShapes.Curvature
