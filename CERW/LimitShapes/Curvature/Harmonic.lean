module

public import CERW.LimitShapes.Curvature.Mass
public import CERW.LimitShapes.Curvature.HarmonicKernel
public import CERW.LimitShapes.Curvature.HarmonicIntegral

@[expose] public section

/-!
# Harmonicity of the curvature integral

The curvature integral in `eq:curvature-improved` is harmonic off the closure of its
integration set. Compact bounds on the first two derivatives justify both differentiations.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory InnerProductSpace Laplacian Filter Topology

/-- The curvature integral in `eq:curvature-improved` is harmonic off the closure of `E`. -/
theorem harmonicOnNhd_curvatureIntegral {d : ℕ} (hd : 3 ≤ d)
    {b R : ℝ} (hb : 0 < b) (hR : b ≤ R)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R) :
    HarmonicOnNhd (curvatureIntegral E) (closure E)ᶜ := by
  have _hd := hd
  have _hR := hR
  let V := EuclideanSpace ℝ (Fin d)
  let K := closure E
  let U := Kᶜ
  let F : V → V → ℝ := fun y v => ‖v - y‖ ^ ((2 : ℝ) - d) / ‖v‖
  let F' : V → V → V →L[ℝ] ℝ := fun y v => fderiv ℝ (fun z => F z v) y
  let F'' : V → V → V →L[ℝ] V →L[ℝ] ℝ :=
    fun y v => fderiv ℝ (fun z => F' z v) y
  have hbandK : ∀ v ∈ K, b ≤ ‖v‖ ∧ ‖v‖ ≤ R := by
    apply closure_minimal (show E ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ R} from hband)
    exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hK : IsCompact K := by
    apply (isCompact_closedBall (0 : V) R).of_isClosed_subset isClosed_closure
    intro v hv
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hbandK v hv).2
  have hU : IsOpen U := isClosed_closure.isOpen_compl
  have hEK : E ⊆ K := subset_closure
  have hfin : volume E ≠ ⊤ := band_measure_ne_top (fun v hv => (hband v hv).2)
  have hne : ∀ y ∈ U, ∀ v ∈ K, y ≠ v := by
    intro y hy v hv h
    exact hy (h ▸ hv)
  have hc : ∀ y ∈ U, ∀ v ∈ K,
      ContDiffAt ℝ 2 (Function.uncurry F) (y, v) := by
    intro y hy v hv
    have hv0 : v ≠ 0 := norm_pos_iff.mp (hb.trans_le (hbandK v hv).1)
    have hvy : v - y ≠ 0 := sub_ne_zero.mpr (hne y hy v hv).symm
    exact (((contDiffAt_snd.sub contDiffAt_fst).norm ℝ hvy).rpow_const_of_ne
      (norm_ne_zero_iff.mpr hvy)).div (contDiffAt_snd.norm ℝ hv0)
        (norm_ne_zero_iff.mpr hv0)
  have hc' : ∀ y ∈ U, ∀ v ∈ K,
      ContDiffAt ℝ 1 (Function.uncurry F') (y, v) := by
    intro y hy v hv
    exact contDiffAt_partial_fderiv (n := 1) (hc y hy v hv)
  have hc'' : ∀ y ∈ U, ∀ v ∈ K,
      ContinuousAt (Function.uncurry F'') (y, v) := by
    intro y hy v hv
    exact (contDiffAt_partial_fderiv (n := 0) (hc' y hy v hv)).continuousAt
  have hdF : ∀ y ∈ U, ∀ v ∈ K, HasFDerivAt (fun z => F z v) (F' y v) y := by
    intro y hy v hv
    exact ((hc y hy v hv).comp y
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hdF' : ∀ y ∈ U, ∀ v ∈ K, HasFDerivAt (fun z => F' z v) (F'' y v) y := by
    intro y hy v hv
    exact ((hc' y hy v hv).comp y
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt_one.hasFDerivAt
  have hi : ∀ y ∈ U, HasFDerivAt (curvatureIntegral E) (∫ v in E, F' y v) y := by
    intro y hy
    exact hasFDerivAt_integral_of_compact hK hE hEK hfin hU
      (fun y hy v hv => (hc y hy v hv).continuousAt)
      (fun y hy v hv => (hc' y hy v hv).continuousAt) hdF hy
  have hi' : ∀ y ∈ U,
      HasFDerivAt (fun z => ∫ v in E, F' z v) (∫ v in E, F'' y v) y := by
    intro y hy
    exact hasFDerivAt_integral_of_compact hK hE hEK hfin hU
      (fun y hy v hv => (hc' y hy v hv).continuousAt) hc'' hdF' hy
  have hreg : ∀ y ∈ U, ContDiffAt ℝ 2 (curvatureIntegral E) y := by
    intro y hy
    exact contDiffAt_two_integral_of_compact hK hE hEK hfin hU
      (fun y hy v hv => (hc y hy v hv).continuousAt)
      (fun y hy v hv => (hc' y hy v hv).continuousAt) hc'' hdF hdF' hy
  have hlap : ∀ y ∈ U, laplacian (curvatureIntegral E) y = 0 := by
    intro y hy
    have he : fderiv ℝ (curvatureIntegral E) =ᶠ[𝓝 y] fun z => ∫ v in E, F' z v := by
      filter_upwards [hU.mem_nhds hy] with z hz using (hi z hz).fderiv
    have he' : fderiv ℝ (fderiv ℝ (curvatureIntegral E)) y = ∫ v in E, F'' y v := by
      rw [he.fderiv_eq, (hi' y hy).fderiv]
    obtain ⟨s, hs, -, C, hC⟩ := integral_compact_local_bound
      (F := F'') hK hE hEK hfin hU hc'' hy
    have hint := (hC y (mem_of_mem_nhds hs)).1
    let e := EuclideanSpace.basisFun (Fin d) ℝ
    have hint₁ (i : Fin d) := hint.apply_continuousLinearMap (e i)
    have hint' : ∀ i : Fin d, IntegrableOn (fun v => F'' y v (e i) (e i)) E := by
      intro i
      exact (hint₁ i).apply_continuousLinearMap (e i)
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ e]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, he']
    have hcomm : ∀ i : Fin d,
        (∫ v in E, F'' y v) (e i) (e i) = ∫ v in E, F'' y v (e i) (e i) := by
      intro i
      rw [ContinuousLinearMap.integral_apply hint,
        ContinuousLinearMap.integral_apply (hint₁ i)]
    simp_rw [hcomm]
    rw [← integral_finsetSum Finset.univ (fun i _ => hint' i)]
    have hzero : ∀ v ∈ E, (∑ i : Fin d, F'' y v (e i) (e i)) = 0 := by
      intro v hv
      have hh := (harmonicAt_curvatureKernel v y (hne y hy v (hEK hv))).2
      have hz : laplacian (fun z => F z v) y = 0 := hh.eq_of_nhds
      rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ e] at hz
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using hz
    rw [setIntegral_congr_fun hE hzero]
    exact integral_zero _ _
  intro y hy
  refine ⟨hreg y hy, ?_⟩
  filter_upwards [hU.mem_nhds hy] with z hz using hlap z hz

end CERW.LimitShapes.Curvature
