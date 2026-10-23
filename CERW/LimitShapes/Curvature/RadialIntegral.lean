import CERW.LimitShapes.Curvature.RadialIntegralAux

/-!
# The integrated radial curvature identity

Pointwise radial differentiation and the fundamental theorem of calculus give the
integrated form of `eq:curvature-improved`. The exceptional radial line has zero
volume, and joint absolute integrability justifies exchanging the two integrals.
-/

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory

/-- A radial line has zero ambient volume in dimension at least three. -/
theorem volume_span_unit_vector_eq_zero {d : ℕ} (hd : 3 ≤ d)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    volume (Submodule.span ℝ {u} : Set (EuclideanSpace ℝ (Fin d))) = 0 := by
  apply Measure.addHaar_submodule
  intro htop
  have hne : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hdim := finrank_span_singleton (K := ℝ) hne
  rw [htop, finrank_top, finrank_euclideanSpace_fin] at hdim
  omega

/-- Outside the radial line the evaluation point never meets a translated kernel singularity. -/
theorem sub_smul_ne_zero_of_not_mem_span {d : ℕ}
    {v u : EuclideanSpace ℝ (Fin d)} (hv : v ∉ Submodule.span ℝ {u}) (s : ℝ) :
    v - s • u ≠ 0 := by
  intro h
  apply hv
  rw [sub_eq_zero.mp h]
  exact Submodule.smul_mem _ s (Submodule.subset_span (Set.mem_singleton u))

/-- Pointwise FTC for the weighted radial kernel away from the exceptional line. -/
theorem weighted_radial_kernel_integral_identity {d : ℕ} (hd : 3 ≤ d)
    (v u : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0)
    (hline : v ∉ Submodule.span ℝ {u})
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    T ^ (d - 2) * (‖v - T • u‖ ^ ((2 : ℝ) - d) / ‖v‖) -
      t ^ (d - 2) * (‖v - t • u‖ ^ ((2 : ℝ) - d) / ‖v‖) =
      ((d : ℝ) - 2) * ∫ s in t..T,
        s ^ (d - 3) * (inner ℝ (unitDir v) (v - s • u) / ‖v - s • u‖ ^ d) := by
  have hn : ∀ s : ℝ, ‖v - s • u‖ ≠ 0 := fun s =>
    norm_ne_zero_iff.mpr (sub_smul_ne_zero_of_not_mem_span hline s)
  have hc : Continuous (fun s : ℝ =>
      s ^ (d - 3) * (inner ℝ (unitDir v) (v - s • u) / ‖v - s • u‖ ^ d)) := by
    apply Continuous.mul (by fun_prop)
    apply Continuous.div (by fun_prop) (by fun_prop)
    exact fun s => pow_ne_zero _ (hn s)
  have hder : ∀ s ∈ Set.uIcc t T, HasDerivAt
      (fun s : ℝ => s ^ (d - 2) * (‖v - s • u‖ ^ ((2 : ℝ) - d) / ‖v‖))
      (((d : ℝ) - 2) *
        (s ^ (d - 3) * (inner ℝ (unitDir v) (v - s • u) / ‖v - s • u‖ ^ d))) s := by
    intro s hs
    rw [Set.uIcc_of_le htT] at hs
    simpa only [mul_assoc] using hasDerivAt_weighted_radial_kernel hd v u s hv
      (ht.trans_le hs.1) (sub_smul_ne_zero_of_not_mem_span hline s)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((hc.const_mul ((d : ℝ) - 2)).intervalIntegrable t T)
  rw [intervalIntegral.integral_const_mul] at hf
  exact hf.symm

/-- Integrating the pointwise radial derivative gives the genuine integrated identity in
`eq:curvature-improved`, with Fubini justified by absolute Riesz integrability. -/
theorem weighted_radial_integral_identity {d : ℕ} (hd : 3 ≤ d)
    {b R : ℝ} (hb : 0 < b) (hR : b ≤ R)
    {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hband : ∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    T ^ (d - 2) * (∫ v in E, ‖v - T • u‖ ^ ((2 : ℝ) - d) / ‖v‖) -
      t ^ (d - 2) * (∫ v in E, ‖v - t • u‖ ^ ((2 : ℝ) - d) / ‖v‖) =
      ((d : ℝ) - 2) * ∫ s in t..T,
        s ^ (d - 3) * (∫ v in E,
          inner ℝ (CERW.unitDir v) (v - s • u) / ‖v - s • u‖ ^ d) := by
  let f : ℝ → EuclideanSpace ℝ (Fin d) → ℝ := fun s v =>
    ‖v - s • u‖ ^ ((2 : ℝ) - d) / ‖v‖
  let k : ℝ → EuclideanSpace ℝ (Fin d) → ℝ := fun s v =>
    inner ℝ (unitDir v) (v - s • u) / ‖v - s • u‖ ^ d
  have hf (s : ℝ) : IntegrableOn (f s) E :=
    integrableOn_radial_endpoint hd hb hE hband (s • u)
  have hfin : volume E ≠ ⊤ := volume_ne_top_of_radial_band (R := 2 * R)
    (fun v hv => by linarith [(hband v hv).2, hb.trans_le hR])
  have hprod := integrable_weighted_radial_curvature_prod hd hE hfin u ht htT
  have hswap : (∫ s in Set.Ioc t T, ∫ v in E, s ^ (d - 3) * k s v) =
      ∫ v in E, ∫ s in Set.Ioc t T, s ^ (d - 3) * k s v :=
    integral_integral_swap hprod
  have hline : ∀ᵐ v : EuclideanSpace ℝ (Fin d), v ∉ Submodule.span ℝ {u} := by
    rw [ae_iff]
    convert volume_span_unit_vector_eq_zero hd u hu using 2
    ext v
    simp only [Set.mem_setOf_eq, not_not, SetLike.mem_coe]
  have hpoint : ∀ᵐ v ∂volume.restrict E,
      T ^ (d - 2) * f T v - t ^ (d - 2) * f t v =
        ((d : ℝ) - 2) * ∫ s in t..T, s ^ (d - 3) * k s v := by
    filter_upwards [ae_restrict_mem hE, ae_restrict_of_ae hline] with v hv hvl
    have hv0 : v ≠ 0 := by
      intro hzero
      have := (hband v hv).1
      rw [hzero, norm_zero] at this
      exact (not_le_of_gt hb) this
    exact weighted_radial_kernel_integral_identity hd v u hv0 hvl ht htT
  change T ^ (d - 2) * (∫ v in E, f T v) - t ^ (d - 2) * (∫ v in E, f t v) =
    ((d : ℝ) - 2) * ∫ s in t..T, s ^ (d - 3) * (∫ v in E, k s v)
  calc
    _ = ∫ v in E, (T ^ (d - 2) * f T v - t ^ (d - 2) * f t v) := by
      rw [integral_sub ((hf T).const_mul _) ((hf t).const_mul _),
        integral_const_mul, integral_const_mul]
    _ = ∫ v in E, ((d : ℝ) - 2) *
        (∫ s in t..T, s ^ (d - 3) * k s v) := integral_congr_ae hpoint
    _ = ((d : ℝ) - 2) * ∫ v in E, ∫ s in Set.Ioc t T,
        s ^ (d - 3) * k s v := by
      rw [integral_const_mul]
      simp only [intervalIntegral.integral_of_le htT]
    _ = ((d : ℝ) - 2) * ∫ s in Set.Ioc t T, ∫ v in E,
        s ^ (d - 3) * k s v := by rw [hswap]
    _ = ((d : ℝ) - 2) * ∫ s in t..T,
        s ^ (d - 3) * (∫ v in E, k s v) := by
      rw [intervalIntegral.integral_of_le htT]
      simp only [integral_const_mul]

end CERW.LimitShapes.Curvature
