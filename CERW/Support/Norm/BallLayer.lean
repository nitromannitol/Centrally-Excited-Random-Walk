import CERW.Model
import CERW.Generic.Norm.Gradient
import CERW.Generic.Norm.Subgradient
import CERW.Generic.Norm.Sphere
import CERW.Generic.Kernel.Integrable
import CERW.Generic.Newton.Polar
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The potential of a norm ball and of a layer between two norm balls

Polar coordinates about a point `y` turn the potential
`U_D(y) = (2ε/ω_d) ∫_D ∇Ψ(v) · (v - y) |v - y|^{-d} dv` of a norm `Ψ` into a spherical average of
integrals along rays. Writing `v = y + tθ`, one has `(v - y)|v - y|^{-d} dv = θ dt dσ(θ)`, and by
Rademacher's theorem, for almost every `θ` the function `t ↦ Ψ(y + tθ)` has derivative
`∇Ψ(y + tθ) · θ` for almost every `t` (`normPotential_eq_integral_sphere_ray`). Along a ray the
integral of the derivative is a change of `Ψ`. For the ball `{Ψ < ρ}` it is `(ρ - Ψ(y))_+`
(`norm_ball_potential`, `lem:ballpotential`). For a set between the level sets `b` and `b + a` the
convexity of `t ↦ Ψ(y + tθ)` bounds it by `a` in absolute value (`layer_potential`, `lem:layer`).
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

section Polar

variable {d : ℕ}

/-- Polar coordinates: the image of the product of the sphere measure and the radial measure
`r^{d-1} dr` under `(θ, r) ↦ rθ` is Lebesgue measure. -/
theorem map_polar_eq_volume (hd : 1 ≤ d) :
    Measure.map (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Set.Ioi (0 : ℝ) =>
        p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d)))
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
        (Measure.volumeIoiPow (d - 1))) = volume := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure (EuclideanSpace ℝ (Fin d)))
  rw [hfin] at hmp
  have hsymm := hmp.symm (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d))).toMeasurableEquiv
  have hΦ : (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Set.Ioi (0 : ℝ) =>
        p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d))) =
      Subtype.val ∘ (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d))).symm := by
    funext p
    simp
  have hmap : Measure.map (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d))).symm
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
        (Measure.volumeIoiPow (d - 1))) = Measure.comap Subtype.val volume := hsymm.map_eq
  rw [hΦ, ← Measure.map_map measurable_subtype_coe (Homeomorph.measurable _),
    hmap, (MeasurableEmbedding.subtype_coe
      (measurableSet_singleton _).compl).map_comap, Subtype.range_coe, restrict_compl_singleton]

/-- The polar-coordinate map `(θ, r) ↦ rθ` is measurable. -/
private lemma measurable_polar :
    Measurable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Set.Ioi (0 : ℝ) =>
      p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d))) :=
  (measurable_subtype_coe.comp measurable_snd).smul (measurable_subtype_coe.comp measurable_fst)

/-- The integral against the radial measure `r^n dr` on `(0, ∞)`, written as an integral over the
half line. -/
private lemma integral_volumeIoiPow (n : ℕ) (g : ℝ → ℝ) :
    ∫ r : Set.Ioi (0 : ℝ), g r.1 ∂Measure.volumeIoiPow n =
      ∫ r in Set.Ioi (0 : ℝ), r ^ n * g r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi fun a : ℝ => Real.toNNReal (a ^ n) • g a,
    setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_]
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]
    rfl
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- Integration in polar coordinates with the sphere outermost: for integrable `f`,
`∫ f = ∫_S ∫_0^∞ r^{d-1} f(rθ) dr dσ(θ)`. -/
theorem integral_eq_integral_sphere_Ioi (hd : 1 ≤ d) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Integrable f) :
    ∫ v, f v = ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      (∫ t in Set.Ioi (0 : ℝ), t ^ (d - 1) * f (t • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have hmap := map_polar_eq_volume (d := d) hd
  have hΦ := measurable_polar (d := d)
  have hg := CERW.Generic.Newton.integrable_prod_polar hf
  have h1 : ∫ v, f v = ∫ p, f (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d)))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
        (Measure.volumeIoiPow (d - 1))) := by
    have hf' : AEStronglyMeasurable f (Measure.map
        (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Set.Ioi (0 : ℝ) =>
          p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d)))
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
          (Measure.volumeIoiPow (d - 1)))) := by
      rw [hmap]
      exact hf.aestronglyMeasurable
    rw [← integral_map hΦ.aemeasurable hf', hmap]
  rw [h1, integral_prod _ hg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  exact integral_volumeIoiPow (d - 1) (fun t => f (t • (θ : EuclideanSpace ℝ (Fin d))))

/-- The radial measure `r^n dr` on `(0, ∞)` has the same null sets as Lebesgue measure. -/
private lemma comap_absolutelyContinuous_volumeIoiPow (n : ℕ) :
    Measure.comap Subtype.val (volume : Measure ℝ) ≪
      (Measure.volumeIoiPow n : Measure (Set.Ioi (0 : ℝ))) := by
  unfold Measure.volumeIoiPow
  refine withDensity_absolutelyContinuous'
      (measurable_subtype_coe.pow_const _).ennreal_ofReal.aemeasurable ?_
  refine Filter.Eventually.of_forall fun r => ?_
  exact (ENNReal.ofReal_pos.2 (pow_pos (Set.mem_Ioi.1 r.2) _)).ne'

/-- A property that holds at Lebesgue-almost every point holds, for almost every direction `θ` of
the unit sphere, at almost every point `tθ`, `t > 0`, of the ray in direction `θ`. -/
theorem ae_sphere_ae_Ioi_smul {P : EuclideanSpace ℝ (Fin d) → Prop} (hd : 1 ≤ d)
    (hP : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), P w) :
    ∀ᵐ θ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere,
      ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi 0),
        P (t • ((θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
          EuclideanSpace ℝ (Fin d))) := by
  have hmap := map_polar_eq_volume (d := d) hd
  have hΦ := measurable_polar (d := d)
  set N : Set (EuclideanSpace ℝ (Fin d)) := toMeasurable volume {w | ¬ P w} with hN
  have hNmeas : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hN, measure_toMeasurable]
    exact ae_iff.1 hP
  have hB : MeasurableSet ((fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
      Set.Ioi (0 : ℝ) => p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d))) ⁻¹' N) := hΦ hNmeas
  have hμB : ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
      (Measure.volumeIoiPow (d - 1))) ((fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
      Set.Ioi (0 : ℝ) => p.2.1 • (p.1 : EuclideanSpace ℝ (Fin d))) ⁻¹' N) = 0 := by
    rw [← Measure.map_apply hΦ hNmeas, hmap]
    exact hN0
  filter_upwards [(Measure.measure_prod_null hB).1 hμB] with θ hθ
  have h2 := measure_eq_zero_iff_ae_notMem.1 hθ
  have h2' : ∀ᵐ r : Set.Ioi (0 : ℝ) ∂Measure.volumeIoiPow (d - 1),
      (r : ℝ) • (θ : EuclideanSpace ℝ (Fin d)) ∉ N := h2
  have h3 : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi 0),
      t • (θ : EuclideanSpace ℝ (Fin d)) ∉ N :=
    (ae_restrict_iff_subtype measurableSet_Ioi).2
      ((comap_absolutelyContinuous_volumeIoiPow (d - 1)).ae_le h2')
  filter_upwards [h3] with t ht
  by_contra hnot
  exact ht (subset_toMeasurable _ _ hnot)

end Polar

section OneVariable

/-- The derivative of a Lipschitz function is integrable on every set of finite measure. -/
private lemma integrableOn_deriv_of_lipschitz {h : ℝ → ℝ} {K : ℝ≥0} (hK : LipschitzWith K h)
    {S : Set ℝ} (hS : volume S ≠ ⊤) : IntegrableOn (deriv h) S :=
  Measure.integrableOn_of_bounded (M := K) hS (measurable_deriv h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hK)

/-- If the derivative of a Lipschitz function `h` is almost everywhere nonnegative on a closed
interval `I`, then the integral of `h'` over a bounded measurable subset `S` of `I` on which `h`
takes values in `[b, b + a]` lies in `[0, a]`: it is at most the increase of `h` between the
extreme points of `S`. -/
private lemma setIntegral_deriv_mem_Icc {h : ℝ → ℝ} {K : ℝ≥0} (hK : LipschitzWith K h)
    {I : Set ℝ} (hI : IsClosed I) (hIc : I.OrdConnected)
    (hpos : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ I → 0 ≤ deriv h t)
    {S : Set ℝ} (hS : MeasurableSet S) (hSb : Bornology.IsBounded S) (hSI : S ⊆ I)
    {b a : ℝ} (ha : 0 ≤ a) (hSh : ∀ t ∈ S, b ≤ h t ∧ h t ≤ b + a) :
    0 ≤ ∫ t in S, deriv h t ∧ ∫ t in S, deriv h t ≤ a := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [ha]
  have hbdd : BddBelow S := hSb.bddBelow
  have hbdd' : BddAbove S := hSb.bddAbove
  have hs1 : sInf S ∈ closure S := csInf_mem_closure hne hbdd
  have hs2 : sSup S ∈ closure S := csSup_mem_closure hne hbdd'
  have hcl : closure S ⊆ I := closure_minimal hSI hI
  have hsub : S ⊆ Set.Icc (sInf S) (sSup S) := fun t ht => ⟨csInf_le hbdd ht, le_csSup hbdd' ht⟩
  have hIcc : Set.Icc (sInf S) (sSup S) ⊆ I := hIc.out (hcl hs1) (hcl hs2)
  have hh1 : b ≤ h (sInf S) := by
    have hc : closure S ⊆ {t | b ≤ h t} :=
      closure_minimal (fun t ht => (hSh t ht).1) (isClosed_le continuous_const hK.continuous)
    exact hc hs1
  have hh2 : h (sSup S) ≤ b + a := by
    have hc : closure S ⊆ {t | h t ≤ b + a} :=
      closure_minimal (fun t ht => (hSh t ht).2) (isClosed_le hK.continuous continuous_const)
    exact hc hs2
  have hle : sInf S ≤ sSup S := csInf_le_csSup hne hbdd hbdd'
  have hint : IntegrableOn (deriv h) (Set.Icc (sInf S) (sSup S)) :=
    integrableOn_deriv_of_lipschitz hK measure_Icc_lt_top.ne
  have hnn : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc (sInf S) (sSup S)),
      0 ≤ deriv h t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hpos] with t ht htI using ht (hIcc htI)
  have hFTC : ∫ t in Set.Icc (sInf S) (sSup S), deriv h t = h (sSup S) - h (sInf S) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    exact hK.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  refine ⟨setIntegral_nonneg_of_ae_restrict ?_, ?_⟩
  · refine (ae_restrict_iff' hS).2 ?_
    filter_upwards [hpos] with t ht htS using ht (hSI htS)
  · calc ∫ t in S, deriv h t ≤ ∫ t in Set.Icc (sInf S) (sSup S), deriv h t :=
          setIntegral_mono_set hint hnn hsub.eventuallyLE
      _ = h (sSup S) - h (sInf S) := hFTC
      _ ≤ a := by linarith

/-- A convex function attaining its minimum at `t₀` is nondecreasing on `[t₀, ∞)`. -/
private lemma monotoneOn_Ici_of_isMin {h : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ h) {t₀ : ℝ}
    (hmin : ∀ t, h t₀ ≤ h t) : MonotoneOn h (Set.Ici t₀) := by
  intro s hs u _ hsu
  rcases eq_or_lt_of_le (Set.mem_Ici.1 hs) with rfl | hlt
  · exact hmin u
  rcases eq_or_lt_of_le hsu with rfl | hlt'
  · exact le_rfl
  have hz : s ∈ openSegment ℝ t₀ u := by
    rw [openSegment_eq_Ioo (hlt.trans hlt')]
    exact ⟨hlt, hlt'⟩
  exact hconv.le_right_of_left_le (Set.mem_univ _) (Set.mem_univ _) hz (hmin s)

/-- A convex function attaining its minimum at `t₀` is nonincreasing on `(-∞, t₀]`. -/
private lemma antitoneOn_Iic_of_isMin {h : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ h) {t₀ : ℝ}
    (hmin : ∀ t, h t₀ ≤ h t) : AntitoneOn h (Set.Iic t₀) := by
  intro s _ u hu hsu
  rcases eq_or_lt_of_le (Set.mem_Iic.1 hu) with rfl | hlt
  · exact hmin s
  rcases eq_or_lt_of_le hsu with rfl | hlt'
  · exact le_rfl
  have hz : u ∈ openSegment ℝ s t₀ := by
    rw [openSegment_eq_Ioo (hlt'.trans hlt)]
    exact ⟨hlt', hlt⟩
  exact hconv.le_left_of_right_le (Set.mem_univ _) (Set.mem_univ _) hz (hmin u)

/-- For a convex Lipschitz function `h` with `h(t) ≥ c|t| - m` for some `c > 0`, the integral of
`h'` over a measurable set on which `h` takes values in `[b, b + a]` has absolute value at most
`a`. -/
private lemma abs_setIntegral_deriv_le {h : ℝ → ℝ} {K : ℝ≥0} (hK : LipschitzWith K h)
    (hconv : ConvexOn ℝ Set.univ h) {c m : ℝ} (hc : 0 < c) (hcoer : ∀ t, c * |t| - m ≤ h t)
    {S : Set ℝ} (hS : MeasurableSet S) {b a : ℝ} (ha : 0 ≤ a)
    (hSh : ∀ t ∈ S, b ≤ h t ∧ h t ≤ b + a) :
    |∫ t in S, deriv h t| ≤ a := by
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := (b + a + m) / c)).subset ?_
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, le_div_iff₀ hc]
    have := hcoer t
    have := (hSh t ht).2
    linarith
  have hlim : Tendsto h (cocompact ℝ) atTop := by
    have h1 : Tendsto (fun t : ℝ => c * ‖t‖ - m) (cocompact ℝ) atTop :=
      tendsto_atTop_add_const_right _ (-m)
        (Tendsto.const_mul_atTop hc tendsto_norm_cocompact_atTop) |>.congr fun t => by ring
    exact tendsto_atTop_mono (fun t => by simpa using hcoer t) h1
  obtain ⟨t₀, hmin⟩ := hK.continuous.exists_forall_le hlim
  have hmono := monotoneOn_Ici_of_isMin hconv hmin
  have hanti := antitoneOn_Iic_of_isMin hconv hmin
  have hpos₁ : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ici t₀ → 0 ≤ deriv h t := by
    filter_upwards [(Set.countable_singleton t₀).ae_notMem (volume : Measure ℝ)] with t ht htI
    have hne : t ≠ t₀ := fun h' => ht (by simp [h'])
    have hmem : Set.Ici t₀ ∈ 𝓝 t := Ici_mem_nhds (lt_of_le_of_ne htI (Ne.symm hne))
    rw [← derivWithin_of_mem_nhds hmem]
    exact hmono.derivWithin_nonneg
  have hpos₂ : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Iic t₀ → 0 ≤ deriv (fun s => -h s) t := by
    filter_upwards [(Set.countable_singleton t₀).ae_notMem (volume : Measure ℝ)] with t ht htI
    have hne : t ≠ t₀ := fun h' => ht (by simp [h'])
    have hmem : Set.Iic t₀ ∈ 𝓝 t := Iic_mem_nhds (lt_of_le_of_ne htI hne)
    rw [← derivWithin_of_mem_nhds hmem]
    exact (hanti.neg : MonotoneOn (fun s => -h s) (Set.Iic t₀)).derivWithin_nonneg
  have hS₁ : MeasurableSet (S ∩ Set.Ici t₀) := hS.inter measurableSet_Ici
  have hS₂ : MeasurableSet (S ∩ Set.Iio t₀) := hS.inter measurableSet_Iio
  have hIcc₁ : S ∩ Set.Ici t₀ ⊆ Set.Ici t₀ := Set.inter_subset_right
  have hIcc₂ : S ∩ Set.Iio t₀ ⊆ Set.Iic t₀ := fun t ht => le_of_lt (Set.mem_Iio.1 ht.2)
  have hb₁ := hSb.subset (Set.inter_subset_left : S ∩ Set.Ici t₀ ⊆ S)
  have hb₂ := hSb.subset (Set.inter_subset_left : S ∩ Set.Iio t₀ ⊆ S)
  obtain ⟨h₁, h₁'⟩ : 0 ≤ ∫ t in S ∩ Set.Ici t₀, deriv h t ∧
      ∫ t in S ∩ Set.Ici t₀, deriv h t ≤ a :=
    setIntegral_deriv_mem_Icc hK isClosed_Ici Set.ordConnected_Ici hpos₁ hS₁ hb₁ hIcc₁ ha
      fun t ht => hSh t ht.1
  obtain ⟨h₂, h₂'⟩ : 0 ≤ ∫ t in S ∩ Set.Iio t₀, deriv (fun s => -h s) t ∧
      ∫ t in S ∩ Set.Iio t₀, deriv (fun s => -h s) t ≤ a :=
    setIntegral_deriv_mem_Icc (h := fun s => -h s) hK.neg isClosed_Iic Set.ordConnected_Iic hpos₂
      hS₂ hb₂ hIcc₂ (b := -(b + a)) ha
      fun t ht => ⟨by linarith [(hSh t ht.1).2], by linarith [(hSh t ht.1).1]⟩
  have hneg : ∫ t in S ∩ Set.Iio t₀, deriv (fun s => -h s) t =
      -∫ t in S ∩ Set.Iio t₀, deriv h t := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [deriv.fun_neg])
  have hsplit : ∫ t in S, deriv h t =
      (∫ t in S ∩ Set.Ici t₀, deriv h t) + ∫ t in S ∩ Set.Iio t₀, deriv h t := by
    have hunion : S = (S ∩ Set.Ici t₀) ∪ (S ∩ Set.Iio t₀) := by
      ext t
      by_cases ht : t₀ ≤ t <;> simp [ht, not_le.1]
    have hdisj : Disjoint (S ∩ Set.Ici t₀) (S ∩ Set.Iio t₀) := by
      refine Set.disjoint_left.2 fun t ht₁ ht₂ => ?_
      exact absurd (Set.mem_Ici.1 ht₁.2) (not_le.2 (Set.mem_Iio.1 ht₂.2))
    conv_lhs => rw [hunion]
    exact setIntegral_union hdisj hS₂ (integrableOn_deriv_of_lipschitz hK hb₁.measure_lt_top.ne)
      (integrableOn_deriv_of_lipschitz hK hb₂.measure_lt_top.ne)
  rw [hsplit]
  rw [hneg] at h₂ h₂'
  rw [abs_le]
  constructor <;> linarith

/-- The derivative of the truncation `(ρ - h)_+` of a function `h` continuous at `t` is
`-1_{h < ρ} h'` at `t`; at a point where `h = ρ` the truncation has a minimum. -/
private lemma deriv_max_sub_zero {h : ℝ → ℝ} {K : ℝ≥0} (hK : LipschitzWith K h) (ρ t : ℝ) :
    deriv (fun s => max (ρ - h s) 0) t = -{s | h s < ρ}.indicator (deriv h) t := by
  rcases lt_trichotomy (h t) ρ with hlt | heq | hgt
  · have hev : (fun s => max (ρ - h s) 0) =ᶠ[𝓝 t] fun s => ρ - h s := by
      filter_upwards [hK.continuous.continuousAt.eventually_lt continuousAt_const hlt] with s hs
      exact max_eq_left (by linarith)
    rw [hev.deriv_eq, deriv_const_sub, Set.indicator_of_mem (show t ∈ {s | h s < ρ} from hlt)]
  · have hmin : IsLocalMin (fun s => max (ρ - h s) 0) t :=
      Filter.Eventually.of_forall fun s => by
        simp [heq]
    rw [hmin.deriv_eq_zero, Set.indicator_of_notMem (show t ∉ {s | h s < ρ} by simp [heq])]
    simp
  · have hev : (fun s => max (ρ - h s) 0) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [continuousAt_const.eventually_lt hK.continuous.continuousAt hgt]
        with s hs
      exact max_eq_right (by linarith)
    rw [hev.deriv_eq, Set.indicator_of_notMem (show t ∉ {s | h s < ρ} by simpa using hgt.le)]
    simp

/-- If `h` is Lipschitz and `h ≥ ρ` on `[T, ∞)` for some `T ≥ 0`, then the integral of `h'` over
`{t > 0 : h(t) < ρ}` is `(ρ - h(0))_+`: it is the drop of the truncation `(ρ - h)_+`. -/
private lemma setIntegral_deriv_lt {h : ℝ → ℝ} {K : ℝ≥0} (hK : LipschitzWith K h) {ρ T : ℝ}
    (hT : 0 ≤ T) (hρ : ∀ t, T ≤ t → ρ ≤ h t) :
    ∫ t in {t : ℝ | 0 < t ∧ h t < ρ}, deriv h t = max (ρ - h 0) 0 := by
  have hk : LipschitzWith K (fun s => max (ρ - h s) 0) := by
    refine LipschitzWith.of_dist_le_mul fun s u => ?_
    rw [Real.dist_eq, Real.dist_eq]
    calc |max (ρ - h s) 0 - max (ρ - h u) 0|
        ≤ |(ρ - h s) - (ρ - h u)| := abs_max_sub_max_le_abs _ _ _
      _ = |h u - h s| := by ring_nf
      _ = |h s - h u| := abs_sub_comm _ _
      _ ≤ K * |s - u| := by
          have := hK.dist_le_mul s u
          rwa [Real.dist_eq, Real.dist_eq] at this
  have hmeas : MeasurableSet {s : ℝ | h s < ρ} :=
    measurableSet_lt hK.continuous.measurable measurable_const
  have hFTC := hk.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    (a := 0) (b := T)
  have hkT : max (ρ - h T) 0 = 0 := max_eq_right (by linarith [hρ T le_rfl])
  have hset : {t : ℝ | 0 < t ∧ h t < ρ} = Set.Ioc 0 T ∩ {s | h s < ρ} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨ht, hlt⟩
      exact ⟨⟨ht, not_lt.1 fun hTt => absurd (hρ t hTt.le) (not_le.2 hlt)⟩, hlt⟩
    · rintro ⟨⟨ht, _⟩, hlt⟩
      exact ⟨ht, hlt⟩
  rw [intervalIntegral.integral_of_le hT] at hFTC
  simp_rw [deriv_max_sub_zero hK ρ] at hFTC
  rw [integral_neg, setIntegral_indicator hmeas, hkT] at hFTC
  rw [hset]
  linarith

end OneVariable

section NormRays

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A norm is Lipschitz, with constant the positive part of `Σ_i Ψ(e_i)`. -/
private lemma lipschitzWith_isNorm (hΨ : CERW.IsNorm Ψ) :
    LipschitzWith (Real.toNNReal (∑ i, Ψ (CERW.coordVec i))) Ψ := by
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  exact CERW.Generic.Norm.abs_sub_le_sum_mul hΨ x y

/-- The gradient of a norm has norm at most the Lipschitz constant of the norm. -/
private lemma norm_gradient_le (hΨ : CERW.IsNorm Ψ) (v : EuclideanSpace ℝ (Fin d)) :
    ‖gradient Ψ v‖ ≤ (Real.toNNReal (∑ i, Ψ (CERW.coordVec i)) : ℝ) := by
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := v) (lipschitzWith_isNorm hΨ)
  have h' : ‖gradient Ψ v‖ = ‖fderiv ℝ Ψ v‖ := by
    unfold gradient
    exact LinearIsometryEquiv.norm_map _ _
  rwa [h']

/-- Restricted to a line through `y` in a unit direction, a norm is Lipschitz in the parameter. -/
private lemma lipschitzWith_ray (hΨ : CERW.IsNorm Ψ) (y : EuclideanSpace ℝ (Fin d))
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) :
    LipschitzWith (Real.toNNReal (∑ i, Ψ (CERW.coordVec i))) (fun t : ℝ => Ψ (y + t • θ)) := by
  refine LipschitzWith.of_dist_le_mul fun s u => ?_
  rw [Real.dist_eq, Real.dist_eq]
  have h := CERW.Generic.Norm.abs_sub_le_sum_mul hΨ (y + s • θ) (y + u • θ)
  have hn : ‖(y + s • θ) - (y + u • θ)‖ = |s - u| := by
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hθ, mul_one, Real.norm_eq_abs]
  rw [hn] at h
  exact h.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (abs_nonneg _))

/-- Restricted to a line, a norm is convex in the parameter. -/
private lemma convexOn_ray (hΨ : CERW.IsNorm Ψ) (y θ : EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Ψ (y + t • θ)) := by
  refine ⟨convex_univ, fun s _ u _ a b ha hb hab => ?_⟩
  have hpt : y + (a • s + b • u) • θ = a • (y + s • θ) + b • (y + u • θ) := by
    obtain rfl : b = 1 - a := by linarith
    simp only [smul_eq_mul]
    module
  simp only [smul_eq_mul]
  calc Ψ (y + (a * s + b * u) • θ)
      = Ψ (a • (y + s • θ) + b • (y + u • θ)) := by rw [← hpt, smul_eq_mul, smul_eq_mul]
    _ ≤ Ψ (a • (y + s • θ)) + Ψ (b • (y + u • θ)) := hΨ.add_le _ _
    _ = a * Ψ (y + s • θ) + b * Ψ (y + u • θ) := by
        rw [hΨ.smul, hΨ.smul, abs_of_nonneg ha, abs_of_nonneg hb]

/-- Along a line through `y`, a norm grows at least linearly: `Ψ(y + tθ) ≥ Ψ(θ)|t| - Ψ(y)`. -/
private lemma coercive_ray (hΨ : CERW.IsNorm Ψ) (y θ : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Ψ θ * |t| - Ψ y ≤ Ψ (y + t • θ) := by
  have h1 : Ψ (t • θ) = |t| * Ψ θ := hΨ.smul t θ
  have h2 : Ψ (t • θ) ≤ Ψ (y + t • θ) + Ψ y := by
    have h := hΨ.add_le (y + t • θ) (-y)
    rwa [show y + t • θ + -y = t • θ by abel,
      (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.2 y] at h
  linarith [mul_comm (Ψ θ) |t|]

/-- A point of the Euclidean unit sphere has norm one. -/
private lemma norm_eq_one_of_mem_sphere
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
  rw [← dist_zero_right]
  exact Metric.mem_sphere.mp θ.2

/-- A norm is positive at a vector of Euclidean norm one. -/
private lemma pos_of_norm_eq_one (hΨ : CERW.IsNorm Ψ) {θ : EuclideanSpace ℝ (Fin d)}
    (hθ : ‖θ‖ = 1) : 0 < Ψ θ := by
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hθ
    exact zero_ne_one hθ
  exact lt_of_le_of_ne ((CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 θ)
    fun h0 => hθ0 (hΨ.eq_zero θ h0.symm)

/-- The sphere measure of the whole unit sphere is `d ω_d`. -/
private lemma toSphere_real_univ :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).real Set.univ =
      d * CERW.unitBallVolume d := by
  rw [MeasureTheory.Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
  rfl

/-- The sublevel sets `{Ψ ≤ r}` of a norm are bounded. -/
private lemma isBounded_sublevel (hΨ : CERW.IsNorm Ψ) (hd : 1 ≤ d) (r : ℝ) :
    Bornology.IsBounded {v | Ψ v ≤ r} := by
  obtain ⟨hc, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d)))
    (r := r / CERW.normMin Ψ)).subset fun v hv => ?_
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc, mul_comm]
  exact (hcle v).trans hv

/-- The parameters `t` for which the point `y + tθ` of the ray lies in a measurable set form a
measurable set. -/
private lemma measurableSet_ray {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (y θ : EuclideanSpace ℝ (Fin d)) : MeasurableSet {t : ℝ | y + t • θ ∈ D} :=
  (measurable_const.add (measurable_id.smul_const _)) hD

/-- For `t > 0`, the quotient `t / t ^ d` is the real power `t ^ (1 - d)`. -/
private lemma div_pow_eq_rpow_one_sub {t : ℝ} (ht : 0 < t) (d : ℕ) :
    t / t ^ d = t ^ (1 - (d : ℝ)) := by
  have h₁ : t / t ^ d = t ^ (1 : ℝ) / t ^ (d : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_one]
  rw [h₁, ← Real.rpow_sub ht (1 : ℝ) (d : ℝ)]

/-- Where `Ψ` is differentiable at `y + tθ`, the function `s ↦ Ψ(y + sθ)` has derivative
`∇Ψ(y + tθ) · θ` at `t`. -/
private lemma hasDerivAt_ray (y θ : EuclideanSpace ℝ (Fin d)) {t : ℝ}
    (h : DifferentiableAt ℝ Ψ (y + t • θ)) :
    HasDerivAt (fun s : ℝ => Ψ (y + s • θ)) (inner ℝ (gradient Ψ (y + t • θ)) θ) t := by
  have hpath : HasDerivAt (fun s : ℝ => y + s • θ) θ t := by
    simpa using ((hasDerivAt_id' t).smul_const θ).const_add y
  have hc := HasFDerivAt.comp_hasDerivAt_of_eq t h.hasGradientAt.hasFDerivAt hpath rfl
  exact hc

/-- The gradient `v ↦ ∇Ψ(v)` is measurable. -/
private lemma measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- On a measurable set of finite volume, the integrand `∇Ψ(v) · (v - y) |v - y|^{-d}` of the
potential of a norm is integrable. -/
private lemma integrableOn_gradient_kernel (hd : 1 ≤ d) (hΨ : CERW.IsNorm Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d) D := by
  obtain ⟨hint, -⟩ := CERW.Generic.Kernel.integrableOn_and_setIntegral_le hd hD hDfin y
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
    measurable_id.sub measurable_const
  refine (hint.const_mul (Real.toNNReal (∑ i, Ψ (CERW.coordVec i)) : ℝ)).mono'
    (((measurable_gradient Ψ).inner hsub).div (hsub.norm.pow_const d)).aestronglyMeasurable ?_
  filter_upwards with v
  rcases eq_or_ne v y with rfl | hne
  · simp only [sub_self, inner_zero_right, zero_div, norm_zero]
    exact mul_nonneg NNReal.zero_le_coe (Real.rpow_nonneg le_rfl _)
  · have hw : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < ‖v - y‖ ^ d := pow_pos hw d
    have h1 : ‖inner ℝ (gradient Ψ v) (v - y)‖ ≤
        (Real.toNNReal (∑ i, Ψ (CERW.coordVec i)) : ℝ) * ‖v - y‖ :=
      (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_gradient_le hΨ v) (norm_nonneg _))
    rw [norm_div, norm_pow, norm_norm, div_le_iff₀ hden, ← div_pow_eq_rpow_one_sub hw d,
      mul_assoc, div_mul_cancel₀ _ hden.ne']
    exact h1

/-- For `t > 0` and a unit vector `θ`, the integrand of the potential of a norm at `y + tθ`, times
the polar weight `t^{d-1}`, is the directional derivative `∇Ψ(y + tθ) · θ` if `y + tθ ∈ D` and `0`
otherwise. -/
private lemma radial_weight_kernel {D : Set (EuclideanSpace ℝ (Fin d))} (hd : 1 ≤ d)
    (y : EuclideanSpace ℝ (Fin d)) {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) {t : ℝ}
    (ht : 0 < t) :
    t ^ (d - 1) * D.indicator (fun v => inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d)
        (y + t • θ) =
      {s : ℝ | y + s • θ ∈ D}.indicator (fun s => inner ℝ (gradient Ψ (y + s • θ)) θ) t := by
  by_cases hmem : y + t • θ ∈ D
  · rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (show t ∈ {s : ℝ | y + s • θ ∈ D} from hmem)]
    have hn : ‖t • θ‖ = t := by
      rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos ht]
    rw [add_sub_cancel_left, hn, real_inner_smul_right]
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (show t ∉ {s : ℝ | y + s • θ ∈ D} from hmem), mul_zero]

/-- **Ray decomposition of the potential of a norm.** For a bounded measurable `D`, writing
`v = y + tθ`, the potential is `(2ε/ω_d)` times the spherical integral over `θ` of the integral of
`(d/dt) Ψ(y + tθ)` over `{t > 0 : y + tθ ∈ D}`. -/
theorem normPotential_eq_integral_sphere_ray (hd : 1 ≤ d) (hΨ : CERW.IsNorm Ψ) (ε : ℝ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (y : EuclideanSpace ℝ (Fin d)) :
    CERW.normPotential d ε Ψ D y = 2 * ε / CERW.unitBallVolume d *
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (∫ t in {t : ℝ | 0 < t ∧ y + t • (θ : EuclideanSpace ℝ (Fin d)) ∈ D},
          deriv (fun s : ℝ => Ψ (y + s • (θ : EuclideanSpace ℝ (Fin d)))) t)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  unfold CERW.normPotential
  congr 1
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun v => inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d
  have hFint : IntegrableOn F D := integrableOn_gradient_kernel hd hΨ hD hDb.measure_lt_top.ne y
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun w => D.indicator F (y + w)
  have hfint : Integrable f :=
    ((integrable_indicator_iff hD).2 hFint).comp_add_left y
  have h1 : ∫ v in D, F v = ∫ w, f w := by
    rw [← integral_indicator hD]
    exact (integral_add_left_eq_self (μ := volume) (fun v => D.indicator F v) y).symm
  rw [h1, integral_eq_integral_sphere_Ioi hd hfint]
  have hdiff : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      DifferentiableAt ℝ Ψ (y + w) :=
    (quasiMeasurePreserving_add_left volume y).ae (CERW.Generic.Norm.ae_differentiableAt hΨ)
  refine integral_congr_ae ?_
  filter_upwards [ae_sphere_ae_Ioi_smul hd hdiff] with θ hθ
  have hθn := norm_eq_one_of_mem_sphere θ
  have hmeas := measurableSet_ray hD y (θ : EuclideanSpace ℝ (Fin d))
  calc ∫ t in Set.Ioi (0 : ℝ), t ^ (d - 1) * f (t • (θ : EuclideanSpace ℝ (Fin d)))
      = ∫ t in Set.Ioi (0 : ℝ), {s : ℝ | y + s • (θ : EuclideanSpace ℝ (Fin d)) ∈ D}.indicator
          (fun s => inner ℝ (gradient Ψ (y + s • (θ : EuclideanSpace ℝ (Fin d)))) θ) t :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht =>
          radial_weight_kernel hd y hθn (Set.mem_Ioi.1 ht)
    _ = ∫ t in Set.Ioi (0 : ℝ) ∩ {s : ℝ | y + s • (θ : EuclideanSpace ℝ (Fin d)) ∈ D},
          inner ℝ (gradient Ψ (y + t • (θ : EuclideanSpace ℝ (Fin d)))) θ :=
        setIntegral_indicator hmeas
    _ = _ := by
        refine setIntegral_congr_ae (measurableSet_Ioi.inter hmeas) ?_
        filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hθ] with t ht htS
        exact (hasDerivAt_ray y θ (ht htS.1)).deriv.symm

end NormRays

theorem norm_ball_potential {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) (ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin d)) :
    CERW.normPotential d ε Ψ {v | Ψ v < ρ} y = 2 * d * ε * max (ρ - Ψ y) 0 := by
  have hd1 : 1 ≤ d := by omega
  have hnonneg := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1
  have hD : MeasurableSet {v | Ψ v < ρ} :=
    measurableSet_lt (CERW.Generic.Norm.norm_continuous hΨ).measurable measurable_const
  have hDb : Bornology.IsBounded {v | Ψ v < ρ} :=
    (isBounded_sublevel hΨ hd1 ρ).subset fun v (hv : Ψ v < ρ) => hv.le
  rw [normPotential_eq_integral_sphere_ray hd1 hΨ ε hD hDb y]
  have hray : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫ t in {t : ℝ | 0 < t ∧ y + t • (θ : EuclideanSpace ℝ (Fin d)) ∈ {v | Ψ v < ρ}},
        deriv (fun s : ℝ => Ψ (y + s • (θ : EuclideanSpace ℝ (Fin d)))) t =
      max (ρ - Ψ y) 0 := by
    intro θ
    have hθn := norm_eq_one_of_mem_sphere θ
    have hΨθ := pos_of_norm_eq_one hΨ hθn
    have hT : 0 ≤ (ρ + Ψ y) / Ψ θ := div_nonneg (by linarith [hnonneg y]) hΨθ.le
    have h := setIntegral_deriv_lt (lipschitzWith_ray hΨ y hθn) hT (ρ := ρ) (fun t ht => by
      have h1 := coercive_ray hΨ y θ t
      have h2 : Ψ θ * ((ρ + Ψ y) / Ψ θ) = ρ + Ψ y := mul_div_cancel₀ _ hΨθ.ne'
      have h3 : Ψ θ * ((ρ + Ψ y) / Ψ θ) ≤ Ψ θ * |t| :=
        mul_le_mul_of_nonneg_left (ht.trans (le_abs_self t)) hΨθ.le
      linarith)
    simpa using h
  simp_rw [hray]
  have hω := CERW.unitBallVolume_pos d
  rw [integral_const, toSphere_real_univ, smul_eq_mul]
  field_simp

/-- `lem:layer`: the potential of a subset of the shell `b ≤ Ψ ≤ b + a` is at most `2dεa` in
absolute value. The paper assumes `b ≥ 0`; the proof does not need it. -/
theorem layer_potential {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ} (_ : 0 ≤ b) (ha : 0 < a) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDm : MeasurableSet D) (hD : D ⊆ {v | b ≤ Ψ v ∧ Ψ v ≤ b + a})
    (y : EuclideanSpace ℝ (Fin d)) :
    |CERW.normPotential d ε Ψ D y| ≤ 2 * d * ε * a := by
  have hd1 : 1 ≤ d := by omega
  have hDb : Bornology.IsBounded D :=
    (isBounded_sublevel hΨ hd1 (b + a)).subset fun v hv => (hD hv).2
  rw [normPotential_eq_integral_sphere_ray hd1 hΨ ε hDm hDb y, abs_mul]
  have hω := CERW.unitBallVolume_pos d
  have hray : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ‖∫ t in {t : ℝ | 0 < t ∧ y + t • (θ : EuclideanSpace ℝ (Fin d)) ∈ D},
        deriv (fun s : ℝ => Ψ (y + s • (θ : EuclideanSpace ℝ (Fin d)))) t‖ ≤ a := by
    intro θ
    have hθn := norm_eq_one_of_mem_sphere θ
    rw [Real.norm_eq_abs]
    exact abs_setIntegral_deriv_le (lipschitzWith_ray hΨ y hθn) (convexOn_ray hΨ y θ)
      (pos_of_norm_eq_one hΨ hθn) (coercive_ray hΨ y θ)
      (measurableSet_Ioi.inter (measurableSet_ray hDm y θ)) ha.le (fun t ht => hD ht.2)
  have key : ∀ J : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ, (∀ θ, ‖J θ‖ ≤ a) →
      |∫ θ, J θ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere| ≤
        a * (d * CERW.unitBallVolume d) := fun J hJ => by
    have h := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (Filter.Eventually.of_forall hJ)
    rwa [toSphere_real_univ, Real.norm_eq_abs] at h
  rw [abs_of_pos (by positivity : 0 < 2 * ε / CERW.unitBallVolume d)]
  refine (mul_le_mul_of_nonneg_left (key _ hray) (by positivity)).trans_eq ?_
  field_simp

end CERW.Support.Norm
