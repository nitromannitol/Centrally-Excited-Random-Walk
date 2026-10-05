import CERW.Support.Norm.GaugeModel
import CERW.Support.Norm.BallLayer
import CERW.Support.Geometry.Holder
import CERW.Generic.Kernel.Modulus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The potential of a ball and of a shell of an asymmetric gauge

For a compact convex set `K ⊆ ℝ^d` with the origin in its interior and `ψ = gauge K`, the potential
`U_D(y) = (2ε/ω_d) ∫_D ∇ψ(v) · (v - y) |v - y|^{-d} dv` (`CERW.normPotential`, with `∇ψ` the
gradient, which exists almost everywhere) has the two properties of the potential of a norm, and
neither uses the evenness `ψ(-x) = ψ(x)`:

* `lem:ballpotential`: `U_{ψ < ρ}(y) = 2dε (ρ - ψ(y))₊` for `ρ > 0` (`gauge_ball_potential`);
* `lem:layer`: `|U_D(y)| ≤ 2dε a` for measurable `D ⊆ {b ≤ ψ ≤ b + a}`, `a > 0`
  (`gauge_layer_potential`).

As for a norm, polar coordinates about `y` turn `U_D(y)` into a spherical average of integrals along
rays (`normPotential_eq_integral_sphere_ray_gauge`), and along the ray `t ↦ ψ(y + tθ)` the integral
of the derivative is a change of `ψ`. The ray is convex and Lipschitz; the coercivity that makes the
ball bounded along the ray is `ψ(y + tθ) ≥ c_θ |t| - ψ(-y)` with `c_θ = min {ψ(θ), ψ(-θ)}`, which
involves `ψ(-y)`, not `ψ(y)`, and the minimum over the two orientations of the ray.

The size bound `sup_y |U_D(y)| ≤ C ε |D|^{1/d}` and the Hölder modulus
`|U_D(y) - U_D(z)| ≤ C ε |D|^{1/(2d)} |y - z|^{1/2}`, hence continuity of `U_D`, are proved from the
same field bound `|∇ψ| ≤ Λ_ψ`.

The one-variable lemmas about convex Lipschitz functions of a real parameter and the field-potential
estimates are the generic ones of the norm development; they are restated here with their proofs
because their originals are private to their files.
-/

open MeasureTheory Filter Topology
open scoped Pointwise NNReal

namespace CERW.Support.Norm.GaugePotential

open CERW LatticeProb CERW.Generic.Kernel CERW.Support.Geometry
open CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel

section OneVariable

/-- The derivative of a Lipschitz function is integrable on every set of finite measure. -/
private lemma integrableOn_deriv_of_lipschitz {h : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L h)
    {S : Set ℝ} (hS : volume S ≠ ⊤) : IntegrableOn (deriv h) S :=
  Measure.integrableOn_of_bounded (M := L) hS (measurable_deriv h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hL)

/-- If the derivative of a Lipschitz function `h` is almost everywhere nonnegative on a closed
interval `I`, then the integral of `h'` over a bounded measurable subset `S` of `I` on which `h`
takes values in `[b, b + a]` lies in `[0, a]`: it is at most the increase of `h` between the
extreme points of `S`. -/
private lemma setIntegral_deriv_mem_Icc {h : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L h)
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
      closure_minimal (fun t ht => (hSh t ht).1) (isClosed_le continuous_const hL.continuous)
    exact hc hs1
  have hh2 : h (sSup S) ≤ b + a := by
    have hc : closure S ⊆ {t | h t ≤ b + a} :=
      closure_minimal (fun t ht => (hSh t ht).2) (isClosed_le hL.continuous continuous_const)
    exact hc hs2
  have hle : sInf S ≤ sSup S := csInf_le_csSup hne hbdd hbdd'
  have hint : IntegrableOn (deriv h) (Set.Icc (sInf S) (sSup S)) :=
    integrableOn_deriv_of_lipschitz hL measure_Icc_lt_top.ne
  have hnn : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc (sInf S) (sSup S)),
      0 ≤ deriv h t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hpos] with t ht htI using ht (hIcc htI)
  have hFTC : ∫ t in Set.Icc (sInf S) (sSup S), deriv h t = h (sSup S) - h (sInf S) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    exact hL.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub
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
private lemma abs_setIntegral_deriv_le {h : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L h)
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
  obtain ⟨t₀, hmin⟩ := hL.continuous.exists_forall_le hlim
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
    setIntegral_deriv_mem_Icc hL isClosed_Ici Set.ordConnected_Ici hpos₁ hS₁ hb₁ hIcc₁ ha
      fun t ht => hSh t ht.1
  obtain ⟨h₂, h₂'⟩ : 0 ≤ ∫ t in S ∩ Set.Iio t₀, deriv (fun s => -h s) t ∧
      ∫ t in S ∩ Set.Iio t₀, deriv (fun s => -h s) t ≤ a :=
    setIntegral_deriv_mem_Icc (h := fun s => -h s) hL.neg isClosed_Iic Set.ordConnected_Iic hpos₂
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
    exact setIntegral_union hdisj hS₂ (integrableOn_deriv_of_lipschitz hL hb₁.measure_lt_top.ne)
      (integrableOn_deriv_of_lipschitz hL hb₂.measure_lt_top.ne)
  rw [hsplit]
  rw [hneg] at h₂ h₂'
  rw [abs_le]
  constructor <;> linarith

/-- The derivative of the truncation `(ρ - h)_+` of a function `h` continuous at `t` is
`-1_{h < ρ} h'` at `t`; at a point where `h = ρ` the truncation has a minimum. -/
private lemma deriv_max_sub_zero {h : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L h) (ρ t : ℝ) :
    deriv (fun s => max (ρ - h s) 0) t = -{s | h s < ρ}.indicator (deriv h) t := by
  rcases lt_trichotomy (h t) ρ with hlt | heq | hgt
  · have hev : (fun s => max (ρ - h s) 0) =ᶠ[𝓝 t] fun s => ρ - h s := by
      filter_upwards [hL.continuous.continuousAt.eventually_lt continuousAt_const hlt] with s hs
      exact max_eq_left (by linarith)
    rw [hev.deriv_eq, deriv_const_sub, Set.indicator_of_mem (show t ∈ {s | h s < ρ} from hlt)]
  · have hmin : IsLocalMin (fun s => max (ρ - h s) 0) t :=
      Filter.Eventually.of_forall fun s => by
        simp [heq]
    rw [hmin.deriv_eq_zero, Set.indicator_of_notMem (show t ∉ {s | h s < ρ} by simp [heq])]
    simp
  · have hev : (fun s => max (ρ - h s) 0) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [continuousAt_const.eventually_lt hL.continuous.continuousAt hgt]
        with s hs
      exact max_eq_right (by linarith)
    rw [hev.deriv_eq, Set.indicator_of_notMem (show t ∉ {s | h s < ρ} by simpa using hgt.le)]
    simp

/-- If `h` is Lipschitz and `h ≥ ρ` on `[T, ∞)` for some `T ≥ 0`, then the integral of `h'` over
`{t > 0 : h(t) < ρ}` is `(ρ - h(0))_+`: it is the drop of the truncation `(ρ - h)_+`. -/
private lemma setIntegral_deriv_lt {h : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L h) {ρ T : ℝ}
    (hT : 0 ≤ T) (hρ : ∀ t, T ≤ t → ρ ≤ h t) :
    ∫ t in {t : ℝ | 0 < t ∧ h t < ρ}, deriv h t = max (ρ - h 0) 0 := by
  have hk : LipschitzWith L (fun s => max (ρ - h s) 0) := by
    refine LipschitzWith.of_dist_le_mul fun s u => ?_
    rw [Real.dist_eq, Real.dist_eq]
    calc |max (ρ - h s) 0 - max (ρ - h u) 0|
        ≤ |(ρ - h s) - (ρ - h u)| := abs_max_sub_max_le_abs _ _ _
      _ = |h u - h s| := by ring_nf
      _ = |h s - h u| := abs_sub_comm _ _
      _ ≤ L * |s - u| := by
          have := hL.dist_le_mul s u
          rwa [Real.dist_eq, Real.dist_eq] at this
  have hmeas : MeasurableSet {s : ℝ | h s < ρ} :=
    measurableSet_lt hL.continuous.measurable measurable_const
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
  simp_rw [deriv_max_sub_zero hL ρ] at hFTC
  rw [integral_neg, setIntegral_indicator hmeas, hkT] at hFTC
  rw [hset]
  linarith

end OneVariable

section FieldPotential

variable {d : ℕ}

/-- The parameters `t` for which the point `y + tθ` of the ray lies in a measurable set form a
measurable set. -/
private lemma measurableSet_ray {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (y θ : EuclideanSpace ℝ (Fin d)) : MeasurableSet {t : ℝ | y + t • θ ∈ D} :=
  (measurable_const.add (measurable_id.smul_const _)) hD

/-- Where `Ψ` is differentiable at `y + tθ`, the function `s ↦ Ψ(y + sθ)` has derivative
`∇Ψ(y + tθ) · θ` at `t`. -/
private lemma hasDerivAt_ray {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (y θ : EuclideanSpace ℝ (Fin d))
    {t : ℝ} (h : DifferentiableAt ℝ Ψ (y + t • θ)) :
    HasDerivAt (fun s : ℝ => Ψ (y + s • θ)) (inner ℝ (gradient Ψ (y + t • θ)) θ) t := by
  have hpath : HasDerivAt (fun s : ℝ => y + s • θ) θ t := by
    simpa using ((hasDerivAt_id' t).smul_const θ).const_add y
  have hc := HasFDerivAt.comp_hasDerivAt_of_eq t h.hasGradientAt.hasFDerivAt hpath rfl
  exact hc

/-- A point of the Euclidean unit sphere has norm one. -/
private lemma norm_eq_one_of_mem_sphere
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
  rw [← dist_zero_right]
  exact Metric.mem_sphere.mp θ.2

/-- The sphere measure of the whole unit sphere is `d ω_d`. -/
private lemma toSphere_real_univ :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).real Set.univ =
      d * CERW.unitBallVolume d := by
  rw [MeasureTheory.Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
  rfl

/-- A field weighted by the Newtonian kernel has a measurable integrand when the field is
measurable. -/
private lemma measurable_fieldIntegrand {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (y : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun v : EuclideanSpace ℝ (Fin d) => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) := by
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
    measurable_id.sub measurable_const
  exact (hg.inner hsub).div (hsub.norm.pow_const d)

/-- The integrand of the field potential is at most `Λ` times the Newtonian kernel `|v - y|^{1-d}`
when the field has norm at most `Λ`. -/
private lemma abs_fieldIntegrand_le {Λ : ℝ} {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ ≤ Λ)
    (v y : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ ξ (v - y) / ‖v - y‖ ^ d| ≤ Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
  have hΛ : 0 ≤ Λ := (norm_nonneg ξ).trans hξ
  rcases eq_or_ne v y with rfl | hne
  · simp only [sub_self, inner_zero_right, zero_div, abs_zero]
    exact mul_nonneg hΛ (Real.rpow_nonneg (norm_nonneg _) _)
  · have hw : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < ‖v - y‖ ^ d := pow_pos hw d
    have h1 : |inner ℝ ξ (v - y)| ≤ ‖ξ‖ * ‖v - y‖ := abs_real_inner_le_norm _ _
    have h2 : ‖ξ‖ * ‖v - y‖ ≤ Λ * ‖v - y‖ := mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    calc |inner ℝ ξ (v - y) / ‖v - y‖ ^ d|
        = |inner ℝ ξ (v - y)| / ‖v - y‖ ^ d := by rw [abs_div, abs_of_nonneg hden.le]
      _ ≤ (Λ * ‖v - y‖) / ‖v - y‖ ^ d :=
          div_le_div_of_nonneg_right (h1.trans h2) hden.le
      _ = Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
          rw [mul_div_assoc, div_pow_eq_rpow_sub hw d]

/-- On a set of finite volume the integrand of a bounded measurable field potential is
integrable. -/
private lemma integrableOn_fieldIntegrand (hd : 1 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) D := by
  obtain ⟨hint, _⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  refine (hint.const_mul Λ).mono' (measurable_fieldIntegrand hg y).aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs]
  exact abs_fieldIntegrand_le (hΛ v) v y

/-- The potential `(2ε/ω_d) ∫_D g(v) · (v - y) |v - y|^{-d} dv` of a measurable field of norm at
most `Λ` is at most `Λ · 2dε ω_d^{-1/d} |D|^{1/d}` in absolute value. -/
private lemma abs_fieldPotential_le (hd : 1 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {Λ : ℝ} (hΛ : ∀ v, ‖g v‖ ≤ Λ)
    {ε : ℝ} (hε : 0 ≤ ε) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    |2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d| ≤
      Λ * (2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) * (volume D).toReal ^ ((1 : ℝ) / d)) := by
  obtain ⟨hint, hbound⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  have hω := unitBallVolume_pos d
  have hR : 0 ≤ (volume D).toReal := ENNReal.toReal_nonneg
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hnorm : |∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d| ≤
      Λ * ∫ v in D, ‖v - y‖ ^ (1 - (d : ℝ)) := by
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hint.const_mul Λ) ?_
    filter_upwards with v
    rw [Real.norm_eq_abs]
    exact abs_fieldIntegrand_le (hΛ v) v y
  calc |2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d|
      = (2 * ε / unitBallVolume d) *
          |∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d| := by
        rw [abs_mul, abs_of_nonneg hc]
    _ ≤ (2 * ε / unitBallVolume d) * (Λ * ∫ v in D, ‖v - y‖ ^ (1 - (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hnorm hc
    _ ≤ (2 * ε / unitBallVolume d) *
          (Λ * (d * unitBallVolume d * ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound hΛ0) hc
    _ = Λ * ((2 * ε / unitBallVolume d) *
          (d * unitBallVolume d * ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d))) := by
        ring
    _ = Λ * (2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) *
          (volume D).toReal ^ ((1 : ℝ) / d)) := by
        rw [potential_bound_algebra d hω hR]

/-- The difference of two field-potential integrands is at most the norm of the difference of the
Newtonian fields when the field has norm at most one. -/
private lemma abs_fieldIntegrand_sub_le {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ ≤ 1)
    (y z v : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ ξ (v - y) / ‖v - y‖ ^ d - inner ℝ ξ (v - z) / ‖v - z‖ ^ d| ≤
      ‖newtonField (v - y) - newtonField (v - z)‖ := by
  rw [← inner_newtonField, ← inner_newtonField, ← inner_sub_right]
  calc |inner ℝ ξ (newtonField (v - y) - newtonField (v - z))|
      ≤ ‖ξ‖ * ‖newtonField (v - y) - newtonField (v - z)‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖newtonField (v - y) - newtonField (v - z)‖ :=
        mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    _ = ‖newtonField (v - y) - newtonField (v - z)‖ := one_mul _

/-- The Hölder modulus of the potential of a measurable field of norm at most one:
`|U(y) - U(z)| ≤ C_d ε |D|^{1/(2d)} |y - z|^{1/2}`. -/
private lemma exists_fieldPotential_holder_one (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)},
      Measurable g → (∀ v, ‖g v‖ ≤ 1) → ∀ {ε : ℝ}, 0 ≤ ε →
      ∀ {D : Set (EuclideanSpace ℝ (Fin d))}, MeasurableSet D → volume D ≠ ⊤ →
      ∀ y z : EuclideanSpace ℝ (Fin d),
        |2 * ε / unitBallVolume d * (∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) -
            2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - z) / ‖v - z‖ ^ d| ≤
          C * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d - 1 := by linarith
  have hω := unitBallVolume_pos d
  obtain ⟨C, hC0, hC⟩ := exists_kernel_modulus hd
  refine ⟨2 / unitBallVolume d * C ^ ((2 * (d : ℝ) - 1) / (2 * d)), by positivity, ?_⟩
  intro g hg hg1 ε hε D hD hDfin y z
  obtain ⟨hgi, hgint⟩ := hC y z
  have hpq : (2 * (d : ℝ)).HolderConjugate (2 * d / (2 * d - 1)) := by
    refine Real.holderConjugate_iff.mpr ⟨by linarith, ?_⟩
    field_simp
    ring
  have hgm : AEStronglyMeasurable (fun v => ‖newtonField (v - y) - newtonField (v - z)‖) volume :=
    (((measurable_newtonField.comp (measurable_id.sub_const y)).sub
      (measurable_newtonField.comp (measurable_id.sub_const z))).norm).aestronglyMeasurable
  have hH := abs_setIntegral_le_rpow_mul_rpow hpq hDfin
    (f := fun v => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d -
      inner ℝ (g v) (v - z) / ‖v - z‖ ^ d)
    (fun v => abs_fieldIntegrand_sub_le (hg1 v) y z v) hgm hgi
  have hsub : 2 * ε / unitBallVolume d * (∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) -
      2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - z) / ‖v - z‖ ^ d =
      2 * ε / unitBallVolume d *
      ∫ v in D, (inner ℝ (g v) (v - y) / ‖v - y‖ ^ d -
        inner ℝ (g v) (v - z) / ‖v - z‖ ^ d) := by
    rw [integral_sub (integrableOn_fieldIntegrand (by omega) hg hg1 hD hDfin y)
      (integrableOn_fieldIntegrand (by omega) hg hg1 hD hDfin z)]
    ring
  have hmod : (∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^ (2 * (d : ℝ) / (2 * d - 1))) ^
      (1 / (2 * (d : ℝ) / (2 * d - 1))) ≤
        C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
    have h1 : 1 / (2 * (d : ℝ) / (2 * d - 1)) = (2 * d - 1) / (2 * d) := by
      field_simp
    have hnn : 0 ≤ ∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^
        (2 * (d : ℝ) / (2 * d - 1)) :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    calc (∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^ (2 * (d : ℝ) / (2 * d - 1))) ^
          (1 / (2 * (d : ℝ) / (2 * d - 1)))
        ≤ (C * ‖y - z‖ ^ ((d : ℝ) / (2 * d - 1))) ^ ((2 * (d : ℝ) - 1) / (2 * d)) := by
          rw [h1]
          exact Real.rpow_le_rpow hnn hgint (by positivity)
      _ = C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
          rw [Real.mul_rpow hC0 (Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_mul
            (norm_nonneg _)]
          congr 2
          rw [div_mul_div_comm, div_eq_div_iff (mul_pos hden (by positivity)).ne' two_ne_zero]
          ring
  rw [hsub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ε / unitBallVolume d)]
  calc 2 * ε / unitBallVolume d * |∫ v in D, (inner ℝ (g v) (v - y) / ‖v - y‖ ^ d -
        inner ℝ (g v) (v - z) / ‖v - z‖ ^ d)|
      ≤ 2 * ε / unitBallVolume d * ((volume D).toReal ^ (1 / (2 * (d : ℝ))) *
          (C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2))) := by
        gcongr
        exact hH.trans (by gcongr)
    _ = 2 / unitBallVolume d * C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ε *
          (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
        ring

/-- The Hölder modulus of the potential of a measurable field of norm at most `Λ > 0`:
`|U(y) - U(z)| ≤ Λ C_d ε |D|^{1/(2d)} |y - z|^{1/2}`. -/
private lemma exists_fieldPotential_holder (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)},
      Measurable g → ∀ {Λ : ℝ}, 0 < Λ → (∀ v, ‖g v‖ ≤ Λ) → ∀ {ε : ℝ}, 0 ≤ ε →
      ∀ {D : Set (EuclideanSpace ℝ (Fin d))}, MeasurableSet D → volume D ≠ ⊤ →
      ∀ y z : EuclideanSpace ℝ (Fin d),
        |2 * ε / unitBallVolume d * (∫ v in D, inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) -
            2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g v) (v - z) / ‖v - z‖ ^ d| ≤
          Λ * (C * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_fieldPotential_holder_one hd
  refine ⟨C, hC0, ?_⟩
  intro g hg Λ hΛ hgΛ ε hε D hD hDfin y z
  set g' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun v => Λ⁻¹ • g v with hg'
  have hg'm : Measurable g' := hg.const_smul Λ⁻¹
  have hg'b : ∀ v, ‖g' v‖ ≤ 1 := by
    intro v
    rw [hg', norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hΛ]
    calc Λ⁻¹ * ‖g v‖ ≤ Λ⁻¹ * Λ := mul_le_mul_of_nonneg_left (hgΛ v) (inv_nonneg.mpr hΛ.le)
      _ = 1 := inv_mul_cancel₀ hΛ.ne'
  have hscale : ∀ w : EuclideanSpace ℝ (Fin d),
      ∫ v in D, inner ℝ (g v) (v - w) / ‖v - w‖ ^ d =
        Λ * ∫ v in D, inner ℝ (g' v) (v - w) / ‖v - w‖ ^ d := by
    intro w
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hgv : g v = Λ • g' v := by
      rw [hg', smul_smul, mul_inv_cancel₀ hΛ.ne', one_smul]
    simp only [hgv, real_inner_smul_left]
    ring
  have h := hC hg'm hg'b hε hD hDfin y z
  rw [hscale y, hscale z]
  have hrew : 2 * ε / unitBallVolume d * (Λ * ∫ v in D, inner ℝ (g' v) (v - y) / ‖v - y‖ ^ d) -
      2 * ε / unitBallVolume d * (Λ * ∫ v in D, inner ℝ (g' v) (v - z) / ‖v - z‖ ^ d) =
      Λ * (2 * ε / unitBallVolume d * (∫ v in D, inner ℝ (g' v) (v - y) / ‖v - y‖ ^ d) -
        2 * ε / unitBallVolume d * ∫ v in D, inner ℝ (g' v) (v - z) / ‖v - z‖ ^ d) := by
    ring
  rw [hrew, abs_mul, abs_of_pos hΛ]
  exact mul_le_mul_of_nonneg_left h hΛ.le

/-- For `t > 0` and a unit vector `θ`, the integrand of the potential at `y + tθ`, times the polar
weight `t^{d-1}`, is the directional derivative `∇Ψ(y + tθ) · θ` if `y + tθ ∈ D` and `0`
otherwise. -/
private lemma radial_weight_kernel {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} (hd : 1 ≤ d)
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

end FieldPotential

section Gauge

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- The constant of coercivity along a ray: `c_θ = min {ψ(θ), ψ(-θ)}` is positive for a unit
vector `θ`. -/
theorem gauge_rayConstant_pos (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) : 0 < min (gauge K θ) (gauge K (-θ)) := by
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hθ
    exact zero_ne_one hθ
  exact lt_min (gauge_pos_of_ne_zero hK h0 hθ0) (gauge_pos_of_ne_zero hK h0 (neg_ne_zero.mpr hθ0))

/-- Coercivity of `ψ_K` along a line in both directions, with the value at `-y`:
`ψ_K(y + tθ) ≥ min {ψ_K(θ), ψ_K(-θ)} |t| - ψ_K(-y)` for every real `t`. -/
theorem gauge_line_coercive (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    (y θ : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    min (gauge K θ) (gauge K (-θ)) * |t| - gauge K (-y) ≤ gauge K (y + t • θ) := by
  rcases le_total 0 t with ht | ht
  · have h := gauge_ray_coercive hc h0 y θ ht
    rw [abs_of_nonneg ht]
    have : min (gauge K θ) (gauge K (-θ)) * t ≤ t * gauge K θ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) ht
    linarith
  · have h := gauge_ray_coercive hc h0 y (-θ) (neg_nonneg.mpr ht)
    rw [abs_of_nonpos ht]
    have hpt : y + (-t) • (-θ) = y + t • θ := by
      rw [smul_neg, neg_smul, neg_neg]
    rw [hpt] at h
    have : min (gauge K θ) (gauge K (-θ)) * (-t) ≤ (-t) * gauge K (-θ) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (neg_nonneg.mpr ht)
    linarith

/-- **Ray decomposition of the potential of `ψ_K`.** For a bounded measurable `D`, writing
`v = y + tθ`, the potential is `(2ε/ω_d)` times the spherical integral over `θ` of the integral of
`(d/dt) ψ_K(y + tθ)` over `{t > 0 : y + tθ ∈ D}`. -/
theorem normPotential_eq_integral_sphere_ray_gauge (hd : 1 ≤ d) (hK : IsCompact K)
    (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (y : EuclideanSpace ℝ (Fin d)) :
    CERW.normPotential d ε (gauge K) D y = 2 * ε / CERW.unitBallVolume d *
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (∫ t in {t : ℝ | 0 < t ∧ y + t • (θ : EuclideanSpace ℝ (Fin d)) ∈ D},
          deriv (fun s : ℝ => gauge K (y + s • (θ : EuclideanSpace ℝ (Fin d)))) t)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  unfold CERW.normPotential
  congr 1
  set F : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun v => inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d
  have hFint : IntegrableOn F D :=
    integrableOn_fieldIntegrand hd (measurable_gradient (gauge K))
      (fun v => norm_gradient_gauge_le hK hc h0 v) hD hDb.measure_lt_top.ne y
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun w => D.indicator F (y + w)
  have hfint : Integrable f :=
    ((integrable_indicator_iff hD).2 hFint).comp_add_left y
  have h1 : ∫ v in D, F v = ∫ w, f w := by
    rw [← integral_indicator hD]
    exact (integral_add_left_eq_self (μ := volume) (fun v => D.indicator F v) y).symm
  rw [h1, integral_eq_integral_sphere_Ioi hd hfint]
  have hdiff : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      DifferentiableAt ℝ (gauge K) (y + w) :=
    (quasiMeasurePreserving_add_left volume y).ae (ae_differentiableAt_gauge hK hc h0)
  refine integral_congr_ae ?_
  filter_upwards [ae_sphere_ae_Ioi_smul hd hdiff] with θ hθ
  have hθn := norm_eq_one_of_mem_sphere θ
  have hmeas := measurableSet_ray hD y (θ : EuclideanSpace ℝ (Fin d))
  calc ∫ t in Set.Ioi (0 : ℝ), t ^ (d - 1) * f (t • (θ : EuclideanSpace ℝ (Fin d)))
      = ∫ t in Set.Ioi (0 : ℝ), {s : ℝ | y + s • (θ : EuclideanSpace ℝ (Fin d)) ∈ D}.indicator
          (fun s => inner ℝ (gradient (gauge K) (y + s • (θ : EuclideanSpace ℝ (Fin d)))) θ) t :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht =>
          radial_weight_kernel hd y hθn (Set.mem_Ioi.1 ht)
    _ = ∫ t in Set.Ioi (0 : ℝ) ∩ {s : ℝ | y + s • (θ : EuclideanSpace ℝ (Fin d)) ∈ D},
          inner ℝ (gradient (gauge K) (y + t • (θ : EuclideanSpace ℝ (Fin d)))) θ :=
        setIntegral_indicator hmeas
    _ = _ := by
        refine setIntegral_congr_ae (measurableSet_Ioi.inter hmeas) ?_
        filter_upwards [(ae_restrict_iff' measurableSet_Ioi).1 hθ] with t ht htS
        exact (hasDerivAt_ray y θ (ht htS.1)).deriv.symm

/-- **`lem:ballpotential` for the gauge of a compact convex body.** For `d ≥ 2` and `ρ > 0`,
the potential of the ball `{ψ_K < ρ}` is `2dε (ρ - ψ_K(y))₊`. -/
theorem gauge_ball_potential (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin d)) :
    CERW.normPotential d ε (gauge K) {v | gauge K v < ρ} y =
      2 * d * ε * max (ρ - gauge K y) 0 := by
  have hd1 : 1 ≤ d := by omega
  have hD : MeasurableSet {v | gauge K v < ρ} := measurableSet_gauge_sublevel hc h0 ρ
  have hDb : Bornology.IsBounded {v | gauge K v < ρ} := isBounded_gauge_sublevel hK h0 hd1 ρ
  rw [normPotential_eq_integral_sphere_ray_gauge hd1 hK hc h0 ε hD hDb y]
  have hray : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫ t in {t : ℝ | 0 < t ∧ y + t • (θ : EuclideanSpace ℝ (Fin d)) ∈ {v | gauge K v < ρ}},
        deriv (fun s : ℝ => gauge K (y + s • (θ : EuclideanSpace ℝ (Fin d)))) t =
      max (ρ - gauge K y) 0 := by
    intro θ
    have hθn := norm_eq_one_of_mem_sphere θ
    have hθ0 : (θ : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hθn
      exact zero_ne_one hθn
    have hψθ : 0 < gauge K (θ : EuclideanSpace ℝ (Fin d)) := gauge_pos_of_ne_zero hK h0 hθ0
    have hT : 0 ≤ (ρ + gauge K (-y)) / gauge K (θ : EuclideanSpace ℝ (Fin d)) :=
      div_nonneg (by linarith [gauge_nonneg (s := K) (-y)]) hψθ.le
    have h := setIntegral_deriv_lt (lipschitzWith_gauge_ray hK hc h0 y hθn) hT (ρ := ρ)
      (fun t ht => by
        have h1 := gauge_ray_coercive hc h0 y (θ : EuclideanSpace ℝ (Fin d)) (hT.trans ht)
        have h2 : gauge K (θ : EuclideanSpace ℝ (Fin d)) *
            ((ρ + gauge K (-y)) / gauge K (θ : EuclideanSpace ℝ (Fin d))) = ρ + gauge K (-y) :=
          mul_div_cancel₀ _ hψθ.ne'
        have h3 : gauge K (θ : EuclideanSpace ℝ (Fin d)) *
            ((ρ + gauge K (-y)) / gauge K (θ : EuclideanSpace ℝ (Fin d))) ≤
            gauge K (θ : EuclideanSpace ℝ (Fin d)) * t :=
          mul_le_mul_of_nonneg_left ht hψθ.le
        linarith [mul_comm t (gauge K (θ : EuclideanSpace ℝ (Fin d)))])
    simpa using h
  simp_rw [hray]
  have hω := CERW.unitBallVolume_pos d
  rw [integral_const, toSphere_real_univ, smul_eq_mul]
  field_simp

/-- **`lem:layer` for the gauge of a compact convex body.** For `d ≥ 2`, `ε > 0`, `b ≥ 0`, `a > 0`
and a measurable `D ⊆ {b ≤ ψ_K ≤ b + a}`, the potential of `D` is at most `2dεa` in absolute
value, at every point `y`. -/
theorem gauge_layer_potential (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    {a b : ℝ} (_hb : 0 ≤ b) (ha : 0 < a) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDm : MeasurableSet D) (hD : D ⊆ {v | b ≤ gauge K v ∧ gauge K v ≤ b + a})
    (y : EuclideanSpace ℝ (Fin d)) :
    |CERW.normPotential d ε (gauge K) D y| ≤ 2 * d * ε * a := by
  have hd1 : 1 ≤ d := by omega
  have hDb : Bornology.IsBounded D :=
    (isBounded_gauge_sublevel hK h0 hd1 (b + a + 1)).subset fun v hv =>
      lt_of_le_of_lt (hD hv).2 (by linarith)
  rw [normPotential_eq_integral_sphere_ray_gauge hd1 hK hc h0 ε hDm hDb y, abs_mul]
  have hω := CERW.unitBallVolume_pos d
  have hray : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ‖∫ t in {t : ℝ | 0 < t ∧ y + t • (θ : EuclideanSpace ℝ (Fin d)) ∈ D},
        deriv (fun s : ℝ => gauge K (y + s • (θ : EuclideanSpace ℝ (Fin d)))) t‖ ≤ a := by
    intro θ
    have hθn := norm_eq_one_of_mem_sphere θ
    rw [Real.norm_eq_abs]
    exact abs_setIntegral_deriv_le (lipschitzWith_gauge_ray hK hc h0 y hθn)
      (convexOn_gauge_ray hc h0 y θ) (gauge_rayConstant_pos hK h0 hθn)
      (gauge_line_coercive hc h0 y θ)
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

/-- The integrand `∇ψ_K(v) · (v - y) |v - y|^{-d}` of the potential is measurable. -/
theorem measurable_potentialIntegrand_gauge (K : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d) :=
  measurable_fieldIntegrand (measurable_gradient (gauge K)) y

/-- On a measurable set of finite volume, the integrand `∇ψ_K(v) · (v - y) |v - y|^{-d}` of the
potential is integrable: it is at most `Λ_ψ |v - y|^{1-d}`. -/
theorem integrableOn_potentialIntegrand_gauge (hd : 1 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d) D :=
  integrableOn_fieldIntegrand hd (measurable_gradient (gauge K))
    (fun v => norm_gradient_gauge_le hK hc h0 v) hD hDfin y

/-- The sphere measure of the whole unit sphere is `d ω_d`: the volume normalization in
`U_D(y) = (2ε/ω_d) ∫ …`, which turns the spherical average of the ray integrals into the factor
`2dε`. -/
theorem toSphere_real_univ_eq (d : ℕ) :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).real Set.univ =
      d * CERW.unitBallVolume d :=
  toSphere_real_univ

/-- **Size of the potential** (`eq:potential-bound`): for a bounded field `|∇ψ_K| ≤ Λ_ψ`,
`|U_D(y)| ≤ Λ_ψ · 2dε ω_d^{-1/d} |D|^{1/d}` for every measurable `D` of finite volume and
`ε ≥ 0`. -/
theorem abs_normPotential_gauge_le (hd : 1 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    |CERW.normPotential d ε (gauge K) D y| ≤
      normMax (gauge K) * (2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) *
        (volume D).toReal ^ ((1 : ℝ) / d)) :=
  abs_fieldPotential_le hd (fun v => norm_gradient_gauge_le hK hc h0 v) hε hD hDfin y

/-- **Size and modulus of the potential of `ψ_K`.** For `d ≥ 2` there is `C(d, K) > 0` such that,
for every `ε ≥ 0` and bounded measurable `D`, `sup_y |U_D(y)| ≤ C ε |D|^{1/d}` and
`|U_D(y) - U_D(z)| ≤ C ε |D|^{1/(2d)} |y - z|^{1/2}`. -/
theorem gauge_potential_geometry (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
        (∀ y, |CERW.normPotential d ε (gauge K) D y| ≤
          C * ε * (volume D).toReal ^ ((1 : ℝ) / d)) ∧
        (∀ y z, |CERW.normPotential d ε (gauge K) D y - CERW.normPotential d ε (gauge K) D z| ≤
          C * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) := by
  have hd1 : 1 ≤ d := by omega
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hΛpos : 0 < normMax (gauge K) :=
    lt_of_lt_of_le (normMin_gauge_pos_mul_le hK h0 hd1).1
      (normMin_gauge_le_normMax_gauge hK h0 hd1)
  have hgm : Measurable (gradient (gauge K)) := measurable_gradient (gauge K)
  have hgb : ∀ v, ‖gradient (gauge K) v‖ ≤ normMax (gauge K) :=
    fun v => norm_gradient_gauge_le hK hc h0 v
  obtain ⟨CH, hCH0, hCH⟩ := exists_fieldPotential_holder hd
  set CB : ℝ := 2 * d * unitBallVolume d ^ (-(1 : ℝ) / d) with hCB
  have hCB0 : 0 ≤ CB := by positivity
  refine ⟨normMax (gauge K) * CB + normMax (gauge K) * CH + 1, by positivity,
    fun ε hε D hD hDb => ?_⟩
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hR0 : 0 ≤ (volume D).toReal := ENNReal.toReal_nonneg
  refine ⟨fun y => ?_, fun y z => ?_⟩
  · calc |CERW.normPotential d ε (gauge K) D y|
        ≤ normMax (gauge K) * (2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) *
            (volume D).toReal ^ ((1 : ℝ) / d)) :=
          abs_fieldPotential_le hd1 hgb hε hD hDfin y
      _ = normMax (gauge K) * CB * ε * (volume D).toReal ^ ((1 : ℝ) / d) := by rw [hCB]; ring
      _ ≤ (normMax (gauge K) * CB + normMax (gauge K) * CH + 1) * ε *
            (volume D).toReal ^ ((1 : ℝ) / d) := by
          have := Real.rpow_nonneg hR0 ((1 : ℝ) / d)
          gcongr
          have := mul_nonneg hΛpos.le hCH0
          linarith
  · calc |CERW.normPotential d ε (gauge K) D y - CERW.normPotential d ε (gauge K) D z|
        ≤ normMax (gauge K) * (CH * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) *
            ‖y - z‖ ^ ((1 : ℝ) / 2)) :=
          hCH hgm hΛpos hgb hε hD hDfin y z
      _ = normMax (gauge K) * CH * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) *
            ‖y - z‖ ^ ((1 : ℝ) / 2) := by ring
      _ ≤ (normMax (gauge K) * CB + normMax (gauge K) * CH + 1) * ε *
            (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
          have h1 := Real.rpow_nonneg hR0 ((1 : ℝ) / (2 * d))
          have h2 := Real.rpow_nonneg (norm_nonneg (y - z)) ((1 : ℝ) / 2)
          gcongr
          have := mul_nonneg hΛpos.le hCB0
          linarith

/-- The potential `U_D` of a bounded measurable set for the gauge `ψ_K` is continuous. -/
theorem continuous_normPotential_gauge (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) :
    Continuous (CERW.normPotential d ε (gauge K) D) := by
  obtain ⟨C, hC, h⟩ := gauge_potential_geometry hd hK hc h0
  exact continuous_of_holder_half
    (A := C * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)))
    (mul_nonneg (mul_nonneg hC.le hε) (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    (fun y z => (h ε hε D hD hDb).2 y z)

/-- The potential of the ball `{ψ_K < ρ}` is nonnegative and at most `2dερ`, for `ε ≥ 0`. -/
theorem gauge_ball_potential_mem_Icc (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin d)) :
    0 ≤ CERW.normPotential d ε (gauge K) {v | gauge K v < ρ} y ∧
      CERW.normPotential d ε (gauge K) {v | gauge K v < ρ} y ≤ 2 * d * ε * ρ := by
  rw [gauge_ball_potential hd hK hc h0 ε hρ y]
  have hd0 : (0 : ℝ) ≤ 2 * d * ε := by positivity
  have hψ : 0 ≤ gauge K y := gauge_nonneg y
  exact ⟨mul_nonneg hd0 (le_max_right _ _),
    mul_le_mul_of_nonneg_left (max_le (by linarith) hρ.le) hd0⟩

/-- The potential of the ball `{ψ_K < ρ}` vanishes at every point with `ψ_K ≥ ρ`, in particular on
the boundary of the ball. -/
theorem gauge_ball_potential_eq_zero (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : ρ ≤ gauge K y) :
    CERW.normPotential d ε (gauge K) {v | gauge K v < ρ} y = 0 := by
  rw [gauge_ball_potential hd hK hc h0 ε hρ y, max_eq_right (by linarith), mul_zero]

/-- The potential of the ball `{ψ_K < ρ}` is `2dεΛ_ψ`-Lipschitz, for `ε ≥ 0`. -/
theorem abs_gauge_ball_potential_sub_le (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε) {ρ : ℝ} (hρ : 0 < ρ)
    (y z : EuclideanSpace ℝ (Fin d)) :
    |CERW.normPotential d ε (gauge K) {v | gauge K v < ρ} y -
        CERW.normPotential d ε (gauge K) {v | gauge K v < ρ} z| ≤
      2 * d * ε * normMax (gauge K) * ‖y - z‖ := by
  rw [gauge_ball_potential hd hK hc h0 ε hρ y, gauge_ball_potential hd hK hc h0 ε hρ z,
    ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * d * ε)]
  calc 2 * d * ε * |max (ρ - gauge K y) 0 - max (ρ - gauge K z) 0|
      ≤ 2 * d * ε * |(ρ - gauge K y) - (ρ - gauge K z)| :=
        mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ _) (by positivity)
    _ = 2 * d * ε * |gauge K z - gauge K y| := by ring_nf
    _ = 2 * d * ε * |gauge K y - gauge K z| := by rw [abs_sub_comm]
    _ ≤ 2 * d * ε * (normMax (gauge K) * ‖y - z‖) :=
        mul_le_mul_of_nonneg_left (abs_gauge_sub_le hK hc h0 y z) (by positivity)
    _ = 2 * d * ε * normMax (gauge K) * ‖y - z‖ := by ring

/-- **The shell bound is attained.** For `d ≥ 2`, `b ≥ 0` and `a > 0`, the potential at the origin
of the shell `{b ≤ ψ_K < b + a}` is exactly `2dεa`, so the constant of `gauge_layer_potential`
is sharp. -/
theorem gauge_layer_potential_zero (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ) {a b : ℝ} (hb : 0 ≤ b)
    (ha : 0 < a) :
    CERW.normPotential d ε (gauge K) {v | b ≤ gauge K v ∧ gauge K v < b + a} 0 =
      2 * d * ε * a := by
  have hd1 : 1 ≤ d := by omega
  rcases hb.eq_or_lt with rfl | hbpos
  · have hset : {v : EuclideanSpace ℝ (Fin d) | 0 ≤ gauge K v ∧ gauge K v < 0 + a} =
        {v | gauge K v < 0 + a} := by
      ext v
      simp only [Set.mem_setOf_eq, and_iff_right_iff_imp]
      exact fun _ => gauge_nonneg v
    rw [hset, gauge_ball_potential hd hK hc h0 ε (by linarith : 0 < 0 + a), gauge_zero]
    rw [max_eq_left (by linarith)]
    ring
  · have hset : {v : EuclideanSpace ℝ (Fin d) | b ≤ gauge K v ∧ gauge K v < b + a} =
        {v | gauge K v < b + a} \ {v | gauge K v < b} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_sdiff, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, h2⟩
    have hA : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | gauge K v < b + a} :=
      measurableSet_gauge_sublevel hc h0 _
    have hB : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | gauge K v < b} :=
      measurableSet_gauge_sublevel hc h0 _
    have hBA : {v : EuclideanSpace ℝ (Fin d) | gauge K v < b} ⊆
        {v | gauge K v < b + a} := by
      intro v hv
      simp only [Set.mem_setOf_eq] at hv ⊢
      linarith
    have hint := integrableOn_potentialIntegrand_gauge hd1 hK hc h0 hA
      (isBounded_gauge_sublevel hK h0 hd1 (b + a)).measure_lt_top.ne (0 : EuclideanSpace ℝ (Fin d))
    have hdiff : CERW.normPotential d ε (gauge K) ({v | gauge K v < b + a} \ {v | gauge K v < b})
        0 = CERW.normPotential d ε (gauge K) {v | gauge K v < b + a} 0 -
          CERW.normPotential d ε (gauge K) {v | gauge K v < b} 0 := by
      unfold CERW.normPotential
      rw [setIntegral_sdiff hB hint hBA]
      ring
    rw [hset, hdiff, gauge_ball_potential hd hK hc h0 ε (by linarith : 0 < b + a),
      gauge_ball_potential hd hK hc h0 ε hbpos, gauge_zero, max_eq_left (by linarith),
      max_eq_left (by linarith)]
    ring

/-! ### The choice of subgradients is irrelevant -/

/-- Where `ψ_K` is differentiable, the only subgradient is the gradient: along every line the
function `s ↦ ψ_K(x + su) - s ξ · u` has a minimum at `s = 0`, so its derivative vanishes there. -/
theorem eq_gradient_of_isSubgradient {x ξ : EuclideanSpace ℝ (Fin d)}
    (hx : DifferentiableAt ℝ (gauge K) x) (h : IsSubgradient (gauge K) x ξ) :
    ξ = gradient (gauge K) x := by
  have key : ∀ u : EuclideanSpace ℝ (Fin d), inner ℝ (gradient (gauge K) x - ξ) u = 0 := by
    intro u
    let f : ℝ → ℝ := fun s => gauge K (x + s • u) - s * inner ℝ ξ u
    have hmin : IsLocalMin f 0 := Filter.Eventually.of_forall fun s => by
      have h1 := h (x + s • u)
      rw [add_sub_cancel_left, real_inner_smul_right] at h1
      simp only [f, zero_smul, add_zero, zero_mul, sub_zero]
      linarith
    have h1 : HasDerivAt (fun s : ℝ => gauge K (x + s • u))
        (inner ℝ (gradient (gauge K) x) u) 0 := by
      have := hasDerivAt_ray (Ψ := gauge K) x u (t := 0) (by simpa using hx)
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ ξ u) (inner ℝ ξ u) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (inner ℝ ξ u)
    have h3 := hmin.hasDerivAt_eq_zero (h1.sub h2)
    rw [inner_sub_left]
    linarith
  have h4 := key (gradient (gauge K) x - ξ)
  rw [inner_self_eq_zero, sub_eq_zero] at h4
  exact h4.symm

/-- Every selection of subgradients of `ψ_K` equals the gradient almost everywhere. -/
theorem ae_eq_gradient_of_isSubgradient (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ v, IsSubgradient (gauge K) v (ξ v)) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ξ v = gradient (gauge K) v := by
  filter_upwards [ae_differentiableAt_gauge hK hc h0] with v hv
  exact eq_gradient_of_isSubgradient hv (hξ v)

/-- The potential does not depend on which subgradient is chosen at the points where `ψ_K` is not
differentiable: with any selection `ξ(v) ∈ ∂ψ_K(v)` in place of the gradient it is `U_D(y)`. -/
theorem normPotential_eq_selection_potential (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d))
    {ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ v, IsSubgradient (gauge K) v (ξ v)) :
    2 * ε / CERW.unitBallVolume d * ∫ v in D, inner ℝ (ξ v) (v - y) / ‖v - y‖ ^ d =
      CERW.normPotential d ε (gauge K) D y := by
  unfold CERW.normPotential
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (ae_eq_gradient_of_isSubgradient hK hc h0 hξ)] with v hv
  rw [hv]

/-- **`lem:ballpotential` with an arbitrary subgradient selection.** For any `ξ` with
`ξ(v) ∈ ∂ψ_K(v)` for every `v`, the potential generated by `-ε ξ` on `{ψ_K < ρ}` is
`2dε (ρ - ψ_K(y))₊`. -/
theorem gauge_ball_potential_selection (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin d))
    {ξ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ v, IsSubgradient (gauge K) v (ξ v)) :
    2 * ε / CERW.unitBallVolume d *
        ∫ v in {v | gauge K v < ρ}, inner ℝ (ξ v) (v - y) / ‖v - y‖ ^ d =
      2 * d * ε * max (ρ - gauge K y) 0 := by
  rw [normPotential_eq_selection_potential hK hc h0 ε _ y hξ]
  exact gauge_ball_potential hd hK hc h0 ε hρ y

/-! ### The gradient identity for the truncation `(ρ - ψ_K)₊` -/

/-- The level set `{ψ_K = ρ}` of the gauge of a convex body has measure zero, for `ρ > 0`: it is
`ρ • ∂K`. -/
theorem volume_gauge_level_eq_zero (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ρ : ℝ} (hρ : 0 < ρ) :
    volume {v : EuclideanSpace ℝ (Fin d) | gauge K v = ρ} = 0 := by
  have hset : {v : EuclideanSpace ℝ (Fin d) | gauge K v = ρ} = ρ • frontier K := by
    ext v
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hρ.ne', ← gauge_eq_one_iff_mem_frontier hc
      (mem_interior_iff_mem_nhds.mp h0), gauge_smul_nonneg K (inv_nonneg.mpr hρ.le),
      inv_mul_eq_one₀ hρ.ne']
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hset, Measure.addHaar_smul_of_nonneg _ hρ.le, hc.addHaar_frontier volume, mul_zero]

/-- Almost everywhere, `∇(ρ - ψ_K)₊ = -1_{ψ_K < ρ} ∇ψ_K`: on `{ψ_K < ρ}` the truncation is
`ρ - ψ_K`, on `{ψ_K > ρ}` it vanishes, and `{ψ_K = ρ}` is null. -/
theorem gradient_truncation_ae (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      gradient (fun w => max (ρ - gauge K w) 0) v =
        -({w | gauge K w < ρ}.indicator (gradient (gauge K)) v) := by
  have hcont : Continuous (gauge K) := continuous_gauge hc (mem_interior_iff_mem_nhds.mp h0)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_gauge_level_eq_zero hc h0 hρ)] with v hv
  have hne : gauge K v ≠ ρ := hv
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hev : (fun w => max (ρ - gauge K w) 0) =ᶠ[𝓝 v] fun w => ρ - gauge K w := by
      filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const hlt] with w hw
      exact max_eq_left (by linarith)
    rw [Set.indicator_of_mem (show v ∈ {w | gauge K w < ρ} from hlt)]
    unfold gradient
    rw [hev.fderiv_eq, fderiv_const_sub, map_neg]
  · have hev : (fun w => max (ρ - gauge K w) 0) =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
      filter_upwards [continuousAt_const.eventually_lt hcont.continuousAt hgt] with w hw
      exact max_eq_right (by linarith)
    rw [Set.indicator_of_notMem (show v ∉ {w | gauge K w < ρ} by simpa using hgt.le)]
    unfold gradient
    rw [hev.fderiv_eq]
    simp

/-- **The gradient identity `eq:gradient-identity` for `f = (ρ - ψ_K)₊`.** For `d ≥ 2` and `ρ > 0`,
`∫ ∇f(v) · (v - y) |v - y|^{-d} dv = -d ω_d f(y)`. -/
theorem gauge_gradient_identity (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin d)) :
    ∫ v, inner ℝ (gradient (fun w => max (ρ - gauge K w) 0) v) (v - y) / ‖v - y‖ ^ d =
      -(d * CERW.unitBallVolume d * max (ρ - gauge K y) 0) := by
  have hae := gradient_truncation_ae hc h0 hρ
  have h1 : ∫ v, inner ℝ (gradient (fun w => max (ρ - gauge K w) 0) v) (v - y) / ‖v - y‖ ^ d =
      -∫ v in {v | gauge K v < ρ}, inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d := by
    rw [← integral_neg, ← integral_indicator (measurableSet_gauge_sublevel hc h0 ρ)]
    refine integral_congr_ae ?_
    filter_upwards [hae] with v hv
    rw [hv]
    by_cases hmem : v ∈ {w | gauge K w < ρ}
    · simp only [Set.indicator_of_mem hmem, inner_neg_left, neg_div]
    · simp only [Set.indicator_of_notMem hmem, neg_zero, inner_zero_left, zero_div]
  have h2 := gauge_ball_potential hd hK hc h0 1 hρ y
  unfold CERW.normPotential at h2
  have hω := CERW.unitBallVolume_pos d
  rw [h1]
  have h3 : ∫ v in {v | gauge K v < ρ}, inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d =
      CERW.unitBallVolume d / 2 * (2 * d * 1 * max (ρ - gauge K y) 0) := by
    rw [← h2]
    field_simp
  rw [h3]
  ring

end Gauge

/-! ### Applications to bodies that are not symmetric -/

section Applications

/-- The squared Euclidean norm in the plane. -/
private lemma norm_sq_two (y : EuclideanSpace ℝ (Fin 2)) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- The potential of the balls of the gauge of `cutDisc`, in closed form: for `ρ > 0`,
`U_{ψ < ρ}(y) = 4ε (ρ - max {|y|/2, -y₀})₊`. -/
theorem cutDisc_ball_potential (ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (y : EuclideanSpace ℝ (Fin 2)) :
    CERW.normPotential 2 ε (gauge cutDisc) {v | gauge cutDisc v < ρ} y =
      4 * ε * max (ρ - max (‖y‖ / 2) (-(y 0))) 0 := by
  rw [gauge_ball_potential (le_refl 2) isCompact_cutDisc convex_cutDisc
    zero_mem_interior_cutDisc ε hρ y, gauge_cutDisc_eq]
  push_cast
  ring

/-- The potential of the unit ball of the gauge of `cutDisc` is not even: `U(e₀) = 2ε` and
`U(-e₀) = 0`, because `ψ(e₀) = 1/2` and `ψ(-e₀) = 1`. -/
theorem cutDisc_ball_potential_not_even (ε : ℝ) :
    CERW.normPotential 2 ε (gauge cutDisc) {v | gauge cutDisc v < 1} (coordVec 0) = 2 * ε ∧
      CERW.normPotential 2 ε (gauge cutDisc) {v | gauge cutDisc v < 1} (-coordVec 0) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [gauge_ball_potential (le_refl 2) isCompact_cutDisc convex_cutDisc
      zero_mem_interior_cutDisc ε one_pos, gauge_cutDisc_coordVec_zero,
      max_eq_left (by norm_num)]
    push_cast
    ring
  · exact gauge_ball_potential_eq_zero (le_refl 2) isCompact_cutDisc convex_cutDisc
      zero_mem_interior_cutDisc ε one_pos (by rw [gauge_cutDisc_neg_coordVec_zero])

/-- The shell bound for the gauge of `cutDisc`: `|U_D(y)| ≤ 4εa` for measurable
`D ⊆ {b ≤ ψ ≤ b + a}`. -/
theorem cutDisc_layer_potential {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hb : 0 ≤ b) (ha : 0 < a)
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : MeasurableSet D)
    (hDs : D ⊆ {v | b ≤ gauge cutDisc v ∧ gauge cutDisc v ≤ b + a})
    (y : EuclideanSpace ℝ (Fin 2)) :
    |CERW.normPotential 2 ε (gauge cutDisc) D y| ≤ 4 * ε * a := by
  have h := gauge_layer_potential (le_refl 2) isCompact_cutDisc convex_cutDisc
    zero_mem_interior_cutDisc hε hb ha hD hDs y
  push_cast at h
  linarith

/-- The shell bound for `cutDisc` is attained at the origin by `{b ≤ ψ < b + a}`. -/
theorem cutDisc_layer_potential_zero (ε : ℝ) {a b : ℝ} (hb : 0 ≤ b) (ha : 0 < a) :
    CERW.normPotential 2 ε (gauge cutDisc) {v | b ≤ gauge cutDisc v ∧ gauge cutDisc v < b + a}
        0 = 4 * ε * a := by
  rw [gauge_layer_potential_zero (le_refl 2) isCompact_cutDisc convex_cutDisc
    zero_mem_interior_cutDisc ε hb ha]
  push_cast
  ring

/-- The potential of the body `cutDisc` itself, for the gauge of `cutDisc`, is continuous. -/
theorem continuous_normPotential_cutDisc (ε : ℝ) (hε : 0 ≤ ε) :
    Continuous (CERW.normPotential 2 ε (gauge cutDisc) cutDisc) :=
  continuous_normPotential_gauge (le_refl 2) isCompact_cutDisc convex_cutDisc
    zero_mem_interior_cutDisc hε isCompact_cutDisc.isClosed.measurableSet
    isCompact_cutDisc.isBounded

/-- The triangle with vertices `(-1,-1)`, `(2,-1)`, `(-1,2)`: a compact convex body with the origin
in its interior, three corners, and no symmetry about the origin. -/
def cornerTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  {y | -1 ≤ y 0 ∧ -1 ≤ y 1 ∧ y 0 + y 1 ≤ 1}

/-- `cornerTriangle` is compact. -/
theorem isCompact_cornerTriangle : IsCompact cornerTriangle := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h0 : Continuous fun y : EuclideanSpace ℝ (Fin 2) => y 0 := by fun_prop
    have h1 : Continuous fun y : EuclideanSpace ℝ (Fin 2) => y 1 := by fun_prop
    exact (isClosed_le continuous_const h0).inter
      ((isClosed_le continuous_const h1).inter (isClosed_le (h0.add h1) continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := 3)).subset
      fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := hy
    rw [mem_closedBall_zero_iff]
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by norm_num))
    rw [norm_sq_two]
    nlinarith [mul_nonneg (by linarith : 0 ≤ y 0 + 1) (by linarith : 0 ≤ 2 - y 0),
      mul_nonneg (by linarith : 0 ≤ y 1 + 1) (by linarith : 0 ≤ 2 - y 1)]

/-- `cornerTriangle` is convex. -/
theorem convex_cornerTriangle : Convex ℝ cornerTriangle := by
  have l0 : IsLinearMap ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y 0) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have l1 : IsLinearMap ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y 1) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have l2 : IsLinearMap ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y 0 + y 1) :=
    ⟨fun x y => by simp only [PiLp.add_apply]; ring,
      fun c x => by simp only [PiLp.smul_apply, smul_eq_mul]; ring⟩
  exact (convex_halfSpace_ge l0 (-1)).inter
    ((convex_halfSpace_ge l1 (-1)).inter (convex_halfSpace_le l2 1))

/-- The origin is an interior point of `cornerTriangle`. -/
theorem zero_mem_interior_cornerTriangle :
    (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior cornerTriangle := by
  refine mem_interior.mpr ⟨Metric.ball 0 (1 / 2), fun y hy => ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by norm_num)⟩
  have hy1 : ‖y‖ < 1 / 2 := by simpa using hy
  have h0 := PiLp.norm_apply_le y 0
  have h1 := PiLp.norm_apply_le y 1
  rw [Real.norm_eq_abs] at h0 h1
  refine ⟨?_, ?_, ?_⟩ <;> linarith [neg_abs_le (y 0), neg_abs_le (y 1), le_abs_self (y 0),
    le_abs_self (y 1)]

/-- A positively homogeneous functional that is at most `1` on `K` is at most the gauge of `K`. -/
private lemma le_gauge_of_le_one_on {K : Set (EuclideanSpace ℝ (Fin 2))}
    (h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior K) (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hℓ : ∀ (t : ℝ) (k : EuclideanSpace ℝ (Fin 2)), ℓ (t • k) = t * ℓ k)
    (hK : ∀ k ∈ K, ℓ k ≤ 1) (y : EuclideanSpace ℝ (Fin 2)) : ℓ y ≤ gauge K y := by
  by_contra h
  obtain ⟨b, hb, hby, hyb⟩ := exists_lt_of_gauge_lt
    (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)) (not_le.mp h)
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.mp hyb
  rw [hℓ] at hby
  nlinarith [mul_le_mul_of_nonneg_left (hK k hk) hb.le]

/-- The gauge of `cornerTriangle` in closed form: `ψ(y) = max {-y₀, -y₁, y₀ + y₁}`, because
`t • cornerTriangle = {y₀ ≥ -t, y₁ ≥ -t, y₀ + y₁ ≤ t}`. -/
theorem gauge_cornerTriangle_eq (y : EuclideanSpace ℝ (Fin 2)) :
    gauge cornerTriangle y = max (max (-(y 0)) (-(y 1))) (y 0 + y 1) := by
  refine le_antisymm ?_ (max_le (max_le ?_ ?_) ?_)
  · rcases eq_or_ne y 0 with rfl | hy
    · simp
    · set M := max (max (-(y 0)) (-(y 1))) (y 0 + y 1) with hM
      have h1 : -(y 0) ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
      have h2 : -(y 1) ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
      have h3 : y 0 + y 1 ≤ M := le_max_right _ _
      have hMpos : 0 < M := by
        by_contra hM0
        have hM0' : M ≤ 0 := not_lt.mp hM0
        apply hy
        ext i
        fin_cases i
        · simp
          linarith
        · simp
          linarith
      have hMi : 0 ≤ M⁻¹ := inv_nonneg.mpr hMpos.le
      have hmem : M⁻¹ • y ∈ cornerTriangle := by
        refine ⟨?_, ?_, ?_⟩
        · show (-1 : ℝ) ≤ M⁻¹ * y 0
          have h := mul_le_mul_of_nonneg_left (neg_le.mp h1) hMi
          rwa [mul_neg, inv_mul_cancel₀ hMpos.ne'] at h
        · show (-1 : ℝ) ≤ M⁻¹ * y 1
          have h := mul_le_mul_of_nonneg_left (neg_le.mp h2) hMi
          rwa [mul_neg, inv_mul_cancel₀ hMpos.ne'] at h
        · show M⁻¹ * y 0 + M⁻¹ * y 1 ≤ 1
          have h := mul_le_mul_of_nonneg_left h3 hMi
          rw [inv_mul_cancel₀ hMpos.ne'] at h
          calc M⁻¹ * y 0 + M⁻¹ * y 1 = M⁻¹ * (y 0 + y 1) := by ring
            _ ≤ 1 := h
      have h := (gauge_le_one_iff isCompact_cornerTriangle convex_cornerTriangle
        zero_mem_interior_cornerTriangle _).mpr hmem
      rw [gauge_smul_nonneg _ hMi, inv_mul_le_iff₀ hMpos] at h
      linarith
  · refine le_gauge_of_le_one_on zero_mem_interior_cornerTriangle (fun y => -(y 0))
      (fun t k => by simp) (fun k hk => by linarith [hk.1]) y
  · refine le_gauge_of_le_one_on zero_mem_interior_cornerTriangle (fun y => -(y 1))
      (fun t k => by simp) (fun k hk => by linarith [hk.2.1]) y
  · refine le_gauge_of_le_one_on zero_mem_interior_cornerTriangle (fun y => y 0 + y 1)
      (fun t k => by simp [mul_add]) (fun k hk => hk.2.2) y

/-- The gauge of `cornerTriangle` is not even: `ψ(a) = 1/2` and `ψ(-a) = 1/4` for
`a = (1/4, 1/4)`. -/
theorem gauge_cornerTriangle_not_even :
    gauge cornerTriangle ((1 / 4 : ℝ) • (coordVec 0 + coordVec 1)) = 1 / 2 ∧
      gauge cornerTriangle (-((1 / 4 : ℝ) • (coordVec 0 + coordVec 1))) = 1 / 4 := by
  rw [gauge_cornerTriangle_eq, gauge_cornerTriangle_eq]
  constructor <;> simp [coordVec] <;> norm_num

/-- The potential of the balls of the gauge of `cornerTriangle`, in closed form: for `ρ > 0`,
`U_{ψ < ρ}(y) = 4ε (ρ - max {-y₀, -y₁, y₀ + y₁})₊`. -/
theorem cornerTriangle_ball_potential (ε : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    CERW.normPotential 2 ε (gauge cornerTriangle) {v | gauge cornerTriangle v < ρ} y =
      4 * ε * max (ρ - max (max (-(y 0)) (-(y 1))) (y 0 + y 1)) 0 := by
  rw [gauge_ball_potential (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
    zero_mem_interior_cornerTriangle ε hρ y, gauge_cornerTriangle_eq]
  push_cast
  ring

/-- The potential of the unit ball of the gauge of `cornerTriangle` is not even: at
`a = (1/4, 1/4)` it is `2ε` and at `-a` it is `3ε`. -/
theorem cornerTriangle_ball_potential_not_even (ε : ℝ) :
    CERW.normPotential 2 ε (gauge cornerTriangle) {v | gauge cornerTriangle v < 1}
        ((1 / 4 : ℝ) • (coordVec 0 + coordVec 1)) = 2 * ε ∧
      CERW.normPotential 2 ε (gauge cornerTriangle) {v | gauge cornerTriangle v < 1}
        (-((1 / 4 : ℝ) • (coordVec 0 + coordVec 1))) = 3 * ε := by
  obtain ⟨h1, h2⟩ := gauge_cornerTriangle_not_even
  constructor
  · rw [gauge_ball_potential (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
      zero_mem_interior_cornerTriangle ε one_pos, h1, max_eq_left (by norm_num)]
    push_cast
    ring
  · rw [gauge_ball_potential (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
      zero_mem_interior_cornerTriangle ε one_pos, h2, max_eq_left (by norm_num)]
    push_cast
    ring

/-- The shell bound for the gauge of `cornerTriangle`: `|U_D(y)| ≤ 4εa` for measurable
`D ⊆ {b ≤ ψ ≤ b + a}`, attained by `{b ≤ ψ < b + a}` at the origin. -/
theorem cornerTriangle_layer_potential {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hb : 0 ≤ b) (ha : 0 < a)
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : MeasurableSet D)
    (hDs : D ⊆ {v | b ≤ gauge cornerTriangle v ∧ gauge cornerTriangle v ≤ b + a})
    (y : EuclideanSpace ℝ (Fin 2)) :
    |CERW.normPotential 2 ε (gauge cornerTriangle) D y| ≤ 4 * ε * a ∧
      CERW.normPotential 2 ε (gauge cornerTriangle)
        {v | b ≤ gauge cornerTriangle v ∧ gauge cornerTriangle v < b + a} 0 = 4 * ε * a := by
  refine ⟨?_, ?_⟩
  · have h := gauge_layer_potential (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
      zero_mem_interior_cornerTriangle hε hb ha hD hDs y
    push_cast at h
    linarith
  · rw [gauge_layer_potential_zero (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
      zero_mem_interior_cornerTriangle ε hb ha]
    push_cast
    ring

/-- The gauge of `cornerTriangle` has a corner: along the ray through the vertex `(-1,-1)` it is
not differentiable, so the gradient exists only almost everywhere. -/
theorem not_differentiableAt_gauge_cornerTriangle :
    ¬ DifferentiableAt ℝ (gauge cornerTriangle) (-coordVec 0 - coordVec 1) := by
  intro hdiff
  have hpath : DifferentiableAt ℝ
      (fun t : ℝ => (-coordVec 0 - coordVec 1 : EuclideanSpace ℝ (Fin 2)) +
        t • (coordVec 0 - coordVec 1)) 0 := by fun_prop
  have hg : DifferentiableAt ℝ (gauge cornerTriangle)
      ((fun t : ℝ => (-coordVec 0 - coordVec 1 : EuclideanSpace ℝ (Fin 2)) +
        t • (coordVec 0 - coordVec 1)) 0) := by simpa using hdiff
  have hline := hg.comp (0 : ℝ) hpath
  have hfun : (gauge cornerTriangle ∘ fun t : ℝ =>
      (-coordVec 0 - coordVec 1 : EuclideanSpace ℝ (Fin 2)) + t • (coordVec 0 - coordVec 1)) =
      fun t => 1 + |t| := by
    funext t
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin 2),
        v = -coordVec 0 - coordVec 1 + t • (coordVec 0 - coordVec 1) := ⟨_, rfl⟩
    have hy0 : v 0 = -1 + t := by rw [hv]; simp [coordVec]
    have hy1 : v 1 = -1 - t := by rw [hv]; simp [coordVec]; ring
    simp only [Function.comp_apply]
    rw [← hv, gauge_cornerTriangle_eq, hy0, hy1]
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht, max_eq_right (show -(-1 + t) ≤ -(-1 - t) by linarith),
        max_eq_left (show -1 + t + (-1 - t) ≤ -(-1 - t) by linarith)]
      ring
    · rw [abs_of_nonpos ht, max_eq_left (show -(-1 - t) ≤ -(-1 + t) by linarith),
        max_eq_left (show -1 + t + (-1 - t) ≤ -(-1 + t) by linarith)]
      ring
  rw [hfun] at hline
  have habs : DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
    have h := hline.sub_const 1
    simpa using h
  exact not_differentiableAt_abs_zero habs

end Applications

end CERW.Support.Norm.GaugePotential
