import CERW.Support.Norm.RadialNewtonConvolution
import CERW.Support.Norm.GaugePotential
import CERW.Support.Contact.ContactCell
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume

/-!
# The Newton convolution and the contact convolution for the gauge of a convex body

The proofs of `sec:norm-setup`--`sec:norms` use the symmetry `Ψ(-x) = Ψ(x)` only to bound the
coordinates of the subgradients (`oct5.tex:896`): for a compact convex set `K ⊆ ℝ^d` with the origin
in its interior, the Minkowski functional `ψ_K = gauge K` is convex and positively homogeneous, but
need not be even and need not be differentiable, and the proofs apply to it without change. This
module carries the passage `oct5.tex:759-771` and the contact geometry of `oct5.tex:633-655` to
`ψ_K`, without `IsNorm`, evenness, smoothness or strict convexity. The potential is literally
`CERW.normPotential d ε (gauge K) D y`, with Mathlib's `gradient` (the gradient where `ψ_K` is
differentiable, `0` elsewhere; the exceptional set is null by Rademacher's theorem).

The geometry of the body enters only through the producers of `GaugeModel` and `GaugePotential`:
measurability of `∇ψ_K` and the bound `|∇ψ_K| ≤ Λ_ψ` (`measurable_gradient`,
`norm_gradient_gauge_le`), the fact that where `ψ_K` is differentiable `∇ψ_K(v)` is a subgradient of
the convex function `ψ_K` (`gradient_isSubgradient_gauge`), continuity and the comparison
`c_ψ |x| ≤ ψ_K(x)` (`normMin_gauge_pos_mul_le`), and the potential of a sublevel set
(`gauge_ball_potential_eq_zero`). The generic part of the proof is that of `RadialNewtonConvolution`
for a measurable field of bounded norm.

* `gauge_normPotential_convolution_eq_radial`: `eq:newton-convolution` at **every** `y`, for every
  nonnegative integrable radial `f` (no measurable profile, no bound, no moment) and every bounded
  measurable `D`, with `(2ε/ω_d)` and the open-ball mass `m(s) = ∫_{|ζ| < s} f` of the source.
* `gauge_contact_convolution_le_radial`: `eq:contact-convolution` at a point `y₀` with
  `ψ_K(y₀) = b`, for every bounded measurable `D ⊇ {ψ_K < b}` and every real `b`.
* The visited-cell set `D_n` of a path: its inner threshold `b = inf {ψ_K(y) : y ∉ D_n}` is a true
  infimum, `{ψ_K < b} ⊆ D_n`, and there is a contact point, a point of the closure of the complement
  with `ψ_K(y₀) = b`, by coercivity `c_ψ |y| ≤ ψ_K(y)` and compactness
  (`exists_contact_point_gauge`, `exists_unvisited_cell_of_contact_point_gauge`);
  `source_contact_convolution_gauge` states the whole passage `oct5.tex:633-655, 759-771` for the
  actual cell set.

No statement assumes that the path takes unit steps, and no statement asserts that `H = U_{D_n}(y₀)`
is positive: for a symmetric body such as the `ℓ^∞` ball, `H` can vanish.
-/

open MeasureTheory LatticeProb

namespace CERW.Support.Norm.GaugeRadialNewtonConvolution

open CERW CERW.Generic.Kernel CERW.Support.Occupation CERW.Support.Contact
  CERW.Support.Norm.MinkowskiGauge

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-! ## The convolution for a field of bounded norm -/

/-- **`eq:newton-convolution` for a potential with a measurable gradient of bounded norm, at every
point.** Let `d ≥ 2`, let `Ψ` be a function on `ℝ^d` whose gradient is measurable and has norm at
most `Λ` (these are the hypotheses that a model supplies; for a gauge they are `GaugeModel`'s), let
`χ` be a nonnegative integrable radial weight (a measurable profile; no bound, no moment), let `D`
be a bounded measurable set and let `y` be any point. Then `ζ ↦ χ(|ζ|) U_D(y - ζ)` is integrable and
`(χ * U_D)(y) = (2ε/ω_d) ∫_D ∇Ψ(v) · (v - y)/|v - y|^d m(|v - y|) dv`, `m(s) = ∫_{|ζ| < s} χ`. -/
theorem normPotential_convolution_eq_of_gradient_bound (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {Λ : ℝ} (hg : Measurable (gradient Ψ))
    (hΛ : ∀ v, ‖gradient Ψ v‖ ≤ Λ) (ε : ℝ) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε Ψ D (y - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε Ψ D (y - ζ) =
      2 * ε / unitBallVolume d * ∫ v in D,
        inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d *
          ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, χ ‖ζ‖ := by
  obtain ⟨hint, heq⟩ := RadialNewtonConvolution.integral_weight_field_eq hd hχm hχ0 hχi hg hΛ hD
    hDb.measure_lt_top.ne y
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun t =>
    χ ‖t‖ * ∫ v in D, inner ℝ (gradient Ψ v) (newtonField (v - y - t)) with hh
  have hfun : (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε Ψ D (y - ζ)) =
      fun ζ => (2 * ε / unitBallVolume d) * h (-ζ) := by
    funext ζ
    have hv : ∀ v : EuclideanSpace ℝ (Fin d), v - y - -ζ = v - (y - ζ) := fun v => by abel
    simp only [hh, normPotential, norm_neg, hv, inner_newtonField]
    ring
  rw [hfun]
  refine ⟨(hint.comp_neg).const_mul _, ?_⟩
  rw [integral_const_mul, integral_neg_eq_self h volume, hh]
  simp only [hh] at heq
  rw [heq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [inner_newtonField]
  ring

/-- **The gauge of a compact convex body: `eq:newton-convolution` at every point, Borel profile.**
Let `d ≥ 2`, let `K` be a compact convex set with the origin in its interior, `ε` real, `χ` a
nonnegative integrable radial weight with a Borel profile, `D` a bounded measurable set and
`y ∈ ℝ^d`. No evenness of `gauge K` is used. -/
theorem gauge_normPotential_convolution_eq (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε (gauge K) D (y - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε (gauge K) D (y - ζ) =
      2 * ε / unitBallVolume d * ∫ v in D,
        inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d *
          ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, χ ‖ζ‖ :=
  normPotential_convolution_eq_of_gradient_bound hd
    (CERW.Support.Norm.GaugeModel.measurable_gradient (gauge K))
    (CERW.Support.Norm.GaugeModel.norm_gradient_gauge_le hK hc h0) ε hχm hχ0 hχi hD hDb y

/-- **The gauge of a compact convex body: `eq:newton-convolution` at every point, for every
nonnegative integrable radial function.** Let `d ≥ 2`, `K` a compact convex set with the origin in
its interior, `ε` real, `f : ℝ^d → ℝ` nonnegative, integrable and radial (`f x = f y` whenever
`|x| = |y|`; no measurable profile, no bound, no moment), `D` a bounded measurable set and
`y ∈ ℝ^d` any point. Then `ζ ↦ f(ζ) U_D(y - ζ)` is integrable and
`(f * U_D)(y) = (2ε/ω_d) ∫_D ∇ψ_K(v) · (v - y)/|v - y|^d m(|v - y|) dv`, `m(s) = ∫_{|ζ| < s} f`. -/
theorem gauge_normPotential_convolution_eq_radial (hd : 2 ≤ d) (hK : IsCompact K)
    (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hrad : ∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) (y : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => f ζ * normPotential d ε (gauge K) D (y - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), f ζ * normPotential d ε (gauge K) D (y - ζ) =
      2 * ε / unitBallVolume d * ∫ v in D,
        inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d *
          ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, f ζ := by
  obtain ⟨χ, hχm, hχ0, hae⟩ := RadialNewtonConvolution.exists_borel_profile hd hrad hf0 hfi
  have hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖) := hfi.congr hae
  obtain ⟨hint, heq⟩ := gauge_normPotential_convolution_eq hd hK hc h0 ε hχm hχ0 hχi hD hDb y
  have hcongr : (fun ζ : EuclideanSpace ℝ (Fin d) =>
      f ζ * normPotential d ε (gauge K) D (y - ζ)) =ᵐ[volume]
      fun ζ => χ ‖ζ‖ * normPotential d ε (gauge K) D (y - ζ) :=
    hae.mono fun ζ h => by simp only [h]
  refine ⟨hint.congr hcongr.symm, ?_⟩
  rw [integral_congr_ae hcongr, heq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [RadialNewtonConvolution.ballMass_congr hae]

/-- **`eq:newton-convolution` for the gauge in the form of the convolution of Mathlib.** -/
theorem gauge_convolution_normPotential_eq_radial (hd : 2 ≤ d) (hK : IsCompact K)
    (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hrad : ∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) (y : EuclideanSpace ℝ (Fin d)) :
    convolution f (normPotential d ε (gauge K) D) (ContinuousLinearMap.mul ℝ ℝ) volume y =
      2 * ε / unitBallVolume d * ∫ v in D,
        inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d *
          ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y‖, f ζ := by
  rw [convolution_def]
  exact (gauge_normPotential_convolution_eq_radial hd hK hc h0 ε hrad hf0 hfi hD hDb y).2

/-! ## `eq:contact-convexity` for the gauge -/

/-- **`eq:contact-convexity` at a point of differentiability.** If `ψ_K` is differentiable at `v`,
then `∇ψ_K(v) · (v - y₀) ≥ ψ_K(v) - ψ_K(y₀)`: the gradient is a subgradient of the convex function
`ψ_K`. No evenness is used. -/
theorem gauge_sub_le_inner_gradient_sub (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {v : EuclideanSpace ℝ (Fin d)}
    (hv : DifferentiableAt ℝ (gauge K) v) (y₀ : EuclideanSpace ℝ (Fin d)) :
    gauge K v - gauge K y₀ ≤ inner ℝ (gradient (gauge K) v) (v - y₀) := by
  have h1 := CERW.Support.Norm.GaugeModel.gradient_isSubgradient_gauge hc h0 hv y₀
  have h2 : inner ℝ (gradient (gauge K) v) (v - y₀) =
      -inner ℝ (gradient (gauge K) v) (y₀ - v) := by
    rw [← inner_neg_right, neg_sub]
  linarith

/-- If `ψ_K(y₀) ≤ ψ_K(v)`, then `∇ψ_K(v) · (v - y₀) ≥ 0`: at a point of differentiability by
`gauge_sub_le_inner_gradient_sub`, and elsewhere because the gradient is `0` there. -/
theorem gauge_inner_gradient_sub_nonneg (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {v y₀ : EuclideanSpace ℝ (Fin d)}
    (h : gauge K y₀ ≤ gauge K v) : 0 ≤ inner ℝ (gradient (gauge K) v) (v - y₀) := by
  by_cases hv : DifferentiableAt ℝ (gauge K) v
  · have := gauge_sub_le_inner_gradient_sub hc h0 hv y₀
    linarith
  · have hz : gradient (gauge K) v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [hz, inner_zero_left]

/-- **`eq:contact-convexity`.** Let `D` be measurable, `E = D ∖ {ψ_K < b}` and `ψ_K(y₀) = b`. For
almost every `v ∈ E`, `∇ψ_K(v) · (v - y₀) ≥ ψ_K(v) - b ≥ 0`. -/
theorem ae_gauge_contact_convexity (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {b : ℝ} {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : gauge K y₀ = b) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (D \ {v | gauge K v < b}),
      gauge K v - b ≤ inner ℝ (gradient (gauge K) v) (v - y₀) ∧ 0 ≤ gauge K v - b := by
  filter_upwards
    [ae_restrict_of_ae (CERW.Support.Norm.GaugeModel.ae_differentiableAt_gauge hK hc h0),
    ae_restrict_mem (hD.diff (CERW.Support.Norm.GaugeModel.measurableSet_gauge_sublevel hc h0 b))]
    with v hv hvE
  have h1 := gauge_sub_le_inner_gradient_sub hc h0 hv y₀
  rw [hy₀] at h1
  exact ⟨h1, sub_nonneg.mpr (not_lt.mp hvE.2)⟩

/-! ## The contact convolution -/

/-- The potential of a set splits over a measurable subset `B`: `U_D = U_B + U_{D ∖ B}`, for a
potential with a measurable gradient of bounded norm. -/
theorem normPotential_union_diff_of_gradient_bound (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {Λ : ℝ} (hg : Measurable (gradient Ψ))
    (hΛ : ∀ v, ‖gradient Ψ v‖ ≤ Λ) (ε : ℝ) {D B : Set (EuclideanSpace ℝ (Fin d))}
    (hBD : B ⊆ D) (hBm : MeasurableSet B) (hDm : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ D y = normPotential d ε Ψ B y + normPotential d ε Ψ (D \ B) y := by
  have hBfin : volume B ≠ ⊤ := (measure_mono hBD).trans_lt hDfin.lt_top |>.ne
  have hDBfin : volume (D \ B) ≠ ⊤ :=
    (measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top |>.ne
  unfold normPotential
  rw [← mul_add, ← setIntegral_union Set.disjoint_sdiff_right (hDm.diff hBm)
    (RadialNewtonConvolution.integrableOn_field_kernel hd hg hΛ hBm hBfin y)
    (RadialNewtonConvolution.integrableOn_field_kernel hd hg hΛ (hDm.diff hBm) hDBfin y),
    Set.union_sdiff_cancel hBD]

/-- **`eq:contact-convolution` for a potential with a gradient of bounded norm.** Let `d ≥ 2`,
let `Ψ` have a measurable gradient of norm at most `Λ`, `ε ≥ 0`, `χ` a nonnegative integrable
radial weight (a measurable profile), `D` a bounded measurable set, `B ⊆ D` measurable, and `y₀` a
point at which the potential of `B` vanishes and `∇Ψ(v) · (v - y₀) ≥ 0` for every `v ∈ D ∖ B`. With
`E = D ∖ B`, `ζ ↦ χ(|ζ|) U_E(y₀ - ζ)` is integrable, `(χ * U_E)(y₀) ≤ ‖χ‖₁ U_D(y₀)` and
`U_E(y₀) = U_D(y₀)`. -/
theorem contact_convolution_le_of_gradient_bound (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {Λ : ℝ} (hg : Measurable (gradient Ψ))
    (hΛ : ∀ v, ‖gradient Ψ v‖ ≤ Λ) {ε : ℝ} (hε : 0 ≤ ε) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D B : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (hB : MeasurableSet B) (hBD : B ⊆ D) {y₀ : EuclideanSpace ℝ (Fin d)}
    (hUB : normPotential d ε Ψ B y₀ = 0)
    (hsign : ∀ v ∈ D \ B, 0 ≤ inner ℝ (gradient Ψ v) (v - y₀)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * normPotential d ε Ψ (D \ B) (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε Ψ (D \ B) (y₀ - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * normPotential d ε Ψ D y₀ ∧
    normPotential d ε Ψ (D \ B) y₀ = normPotential d ε Ψ D y₀ := by
  have hEm : MeasurableSet (D \ B) := hD.diff hB
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hEfin : volume (D \ B) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top).ne
  have hsplit := normPotential_union_diff_of_gradient_bound hd hg hΛ ε hBD hB hD hDfin y₀
  have hUE : normPotential d ε Ψ (D \ B) y₀ = normPotential d ε Ψ D y₀ := by
    rw [hsplit, hUB, zero_add]
  obtain ⟨hint, heq⟩ := normPotential_convolution_eq_of_gradient_bound hd hg hΛ ε hχm hχ0 hχi hEm
    (hDb.subset Set.sdiff_subset) y₀
  refine ⟨hint, ?_, hUE⟩
  rw [heq, ← hUE]
  have hq := RadialNewtonConvolution.integrableOn_field_kernel hd hg hΛ hEm hEfin y₀
  have hm := RadialNewtonConvolution.measurable_ballMass hχ0 hχi
  have hpos : ∀ v ∈ D \ B, 0 ≤ inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d := fun v hv =>
    div_nonneg (hsign v hv) (pow_nonneg (norm_nonneg _) _)
  have hqm : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d *
        ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y₀‖, χ ‖ζ‖) (D \ B) := by
    refine Integrable.mul_bdd (c := ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) hq
      (hm.comp (measurable_id.sub measurable_const).norm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    obtain ⟨h0, h1⟩ := RadialNewtonConvolution.ballMass_bounds hχ0 hχi ‖v - y₀‖
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have hle : ∫ v in D \ B, inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d *
        ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y₀‖, χ ‖ζ‖ ≤
      ∫ v in D \ B, (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
        (inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d) := by
    refine setIntegral_mono_on hqm (hq.const_mul _) hEm fun v hv => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (RadialNewtonConvolution.ballMass_bounds hχ0 hχi _).2
      (hpos v hv)
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  unfold normPotential
  calc 2 * ε / unitBallVolume d * ∫ v in D \ B, inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d *
        ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖v - y₀‖, χ ‖ζ‖
      ≤ 2 * ε / unitBallVolume d * ∫ v in D \ B, (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
          (inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d) :=
        mul_le_mul_of_nonneg_left hle hc
    _ = (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
          (2 * ε / unitBallVolume d *
            ∫ v in D \ B, inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d) := by
        rw [integral_const_mul]
        ring

/-- The potential of the empty set vanishes. -/
private theorem normPotential_empty (ε : ℝ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : normPotential d ε Ψ ∅ y = 0 := by
  simp [normPotential]

/-- **The potential of `{ψ_K < b}` at a point with `ψ_K(y₀) = b` is `0`** (`lem:ballpotential`, for
every real `b`: for `b > 0` the potential is `2dε (b - ψ_K(y₀))₊ = 0`, and for `b ≤ 0` the set is
empty because `ψ_K ≥ 0`). -/
theorem gauge_ball_potential_contact (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ε : ℝ) {b : ℝ}
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : gauge K y₀ = b) :
    normPotential d ε (gauge K) {v | gauge K v < b} y₀ = 0 := by
  rcases lt_or_ge 0 b with hb | hb
  · exact CERW.Support.Norm.GaugePotential.gauge_ball_potential_eq_zero hd hK hc h0 ε hb hy₀.ge
  · have hempty : {v : EuclideanSpace ℝ (Fin d) | gauge K v < b} = ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact hb.trans (gauge_nonneg v)
    rw [hempty]
    exact normPotential_empty ε (gauge K) y₀

/-- **`eq:contact-convolution` for the gauge of a compact convex body.** Let `d ≥ 2`, `K` a compact
convex set with the origin in its interior, `ε ≥ 0`, `χ` a nonnegative integrable radial weight (a
measurable profile), `D` a bounded measurable set, `b` real with `{ψ_K < b} ⊆ D`, and `y₀` with
`ψ_K(y₀) = b`. With `E = D ∖ {ψ_K < b}`: `ζ ↦ χ(|ζ|) U_E(y₀ - ζ)` is integrable,
`(χ * U_E)(y₀) ≤ ‖χ‖₁ U_D(y₀)` and `U_E(y₀) = U_D(y₀)`. -/
theorem gauge_contact_convolution_le (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    {b : ℝ} (hBD : {v | gauge K v < b} ⊆ D) {y₀ : EuclideanSpace ℝ (Fin d)}
    (hy₀ : gauge K y₀ = b) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * normPotential d ε (gauge K) (D \ {v | gauge K v < b}) (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d),
        χ ‖ζ‖ * normPotential d ε (gauge K) (D \ {v | gauge K v < b}) (y₀ - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * normPotential d ε (gauge K) D y₀ ∧
    normPotential d ε (gauge K) (D \ {v | gauge K v < b}) y₀ =
      normPotential d ε (gauge K) D y₀ :=
  contact_convolution_le_of_gradient_bound hd
    (CERW.Support.Norm.GaugeModel.measurable_gradient (gauge K))
    (CERW.Support.Norm.GaugeModel.norm_gradient_gauge_le hK hc h0) hε hχm hχ0 hχi hD hDb
    (CERW.Support.Norm.GaugeModel.measurableSet_gauge_sublevel hc h0 b) hBD
    (gauge_ball_potential_contact hd hK hc h0 ε hy₀)
    (fun v hv => gauge_inner_gradient_sub_nonneg hc h0 (by
      have : ¬ gauge K v < b := hv.2
      rw [hy₀]
      exact not_lt.mp this))

/-- **`eq:contact-convolution` for the gauge of a compact convex body, for every nonnegative
integrable radial function.** The statement of `gauge_contact_convolution_le` for a nonnegative
integrable radial function `f : ℝ^d → ℝ`: no measurable profile, no bound, no moment. -/
theorem gauge_contact_convolution_le_radial (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hrad : ∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {b : ℝ} (hBD : {v | gauge K v < b} ⊆ D)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : gauge K y₀ = b) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      f ζ * normPotential d ε (gauge K) (D \ {v | gauge K v < b}) (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d),
        f ζ * normPotential d ε (gauge K) (D \ {v | gauge K v < b}) (y₀ - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) * normPotential d ε (gauge K) D y₀ ∧
    normPotential d ε (gauge K) (D \ {v | gauge K v < b}) y₀ =
      normPotential d ε (gauge K) D y₀ := by
  obtain ⟨χ, hχm, hχ0, hae⟩ := RadialNewtonConvolution.exists_borel_profile hd hrad hf0 hfi
  have hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖) := hfi.congr hae
  obtain ⟨hint, hle, hUE⟩ := gauge_contact_convolution_le hd hK hc h0 hε hχm hχ0 hχi hD hDb hBD hy₀
  have hcongr : (fun ζ : EuclideanSpace ℝ (Fin d) =>
      f ζ * normPotential d ε (gauge K) (D \ {v | gauge K v < b}) (y₀ - ζ)) =ᵐ[volume]
      fun ζ => χ ‖ζ‖ * normPotential d ε (gauge K) (D \ {v | gauge K v < b}) (y₀ - ζ) :=
    hae.mono fun ζ h => by simp only [h]
  refine ⟨hint.congr hcongr.symm, ?_, hUE⟩
  rw [integral_congr_ae hcongr, integral_congr_ae hae]
  exact hle

/-! ## The visited-cell set of a path -/

/-- A nonempty set `S ⊆ ℝ^d` has a point `y₀` in its closure at which a continuous coercive
nonnegative function `Ψ` attains the infimum of `Ψ` over `S`: coercivity `c |y| ≤ Ψ(y)` makes the
intersection of the closure of `S` with `{Ψ ≤ inf + 1}` compact. -/
theorem exists_mem_closure_eq_sInf_of_coercive {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcont : Continuous Ψ) (hnn : ∀ y, 0 ≤ Ψ y) {c : ℝ} (hc : 0 < c)
    (hcoe : ∀ y, c * ‖y‖ ≤ Ψ y) {S : Set (EuclideanSpace ℝ (Fin d))} (hS : S.Nonempty) :
    ∃ y₀ ∈ closure S, Ψ y₀ = sInf (Ψ '' S) := by
  set b := sInf (Ψ '' S) with hb
  have hbdd : BddBelow (Ψ '' S) := ⟨0, by rintro _ ⟨y, -, rfl⟩; exact hnn y⟩
  have hle : ∀ y ∈ S, b ≤ Ψ y := fun y hy => csInf_le hbdd ⟨y, hy, rfl⟩
  have hlt : b < b + 1 := by linarith
  obtain ⟨_, ⟨y1, hy1, rfl⟩, h1⟩ := exists_lt_of_csInf_lt (hS.image Ψ) hlt
  have hFclosed : IsClosed (closure S ∩ {y | Ψ y ≤ b + 1}) :=
    isClosed_closure.inter (isClosed_le hcont continuous_const)
  have hFbdd : Bornology.IsBounded (closure S ∩ {y | Ψ y ≤ b + 1}) := by
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := (b + 1) / c)).subset fun y hy => ?_
    rw [mem_closedBall_zero_iff, le_div_iff₀ hc]
    have := hcoe y
    have h2 : Ψ y ≤ b + 1 := hy.2
    nlinarith
  have hFc : IsCompact (closure S ∩ {y | Ψ y ≤ b + 1}) :=
    Metric.isCompact_of_isClosed_isBounded hFclosed hFbdd
  have hFne : (closure S ∩ {y | Ψ y ≤ b + 1}).Nonempty := ⟨y1, subset_closure hy1, h1.le⟩
  obtain ⟨y₀, hy₀F, hminOn⟩ := hFc.exists_isMinOn hFne hcont.continuousOn
  refine ⟨y₀, hy₀F.1, le_antisymm ?_ ?_⟩
  · refine le_of_not_gt fun hcon => ?_
    obtain ⟨_, ⟨y2, hy2, rfl⟩, h2⟩ := exists_lt_of_csInf_lt (hS.image Ψ) (lt_min hcon hlt)
    have hy2F : y2 ∈ closure S ∩ {y | Ψ y ≤ b + 1} :=
      ⟨subset_closure hy2, (h2.trans_le (min_le_right _ _)).le⟩
    have h3 : Ψ y₀ ≤ Ψ y2 := isMinOn_iff.mp hminOn y2 hy2F
    have h4 := h2.trans_le (min_le_left _ _)
    linarith
  · exact closure_minimal hle (isClosed_le continuous_const hcont) hy₀F.1

/-- The cell set `D_n` of a path is bounded. -/
theorem isBounded_cellSet (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ) :
    Bornology.IsBounded (cellSet x n) :=
  Metric.isBounded_ball.subset (cellSet_subset_ball hd x n)

/-- The complement of the cell set is nonempty, since `D_n` is bounded. -/
theorem compl_cellSet_nonempty (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ) :
    (cellSet x n)ᶜ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
  have hbdd : Bornology.IsBounded (Set.univ : Set (EuclideanSpace ℝ (Fin d))) := by
    rw [← h]
    exact isBounded_cellSet hd x n
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact NormedSpace.unbounded_univ ℝ _ hbdd

/-- **The inner threshold of the gauge is the infimum.** `normInnerRadius (gauge K) x n` is the
greatest lower bound of `ψ_K` over the nonempty complement of `D_n`, not the value of `sInf` at an
empty or unbounded set. -/
theorem isGLB_normInnerRadius_gauge (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ) :
    IsGLB (gauge K '' (cellSet x n)ᶜ) (normInnerRadius (gauge K) x n) :=
  isGLB_csInf ((compl_cellSet_nonempty hd x n).image (gauge K))
    ⟨0, by rintro _ ⟨y, -, rfl⟩; exact gauge_nonneg y⟩

/-- **`{ψ_K < b} ⊆ D_n`.** -/
theorem gauge_sublevel_subset_cellSet (x : ℕ → Site d) (n : ℕ) :
    {v | gauge K v < normInnerRadius (gauge K) x n} ⊆ cellSet x n := by
  intro v hv
  by_contra hvD
  exact absurd (csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact gauge_nonneg y⟩
    ⟨v, hvD, rfl⟩ : normInnerRadius (gauge K) x n ≤ gauge K v) (not_le.mpr hv)

/-- **The contact point of the gauge.** For a compact convex `K` with the origin in its interior
and a path `x`, there is a point `y₀` of the closure of `ℝ^d ∖ D_n` with `ψ_K(y₀) = b`: a limit of
points outside `D_n` at which `ψ_K` attains its infimum. Coercivity `c_ψ |y| ≤ ψ_K(y)` is
`GaugeModel.normMin_gauge_pos_mul_le`. -/
theorem exists_contact_point_gauge (hd : 1 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (x : ℕ → Site d) (n : ℕ) :
    ∃ y₀ : EuclideanSpace ℝ (Fin d), gauge K y₀ = normInnerRadius (gauge K) x n ∧
      y₀ ∈ closure (cellSet x n)ᶜ := by
  obtain ⟨hcpos, hcoe⟩ := CERW.Support.Norm.GaugeModel.normMin_gauge_pos_mul_le hK h0 hd
  obtain ⟨y₀, hy₀, hΨy₀⟩ := exists_mem_closure_eq_sInf_of_coercive
    (continuous_gauge hc (mem_interior_iff_mem_nhds.mp h0)) (fun y => gauge_nonneg y) hcpos hcoe
    (compl_cellSet_nonempty hd x n)
  exact ⟨y₀, hΨy₀, hy₀⟩

/-- **The unvisited cell at a contact point.** If `y₀` lies in the closure of `ℝ^d ∖ D_n`, it lies
in the closure of the cell `C_z` of a site `z` not visited before time `n`; then `ℓ_n(z) = 0`,
`|z - y₀| ≤ √d/2`, and `ψ_K(z) ≥ b` because `z` lies outside `D_n`. -/
theorem exists_unvisited_cell_of_contact_point_gauge (x : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hcl : y₀ ∈ closure (cellSet x n)ᶜ) :
    ∃ z : Site d, localTime x n z = 0 ∧ y₀ ∈ closure (cell z) ∧
      ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 ∧
      normInnerRadius (gauge K) x n ≤ gauge K (toSpace z) := by
  obtain ⟨z, hzA, hzcl⟩ := exists_unvisited_mem_closure_cell x n hcl
  refine ⟨z, ?_, hzcl, ?_, ?_⟩
  · rwa [mem_departureRange_iff, not_lt, Nat.le_zero] at hzA
  · rw [norm_sub_rev]
    exact norm_sub_toSpace_le_of_mem_closure_cell hzcl
  · exact csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact gauge_nonneg y⟩
      ⟨toSpace z, fun h => hzA ((toSpace_mem_cellSet_iff x n z).mp h), rfl⟩

/-- **`eq:contact-convolution` for the visited-cell set and the gauge, at every point with
`ψ_K(y₀) = b`.** For every path `x`, every `n`, every nonnegative integrable radial `f`
(no measurable profile, no bound, no moment) and every `y₀` with `ψ_K(y₀) = b = normInnerRadius`,
with `D_n = cellSet x n` and `E = D_n ∖ {ψ_K < b}`: `ζ ↦ f(ζ) U_E(y₀ - ζ)` is integrable,
`(f * U_E)(y₀) ≤ ‖f‖₁ H` with `H = U_{D_n}(y₀)`, and `U_E(y₀) = H`. -/
theorem gauge_contact_convolution_le_cellSet (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hrad : ∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) (x : ℕ → Site d) (n : ℕ) {y₀ : EuclideanSpace ℝ (Fin d)}
    (hy₀ : gauge K y₀ = normInnerRadius (gauge K) x n) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      f ζ * normPotential d ε (gauge K)
        (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d),
        f ζ * normPotential d ε (gauge K)
          (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) (y₀ - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) * normPotential d ε (gauge K) (cellSet x n) y₀ ∧
    normPotential d ε (gauge K) (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) y₀ =
      normPotential d ε (gauge K) (cellSet x n) y₀ :=
  gauge_contact_convolution_le_radial hd hK hc h0 hε hrad hf0 hfi (measurableSet_cellSet x n)
    (isBounded_cellSet (by omega) x n) (gauge_sublevel_subset_cellSet x n) hy₀

/-- **The passage of the source for the visited-cell set and the gauge of a convex body**
(`oct5.tex:633-655, 759-771, 896`). For every path `x` and time `n`, with `D_n = cellSet x n` and
`b = normInnerRadius (gauge K) x n`: `b` is the infimum of `ψ_K` over the complement of `D_n`,
`{ψ_K < b} ⊆ D_n`, and there is a contact point `y₀`, a point of the closure of the complement with
`ψ_K(y₀) = b`, in the closure of the cell of an unvisited site, at which for every nonnegative
integrable radial `f` the function `ζ ↦ f(ζ) U_E(y₀ - ζ)` is integrable,
`(f * U_E)(y₀) ≤ ‖f‖₁ H` with `H = U_{D_n}(y₀)`, and `U_E(y₀) = H`. -/
theorem source_contact_convolution_gauge (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε) (x : ℕ → Site d)
    (n : ℕ) :
    IsGLB (gauge K '' (cellSet x n)ᶜ) (normInnerRadius (gauge K) x n) ∧
    {v | gauge K v < normInnerRadius (gauge K) x n} ⊆ cellSet x n ∧
    ∃ y₀ : EuclideanSpace ℝ (Fin d), gauge K y₀ = normInnerRadius (gauge K) x n ∧
      y₀ ∈ closure (cellSet x n)ᶜ ∧
      (∃ z : Site d, localTime x n z = 0 ∧ y₀ ∈ closure (cell z) ∧
        ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 ∧ normInnerRadius (gauge K) x n ≤ gauge K (toSpace z)) ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ x y : EuclideanSpace ℝ (Fin d), ‖x‖ = ‖y‖ → f x = f y) → (∀ x, 0 ≤ f x) →
        Integrable f →
        Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
          f ζ * normPotential d ε (gauge K)
            (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) (y₀ - ζ)) ∧
        ∫ ζ : EuclideanSpace ℝ (Fin d),
            f ζ * normPotential d ε (gauge K)
              (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) (y₀ - ζ) ≤
          (∫ ζ : EuclideanSpace ℝ (Fin d), f ζ) * normPotential d ε (gauge K) (cellSet x n) y₀ ∧
        normPotential d ε (gauge K)
            (cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n}) y₀ =
          normPotential d ε (gauge K) (cellSet x n) y₀ := by
  obtain ⟨y₀, hy₀, hcl⟩ := exists_contact_point_gauge (by omega : 1 ≤ d) hK hc h0 x n
  exact ⟨isGLB_normInnerRadius_gauge (by omega) x n, gauge_sublevel_subset_cellSet x n, y₀, hy₀,
    hcl, exists_unvisited_cell_of_contact_point_gauge x n hcl,
    fun f hrad hf0 hfi => gauge_contact_convolution_le_cellSet hd hK hc h0 hε hrad hf0 hfi x n hy₀⟩

end CERW.Support.Norm.GaugeRadialNewtonConvolution
