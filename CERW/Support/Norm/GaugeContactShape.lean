import CERW.Support.Norm.GaugePotential
import CERW.Support.Contact.ContactCell
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.Cells
import CERW.Generic.Kernel.NewtonField
import CERW.Generic.Kernel.Modulus
import CERW.Generic.Kernel.Integrable
import CERW.Generic.Newton.Polar
import CERW.Support.Geometry.Newton
import CERW.Support.Occupation.SiteArith
import CERW.Support.LocalTime.Bracket
import CERW.Generic.Lattice.Centered
import CERW.Generic.Kernel.LogRadial
import CERW.Generic.Kernel.RadialPower
import CERW.Support.Law.ScaleArith
import CERW.Support.Occupation.CellIntegral
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Geometry.BallCompare
import CERW.Support.Drift
import CERW.Support.Occupation.FreshSum
import CERW.Support.Crossing.LastEntrance
import CERW.Support.Law.Moments
import CERW.Support.Geometry.Bound
import CERW.Model.NormPotential
import CERW.Support.Occupation.Facts

/-!
# The contact potential, the profile and the shape rates for the gauge of a convex body

For a compact convex body `K` with the origin in its interior and its Minkowski functional
`ψ = gauge K`, which need not be even, this module proves the deterministic mathematics behind the
rates of the limit shape of the centrally excited random walk with drift opposite to subgradients
of `ψ`:

* the convolution bound of the gauge, which absorbs the cone profile of the resolvent;
* the bound on the potential of the cell set at a contact point of the inradius, `C √(r log n)` in
  the plane and `C log n` in dimension `d ≥ 3`, from the pointwise and the crude local-time bounds,
  for an arbitrary choice of subgradients, and its rate form `C r q`;
* the geometry of the inradius: the excess of the cell set over the largest ball, the mass identity
  that normalizes the scale by `|K|`, and the rates of the inner radius and of the profile of the
  local times;
* the outer crossing lemma for the gauge, the nearest point of `{ψ ≤ r}` and the drift at the
  visited sites farthest from this set, which give the outer radius;
* the three rates together, and their instances for the cut disc and for the triangle with corners.

The estimates that hold only with high probability, namely the coarse bounds, the pointwise
local-time bound, the crude bound on the cell local times, the compensated-path bound and the linear
martingale bounds, enter as the hypotheses of deterministic implications about a path of the walk.
Evenness of `ψ` is never used.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal ContDiff
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeContactShape

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugePotential

/-!
## Contact, profile and shape estimates for the gauge of a convex body

Deterministic parts of the proof of Proposition 5.1 for the literal gauge `ψ = gauge K` of a compact
convex body `K` with the origin in its interior; no evenness and no assumption beyond these three.
-/

/-! ### The hypotheses on the body, bundled -/

/-- The three hypotheses on the body `K`: compact, convex, with the origin in the interior. -/
structure Adm {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : Prop where
  /-- `K` is compact. -/
  compact : IsCompact K
  /-- `K` is convex. -/
  convex : Convex ℝ K
  /-- The origin is an interior point of `K`. -/
  zero_mem : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K

namespace Adm

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- The gauge is continuous. -/
theorem continuous (h : Adm K) : Continuous (gauge K) :=
  continuous_gauge h.convex (mem_interior_iff_mem_nhds.mp h.zero_mem)

/-- The gauge vanishes at the origin. -/
theorem map_zero (_h : Adm K) : gauge K 0 = 0 := gauge_zero

/-- The gauge is nonnegative. -/
theorem nonneg (_h : Adm K) (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ gauge K x := gauge_nonneg x

/-- The gauge is subadditive. -/
theorem add_le (h : Adm K) (x y : EuclideanSpace ℝ (Fin d)) :
    gauge K (x + y) ≤ gauge K x + gauge K y :=
  gauge_subadditive h.convex h.zero_mem x y

/-- Positive homogeneity. -/
theorem smul_nonneg (_h : Adm K) {t : ℝ} (ht : 0 ≤ t) (x : EuclideanSpace ℝ (Fin d)) :
    gauge K (t • x) = t * gauge K x :=
  gauge_smul_nonneg K ht x

/-- `ψ(x) ≤ Λ_ψ |x|`. -/
theorem le_normMax_mul (h : Adm K) (x : EuclideanSpace ℝ (Fin d)) :
    gauge K x ≤ normMax (gauge K) * ‖x‖ :=
  gauge_le_normMax_mul h.compact h.zero_mem x

/-- `c_ψ > 0` and `c_ψ |x| ≤ ψ(x)`. -/
theorem normMin_pos_mul_le (h : Adm K) (hd : 1 ≤ d) :
    0 < normMin (gauge K) ∧ ∀ x : EuclideanSpace ℝ (Fin d), normMin (gauge K) * ‖x‖ ≤ gauge K x :=
  normMin_gauge_pos_mul_le h.compact h.zero_mem hd

/-- `Λ_ψ ≥ 0`. -/
theorem normMax_nonneg (_h : Adm K) : 0 ≤ normMax (gauge K) := normMax_gauge_nonneg K

/-- Almost everywhere differentiability. -/
theorem ae_differentiableAt (h : Adm K) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ (gauge K) v :=
  ae_differentiableAt_gauge h.compact h.convex h.zero_mem

/-- The gradient is a subgradient where it exists. -/
theorem gradient_isSubgradient (h : Adm K) {v : EuclideanSpace ℝ (Fin d)}
    (hv : DifferentiableAt ℝ (gauge K) v) : IsSubgradient (gauge K) v (gradient (gauge K) v) :=
  gradient_isSubgradient_gauge h.convex h.zero_mem hv

/-- Euler's relation and the bound for a subgradient. -/
theorem subgradient_euler (_h : Adm K) {x ξ : EuclideanSpace ℝ (Fin d)}
    (h' : IsSubgradient (gauge K) x ξ) :
    inner ℝ ξ x = gauge K x ∧ ∀ y, inner ℝ ξ y ≤ gauge K y :=
  (isSubgradient_gauge_iff K).mp h'

/-- The gradient has norm at most `Λ_ψ`. -/
theorem norm_gradient_le (h : Adm K) (v : EuclideanSpace ℝ (Fin d)) :
    ‖gradient (gauge K) v‖ ≤ normMax (gauge K) :=
  norm_gradient_gauge_le h.compact h.convex h.zero_mem v

end Adm

section Shared

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

open LatticeProb CERW.Support.Occupation CERW.Support.Contact

/-- A point outside the cell set of a path that starts at the origin has Euclidean norm at least
`1/2`. -/
private theorem half_le_norm_of_not_mem_cellSet {X : ℕ → Site d} {n : ℕ} (hn : 1 ≤ n)
    (hX0 : X 0 = 0) {y : EuclideanSpace ℝ (Fin d)} (hy : y ∉ cellSet X n) :
    (1 / 2 : ℝ) ≤ ‖y‖ := by
  by_contra h
  rw [not_le] at h
  have h0 : (0 : Site d) ∈ departureRange X n := by
    rw [mem_departureRange_iff, localTime, Finset.card_pos]
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hX0⟩⟩
  have hy_cell : y ∈ cell (0 : Site d) := by
    intro i
    have hi : |y i| < 1 / 2 := by
      have hle : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
      rw [Real.norm_eq_abs] at hle
      linarith
    constructor <;> simp only [Pi.zero_apply, Int.cast_zero] <;>
      linarith [(abs_lt.mp hi).1, (abs_lt.mp hi).2]
  exact hy (by rw [cellSet]; exact Set.mem_iUnion₂.mpr ⟨0, h0, hy_cell⟩)

/-- A path with `|X_j| ≤ j` has `H_n ≤ n`. -/
theorem maxRadius_le_nat (X : ℕ → Site d) (n : ℕ) (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    maxRadius X n ≤ n := by
  unfold maxRadius
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact (hXn j).trans (by exact_mod_cast hjn)

/-- The contact setup for a norm: the inradius `b` is positive and at most `Λ_ψ (n + √d)`, the
sublevel set `{ψ < b}` lies in `D_n`, every contact point lies within `n + √d` of the origin, and
the closure of the cell of some unvisited site `z` contains it. The radius `H_n = maxRadius X n`
replaces `n` in the bounds. -/
theorem contact_setup (hd : 2 ≤ d) (hΨ : Adm K)
    (X : ℕ → Site d) (n : ℕ) (hn : 1 ≤ n) (hX0 : X 0 = 0)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : (gauge K) y₀ = normInnerRadius (gauge K) X n)
    (hcl : y₀ ∈ closure (cellSet X n)ᶜ) :
    0 < normInnerRadius (gauge K) X n ∧ {v | (gauge K) v < normInnerRadius (gauge K) X n} ⊆
        cellSet X n ∧
      normInnerRadius (gauge K) X n ≤ normMax (gauge K) * (maxRadius X n + Real.sqrt d) ∧
      ‖y₀‖ ≤ maxRadius X n + Real.sqrt d ∧
      ∃ z : Site d, localTime X n z = 0 ∧ ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 ∧
        euclidNorm z ≤ maxRadius X n + 2 * Real.sqrt d := by
  have hd1 : 1 ≤ d := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set D := cellSet X n with hD
  set b := normInnerRadius (gauge K) X n with hb
  have hDball : D ⊆ Metric.ball 0 (maxRadius X n + Real.sqrt d) := cellSet_subset_ball hd1 X n
  have hRpos : 0 < maxRadius X n + Real.sqrt d := by
    have h1 : 0 ≤ maxRadius X n :=
      (euclidNorm_nonneg (X 0)).trans (euclidNorm_le_maxRadius X (Nat.zero_le n))
    have : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    linarith
  obtain ⟨y₁, hy₁⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin d)))
    (r := maxRadius X n + Real.sqrt d)).mpr hRpos.le
  have hy₁norm : ‖y₁‖ = maxRadius X n + Real.sqrt d := by simpa using (mem_sphere_iff_norm.mp hy₁)
  have hy₁c : y₁ ∉ D := by
    intro hyD
    have hmem := hDball hyD
    rw [Metric.mem_ball, dist_zero_right] at hmem
    linarith
  have hne : ((gauge K) '' Dᶜ).Nonempty := ⟨(gauge K) y₁, ⟨y₁, hy₁c, rfl⟩⟩
  have hnonneg : ∀ y, 0 ≤ (gauge K) y := hΨ.nonneg
  have hbdd : BddBelow ((gauge K) '' Dᶜ) := ⟨0, by rintro _ ⟨y, -, rfl⟩; exact hnonneg y⟩
  obtain ⟨hcpos, hcle⟩ := hΨ.normMin_pos_mul_le hd1
  have hb_ge : normMin (gauge K) / 2 ≤ b := by
    refine le_csInf hne ?_
    rintro _ ⟨y, hyc, rfl⟩
    have h1 := half_le_norm_of_not_mem_cellSet hn hX0 hyc
    have h2 := hcle y
    nlinarith
  have hbpos : 0 < b := lt_of_lt_of_le (by linarith) hb_ge
  have hball : {v | (gauge K) v < b} ⊆ D := by
    intro v hv
    by_contra hvD
    exact absurd (csInf_le hbdd ⟨v, hvD, rfl⟩) (not_le.mpr hv)
  have hb_le : b ≤ normMax (gauge K) * (maxRadius X n + Real.sqrt d) := by
    calc b ≤ (gauge K) y₁ := csInf_le hbdd ⟨y₁, hy₁c, rfl⟩
      _ ≤ normMax (gauge K) * ‖y₁‖ := hΨ.le_normMax_mul y₁
      _ = normMax (gauge K) * (maxRadius X n + Real.sqrt d) := by rw [hy₁norm]
  have hy₀norm : ‖y₀‖ ≤ maxRadius X n + Real.sqrt d := by
    by_contra hcon
    rw [not_le] at hcon
    set R : ℝ := maxRadius X n + Real.sqrt d with hR
    have hy₀pos : 0 < ‖y₀‖ := lt_trans hRpos hcon
    set t : ℝ := (R + ‖y₀‖) / (2 * ‖y₀‖) with ht
    have ht1 : t < 1 := by
      rw [ht, div_lt_one (by positivity)]
      linarith
    have ht0 : 0 < t := by
      rw [ht]
      positivity
    have hΨt : (gauge K) (t • y₀) < b := by
      rw [hΨ.smul_nonneg ht0.le, hy₀]
      nlinarith
    have hmem : t • y₀ ∈ D := hball hΨt
    have hlt := hDball hmem
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hlt
    have : t * ‖y₀‖ = (R + ‖y₀‖) / 2 := by
      rw [ht]
      field_simp
    linarith
  obtain ⟨z, hzA, hzcl⟩ := exists_unvisited_mem_closure_cell X n hcl
  have hzy := norm_sub_toSpace_le_of_mem_closure_cell hzcl
  refine ⟨hbpos, hball, hb_le, hy₀norm, z, ?_, ?_, ?_⟩
  · rwa [mem_departureRange_iff, not_lt, Nat.le_zero] at hzA
  · rw [norm_sub_rev]
    exact hzy
  · rw [← norm_toSpace]
    calc ‖toSpace z‖ ≤ ‖y₀‖ + ‖toSpace z - y₀‖ := norm_le_norm_add_norm_sub' (toSpace z) y₀
      _ ≤ (maxRadius X n + Real.sqrt d) + Real.sqrt d / 2 := by
          rw [norm_sub_rev] at hzy
          linarith
      _ ≤ maxRadius X n + 2 * Real.sqrt d := by linarith [Real.sqrt_nonneg (d : ℝ)]

end Shared

/-!
## The convolution bound for the potential of the gauge

Newton's theorem for a radial weight and the convolution of the potential of a set containing a
sublevel ball of the gauge against a radial weight, at a contact point.
-/

namespace Convolution

open CERW.Generic.Kernel CERW.Generic.Newton CERW.Support.Geometry

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}



/-- A measurable field weighted by the Newtonian kernel has a measurable integrand. -/
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


/-- A linear isometry of `ℝ^d` acts on the Euclidean unit sphere. -/
private noncomputable def sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
  ⟨A θ, by simp⟩

/-- The action of a linear isometry on the unit sphere is measurable. -/
private lemma measurable_sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measurable (sphereMap A) :=
  ((A.continuous.comp continuous_subtype_val).subtype_mk _).measurable

/-- Surface measure on the unit sphere is invariant under linear isometries. -/
private lemma map_sphereMap_toSphere
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Measure.map (sphereMap A) (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  ext S hS
  rw [Measure.map_apply (measurable_sphereMap A) hS,
    Measure.toSphere_apply' _ ((measurable_sphereMap A) hS), Measure.toSphere_apply' _ hS]
  congr 1
  have hset : Set.Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap A ⁻¹' S) : Set (EuclideanSpace ℝ (Fin d))) =
      A ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' S)) := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨sphereMap A θ, hθ, rfl⟩, ?_⟩
      simp [sphereMap]
    · rintro ⟨t, ht, _, ⟨θ, hθ, rfl⟩, h⟩
      refine ⟨t, ht, _, ⟨⟨A.symm θ, by simp⟩, ?_, rfl⟩, ?_⟩
      · simpa [sphereMap] using hθ
      · have h' : t • (θ : EuclideanSpace ℝ (Fin d)) = A x := h
        show t • A.symm (θ : EuclideanSpace ℝ (Fin d)) = x
        rw [← A.symm.map_smul, h', A.symm_apply_apply]
  rw [hset]
  exact (LinearIsometryEquiv.measurePreserving A).measure_preimage_equiv
    (f := A.toMeasurableEquiv) _

/-- Integrals over the unit sphere are invariant under linear isometries. -/
private lemma integral_sphereMap (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {f : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ} (hf : Measurable f) :
    ∫ θ, f (sphereMap A θ) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ θ, f θ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  have h := integral_map (measurable_sphereMap A).aemeasurable
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) (f := f)
    (by rw [map_sphereMap_toSphere]; exact hf.aestronglyMeasurable)
  rw [map_sphereMap_toSphere] at h
  exact h.symm

/-- The Newtonian field commutes with linear isometries. -/
private lemma newtonField_map (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : newtonField (A x) = A (newtonField x) := by
  simp only [newtonField, A.norm_map, LinearIsometryEquiv.map_smul]

/-- The sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is measurable. -/
private lemma measurable_inner_newtonField (ξ v : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    Measurable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))) :=
  measurable_const.inner (measurable_newtonField.comp
    (measurable_const.sub (measurable_subtype_coe.const_smul s)))

/-- The component of the spherical average of the Newtonian field orthogonal to `v` vanishes:
a reflection fixing `v` and reversing `w ⟂ v` preserves surface measure. -/
private lemma integral_sphere_inner_newtonField_perp {v w : EuclideanSpace ℝ (Fin d)}
    (hvw : inner ℝ w v = 0) (s : ℝ) :
    ∫ θ, inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere = 0 := by
  set R := Submodule.reflection (ℝ ∙ w)ᗮ with hR
  have hRv : R v = v :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hvw)
  have hRw : R w = -w := Submodule.reflection_orthogonalComplement_singleton_eq_neg w
  have h := integral_sphereMap R (measurable_inner_newtonField w v s)
  have hpt : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ w (newtonField (v - s • (sphereMap R θ : EuclideanSpace ℝ (Fin d)))) =
        -inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    intro θ
    have h1 : v - s • (sphereMap R θ : EuclideanSpace ℝ (Fin d)) =
        R (v - s • (θ : EuclideanSpace ℝ (Fin d))) := by
      rw [R.map_sub, R.map_smul, hRv]
      rfl
    rw [h1, newtonField_map, ← R.inner_map_map w, hRw, hR, Submodule.reflection_reflection,
      inner_neg_left]
  simp_rw [hpt, integral_neg] at h
  linarith

/-- The Newtonian field is continuous away from the origin. -/
private lemma continuousAt_newtonField_of_ne {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    ContinuousAt (newtonField : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) x :=
  ((continuous_norm.pow d).continuousAt.inv₀
    (pow_ne_zero d (norm_ne_zero_iff.mpr hx))).smul continuousAt_id

/-- For `|v| ≠ s` the sphere integrand `θ ↦ ⟨ξ, K(v - sθ)⟩` is integrable, being continuous on a
compact space. -/
private lemma integrable_inner_newtonField (ξ : EuclideanSpace ℝ (Fin d))
    {v : EuclideanSpace ℝ (Fin d)} {s : ℝ} (hs : 0 < s) (hvs : ‖v‖ ≠ s) :
    Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))))
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  haveI : CompactSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hcont : Continuous (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      simp
    have hne : v - s • (θ : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro h
      have hv : v = s • (θ : EuclideanSpace ℝ (Fin d)) := sub_eq_zero.mp h
      apply hvs
      rw [hv, norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hs, mul_one]
    have hc : ContinuousAt (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        v - s • (θ : EuclideanSpace ℝ (Fin d))) θ :=
      continuousAt_const.sub (continuousAt_subtype_val.const_smul s)
    exact ContinuousAt.comp_of_eq (g := newtonField)
      (f := fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
        v - s • (θ : EuclideanSpace ℝ (Fin d))) (continuousAt_newtonField_of_ne hne) hc rfl
  exact Continuous.integrable_of_hasCompactSupport (continuous_const.inner hcont)
    (HasCompactSupport.of_compactSpace _)

/-- The kernel average `eq:kernel-average` against an arbitrary vector `ξ`: for `v ≠ 0`, `s > 0` and
`|v| ≠ s`, `∫_S ξ · K(v - sθ) dσ(θ) = σ_d |v|^{-d} (ξ · v) 1{s < |v|}`. -/
private lemma integral_sphere_inner_newtonField_vec (hd : 2 ≤ d)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) {s : ℝ} (hs : 0 < s) (hvs : ‖v‖ ≠ s)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ θ, inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      if s < ‖v‖ then d * unitBallVolume d * (inner ℝ ξ v / ‖v‖ ^ d) else 0 := by
  have hrpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvv : inner ℝ v v = ‖v‖ * ‖v‖ := real_inner_self_eq_norm_mul_norm v
  set a : ℝ := inner ℝ ξ (unitDir v) with ha_def
  have ha : a = ‖v‖⁻¹ * inner ℝ ξ v := by
    rw [ha_def, unitDir, real_inner_smul_right]
  set w : EuclideanSpace ℝ (Fin d) := ξ - a • unitDir v with hw_def
  have hperp : inner ℝ w v = 0 := by
    rw [hw_def, inner_sub_left, real_inner_smul_left, unitDir, real_inner_smul_left, hvv, ha]
    field_simp
    ring
  have hdecomp : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ ξ (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) =
        a * inner ℝ (unitDir v) (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) +
          inner ℝ w (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) := by
    intro θ
    rw [hw_def, inner_sub_left, real_inner_smul_left]
    ring
  simp_rw [hdecomp]
  rw [integral_add ((integrable_inner_newtonField (unitDir v) hs hvs).const_mul a)
    (integrable_inner_newtonField w hs hvs), integral_const_mul,
    integral_sphere_inner_newtonField hd hv hs hvs, integral_sphere_inner_newtonField_perp hperp,
    add_zero]
  split_ifs
  · rw [ha, ← div_pow_eq_rpow_sub hrpos d]
    field_simp
  · simp


/-- The weight `χ(|ζ|)` times the kernel `|a - ζ|^{1-d}` is integrable, with integral at most
`M d ω_d + ∫ χ(|ζ|) dζ`: inside the unit ball around `a` the weight is at most `M` and the kernel
has integral `d ω_d`, outside the kernel is at most one. -/
private lemma integrable_weight_mul_kernel (hd : 1 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (a : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤
        M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ := by
  obtain ⟨hint, hval⟩ := integrableOn_ball_and_integral_eq hd a one_pos
  have hind := hint.integrable_indicator (Metric.isOpen_ball.measurableSet)
  have hGi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖) :=
    (hind.const_mul M).add hχi
  have hmeas : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) :=
    (hχm.comp measurable_norm).mul ((measurable_const.sub measurable_id).norm.pow_const _)
  have hle : ∀ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤
      M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖ := by
    intro ζ
    have hk : 0 ≤ ‖a - ζ‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have hsw : ‖a - ζ‖ = ‖ζ - a‖ := norm_sub_rev a ζ
    by_cases hζ : ζ ∈ Metric.ball a 1
    · rw [Set.indicator_of_mem hζ, ← hsw]
      have h1 : χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ M * ‖a - ζ‖ ^ (1 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_right (hM _) hk
      linarith [hχ0 ‖ζ‖]
    · rw [Set.indicator_of_notMem hζ]
      have hge : 1 ≤ ‖a - ζ‖ := by
        rw [hsw]
        simpa [Metric.mem_ball, dist_eq_norm] using hζ
      have hk1 : ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hge (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      have h1 : χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ)) ≤ χ ‖ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left hk1 (hχ0 _)
      linarith
  have hfi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))) := by
    refine hGi.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχ0 _) (Real.rpow_nonneg (norm_nonneg _) _))]
    exact hle ζ
  refine ⟨hfi, ?_⟩
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖a - ζ‖ ^ (1 - (d : ℝ))
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d),
          (M * (Metric.ball a 1).indicator (fun v => ‖v - a‖ ^ (1 - (d : ℝ))) ζ + χ ‖ζ‖) :=
        integral_mono hfi hGi hle
    _ = M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ := by
        rw [integral_add (hind.const_mul M) hχi, integral_const_mul,
          integral_indicator Metric.isOpen_ball.measurableSet, hval, mul_one]


/-- Pointwise bound of the radial weight times the field `⟨ξ, K(w - ζ)⟩` by `|ξ|` times the
weighted kernel `χ(|ζ|) |w - ζ|^{1-d}`. -/
private lemma norm_weight_inner_le (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (w ξ ζ : EuclideanSpace ℝ (Fin d)) :
    ‖χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))‖ ≤ ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχ0 _), Real.norm_eq_abs]
  have h1 : |inner ℝ ξ (newtonField (w - ζ))| ≤ ‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ)) := by
    rw [← norm_newtonField hd]
    exact abs_real_inner_le_norm _ _
  calc χ ‖ζ‖ * |inner ℝ ξ (newtonField (w - ζ))|
      ≤ χ ‖ζ‖ * (‖ξ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := mul_le_mul_of_nonneg_left h1 (hχ0 _)
    _ = ‖ξ‖ * (χ ‖ζ‖ * ‖w - ζ‖ ^ (1 - (d : ℝ))) := by ring

/-- The radial weight times the field `⟨ξ, K(w - ζ)⟩` is integrable. -/
private lemma integrable_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    (w ξ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) := by
  have hk := (integrable_weight_mul_kernel (by omega) hχm hχ0 hM hχi w).1
  have hmeas : Measurable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ))) :=
    (hχm.comp measurable_norm).mul
      (measurable_const.inner (measurable_newtonField.comp (measurable_const.sub measurable_id)))
  exact (hk.const_mul ‖ξ‖).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => norm_weight_inner_le hd hχ0 w ξ ζ)

/-- The mass of a radial weight in a centred ball, in polar coordinates:
`∫_{B(0,s)} χ(|ζ|) dζ = d ω_d ∫_0^s r^{d-1} χ(r) dr`. -/
private lemma integral_ball_weight (hd : 1 ≤ d) (χ : ℝ → ℝ) (s : ℝ) :
    ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ =
      d * unitBallVolume d * ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * (Set.Iio s).indicator χ r := by
  haveI : NeZero d := ⟨by omega⟩
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hind : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s).indicator (fun ζ => χ ‖ζ‖) =
      fun ζ => (Set.Iio s).indicator χ ‖ζ‖ := by
    funext ζ
    by_cases hζ : ‖ζ‖ < s <;> simp [Set.indicator, hζ]
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, hind,
    integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))), hfin]
  simp only [unitBallVolume, Measure.real, nsmul_eq_mul, smul_eq_mul]
  ring


/-- Newton's theorem for a radial weight: for `w ≠ 0` and any vector `ξ`,
`∫ χ(|ζ|) ⟨ξ, K(w - ζ)⟩ dζ = (∫_{B(0,|w|)} χ(|ζ|) dζ) ⟨ξ, w⟩ / |w|^d`. -/
private lemma integral_weight_inner_newtonField (hd : 2 ≤ d) {χ : ℝ → ℝ}
    (hχm : Measurable χ) (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) (ξ : EuclideanSpace ℝ (Fin d)) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * inner ℝ ξ (newtonField (w - ζ)) =
      (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ‖w‖, χ ‖ζ‖) *
        (inner ℝ ξ w / ‖w‖ ^ d) := by
  have hint := integrable_weight_inner_newtonField hd hχm hχ0 hM hχi w ξ
  rw [integral_eq_integral_Ioi_sphere (by omega) hint, integral_ball_weight (by omega)]
  have hae : ∀ᵐ r : ℝ ∂(volume : Measure ℝ), r ≠ ‖w‖ := by
    rw [ae_iff]
    simp
  have hpt : ∀ᵐ r : ℝ ∂(volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)),
      r ^ (d - 1) * ∫ θ, χ ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ *
          inner ℝ ξ (newtonField (w - r • (θ : EuclideanSpace ℝ (Fin d))))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        d * unitBallVolume d * (inner ℝ ξ w / ‖w‖ ^ d) *
          (r ^ (d - 1) * (Set.Iio ‖w‖).indicator χ r) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hae] with r hr hr0
    have hr0' : 0 < r := hr0
    have hθ : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := fun θ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0', mem_sphere_zero_iff_norm.mp θ.2, mul_one]
    simp_rw [hθ]
    rw [integral_const_mul, integral_sphere_inner_newtonField_vec hd hw hr0' hr.symm ξ]
    by_cases hlt : r < ‖w‖
    · simp only [hlt, if_true, Set.indicator_of_mem (Set.mem_Iio.mpr hlt)]
      ring
    · simp only [hlt, if_false, Set.indicator_of_notMem (mt Set.mem_Iio.mp hlt)]
      ring
  rw [integral_congr_ae hpt, integral_const_mul]
  ring


/-- For each position `v`, the radial weight times the field `⟨g(v), K(v - y₀ - ζ)⟩` is integrable
in `ζ`, uniformly in `v`, and jointly integrable in `(v, ζ)` over `F × ℝ^d` for a set `F` of finite
volume. -/
private lemma integrable_weight_fieldPair (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {F : Set (EuclideanSpace ℝ (Fin d))} (hFfin : volume F ≠ ⊤)
    (y₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y₀ - p.2)))
      (((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict F).prod volume) := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hmeas : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      χ ‖p.2‖ * inner ℝ (g p.1) (newtonField (p.1 - y₀ - p.2))) :=
    (hχm.comp measurable_snd.norm).mul ((hg.comp measurable_fst).inner
      (measurable_newtonField.comp ((measurable_fst.sub_const y₀).sub measurable_snd)))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun v =>
    integrable_weight_inner_newtonField hd hχm hχ0 hM hχi (v - y₀) (g v), ?_⟩
  refine Integrable.mono' (integrableOn_const hFfin (C := Λ * (M * (d * unitBallVolume d) +
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖)))
    hmeas.norm.aestronglyMeasurable.integral_prod_right' (Filter.Eventually.of_forall fun v => ?_)
  obtain ⟨hki, hkle⟩ := integrable_weight_mul_kernel (by omega) hχm hχ0 hM hχi (v - y₀)
  have hfi := integrable_weight_inner_newtonField hd hχm hχ0 hM hχi (v - y₀) (g v)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ζ => norm_nonneg _)]
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), ‖χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y₀ - ζ))‖
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), Λ * (χ ‖ζ‖ * ‖v - y₀ - ζ‖ ^ (1 - (d : ℝ))) := by
        refine integral_mono hfi.norm (hki.const_mul Λ) fun ζ => ?_
        exact (norm_weight_inner_le hd hχ0 (v - y₀) (g v) ζ).trans
          (mul_le_mul_of_nonneg_right (hΛ v) (mul_nonneg (hχ0 _) (Real.rpow_nonneg
            (norm_nonneg _) _)))
    _ = Λ * ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * ‖v - y₀ - ζ‖ ^ (1 - (d : ℝ)) :=
        integral_const_mul _ _
    _ ≤ Λ * (M * (d * unitBallVolume d) + ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hkle hΛ0


/-- The mass of a radial weight in a centred ball lies between `0` and the total mass. -/
private lemma ball_weight_bounds {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) (s : ℝ) :
    0 ≤ ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ∧
      ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) s, χ ‖ζ‖ ≤
        ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ :=
  ⟨integral_nonneg fun _ => hχ0 _,
    setIntegral_le_integral hχi (Filter.Eventually.of_forall fun _ => hχ0 _)⟩

/-- Fubini and Newton's theorem for the radial weight: for a field `g` of norm at most `Λ` whose
pairing `⟨g(v), v - y₀⟩` is nonnegative on `F`, the weighted field potential of `F` is integrable
and its integral is at most the total weight times the field potential at `y₀`. -/
private lemma weighted_fieldPotential_le (hd : 2 ≤ d) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F)
    (hFfin : volume F ≠ ⊤) (y₀ : EuclideanSpace ℝ (Fin d))
    (hpos : ∀ v ∈ F, 0 ≤ inner ℝ (g v) (v - y₀)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * ∫ v in F, inner ℝ (g v) (newtonField (v - y₀ - ζ))) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d),
        χ ‖ζ‖ * ∫ v in F, inner ℝ (g v) (newtonField (v - y₀ - ζ)) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
        ∫ v in F, inner ℝ (g v) (newtonField (v - y₀)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hI := integrable_weight_fieldPair hd hχm hχ0 hM hχi hg hΛ hFfin y₀
  have hcm : ∀ ζ : EuclideanSpace ℝ (Fin d),
      χ ‖ζ‖ * ∫ v in F, inner ℝ (g v) (newtonField (v - y₀ - ζ)) =
        ∫ v in F, χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y₀ - ζ)) := fun ζ =>
    (integral_const_mul _ _).symm
  simp_rw [hcm]
  refine ⟨hI.integral_prod_right, ?_⟩
  rw [← integral_integral_swap (f := fun (v ζ : EuclideanSpace ℝ (Fin d)) =>
    χ ‖ζ‖ * inner ℝ (g v) (newtonField (v - y₀ - ζ))) hI]
  have hgi : Integrable (fun v : EuclideanSpace ℝ (Fin d) =>
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * inner ℝ (g v) (newtonField (v - y₀)))
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict F) := by
    refine Integrable.const_mul ?_ _
    simp_rw [inner_newtonField]
    exact integrableOn_fieldIntegrand (by omega) hg hΛ hF hFfin y₀
  rw [← integral_const_mul]
  refine integral_mono_ae hI.integral_prod_left hgi ?_
  have hne : ∀ᵐ v : EuclideanSpace ℝ (Fin d), v ≠ y₀ := by
    rw [ae_iff]
    simp
  rw [Filter.EventuallyLE, ae_restrict_iff' hF]
  filter_upwards [hne] with v hv hvF
  have hw : v - y₀ ≠ 0 := sub_ne_zero.mpr hv
  rw [integral_weight_inner_newtonField hd hχm hχ0 hM hχi hw (g v), inner_newtonField]
  have hq : 0 ≤ inner ℝ (g v) (v - y₀) / ‖v - y₀‖ ^ d :=
    div_nonneg (hpos v hvF) (pow_nonneg (norm_nonneg _) _)
  exact mul_le_mul_of_nonneg_right (ball_weight_bounds hχ0 hχi _).2 hq


/-- The field potential of `F` weighted by the radial weight, in the normalisation of
`normPotential`: if `⟨∇ψ(v), v - y₀⟩ ≥ 0` on `F`, it is integrable with integral at most the total
weight times the potential of `F` at `y₀`. -/
private lemma weighted_normPotential_le (hd : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε) {χ : ℝ → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ s, 0 ≤ χ s) {M : ℝ} (hM : ∀ s, χ s ≤ M)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : MeasurableSet F) (hFfin : volume F ≠ ⊤)
    (y₀ : EuclideanSpace ℝ (Fin d))
    (hpos : ∀ v ∈ F, 0 ≤ inner ℝ (gradient (gauge K) v) (v - y₀)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * normPotential d ε (gauge K) F (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε (gauge K) F (y₀ - ζ) ≤
      (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * normPotential d ε (gauge K) F y₀ := by
  obtain ⟨hint, hle⟩ := weighted_fieldPotential_le hd hχm hχ0 hM hχi (measurable_gradient (gauge K))
    (hΨ.norm_gradient_le) hF hFfin y₀ hpos
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  set h : EuclideanSpace ℝ (Fin d) → ℝ := fun t =>
    χ ‖t‖ * ∫ v in F, inner ℝ (gradient (gauge K) v) (newtonField (v - y₀ - t)) with hh
  have hfun : (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * normPotential d ε (gauge K) F (y₀ - ζ)) =
      fun ζ => (2 * ε / unitBallVolume d) * h (-ζ) := by
    funext ζ
    have hv : ∀ v : EuclideanSpace ℝ (Fin d), v - y₀ - -ζ = v - (y₀ - ζ) := fun v => by abel
    simp only [hh, normPotential, norm_neg, hv, inner_newtonField]
    ring
  rw [hfun]
  refine ⟨(hint.comp_neg).const_mul _, ?_⟩
  rw [integral_const_mul, integral_neg_eq_self h volume]
  calc (2 * ε / unitBallVolume d) * ∫ t : EuclideanSpace ℝ (Fin d), h t
      ≤ (2 * ε / unitBallVolume d) * ((∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) *
          ∫ v in F, inner ℝ (gradient (gauge K) v) (newtonField (v - y₀))) :=
        mul_le_mul_of_nonneg_left hle hc
    _ = (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * normPotential d ε (gauge K) F y₀ := by
        simp only [normPotential, inner_newtonField]
        ring


/-- If `ψ(y₀) ≤ ψ(v)`, then `⟨∇ψ(v), v - y₀⟩ ≥ 0`: Euler's relation `⟨∇ψ(v), v⟩ = ψ(v)` and the
subgradient bound `⟨∇ψ(v), y₀⟩ ≤ ψ(y₀)` where `ψ` is differentiable, and `∇ψ(v) = 0` elsewhere. -/
private lemma inner_gradient_sub_nonneg {K : Set (EuclideanSpace ℝ (Fin d))} (hΨ : Adm K)
    {v y₀ : EuclideanSpace ℝ (Fin d)} (h : (gauge K) y₀ ≤ (gauge K) v) :
    0 ≤ inner ℝ (gradient (gauge K) v) (v - y₀) := by
  by_cases hv : DifferentiableAt ℝ (gauge K) v
  · have h1 := hΨ.subgradient_euler (hΨ.gradient_isSubgradient hv)
    rw [inner_sub_right, h1.1]
    have := h1.2 y₀
    linarith
  · have h0 : gradient (gauge K) v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, inner_zero_left]

/-- The radial weight times the potential of a bounded measurable set is integrable, by the
boundedness and the continuity of the potential. -/
private lemma integrable_weight_normPotential (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    {χ : ℝ → ℝ}
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖))
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (y₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ *
        normPotential d ε (gauge K) D (y₀ - ζ)) := by
  obtain ⟨C, -, hC⟩ := gauge_potential_geometry hd hΨ.compact hΨ.convex hΨ.zero_mem
  obtain ⟨hbound, -⟩ := hC ε hε.le D hD hDb
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin d) => normPotential d ε (gauge K) D y) :=
    continuous_normPotential_gauge hd hΨ.compact hΨ.convex hΨ.zero_mem hε.le hD hDb
  have hcont' : Continuous
      (fun ζ : EuclideanSpace ℝ (Fin d) => normPotential d ε (gauge K) D (y₀ - ζ)) :=
    hcont.comp (continuous_const.sub continuous_id)
  exact hχi.mul_bdd hcont'.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => by
    rw [Real.norm_eq_abs]
    exact hbound (y₀ - ζ))

/-- The sublevel-ball part: if the potential of `B` is `2dε (b - ψ(y))_+`, then, at a point `y₀`
with `ψ(y₀) = b`, the radial weight times the potential of `B` around `y₀` is integrable and its
integral is at most `2dε ∫ χ(|ζ|) min(b, ψ(ζ)) dζ`. -/
private lemma weighted_ballPotential_le {K : Set (EuclideanSpace ℝ (Fin d))} (hΨ : Adm K)
    {ε : ℝ} (hε : 0 < ε) {χ : ℝ → ℝ} (hχ0 : ∀ s, 0 ≤ χ s)
    (hχi : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖)) {b : ℝ}
    {B : Set (EuclideanSpace ℝ (Fin d))}
    (hU : ∀ y, normPotential d ε (gauge K) B y = 2 * d * ε * max (b - (gauge K) y) 0)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : (gauge K) y₀ = b) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ *
        normPotential d ε (gauge K) B (y₀ - ζ)) ∧
    ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε (gauge K) B (y₀ - ζ) ≤
      2 * d * ε * ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * min b ((gauge K) ζ) := by
  have hnn : ∀ x, 0 ≤ (gauge K) x := hΨ.nonneg
  have hΨc := hΨ.continuous
  have hb : 0 ≤ b := by rw [← hy₀]; exact hnn y₀
  have hc : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hmaxle : ∀ ζ : EuclideanSpace ℝ (Fin d), max (b - (gauge K) (y₀ - ζ)) 0 ≤ b := fun ζ =>
    max_le (by linarith [hnn (y₀ - ζ)]) hb
  have hmaxc : Continuous (fun ζ : EuclideanSpace ℝ (Fin d) => max (b - (gauge K) (y₀ - ζ)) 0) :=
    (continuous_const.sub (hΨc.comp (continuous_const.sub continuous_id))).max continuous_const
  have hint : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      χ ‖ζ‖ * normPotential d ε (gauge K) B (y₀ - ζ)) := by
    simp_rw [hU]
    refine hχi.mul_bdd (c := 2 * d * ε * b) (hmaxc.const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (le_max_right _ _))]
    exact mul_le_mul_of_nonneg_left (hmaxle ζ) hc
  have hminc : Continuous (fun ζ : EuclideanSpace ℝ (Fin d) => min b ((gauge K) ζ)) :=
    continuous_const.min hΨc
  have hmini : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖ * min b ((gauge K) ζ)) :=
    hχi.mul_bdd (c := b) hminc.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hb (hnn ζ))]
      exact min_le_left _ _)
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  refine integral_mono hint (hmini.const_mul _) fun ζ => ?_
  have h1 : max (b - (gauge K) (y₀ - ζ)) 0 ≤ min b ((gauge K) ζ) := by
    refine max_le (le_min (by linarith [hnn (y₀ - ζ)]) ?_) (le_min hb (hnn ζ))
    have h := hΨ.add_le (y₀ - ζ) ζ
    rw [sub_add_cancel, hy₀] at h
    linarith
  rw [hU, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (hχ0 _)) hc

/-- The potential of a set splits over a measurable subset `B`: `U_D = U_B + U_{D \ B}`. -/
private lemma normPotential_union_diff {K : Set (EuclideanSpace ℝ (Fin d))} (hΨ : Adm K)
    (hd : 1 ≤ d) (ε : ℝ) {D B : Set (EuclideanSpace ℝ (Fin d))} (hBD : B ⊆ D)
    (hBm : MeasurableSet B) (hDm : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε (gauge K) D y = normPotential d ε (gauge K) B y +
        normPotential d ε (gauge K) (D \ B) y := by
  have hg := measurable_gradient (gauge K)
  have hΛ := hΨ.norm_gradient_le
  have hBfin : volume B ≠ ⊤ := (measure_mono hBD).trans_lt hDfin.lt_top |>.ne
  have hDBfin : volume (D \ B) ≠ ⊤ := (measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top |>.ne
  unfold normPotential
  rw [← mul_add, ← setIntegral_union Set.disjoint_sdiff_right (hDm.diff hBm)
    (integrableOn_fieldIntegrand hd hg hΛ hBm hBfin y)
    (integrableOn_fieldIntegrand hd hg hΛ (hDm.diff hBm) hDBfin y), Set.union_sdiff_cancel hBD]


end Convolution

/-- The convolution bound for the potential of a set containing a sublevel ball of the gauge: the
convolution of the potential of a set containing `{ψ < b}`, against a radial weight, at a point
`y₀` with `ψ(y₀) = b`. -/
def GaugeConvBound (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) : Prop :=
  ∀ χ : ℝ → ℝ, Measurable χ → (∀ s, 0 ≤ χ s) → (∃ M : ℝ, ∀ s, χ s ≤ M) →
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => χ ‖ζ‖) →
    ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
    ∀ b : ℝ, 0 < b → {v | gauge K v < b} ⊆ D → ∀ y₀ : EuclideanSpace ℝ (Fin d), gauge K y₀ = b →
      Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
        χ ‖ζ‖ * normPotential d ε (gauge K) D (y₀ - ζ)) ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε (gauge K) D (y₀ - ζ) ≤
        2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * min b (gauge K ζ)) +
          (∫ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖) * normPotential d ε (gauge K) D y₀

/-- **The convolution bound** for the gauge of a compact convex body: `GaugeConvBound d K ε`, for
every `ε > 0` and `d ≥ 2`. The potential of the ball `{ψ < b}` is `2dε (b - ψ)₊`, which is at most
`2dε min {b, ψ(ζ)}` at `y₀ - ζ` because `ψ(y₀) = b ≤ ψ(y₀ - ζ) + ψ(ζ)`; the rest of the set has a
nonnegative pairing `∇ψ(v) · (v - y₀)` by the subgradient inequality, and Newton's theorem for a
radial weight bounds its weighted potential by the total weight times its potential at `y₀`. -/
theorem gauge_convBound {d : ℕ} (hd : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ε : ℝ} (hε : 0 < ε) : GaugeConvBound d K ε := by
  have hΨ : Adm K := ⟨hK, hc, h0⟩
  intro χ hχm hχ0 hMex hχi D hD hDb b hb hBD y₀ hy₀
  obtain ⟨M, hM⟩ := hMex
  have hBm : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | gauge K v < b} :=
    measurableSet_lt hΨ.continuous.measurable measurable_const
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hFfin : volume (D \ {v : EuclideanSpace ℝ (Fin d) | gauge K v < b}) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top).ne
  have hsplit := Convolution.normPotential_union_diff hΨ (by omega) ε hBD hBm hD hDfin
  have hU : ∀ y, normPotential d ε (gauge K) {v : EuclideanSpace ℝ (Fin d) | gauge K v < b} y =
      2 * d * ε * max (b - gauge K y) 0 := fun y =>
    gauge_ball_potential hd hK hc h0 ε hb y
  have hU0 : normPotential d ε (gauge K) {v : EuclideanSpace ℝ (Fin d) | gauge K v < b} y₀ = 0 := by
    rw [hU, hy₀]
    simp
  obtain ⟨hBi, hBle⟩ := Convolution.weighted_ballPotential_le hΨ hε hχ0 hχi hU hy₀
  obtain ⟨hFi, hFle⟩ := Convolution.weighted_normPotential_le hd hΨ hε hχm hχ0 hM hχi (hD.diff hBm)
    hFfin y₀ (fun v hv => Convolution.inner_gradient_sub_nonneg hΨ (by
      have : ¬ gauge K v < b := hv.2
      rw [hy₀]
      exact not_lt.mp this))
  refine ⟨Convolution.integrable_weight_normPotential hd hΨ hε hχi hD hDb y₀, ?_⟩
  have hfun : ∀ ζ : EuclideanSpace ℝ (Fin d), χ ‖ζ‖ * normPotential d ε (gauge K) D (y₀ - ζ) =
      χ ‖ζ‖ * normPotential d ε (gauge K) {v : EuclideanSpace ℝ (Fin d) | gauge K v < b}
          (y₀ - ζ) +
        χ ‖ζ‖ * normPotential d ε (gauge K)
          (D \ {v : EuclideanSpace ℝ (Fin d) | gauge K v < b}) (y₀ - ζ) :=
    fun ζ => by rw [hsplit, mul_add]
  simp_rw [hfun]
  rw [integral_add hBi hFi, hsplit y₀, hU0, zero_add]
  linarith

/-!
## The deterministic contact argument in the plane

For `d = 2` the potential of the cell set at a contact point of the inradius of the gauge is at most
`C √(r log (n + 2))`, from the pointwise local-time bound, the modulus of the potential on cells and
the convolution bound of the gauge.
-/

namespace Planar

open CERW.Support.Occupation

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}



/-- The truncated radial weight `s ↦ (1 + |s|)^{-d}` for `s < R`, and `0` for `s ≥ R`. -/
private noncomputable def radialWeight (d : ℕ) (R s : ℝ) : ℝ :=
  Set.indicator (Set.Iio R) (fun t : ℝ => (1 + |t|) ^ (-(d : ℝ))) s

/-- The truncated radial weight is measurable. -/
private theorem radialWeight_measurable (d : ℕ) (R : ℝ) : Measurable (radialWeight d R) := by
  unfold radialWeight
  exact (by fun_prop : Measurable fun t : ℝ => (1 + |t|) ^ (-(d : ℝ))).indicator
    measurableSet_Iio

/-- The truncated radial weight is nonnegative. -/
private theorem radialWeight_nonneg (d : ℕ) (R s : ℝ) : 0 ≤ radialWeight d R s := by
  unfold radialWeight
  exact Set.indicator_nonneg (fun t _ => Real.rpow_nonneg (by positivity) _) s

/-- The truncated radial weight is at most `1`. -/
private theorem radialWeight_le_one (d : ℕ) (R s : ℝ) : radialWeight d R s ≤ 1 := by
  unfold radialWeight
  by_cases h : s < R
  · rw [Set.indicator_of_mem (show s ∈ Set.Iio R from h)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg s])
      (by simp)
  · rw [Set.indicator_of_notMem (show s ∉ Set.Iio R from h)]
    exact zero_le_one

/-- Below the truncation radius the weight is `(1 + |s|)^{-d}`. -/
private theorem radialWeight_of_lt (d : ℕ) {R s : ℝ} (h : s < R) :
    radialWeight d R s = (1 + |s|) ^ (-(d : ℝ)) :=
  Set.indicator_of_mem (show s ∈ Set.Iio R from h) _

/-- Beyond the truncation radius the weight vanishes. -/
private theorem radialWeight_of_le (d : ℕ) {R s : ℝ} (h : R ≤ s) : radialWeight d R s = 0 :=
  Set.indicator_of_notMem (show s ∉ Set.Iio R from not_lt.mpr h) _

/-- The weight of the norm is the indicator of the ball of `(1 + ‖ζ‖)^{-d}`. -/
private theorem radialWeight_norm_eq_indicator (d : ℕ) (R : ℝ) :
    (fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖ζ‖) =
      Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)
        (fun ζ => (1 + ‖ζ‖) ^ (-(d : ℝ))) := by
  ext ζ
  by_cases h : ‖ζ‖ < R
  · rw [radialWeight_of_lt d h, abs_of_nonneg (norm_nonneg ζ),
      Set.indicator_of_mem (show ζ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from
        mem_ball_zero_iff.mpr h)]
  · rw [radialWeight_of_le d (not_lt.mp h),
      Set.indicator_of_notMem (show ζ ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from
        fun hζ => h (mem_ball_zero_iff.mp hζ))]

/-- The truncated weight of the norm is integrable, with integral at most `σ_d log (1 + R)`. -/
private theorem integrable_radialWeight_norm (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖ζ‖) ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ ≤
        d * unitBallVolume d * Real.log (1 + R) := by
  obtain ⟨hint, hval⟩ := CERW.Generic.Kernel.integrableOn_ball_one_add_norm_rpow_and_integral_le
    hd hR
  rw [radialWeight_norm_eq_indicator]
  exact ⟨(integrable_indicator_iff measurableSet_ball).mpr hint,
    by rw [integral_indicator measurableSet_ball]; exact hval⟩

/-- For `t ≥ 0`: `t (1 + t)^{-2} ≤ t^{-1}`. -/
private theorem rpow_mul_le_rpow_neg_one (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ (-(2 : ℝ)) * t ≤ t ^ (-(1 : ℝ)) := by
  rcases ht.eq_or_lt with rfl | hpos
  · simp
  · rw [Real.rpow_neg (by positivity), Real.rpow_neg hpos.le, Real.rpow_one, Real.rpow_two]
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity), ← div_eq_inv_mul, le_div_iff₀ hpos]
    nlinarith

/-- The ball integral in the convolution estimate: for `d = 2`, the weighted `min (b, ψ)` is
dominated by `Λ_ψ |ζ|^{-1}` on the ball, which integrates to `Λ_ψ σ_2 R`. -/
private theorem integral_weight_mul_min_le (hd : d = 2) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hΨ : Adm K) {R b : ℝ} (hR : 0 < R) (hb : 0 ≤ b) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ * min b ((gauge K) ζ) ≤
      normMax (gauge K) * (d * unitBallVolume d * R) := by
  have hd2 : (d : ℝ) = 2 := by rw [hd]; norm_num
  have hd1 : 1 ≤ d := by omega
  have hΛ := hΨ.normMax_nonneg
  obtain ⟨hint, hval⟩ := CERW.Generic.Kernel.integrableOn_ball_rpow_neg_and_integral_eq
    (d := d) (s := 1) (ρ := R) hd1 (by rw [hd2]; norm_num) hR
  have hgint : Integrable (Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)
      (fun ζ => normMax (gauge K) * ‖ζ‖ ^ (-(1 : ℝ)))) :=
    (integrable_indicator_iff measurableSet_ball).mpr (hint.const_mul _)
  have hnn : ∀ y, 0 ≤ (gauge K) y := hΨ.nonneg
  calc ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ * min b ((gauge K) ζ)
      ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), Set.indicator (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)
          (fun ζ => normMax (gauge K) * ‖ζ‖ ^ (-(1 : ℝ))) ζ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ζ => ?_) hgint
          (Filter.Eventually.of_forall fun ζ => ?_)
        · exact mul_nonneg (radialWeight_nonneg d R _) (le_min hb (hnn ζ))
        · beta_reduce
          by_cases h : ‖ζ‖ < R
          · rw [radialWeight_of_lt d h, abs_of_nonneg (norm_nonneg ζ),
              Set.indicator_of_mem (show ζ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from
                mem_ball_zero_iff.mpr h), hd2]
            calc (1 + ‖ζ‖) ^ (-(2 : ℝ)) * min b ((gauge K) ζ)
                ≤ (1 + ‖ζ‖) ^ (-(2 : ℝ)) * (normMax (gauge K) * ‖ζ‖) :=
                  mul_le_mul_of_nonneg_left
                    ((min_le_right _ _).trans (hΨ.le_normMax_mul ζ))
                    (Real.rpow_nonneg (by positivity) _)
              _ = normMax (gauge K) * ((1 + ‖ζ‖) ^ (-(2 : ℝ)) * ‖ζ‖) := by ring
              _ ≤ normMax (gauge K) * ‖ζ‖ ^ (-(1 : ℝ)) :=
                  mul_le_mul_of_nonneg_left (rpow_mul_le_rpow_neg_one _ (norm_nonneg ζ)) hΛ
          · rw [radialWeight_of_le d (not_lt.mp h), zero_mul,
              Set.indicator_of_notMem (show ζ ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R from
                fun hζ => h (mem_ball_zero_iff.mp hζ))]
      _ = normMax (gauge K) * ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R,
          ‖ζ‖ ^ (-(1 : ℝ)) := by
        rw [integral_indicator measurableSet_ball, integral_const_mul]
      _ = normMax (gauge K) * (d * unitBallVolume d * R) := by
        rw [hval, hd2]
        norm_num

/-- The sites of the departure range of a path with `|X_j| ≤ j` lie within `n` of the origin. -/
private theorem euclidNorm_le_of_mem_departureRange {X : ℕ → Site d} {n : ℕ}
    (hXn : ∀ j, euclidNorm (X j) ≤ j) {x : Site d} (hx : x ∈ departureRange X n) :
    euclidNorm x ≤ n := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  exact (hXn j).trans (by exact_mod_cast (Finset.mem_range.mp hj).le)

/-- The kernel `(1 + |x - z|)^{-d}` summed over the departure range, at a site `z` with
`|z| ≤ 3n`, is at most `C' log (n + 2)`. -/
private theorem kernel_sum_le (hd : d = 2) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (X : ℕ → Site d) (n : ℕ) (z : Site d), 1 ≤ n →
      (∀ j, euclidNorm (X j) ≤ j) → euclidNorm z ≤ 3 * n →
      ∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
        C' * Real.log ((n : ℝ) + 2) := by
  obtain ⟨C, hC, hCs⟩ := CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) (by omega)
  refine ⟨3 * C, by positivity, fun X n z hn hXn hz => ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4 : ∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
      C * Real.log (4 * (n : ℝ) + 2) := by
    refine hCs (departureRange X n) z (4 * n) (by linarith) fun x hx => ?_
    calc euclidNorm (x - z) ≤ euclidNorm x + euclidNorm z := euclidNorm_sub_le x z
      _ ≤ n + 3 * n := add_le_add (euclidNorm_le_of_mem_departureRange hXn hx) hz
      _ = 4 * n := by ring
  have hlog : Real.log (4 * (n : ℝ) + 2) ≤ 3 * Real.log ((n : ℝ) + 2) := by
    have h3 : 3 * Real.log ((n : ℝ) + 2) = Real.log (((n : ℝ) + 2) ^ 3) := by
      rw [Real.log_pow]; norm_num
    rw [h3]
    refine Real.log_le_log (by linarith) ?_
    have : (0 : ℝ) ≤ n := by linarith
    nlinarith [sq_nonneg (n : ℝ), mul_nonneg this (sq_nonneg (n : ℝ))]
  calc _ ≤ C * Real.log (4 * (n : ℝ) + 2) := h4
    _ ≤ C * (3 * Real.log ((n : ℝ) + 2)) := mul_le_mul_of_nonneg_left hlog hC.le
    _ = 3 * C * Real.log ((n : ℝ) + 2) := by ring

/-- The recentred truncated weight `ζ ↦ w(‖y₀ - ζ‖)` is integrable. -/
private theorem integrable_radialWeight_sub (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R)
    (y₀ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖y₀ - ζ‖) :=
  (integrable_radialWeight_norm hd hR).1.comp_sub_left y₀

/-- The elementary comparison `1 + t + s ≤ (1 + s)(1 + t)`, in the form used for the weights. -/
private theorem rpow_mul_le_rpow_add {s t u : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : u ≤ t + s)
    (p : ℝ) (hp : p ≤ 0) (hu0 : 0 ≤ u) :
    (1 + s) ^ p * (1 + t) ^ p ≤ (1 + u) ^ p := by
  rw [← Real.mul_rpow (by linarith) (by linarith)]
  refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ hp
  nlinarith [mul_nonneg hs ht]

/-- If the cell of a site `y` lies in the ball `B(y₀, R)` and `z` is a site near `y₀`, the weight
of the cell is bounded below by the kernel at `z - y`. -/
private theorem weight_lower (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) (y₀ : EuclideanSpace ℝ (Fin d))
    (z y : Site d) (hzy : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2)
    (hcell : cell y ⊆ Metric.ball y₀ R) :
    (1 + Real.sqrt d) ^ (-(d : ℝ)) * (1 + euclidNorm (z - y)) ^ (-(d : ℝ)) ≤
      ∫ ζ in cell y, radialWeight d R ‖y₀ - ζ‖ := by
  have hint := (integrable_radialWeight_sub hd hR y₀).integrableOn (s := cell y)
  have hmeas := measurableSet_cell y
  have hvol : volume.real (cell y) = 1 := by rw [measureReal_def, volume_cell]; simp
  have hbound := setIntegral_ge_of_const_le_real (μ := volume) (s := cell y)
    (f := fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖y₀ - ζ‖)
    (c := (1 + Real.sqrt d) ^ (-(d : ℝ)) * (1 + euclidNorm (z - y)) ^ (-(d : ℝ))) hmeas
    (by rw [volume_cell]; exact ENNReal.one_ne_top) (fun ζ hζ => ?_) hint
  · rwa [hvol, mul_one] at hbound
  · have hζR : ‖y₀ - ζ‖ < R := by
      have := hcell hζ
      rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at this
    rw [radialWeight_of_lt d hζR, abs_of_nonneg (norm_nonneg _)]
    have h1 : ‖y₀ - ζ‖ ≤ euclidNorm (z - y) + Real.sqrt d := by
      have h2 : ‖ζ - toSpace y‖ ≤ Real.sqrt d / 2 := norm_sub_toSpace_le_of_mem_cell hζ
      have e1 : ‖y₀ - toSpace z‖ ≤ Real.sqrt d / 2 := by rw [norm_sub_rev]; exact hzy
      have e2 : ‖toSpace z - toSpace y‖ = euclidNorm (z - y) := by
        rw [← toSpace_sub, norm_toSpace]
      have e3 : ‖toSpace y - ζ‖ ≤ Real.sqrt d / 2 := by rw [norm_sub_rev]; exact h2
      calc ‖y₀ - ζ‖ = ‖(y₀ - toSpace z) + (toSpace z - toSpace y) + (toSpace y - ζ)‖ := by
            congr 1; abel
        _ ≤ ‖y₀ - toSpace z‖ + ‖toSpace z - toSpace y‖ + ‖toSpace y - ζ‖ := norm_add₃_le
        _ ≤ euclidNorm (z - y) + Real.sqrt d := by rw [e2] at *; linarith
    exact rpow_mul_le_rpow_add (Real.sqrt_nonneg _) (LatticeProb.euclidNorm_nonneg _)
      (by linarith) _ (by simp) (norm_nonneg _)

/-- On a cell of the departure range, the local time times the weight of the cell is at most the
integral over the cell of the weight times the dominating function. -/
private theorem cell_term_le (hd : 1 ≤ d) {R δ : ℝ} (hR : 0 < R) (X : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (hDball : cellSet X n ⊆ Metric.ball y₀ R)
    (hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < R → |cellLocalTime X n ζ - U ζ| ≤ δ)
    (hg : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ))
    {x : Site d} (hx : x ∈ departureRange X n) :
    (localTime X n x : ℝ) * ∫ ζ in cell x, radialWeight d R ‖y₀ - ζ‖ ≤
      ∫ ζ in cell x, (radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on ((integrable_radialWeight_sub hd hR y₀).const_mul _).integrableOn
    hg.integrableOn (measurableSet_cell x) fun ζ hζ => ?_
  have hζR : ‖y₀ - ζ‖ < R := by
    have := hDball (Set.mem_iUnion₂.mpr ⟨x, hx, hζ⟩)
    rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at this
  have hcl := hcr ζ hζR
  rw [cellLocalTime_of_mem_cell X n hζ] at hcl
  have hle' : (localTime X n x : ℝ) ≤ U ζ + δ := by linarith [(abs_le.mp hcl).2]
  calc (localTime X n x : ℝ) * radialWeight d R ‖y₀ - ζ‖
      = radialWeight d R ‖y₀ - ζ‖ * (localTime X n x : ℝ) := mul_comm _ _
    _ ≤ radialWeight d R ‖y₀ - ζ‖ * (U ζ + δ) :=
        mul_le_mul_of_nonneg_left hle' (radialWeight_nonneg d R _)
    _ = _ := by ring

/-- Outside the cell set the dominating function times the weight is nonnegative, because the
local time vanishes there. -/
private theorem dominating_nonneg_off {R δ : ℝ} (X : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < R → |cellLocalTime X n ζ - U ζ| ≤ δ)
    {ζ : EuclideanSpace ℝ (Fin d)} (hζ : ζ ∈ (cellSet X n)ᶜ) :
    0 ≤ radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ := by
  by_cases hζR : ‖y₀ - ζ‖ < R
  · have hcl := hcr ζ hζR
    rw [cellLocalTime_eq_zero_of_not_mem X n hζ] at hcl
    have hU : 0 ≤ U ζ + δ := by linarith [(abs_le.mp hcl).2]
    calc (0 : ℝ) ≤ radialWeight d R ‖y₀ - ζ‖ * (U ζ + δ) :=
          mul_nonneg (radialWeight_nonneg d R _) hU
      _ = _ := by ring
  · rw [radialWeight_of_le d (not_lt.mp hζR)]
    simp

/-- The weighted sum of local times is at most the integral over the whole space of the weight
times the dominating function. -/
private theorem cell_sum_le_integral (hd : 1 ≤ d) {R δ : ℝ} (hR : 0 < R) (X : ℕ → Site d)
    (n : ℕ) {y₀ : EuclideanSpace ℝ (Fin d)} (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (hDball : cellSet X n ⊆ Metric.ball y₀ R)
    (hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < R → |cellLocalTime X n ζ - U ζ| ≤ δ)
    (hint : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => radialWeight d R ‖y₀ - ζ‖ * U ζ)) :
    ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * ∫ ζ in cell x, radialWeight d R ‖y₀ - ζ‖ ≤
      ∫ ζ : EuclideanSpace ℝ (Fin d),
        (radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) := by
  have hg : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) :=
    hint.add ((integrable_radialWeight_sub hd hR y₀).mul_const δ)
  calc _ ≤ ∑ x ∈ departureRange X n, ∫ ζ in cell x,
        (radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) :=
        Finset.sum_le_sum fun x hx => cell_term_le hd hR X n U hDball hcr hg hx
    _ = ∫ ζ in cellSet X n,
        (radialWeight d R ‖y₀ - ζ‖ * U ζ + radialWeight d R ‖y₀ - ζ‖ * δ) :=
        (integral_biUnion_finset (departureRange X n) (fun x _ => measurableSet_cell x)
          (fun x _ y _ hxy => cell_disjoint hxy) (fun x _ => hg.integrableOn)).symm
    _ ≤ _ := by
        rw [← integral_add_compl (measurableSet_cellSet X n) hg]
        exact le_add_of_nonneg_right (setIntegral_nonneg (measurableSet_cellSet X n).compl
          fun ζ hζ => dominating_nonneg_off X n U hcr hζ)

/-- The weighted sum of local times `∑_x ℓ(x) a(x)`, where `a(x)` is the weight of the cell of `x`,
is bounded by the convolution estimate: the local time is dominated by the potential plus the
error `δ` on the support of the weight, and `hconv` bounds the convolution of the potential. -/
private theorem weighted_sum_le {K : Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ}
    (hconv : GaugeConvBound d K ε) (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ) {b R δ : ℝ}
    {y₀ : EuclideanSpace ℝ (Fin d)} (hb : 0 < b) (hsub : {v | (gauge K) v < b} ⊆ cellSet X n)
    (hy₀ : (gauge K) y₀ = b) (hR : 0 < R) (hDball : cellSet X n ⊆ Metric.ball y₀ R)
    (hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < R →
      |cellLocalTime X n ζ - normPotential d ε (gauge K) (cellSet X n) ζ| ≤ δ) :
    ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * ∫ ζ in cell x, radialWeight d R ‖y₀ - ζ‖ ≤
      2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ * min b ((gauge K) ζ)) +
        (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖) *
          (normPotential d ε (gauge K) (cellSet X n) y₀ + δ) := by
  obtain ⟨hint, hle⟩ := hconv (radialWeight d R) (radialWeight_measurable d R)
    (radialWeight_nonneg d R) ⟨1, radialWeight_le_one d R⟩
    (integrable_radialWeight_norm hd hR).1 (cellSet X n) (measurableSet_cellSet X n)
    (Metric.isBounded_ball.subset hDball) b hb hsub y₀ hy₀
  have hint2 : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖y₀ - ζ‖ * normPotential d ε (gauge K) (cellSet X n) ζ) := by
    simpa only [sub_sub_cancel] using hint.comp_sub_left y₀
  have h1 := cell_sum_le_integral hd hR X n (normPotential d ε (gauge K) (cellSet X n))
      hDball hcr hint2
  have hD : ∫ ζ : EuclideanSpace ℝ (Fin d), (radialWeight d R ‖y₀ - ζ‖ *
        normPotential d ε (gauge K) (cellSet X n) ζ + radialWeight d R ‖y₀ - ζ‖ * δ) =
      (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ *
        normPotential d ε (gauge K) (cellSet X n) (y₀ - ζ)) +
      (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖) * δ := by
    rw [integral_add hint2 ((integrable_radialWeight_sub hd hR y₀).mul_const δ),
      integral_mul_const]
    have e1 := integral_sub_left_eq_self (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖ζ‖ * normPotential d ε (gauge K) (cellSet X n) (y₀ - ζ)) volume y₀
    have e2 := integral_sub_left_eq_self (fun ζ : EuclideanSpace ℝ (Fin d) =>
      radialWeight d R ‖ζ‖) volume y₀
    simp only [sub_sub_cancel] at e1
    rw [e1, e2]
  rw [hD] at h1
  linarith

/-- Consequences of `L ≥ 1`, `r ≥ 1` and `L⁴ ≤ r`: `L ≤ L² ≤ √r ≤ r`. -/
private theorem log_power_bounds {L r : ℝ} (hL : 1 ≤ L) (hr : 1 ≤ r) (h : L ^ 4 ≤ r) :
    L ≤ L ^ 2 ∧ L ^ 2 ≤ Real.sqrt r ∧ Real.sqrt r ≤ r ∧ 1 ≤ Real.sqrt r ∧ L ≤ r := by
  have h1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have hu2 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (by linarith)
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL2s : L ^ 2 ≤ Real.sqrt r := by
    refine Real.le_sqrt_of_sq_le ?_
    calc (L ^ 2) ^ 2 = L ^ 4 := by ring
      _ ≤ r := h
  have hur : Real.sqrt r ≤ r := by nlinarith
  exact ⟨hL2, hL2s, hur, h1, by linarith⟩

/-- The square root of a product with a bounded factor: `√(a) ≤ √c · t` when `a ≤ c t²`. -/
private theorem sqrt_le_sqrt_mul {a c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) (h : a ≤ c * t ^ 2) :
    Real.sqrt a ≤ Real.sqrt c * t := by
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) ht, ?_⟩
  calc a ≤ c * t ^ 2 := h
    _ = (Real.sqrt c * t) ^ 2 := by rw [mul_pow, Real.sq_sqrt hc]

/-- The crude bound on the potential at the contact point, in terms of `√r` and `L`: the local
times are at most `M ≤ C_M r`, so the weighted sum `W` is at most `C' M L`. -/
private theorem potential_crude_bound {C₁ C₂ C₃ CM C' L L' r M W H : ℝ} (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hCM : 0 ≤ CM) (hC' : 0 ≤ C') (hL : 1 ≤ L) (hL'0 : 0 ≤ L') (hL'L : L' ≤ L)
    (hr : 1 ≤ r) (hM : M ≤ CM * r) (hW : W ≤ C' * M * L)
    (hstar : H ≤ C₁ * Real.sqrt (W * L) + (C₁ + C₃) * L) :
    H + (C₂ * L' + C₂ * (Real.sqrt M * L')) ≤
      (C₁ * Real.sqrt (C' * CM) + C₂ * Real.sqrt CM) * Real.sqrt r * L + (C₁ + C₃ + C₂) * L := by
  have hu2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt (by linarith)
  have hL0 : 0 ≤ L := by linarith
  have hu0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hMu : Real.sqrt M ≤ Real.sqrt CM * Real.sqrt r :=
    sqrt_le_sqrt_mul hCM hu0 (by rw [hu2]; exact hM)
  have hWL : Real.sqrt (W * L) ≤ Real.sqrt (C' * CM) * (Real.sqrt r * L) := by
    refine sqrt_le_sqrt_mul (mul_nonneg hC' hCM) (mul_nonneg hu0 hL0) ?_
    calc W * L ≤ C' * M * L * L := mul_le_mul_of_nonneg_right hW hL0
      _ ≤ C' * (CM * r) * L * L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hM hC') hL0) hL0
      _ = C' * CM * (Real.sqrt r * L) ^ 2 := by rw [mul_pow, hu2]; ring
  have hH1 : H ≤ C₁ * (Real.sqrt (C' * CM) * (Real.sqrt r * L)) + (C₁ + C₃) * L :=
    hstar.trans (add_le_add_left (mul_le_mul_of_nonneg_left hWL hC₁) _)
  have h1 : Real.sqrt M * L' ≤ Real.sqrt CM * Real.sqrt r * L :=
    mul_le_mul hMu hL'L hL'0 (mul_nonneg (Real.sqrt_nonneg _) hu0)
  have h2 := mul_le_mul_of_nonneg_left hL'L hC₂
  have h3 := mul_le_mul_of_nonneg_left h1 hC₂
  linarith

/-- The real-variable arithmetic of the contact argument. -/
private theorem final_bound (C₁ C₂ C₃ CM CR C' c₀ κ σ s : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hC₃ : 0 ≤ C₃) (hCM : 0 ≤ CM) (hCR : 0 ≤ CR) (hC' : 0 ≤ C') (hc₀ : 0 < c₀) (hκ : 0 ≤ κ)
    (hσ : 0 ≤ σ) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ L L' r M R H W Λa m tB : ℝ, 1 ≤ L → 0 ≤ L' → L' ≤ L → 1 ≤ r →
      L ^ 4 ≤ r → M ≤ CM * r → R = 2 * CR * r + 2 * s → 0 ≤ W →
      H ≤ C₁ * Real.sqrt (W * L) + (C₁ + C₃) * L → W ≤ C' * M * L → c₀ * W ≤ Λa →
      Λa ≤ tB + m * (H + (C₂ * L' + C₂ * (Real.sqrt M * L'))) → tB ≤ κ * R → 0 ≤ m →
      m ≤ σ * L → H ≤ C * Real.sqrt (r * L) := by
  set P : ℝ := C₁ * Real.sqrt (C' * CM) + C₂ * Real.sqrt CM with hP
  set Q : ℝ := C₁ + C₃ + C₂ with hQ
  set K : ℝ := κ * (2 * CR + 2 * s) + σ * P + σ * Q with hK
  have hP0 : 0 ≤ P := add_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg _))
    (mul_nonneg hC₂ (Real.sqrt_nonneg _))
  have hQ0 : 0 ≤ Q := add_nonneg (add_nonneg hC₁ hC₃) hC₂
  have hK0 : 0 ≤ K := add_nonneg (add_nonneg (mul_nonneg hκ (by linarith)) (mul_nonneg hσ hP0))
    (mul_nonneg hσ hQ0)
  refine ⟨C₁ * Real.sqrt (K / c₀) + C₁ + C₃ + 1, ?_, ?_⟩
  · have := mul_nonneg hC₁ (Real.sqrt_nonneg (K / c₀))
    linarith
  intro L L' r M R H W Λa m tB hL hL'0 hL'L hr hLr hM hR hW0 hstar hW hc hΛ htB hm0 hmσ
  obtain ⟨hLL, hL2u, hur, hu1, hLr'⟩ := log_power_bounds hL hr hLr
  have hu2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt (by linarith)
  have hL0 : 0 ≤ L := by linarith
  have hu0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hT := potential_crude_bound hC₁ hC₂ hCM hC' hL hL'0 hL'L hr hM hW hstar
  have hT0 : 0 ≤ P * Real.sqrt r * L + Q * L :=
    add_nonneg (mul_nonneg (mul_nonneg hP0 hu0) hL0) (mul_nonneg hQ0 hL0)
  have hmT : m * (H + (C₂ * L' + C₂ * (Real.sqrt M * L'))) ≤
      σ * L * (P * Real.sqrt r * L + Q * L) :=
    (mul_le_mul_of_nonneg_left hT hm0).trans (mul_le_mul_of_nonneg_right hmσ hT0)
  have hσT : σ * L * (P * Real.sqrt r * L + Q * L) ≤ σ * P * r + σ * Q * r := by
    have h1 : Real.sqrt r * L ^ 2 ≤ r := by
      calc Real.sqrt r * L ^ 2 ≤ Real.sqrt r * Real.sqrt r :=
            mul_le_mul_of_nonneg_left hL2u hu0
        _ = r := by rw [← sq, hu2]
    have h2 : L ^ 2 ≤ r := hL2u.trans hur
    calc σ * L * (P * Real.sqrt r * L + Q * L)
        = σ * P * (Real.sqrt r * L ^ 2) + σ * Q * L ^ 2 := by ring
      _ ≤ σ * P * r + σ * Q * r :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (mul_nonneg hσ hP0))
            (mul_le_mul_of_nonneg_left h2 (mul_nonneg hσ hQ0))
  have hκR : κ * R ≤ κ * (2 * CR + 2 * s) * r := by
    have h1 : 2 * CR * r + 2 * s ≤ (2 * CR + 2 * s) * r := by
      have := mul_nonneg hs (sub_nonneg.mpr hr)
      linarith
    rw [hR]
    exact (mul_le_mul_of_nonneg_left h1 hκ).trans_eq (by ring)
  have hΛK : Λa ≤ K * r := by
    calc Λa ≤ tB + m * (H + (C₂ * L' + C₂ * (Real.sqrt M * L'))) := hΛ
      _ ≤ κ * (2 * CR + 2 * s) * r + (σ * P * r + σ * Q * r) := add_le_add (htB.trans hκR)
          (hmT.trans hσT)
      _ = K * r := by rw [hK]; ring
  have hWK : W ≤ K / c₀ * r := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    linarith
  have hsq : Real.sqrt (W * L) ≤ Real.sqrt (K / c₀) * Real.sqrt (r * L) := by
    rw [← Real.sqrt_mul (div_nonneg hK0 hc₀.le)]
    refine Real.sqrt_le_sqrt ?_
    calc W * L ≤ K / c₀ * r * L := mul_le_mul_of_nonneg_right hWK hL0
      _ = K / c₀ * (r * L) := by ring
  have hLsq : L ≤ Real.sqrt (r * L) := by
    refine Real.le_sqrt_of_sq_le ?_
    calc L ^ 2 = L * L := sq L
      _ ≤ r * L := mul_le_mul_of_nonneg_right hLr' hL0
  have hs0 : 0 ≤ Real.sqrt (r * L) := Real.sqrt_nonneg _
  calc H ≤ C₁ * Real.sqrt (W * L) + (C₁ + C₃) * L := hstar
    _ ≤ C₁ * (Real.sqrt (K / c₀) * Real.sqrt (r * L)) + (C₁ + C₃) * Real.sqrt (r * L) :=
        add_le_add (mul_le_mul_of_nonneg_left hsq hC₁)
          (mul_le_mul_of_nonneg_left hLsq (add_nonneg hC₁ hC₃))
    _ ≤ _ := by linarith

/-- The cell set of a path lies in the ball of radius `2 C_R r + 2 √d` about a contact point `y₀`
with `|y₀| ≤ H_n + √d`, when `H_n ≤ C_R r`. -/
private theorem cellSet_subset_ball_contact (hd : 1 ≤ d) (X : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} {CR r : ℝ} (hHm : maxRadius X n ≤ CR * r)
    (hy₀ : ‖y₀‖ ≤ maxRadius X n + Real.sqrt d) :
    cellSet X n ⊆ Metric.ball y₀ (2 * CR * r + 2 * Real.sqrt d) := by
  intro v hv
  have hv' := cellSet_subset_ball hd X n hv
  rw [mem_ball_zero_iff] at hv'
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖v - y₀‖ ≤ ‖v‖ + ‖y₀‖ := norm_sub_le _ _
    _ < (maxRadius X n + Real.sqrt d) + (maxRadius X n + Real.sqrt d) :=
        add_lt_add_of_lt_of_le hv' hy₀
    _ ≤ 2 * CR * r + 2 * Real.sqrt d := by linarith

/-- The kernel `(1 + |x - z|)^{-d}` is nonnegative. -/
private theorem kernel_nonneg (x z : Site d) : 0 ≤ (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) :=
  Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (x - z)]) _

/-- The local-time-weighted kernel sum over the departure range is at most `C' M L`, where `M` is
the maximal local time, once the unweighted kernel sum is at most `C' L`. -/
private theorem kernel_weight_le {C' : ℝ} (X : ℕ → Site d) (n : ℕ) (z : Site d)
    (hsum : ∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
      C' * Real.log ((n : ℝ) + 2)) :
    ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
      C' * (maxLocalTime X n : ℝ) * Real.log ((n : ℝ) + 2) := by
  calc ∑ x ∈ departureRange X n, (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ))
      ≤ ∑ x ∈ departureRange X n, (maxLocalTime X n : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right
          (by exact_mod_cast localTime_le_maxLocalTime X n x) (kernel_nonneg x z)
    _ = (maxLocalTime X n : ℝ) * ∑ x ∈ departureRange X n, (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (maxLocalTime X n : ℝ) * (C' * Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = C' * (maxLocalTime X n : ℝ) * Real.log ((n : ℝ) + 2) := by ring

/-- The local-time-weighted kernel sum at an unvisited site `z` near `y₀` is at most a constant
multiple of the weighted sum of local times `∑_x ℓ(x) a(x)`. -/
private theorem kernel_weight_ge (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) (X : ℕ → Site d) (n : ℕ)
    {y₀ : EuclideanSpace ℝ (Fin d)} {z : Site d} (hzy : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2)
    (hDball : cellSet X n ⊆ Metric.ball y₀ R) :
    (1 + Real.sqrt d) ^ (-(d : ℝ)) * ∑ x ∈ departureRange X n,
        (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) ≤
      ∑ x ∈ departureRange X n,
        (localTime X n x : ℝ) * ∫ ζ in cell x, radialWeight d R ‖y₀ - ζ‖ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  have hcell : cell x ⊆ Metric.ball y₀ R :=
    (Set.subset_iUnion₂ (s := fun x (_ : x ∈ departureRange X n) => cell x) x hx).trans hDball
  have hlow := weight_lower hd hR y₀ z x hzy hcell
  have hsym : euclidNorm (z - x) = euclidNorm (x - z) := by
    rw [← neg_sub x z, CERW.Generic.Lattice.euclidNorm_neg]
  rw [hsym] at hlow
  calc (1 + Real.sqrt d) ^ (-(d : ℝ)) * ((localTime X n x : ℝ) *
        (1 + euclidNorm (x - z)) ^ (-(d : ℝ)))
      = (localTime X n x : ℝ) * ((1 + Real.sqrt d) ^ (-(d : ℝ)) *
        (1 + euclidNorm (x - z)) ^ (-(d : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg _)

/-- The ball term of the convolution estimate, for `d = 2`: `2 d ε ∫ w min(b, ψ)` is at most
`2 d ε Λ_ψ σ_2 R`. -/
private theorem ball_term_le (hd : d = 2) {K : Set (EuclideanSpace ℝ (Fin d))} (hΨ : Adm K)
    {ε R b : ℝ} (hε : 0 < ε) (hR : 0 < R) (hb : 0 ≤ b) :
    2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ * min b ((gauge K) ζ)) ≤
      2 * (d : ℝ) * ε * (normMax (gauge K) * ((d : ℝ) * unitBallVolume d)) * R := by
  have hd2 : (d : ℝ) = 2 := by rw [hd]; norm_num
  calc _ ≤ 2 * (d : ℝ) * ε * (normMax (gauge K) * ((d : ℝ) * unitBallVolume d * R)) :=
        mul_le_mul_of_nonneg_left (integral_weight_mul_min_le hd hΨ hR hb)
          (by rw [hd2]; linarith)
    _ = _ := by ring

/-- The mass `∫ w(|ζ|)` of the truncated weight is nonnegative and at most `σ_d log (n + 2)` when
the truncation radius is at most `n`. -/
private theorem weight_mass_le (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) {n : ℕ} (hRn : R ≤ n) :
    0 ≤ ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ ∧
      ∫ ζ : EuclideanSpace ℝ (Fin d), radialWeight d R ‖ζ‖ ≤
        (d : ℝ) * unitBallVolume d * Real.log ((n : ℝ) + 2) := by
  refine ⟨integral_nonneg fun ζ => radialWeight_nonneg d _ _, ?_⟩
  have hlog : Real.log (1 + R) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hσ : 0 ≤ (d : ℝ) * unitBallVolume d :=
    mul_nonneg (Nat.cast_nonneg _) (unitBallVolume_pos d).le
  exact (integrable_radialWeight_norm hd hR).2.trans (mul_le_mul_of_nonneg_left hlog hσ)

/-- The deterministic contact argument in the plane: for `d = 2`, the potential at a contact point
of the inradius is at most `C √(r log (n + 2))`. -/
theorem gauge_contact_bound_two {d : ℕ} (hd : d = 2) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ε : ℝ} (hε : 0 < ε)
    (C₁ C₂ C₃ CM CR : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hCM : 0 ≤ CM)
    (hCR : 0 ≤ CR) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d) (n : ℕ) (r : ℝ), 2 ≤ n → X 0 = 0 →
      (∀ j, euclidNorm (X j) ≤ j) → 1 ≤ r → Real.log ((n : ℝ) + 2) ^ 4 ≤ r →
      3 * CR * r + 6 * Real.sqrt d ≤ n → (maxLocalTime X n : ℝ) ≤ CM * r →
      maxRadius X n ≤ CR * r →
      (∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - normPotential d ε (gauge K) (cellSet X n) (toSpace y)| ≤
          C₁ * (Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2))) →
      (∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ 2 * n →
        |cellLocalTime X n v - normPotential d ε (gauge K) (cellSet X n) v| ≤
          C₂ * Real.log n + C₂ * (Real.sqrt (maxLocalTime X n) * Real.log n)) →
      (∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε (gauge K) (cellSet X n) y -
            normPotential d ε (gauge K) (cellSet X n) z| ≤
          C₃ * Real.log ((n : ℝ) + 2)) →
      ∀ y₀ : EuclideanSpace ℝ (Fin d), (gauge K) y₀ = normInnerRadius (gauge K) X n →
        y₀ ∈ closure (cellSet X n)ᶜ →
        normPotential d ε (gauge K) (cellSet X n) y₀ ≤ C *
            Real.sqrt (r * Real.log ((n : ℝ) + 2)) := by
  have hΨ : Adm K := ⟨hK, hc, h0⟩
  have hconv : GaugeConvBound d K ε := gauge_convBound (by omega) hK hc h0 hε
  have hd1 : 1 ≤ d := by omega
  have hd2 : (d : ℝ) = 2 := by rw [hd]; norm_num
  have hexp : (2 - 2 * (d : ℝ)) = -(d : ℝ) := by rw [hd2]; norm_num
  have hs0 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by rw [hd2]; norm_num)
  have hΛ : 0 ≤ normMax (gauge K) := hΨ.normMax_nonneg
  obtain ⟨C', hC'pos, hC'⟩ := kernel_sum_le hd
  have hc₀ : 0 < (1 + Real.sqrt d) ^ (-(d : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hσ : 0 ≤ (d : ℝ) * unitBallVolume d :=
    mul_nonneg (Nat.cast_nonneg _) (unitBallVolume_pos d).le
  have hκ : 0 ≤ 2 * (d : ℝ) * ε * (normMax (gauge K) * ((d : ℝ) * unitBallVolume d)) :=
    mul_nonneg (by rw [hd2]; linarith) (mul_nonneg hΛ hσ)
  obtain ⟨C, hCpos, hCfin⟩ := final_bound C₁ C₂ C₃ CM CR C' ((1 + Real.sqrt d) ^ (-(d : ℝ)))
    (2 * (d : ℝ) * ε * (normMax (gauge K) * ((d : ℝ) * unitBallVolume d)))
        ((d : ℝ) * unitBallVolume d)
    (Real.sqrt d) hC₁ hC₂ hC₃ hCM hCR hC'pos.le hc₀ hκ hσ hs0.le
  refine ⟨C, hCpos, ?_⟩
  intro X n r hn2 hX0 hXn hr hLr hnr hM hHm hfine hcrude hmod y₀ hy₀ hcl
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn2
  have hL'0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hL'L : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  obtain ⟨hbpos, hsub, -, hy₀norm, z, hz0, hzy, hzn⟩ :=
    contact_setup (by omega) hΨ X n hn1 hX0 hy₀ hcl
  have hHm0 : 0 ≤ maxRadius X n :=
    (LatticeProb.euclidNorm_nonneg (X 0)).trans (euclidNorm_le_maxRadius X (Nat.zero_le n))
  have hCRr : 0 ≤ CR * r := mul_nonneg hCR (by linarith)
  have hRpos : 0 < 2 * CR * r + 2 * Real.sqrt d := by linarith
  have hRn : 2 * CR * r + 2 * Real.sqrt d ≤ n := by linarith
  have hDball := cellSet_subset_ball_contact hd1 X n hHm hy₀norm
  have hcr : ∀ ζ : EuclideanSpace ℝ (Fin d), ‖y₀ - ζ‖ < 2 * CR * r + 2 * Real.sqrt d →
      |cellLocalTime X n ζ - normPotential d ε (gauge K) (cellSet X n) ζ| ≤
        C₂ * Real.log (n : ℝ) + C₂ * (Real.sqrt (maxLocalTime X n) * Real.log (n : ℝ)) := by
    intro ζ hζ
    refine hcrude ζ ?_
    have h1 : ‖ζ‖ ≤ ‖y₀‖ + ‖y₀ - ζ‖ := by
      calc ‖ζ‖ = ‖y₀ - (y₀ - ζ)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖y₀‖ + ‖y₀ - ζ‖ := norm_sub_le _ _
    linarith
  have hws := weighted_sum_le hconv hd1 X n hbpos hsub hy₀ hRpos hDball hcr
  have hzn3 : euclidNorm z ≤ 3 * n := by linarith
  have hfz := hfine z hzn3
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = ∑ j ∈ Finset.range n,
      (1 + euclidNorm (X j - z)) ^ (-(d : ℝ)) := ⟨_, rfl⟩
  rw [hexp, ← hWdef, hz0, Nat.cast_zero, zero_sub, abs_neg] at hfz
  have hmz := hmod y₀ (toSpace z) (by linarith) (by rw [norm_sub_rev]; linarith)
  have hstar : normPotential d ε (gauge K) (cellSet X n) y₀ ≤
      C₁ * Real.sqrt (W * Real.log ((n : ℝ) + 2)) + (C₁ + C₃) * Real.log ((n : ℝ) + 2) := by
    linarith [(abs_le.mp hfz).2, (abs_le.mp hmz).2]
  have hW_eq : W = ∑ x ∈ departureRange X n,
      (localTime X n x : ℝ) * (1 + euclidNorm (x - z)) ^ (-(d : ℝ)) := by
    rw [hWdef]
    exact CERW.Support.LocalTime.sum_range_eq_sum_localTime X n
      (fun x => (1 + euclidNorm (x - z)) ^ (-(d : ℝ)))
  have hW0 : 0 ≤ W := by
    rw [hW_eq]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (Nat.cast_nonneg _) (kernel_nonneg x z)
  obtain ⟨hm0, hmσ⟩ := weight_mass_le hd1 hRpos hRn
  exact hCfin (Real.log ((n : ℝ) + 2)) (Real.log (n : ℝ)) r (maxLocalTime X n : ℝ)
    (2 * CR * r + 2 * Real.sqrt d) _ W _ _ _ hL1 hL'0 hL'L hr hLr hM rfl hW0 hstar
    (hW_eq ▸ kernel_weight_le X n z (hC' X n z hn1 hXn hzn3))
    (hW_eq ▸ kernel_weight_ge hd1 hRpos X n hzy hDball) hws
    (ball_term_le hd hΨ hε hRpos hbpos.le) hm0 hmσ


end Planar

/-!
## The deterministic contact argument in dimension at least three

For `d ≥ 3` the potential of the cell set at a contact point of the inradius of the gauge is at most
`C log (n + 2)`: the resolvent absorption `ℓ̃ ≤ U + C log n + γ χ * ℓ̃` for the kernel
`(1 + |ζ|)^{2-2d}`, the cone convolution bound and the convolution bound of the gauge.
-/

namespace HighDimensional

open CERW.Generic.Lattice CERW.Support.Occupation

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}



/-- Young's inequality for a square root: `A √(B L) ≤ λ B + A² L / (4 λ)`. -/
private lemma mul_sqrt_le_add (B L A lam : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hlam : 0 < lam) :
    A * Real.sqrt (B * L) ≤ lam * B + A ^ 2 * L / (4 * lam) := by
  set u : ℝ := lam * B with hu
  set v : ℝ := A ^ 2 * L / (4 * lam) with hv
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hsq : (A * Real.sqrt (B * L) / 2) ^ 2 = u * v := by
    rw [hu, hv]
    rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg hB hL)]
    field_simp
    ring
  have hroot : Real.sqrt (u * v) = A * Real.sqrt (B * L) / 2 := by
    rw [← hsq, Real.sqrt_sq]
    positivity
  have hamgm : 2 * Real.sqrt (u * v) ≤ u + v := by
    have h := two_mul_le_add_sq (Real.sqrt u) (Real.sqrt v)
    rw [Real.sq_sqrt hu0, Real.sq_sqrt hv0] at h
    rw [mul_assoc, ← Real.sqrt_mul hu0 v] at h
    linarith
  rw [hroot] at hamgm
  have : 2 * (A * Real.sqrt (B * L) / 2) = A * Real.sqrt (B * L) := by ring
  rw [this] at hamgm
  rw [hu, hv] at hamgm
  exact hamgm

/-- The lattice weight `k(w) = (1 + |w|)^{2-2d}`. -/
private noncomputable def kern (d : ℕ) (w : Site d) : ℝ :=
  (1 + euclidNorm w) ^ (2 - 2 * (d : ℝ))

/-- The lattice weight is nonnegative. -/
private lemma kern_nonneg (w : Site d) : 0 ≤ kern d w :=
  Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg w]) _

/-- The lattice weight is symmetric: `k(x - y) = k(y - x)`. -/
private lemma kern_sub_comm (x y : Site d) : kern d (x - y) = kern d (y - x) := by
  unfold kern
  rw [← neg_sub y x, euclidNorm_neg]

/-- Comparison of powers with a nonpositive exponent: if `1 + f ≤ c (1 + e)` then
`(1 + e)^q ≤ c^{-q} (1 + f)^q`. -/
private lemma rpow_le_mul_rpow_of_le {e f c q : ℝ} (he : 0 ≤ e) (hf : 0 ≤ f) (hc : 0 < c)
    (hq : q ≤ 0) (h : 1 + f ≤ c * (1 + e)) :
    (1 + e) ^ q ≤ c ^ (-q) * (1 + f) ^ q := by
  have h1 : (c * (1 + e)) ^ q ≤ (1 + f) ^ q :=
    Real.rpow_le_rpow_of_nonpos (by linarith) h hq
  rw [Real.mul_rpow hc.le (by linarith)] at h1
  have h2 : c ^ (-q) * c ^ q = 1 := by
    rw [← Real.rpow_add hc, neg_add_cancel, Real.rpow_zero]
  calc (1 + e) ^ q = c ^ (-q) * (c ^ q * (1 + e) ^ q) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ c ^ (-q) * (1 + f) ^ q :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hc.le _)

/-- The triangle inequality for the lattice kernel: `|z - x| ≤ |z - y| + |y - x|`. -/
private lemma euclidNorm_sub_le_add (z y x : Site d) :
    euclidNorm (z - x) ≤ euclidNorm (z - y) + euclidNorm (y - x) := by
  have h := CERW.Support.Occupation.euclidNorm_add_le (z - y) (y - x)
  rwa [sub_add_sub_cancel] at h

/-- If `e ≥ ρ / 2` then the weight at `e` is at most `2^{2d-2}` times the weight at `ρ`. -/
private lemma rpow_le_two_rpow_mul {e ρ q : ℝ} (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hq : q ≤ 0)
    (h : ρ / 2 ≤ e) : (1 + e) ^ q ≤ (2 : ℝ) ^ (-q) * (1 + ρ) ^ q :=
  rpow_le_mul_rpow_of_le he hρ (by norm_num) hq (by linarith)

/-- Each term of the lattice convolution of two weights is at most `2^{2d-2} k(z - x)` times
the sum of the two weights. -/
private lemma kern_mul_le (hd : 1 ≤ d) (z y x : Site d) :
    kern d (z - y) * kern d (y - x) ≤
      (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * (kern d (z - y) + kern d (y - x)) := by
  have hq : 2 - 2 * (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hk1 := kern_nonneg (z - y)
  have hk2 := kern_nonneg (y - x)
  have hk3 := kern_nonneg (z - x)
  have hc : 0 ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have htri := euclidNorm_sub_le_add z y x
  have hn1 := LatticeProb.euclidNorm_nonneg (z - y)
  have hn2 := LatticeProb.euclidNorm_nonneg (y - x)
  have hn3 := LatticeProb.euclidNorm_nonneg (z - x)
  by_cases hcase : euclidNorm (z - x) / 2 ≤ euclidNorm (y - x)
  · have hb : kern d (y - x) ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) :=
      rpow_le_two_rpow_mul hn2 hn3 hq hcase
    calc kern d (z - y) * kern d (y - x)
        ≤ kern d (z - y) * ((2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x)) :=
          mul_le_mul_of_nonneg_left hb hk1
      _ = (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * kern d (z - y) := by ring
      _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * (kern d (z - y) + kern d (y - x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hk3)
  · have hcase' : euclidNorm (z - x) / 2 ≤ euclidNorm (z - y) := by
      rw [not_le] at hcase
      linarith
    have ha : kern d (z - y) ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) :=
      rpow_le_two_rpow_mul hn1 hn3 hq hcase'
    calc kern d (z - y) * kern d (y - x)
        ≤ ((2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x)) * kern d (y - x) :=
          mul_le_mul_of_nonneg_right ha hk2
      _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * (kern d (z - y) + kern d (y - x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hk3)

/-- The lattice convolution of the weight with itself, over any finite set, is bounded by a
constant multiple of the weight. -/
private lemma sum_kern_mul_kern_le (hd : 1 ≤ d) {K₀ : ℝ}
    (hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, kern d (y - u) ≤ K₀)
    (F : Finset (Site d)) (z x : Site d) :
    ∑ y ∈ F, kern d (z - y) * kern d (y - x) ≤
      (2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀) * kern d (z - x) := by
  have hk3 := kern_nonneg (z - x)
  have hc : 0 ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hsum1 : ∑ y ∈ F, kern d (z - y) ≤ K₀ := by
    have := hK₀ F z
    simpa only [kern_sub_comm z] using this
  have hsum2 := hK₀ F x
  calc ∑ y ∈ F, kern d (z - y) * kern d (y - x)
      ≤ ∑ y ∈ F, (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) *
          (kern d (z - y) + kern d (y - x)) :=
        Finset.sum_le_sum fun y _ => kern_mul_le hd z y x
    _ = (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) *
          (∑ y ∈ F, kern d (z - y) + ∑ y ∈ F, kern d (y - x)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - x) * (K₀ + K₀) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) (mul_nonneg hc hk3)
    _ = (2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀) * kern d (z - x) := by ring

/-- The lattice absorption estimate: if the local time satisfies the pointwise bound on `S`
with a square root of the kernel sum, and `a` is comparable to the kernel at `z`, then the
`a`-weighted local time sum is bounded by twice the `a`-weighted potential sum, up to a
multiple of `L`. -/
private lemma absorb_sum {ℓ U a : Site d → ℝ} {S : Finset (Site d)} {z : Site d}
    {c₀ c₁ K₀ A₀ C₁ L γ : ℝ}
    (hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, kern d (y - u) ≤ K₀)
    (hconv : ∀ (F : Finset (Site d)) (x : Site d),
      ∑ y ∈ F, kern d (z - y) * kern d (y - x) ≤ A₀ * kern d (z - x))
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hA₀ : 0 ≤ A₀)
    (ha : ∀ y, c₀ * kern d (z - y) ≤ a y ∧ a y ≤ c₁ * kern d (z - y))
    (hℓ0 : ∀ y, 0 ≤ ℓ y) (hC₁ : 0 ≤ C₁) (hL : 0 ≤ L) (hγ : 0 < γ)
    (hγ' : γ * (c₁ * A₀) ≤ c₀ / 2)
    (hfine : ∀ y ∈ S,
      ℓ y ≤ U y + C₁ * (Real.sqrt ((∑ x ∈ S, ℓ x * kern d (x - y)) * L) + L)) :
    ∑ y ∈ S, a y * ℓ y ≤
      2 * ∑ y ∈ S, a y * U y + 2 * ((C₁ + C₁ ^ 2 / (4 * γ)) * L) * (c₁ * K₀) := by
  have ha0 : ∀ y, 0 ≤ a y := fun y => (mul_nonneg hc₀.le (kern_nonneg _)).trans (ha y).1
  set W : Site d → ℝ := fun y => ∑ x ∈ S, ℓ x * kern d (x - y) with hW
  have hW0 : ∀ y, 0 ≤ W y := fun y =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hℓ0 x) (kern_nonneg _)
  set Cg : ℝ := C₁ + C₁ ^ 2 / (4 * γ) with hCg
  have hCg0 : 0 ≤ Cg := by rw [hCg]; positivity
  have h1 : ∀ y ∈ S, ℓ y ≤ U y + Cg * L + γ * W y := by
    intro y hy
    have h := hfine y hy
    have hyoung := mul_sqrt_le_add (W y) L C₁ γ (hW0 y) hL hC₁ hγ
    calc ℓ y ≤ U y + C₁ * (Real.sqrt (W y * L) + L) := h
      _ = U y + (C₁ * Real.sqrt (W y * L) + C₁ * L) := by ring
      _ ≤ U y + (γ * W y + C₁ ^ 2 * L / (4 * γ) + C₁ * L) := by linarith
      _ = U y + Cg * L + γ * W y := by rw [hCg]; ring
  have h2 : ∑ y ∈ S, a y * ℓ y ≤
      ∑ y ∈ S, (a y * U y + (Cg * L) * a y + γ * (a y * W y)) := by
    refine Finset.sum_le_sum fun y hy => ?_
    calc a y * ℓ y ≤ a y * (U y + Cg * L + γ * W y) :=
          mul_le_mul_of_nonneg_left (h1 y hy) (ha0 y)
      _ = a y * U y + (Cg * L) * a y + γ * (a y * W y) := by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
  have hsumA : ∑ y ∈ S, a y ≤ c₁ * K₀ := by
    calc ∑ y ∈ S, a y ≤ ∑ y ∈ S, c₁ * kern d (y - z) :=
          Finset.sum_le_sum fun y _ => by rw [← kern_sub_comm z y]; exact (ha y).2
      _ = c₁ * ∑ y ∈ S, kern d (y - z) := by rw [Finset.mul_sum]
      _ ≤ c₁ * K₀ := mul_le_mul_of_nonneg_left (hK₀ S z) hc₁.le
  have hswap : ∑ y ∈ S, a y * W y = ∑ x ∈ S, ℓ x * ∑ y ∈ S, a y * kern d (x - y) := by
    simp only [hW, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hinner : ∀ x, ∑ y ∈ S, a y * kern d (x - y) ≤ c₁ * A₀ * kern d (z - x) := by
    intro x
    calc ∑ y ∈ S, a y * kern d (x - y)
        ≤ ∑ y ∈ S, c₁ * (kern d (z - y) * kern d (y - x)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [kern_sub_comm x y]
          calc a y * kern d (y - x) ≤ (c₁ * kern d (z - y)) * kern d (y - x) :=
                mul_le_mul_of_nonneg_right (ha y).2 (kern_nonneg _)
            _ = c₁ * (kern d (z - y) * kern d (y - x)) := by ring
      _ = c₁ * ∑ y ∈ S, kern d (z - y) * kern d (y - x) := by rw [Finset.mul_sum]
      _ ≤ c₁ * (A₀ * kern d (z - x)) := mul_le_mul_of_nonneg_left (hconv S x) hc₁.le
      _ = c₁ * A₀ * kern d (z - x) := by ring
  have hAW : c₀ * ∑ y ∈ S, a y * W y ≤ c₁ * A₀ * ∑ x ∈ S, a x * ℓ x := by
    rw [hswap, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hnn : 0 ≤ c₁ * A₀ * ℓ x := mul_nonneg (mul_nonneg hc₁.le hA₀) (hℓ0 x)
    calc c₀ * (ℓ x * ∑ y ∈ S, a y * kern d (x - y))
        ≤ c₀ * (ℓ x * (c₁ * A₀ * kern d (z - x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hinner x) (hℓ0 x)) hc₀.le
      _ = c₁ * A₀ * ℓ x * (c₀ * kern d (z - x)) := by ring
      _ ≤ c₁ * A₀ * ℓ x * a x := mul_le_mul_of_nonneg_left (ha x).1 hnn
      _ = c₁ * A₀ * (a x * ℓ x) := by ring
  have hΛ0 : 0 ≤ ∑ x ∈ S, a x * ℓ x :=
    Finset.sum_nonneg fun x _ => mul_nonneg (ha0 x) (hℓ0 x)
  have hγAW : γ * ∑ y ∈ S, a y * W y ≤ (∑ x ∈ S, a x * ℓ x) / 2 := by
    have h3 : γ * (c₁ * A₀) * ∑ x ∈ S, a x * ℓ x ≤ c₀ / 2 * ∑ x ∈ S, a x * ℓ x :=
      mul_le_mul_of_nonneg_right hγ' hΛ0
    have h4 : c₀ * (γ * ∑ y ∈ S, a y * W y) ≤ c₀ * ((∑ x ∈ S, a x * ℓ x) / 2) := by
      calc c₀ * (γ * ∑ y ∈ S, a y * W y) = γ * (c₀ * ∑ y ∈ S, a y * W y) := by ring
        _ ≤ γ * (c₁ * A₀ * ∑ x ∈ S, a x * ℓ x) := mul_le_mul_of_nonneg_left hAW hγ.le
        _ = γ * (c₁ * A₀) * ∑ x ∈ S, a x * ℓ x := by ring
        _ ≤ c₀ / 2 * ∑ x ∈ S, a x * ℓ x := h3
        _ = c₀ * ((∑ x ∈ S, a x * ℓ x) / 2) := by ring
    exact le_of_mul_le_mul_left h4 hc₀
  have hCL : Cg * L * ∑ y ∈ S, a y ≤ Cg * L * (c₁ * K₀) :=
    mul_le_mul_of_nonneg_left hsumA (mul_nonneg hCg0 hL)
  linarith

/-- The radial weight `χ(s) = (1 + |s|)^{2-2d}`. -/
private noncomputable def chi (d : ℕ) (s : ℝ) : ℝ := (1 + |s|) ^ (2 - 2 * (d : ℝ))

/-- The radial weight is nonnegative. -/
private lemma chi_nonneg (s : ℝ) : 0 ≤ chi d s :=
  Real.rpow_nonneg (by linarith [abs_nonneg s]) _

/-- The radial weight is at most one. -/
private lemma chi_le_one (hd : 1 ≤ d) (s : ℝ) : chi d s ≤ 1 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg s]) (by linarith)

/-- The radial weight is measurable. -/
private lemma measurable_chi : Measurable (chi d) := by
  unfold chi
  fun_prop

/-- The weight of a norm is `(1 + ‖ζ‖)^{2-2d}`. -/
private lemma chi_norm (ζ : EuclideanSpace ℝ (Fin d)) :
    chi d ‖ζ‖ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) := by
  rw [chi, abs_norm]

/-- For `d ≥ 3` the radial weight is integrable on `ℝ^d`. -/
private lemma integrable_chi_norm (hd : 3 ≤ d) :
    Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => chi d ‖ζ‖) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin d)) (μ := volume)
    (r := 2 * (d : ℝ) - 2) (by rw [finrank_euclideanSpace_fin]; linarith)
  refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
  show (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) = chi d ‖ζ‖
  rw [chi_norm, show -(2 * (d : ℝ) - 2) = 2 - 2 * (d : ℝ) by ring]

/-- The cell weight `a(y) = ∫_{C_y} χ(|y₀ - ζ|) dζ`. -/
private noncomputable def cellWeight (d : ℕ) (y₀ : EuclideanSpace ℝ (Fin d)) (y : Site d) : ℝ :=
  ∫ ζ in cell y, chi d ‖y₀ - ζ‖

/-- Two-sided bounds for the integral over a unit cell of a function bounded on the cell. -/
private lemma setIntegral_cell_mem_Icc {G : EuclideanSpace ℝ (Fin d) → ℝ} (y : Site d)
    (hG : IntegrableOn G (cell y)) {lo hi : ℝ}
    (h : ∀ ζ ∈ cell y, lo ≤ G ζ ∧ G ζ ≤ hi) :
    lo ≤ ∫ ζ in cell y, G ζ ∧ ∫ ζ in cell y, G ζ ≤ hi := by
  have hvol : volume (cell y) ≠ ⊤ := by
    rw [CERW.Support.Occupation.volume_cell]
    exact ENNReal.one_ne_top
  have hmeas := CERW.Support.Occupation.measurableSet_cell (d := d) y
  have hreal : volume.real (cell y) = 1 := by
    rw [Measure.real, CERW.Support.Occupation.volume_cell]
    simp
  have hc : ∀ c : ℝ, IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => c) (cell y) :=
    fun c => integrableOn_const hvol
  constructor
  · have := setIntegral_mono_on (hc lo) hG hmeas fun ζ hζ => (h ζ hζ).1
    rwa [setIntegral_const, hreal, one_smul] at this
  · have := setIntegral_mono_on hG (hc hi) hmeas fun ζ hζ => (h ζ hζ).2
    rwa [setIntegral_const, hreal, one_smul] at this

/-- For a point `ζ` of the cell of `y`, and a site `z` whose cell is near `y₀`, the distance
`|y₀ - ζ|` differs from `|z - y|` by at most `√d`. -/
private lemma abs_norm_sub_sub_euclidNorm_le {y₀ ζ : EuclideanSpace ℝ (Fin d)} {y z : Site d}
    (hζ : ζ ∈ cell y) (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) :
    |‖y₀ - ζ‖ - euclidNorm (z - y)| ≤ Real.sqrt d := by
  have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hζ
  have hw : euclidNorm (z - y) = ‖toSpace z - toSpace y‖ := by
    rw [← norm_toSpace, CERW.Support.Occupation.toSpace_sub]
  set w : EuclideanSpace ℝ (Fin d) := toSpace z - toSpace y with hwdef
  set r : EuclideanSpace ℝ (Fin d) := (y₀ - toSpace z) + (toSpace y - ζ) with hr
  have hsplit : y₀ - ζ = w + r := by rw [hwdef, hr]; abel
  have hrn : ‖r‖ ≤ Real.sqrt d := by
    calc ‖r‖ ≤ ‖y₀ - toSpace z‖ + ‖toSpace y - ζ‖ := norm_add_le _ _
      _ ≤ Real.sqrt d / 2 + Real.sqrt d / 2 := by
          rw [norm_sub_rev y₀, norm_sub_rev (toSpace y)]
          exact add_le_add hz h1
      _ = Real.sqrt d := by ring
  have h3 := abs_norm_sub_norm_le (w + r) w
  rw [add_sub_cancel_left] at h3
  rw [hw, hsplit]
  exact h3.trans hrn

/-- The comparison of the cell weight with the lattice kernel, pointwise on the cell. -/
private lemma chi_cell_bounds (hd : 1 ≤ d) {y₀ ζ : EuclideanSpace ℝ (Fin d)} {y z : Site d}
    (hζ : ζ ∈ cell y) (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) :
    ((1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))))⁻¹ * kern d (z - y) ≤ chi d ‖y₀ - ζ‖ ∧
      chi d ‖y₀ - ζ‖ ≤ (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - y) := by
  have hq : 2 - 2 * (d : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have habs := abs_norm_sub_sub_euclidNorm_le (y₀ := y₀) hζ hz
  have hr0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hs0 : 0 ≤ ‖y₀ - ζ‖ := norm_nonneg _
  have ht0 := LatticeProb.euclidNorm_nonneg (z - y)
  have hc : 0 < 1 + Real.sqrt d := by linarith
  have hcpos : 0 < (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) := Real.rpow_pos_of_pos hc _
  obtain ⟨habs1, habs2⟩ := abs_le.mp habs
  have hup := rpow_le_mul_rpow_of_le hs0 ht0 hc hq
    (show 1 + euclidNorm (z - y) ≤ (1 + Real.sqrt d) * (1 + ‖y₀ - ζ‖) by
      linarith [mul_nonneg hr0 hs0])
  have hlow := rpow_le_mul_rpow_of_le ht0 hs0 hc hq
    (show 1 + ‖y₀ - ζ‖ ≤ (1 + Real.sqrt d) * (1 + euclidNorm (z - y)) by
      linarith [mul_nonneg hr0 ht0])
  rw [chi_norm]
  constructor
  · rw [inv_mul_le_iff₀ hcpos]
    exact hlow
  · exact hup

/-- Two-sided bounds for the cell weight by the lattice kernel. -/
private lemma cellWeight_bounds (hd : 3 ≤ d) {y₀ : EuclideanSpace ℝ (Fin d)} {z : Site d}
    (hz : ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2) (y : Site d) :
    ((1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))))⁻¹ * kern d (z - y) ≤ cellWeight d y₀ y ∧
      cellWeight d y₀ y ≤ (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) * kern d (z - y) := by
  have hint : Integrable (fun ζ : EuclideanSpace ℝ (Fin d) => chi d ‖y₀ - ζ‖) :=
    (integrable_chi_norm hd).comp_sub_left y₀
  exact setIntegral_cell_mem_Icc y hint.integrableOn fun ζ hζ =>
    chi_cell_bounds (by omega) hζ hz

/-- Summing over the cells of a finite set of sites: if `Uf` varies by at most `M` across each
cell and is at least `-Cf` off the union of the cells, then the cell-weighted sum of the values
of `Uf` at the sites is at most the integral of `G Uf` plus `(M + Cf) ∫ G`. -/
private lemma sum_setIntegral_mul_le {G Uf : EuclideanSpace ℝ (Fin d) → ℝ} {S : Finset (Site d)}
    {M Cf : ℝ} (hG0 : ∀ ζ, 0 ≤ G ζ) (hG : Integrable G)
    (hGU : Integrable (fun ζ => G ζ * Uf ζ)) (hM : 0 ≤ M) (hCf : 0 ≤ Cf)
    (hmod : ∀ y ∈ S, ∀ ζ ∈ cell y, Uf (toSpace y) ≤ Uf ζ + M)
    (hfar : ∀ ζ ∉ ⋃ y ∈ S, cell y, -Cf ≤ Uf ζ) :
    ∑ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y) ≤
      (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := by
  set F : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => G ζ * (Uf ζ + M + Cf) with hF
  have hFeq : F = fun ζ => G ζ * Uf ζ + (M + Cf) * G ζ := by
    funext ζ
    rw [hF]
    ring
  have hFint : Integrable F := by
    rw [hFeq]
    exact hGU.add (hG.const_mul _)
  have hVmeas : MeasurableSet (⋃ y ∈ S, cell y) :=
    Finset.measurableSet_biUnion S fun y _ => CERW.Support.Occupation.measurableSet_cell y
  have hterm : ∀ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y) ≤ ∫ ζ in cell y, F ζ := by
    intro y hy
    rw [← integral_mul_const]
    refine setIntegral_mono_on (hG.integrableOn.mul_const _) hFint.integrableOn
      (CERW.Support.Occupation.measurableSet_cell y) fun ζ hζ => ?_
    have h1 := mul_le_mul_of_nonneg_left (hmod y hy ζ hζ) (hG0 ζ)
    have h2 : G ζ * (Uf ζ + M) ≤ G ζ * (Uf ζ + M + Cf) :=
      mul_le_mul_of_nonneg_left (by linarith) (hG0 ζ)
    exact h1.trans h2
  have hsum : ∑ y ∈ S, ∫ ζ in cell y, F ζ = ∫ ζ in ⋃ y ∈ S, cell y, F ζ := by
    rw [integral_biUnion_finset S (fun y _ => CERW.Support.Occupation.measurableSet_cell y)
      (fun x _ y _ hxy => cell_disjoint hxy) (fun y _ => hFint.integrableOn)]
  have hcompl : 0 ≤ ∫ ζ in (⋃ y ∈ S, cell y)ᶜ, F ζ := by
    refine setIntegral_nonneg hVmeas.compl fun ζ hζ => ?_
    have := hfar ζ hζ
    exact mul_nonneg (hG0 ζ) (by linarith)
  have htot := integral_add_compl hVmeas hFint
  have hFval : ∫ ζ, F ζ = (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := by
    rw [hFeq, integral_add hGU (hG.const_mul _), integral_const_mul]
  calc ∑ y ∈ S, (∫ ζ in cell y, G ζ) * Uf (toSpace y)
      ≤ ∑ y ∈ S, ∫ ζ in cell y, F ζ := Finset.sum_le_sum hterm
    _ = ∫ ζ in ⋃ y ∈ S, cell y, F ζ := hsum
    _ ≤ ∫ ζ, F ζ := by linarith
    _ = (∫ ζ, G ζ * Uf ζ) + (M + Cf) * ∫ ζ, G ζ := hFval

/-- The potential of a finite-volume set `D` at a point at distance at least `R ≥ 1` from every
point of `D` is at most `(2ε/ω_d) Λ |D| / R` in absolute value. -/
private lemma abs_normPotential_le_of_far {K : Set (EuclideanSpace ℝ (Fin d))} (hΨ : Adm K)
    (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDfin : volume D ≠ ⊤) {R : ℝ} (hR : 1 ≤ R) {ζ : EuclideanSpace ℝ (Fin d)}
    (hfar : ∀ v ∈ D, R ≤ ‖v - ζ‖) :
    |normPotential d ε (gauge K) D ζ| ≤
      2 * ε / unitBallVolume d * (normMax (gauge K) * (volume D).toReal / R) := by
  have hω := unitBallVolume_pos d
  have hΛ := hΨ.normMax_nonneg
  have hbd : ∀ v ∈ D, ‖inner ℝ (gradient (gauge K) v) (v - ζ) / ‖v - ζ‖ ^ d‖ ≤
      normMax (gauge K) / R := by
    intro v hv
    have hw := hfar v hv
    have hw1 : 1 ≤ ‖v - ζ‖ := hR.trans hw
    have hwpos : 0 < ‖v - ζ‖ := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hwpos d)]
    have h1 : |inner ℝ (gradient (gauge K) v) (v - ζ)| ≤ normMax (gauge K) * ‖v - ζ‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hΨ.norm_gradient_le v) (norm_nonneg _))
    have h2 : ‖v - ζ‖ ^ 2 ≤ ‖v - ζ‖ ^ d := pow_le_pow_right₀ hw1 hd
    rw [div_le_div_iff₀ (pow_pos hwpos d) (by linarith)]
    calc |inner ℝ (gradient (gauge K) v) (v - ζ)| * R ≤ (normMax (gauge K) * ‖v - ζ‖) * ‖v - ζ‖ :=
          mul_le_mul h1 hw (by linarith) (mul_nonneg hΛ hwpos.le)
      _ = normMax (gauge K) * ‖v - ζ‖ ^ 2 := by ring
      _ ≤ normMax (gauge K) * ‖v - ζ‖ ^ d := mul_le_mul_of_nonneg_left h2 hΛ
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) hDfin.lt_top hbd
  have hreal : volume.real D = (volume D).toReal := rfl
  rw [hreal] at hint
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  unfold normPotential
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← Real.norm_eq_abs]
  calc ‖∫ v in D, inner ℝ (gradient (gauge K) v) (v - ζ) / ‖v - ζ‖ ^ d‖
      ≤ normMax (gauge K) / R * (volume D).toReal := hint
    _ = normMax (gauge K) * (volume D).toReal / R := by ring

/-- Near the origin the integrand of the radial estimate is at most `Λ (1 + |ζ|)^{-d}`. -/
private lemma chi_mul_min_le_near (hd : 3 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hΨ : Adm K) (b : ℝ) (ζ : EuclideanSpace ℝ (Fin d)) :
    chi d ‖ζ‖ * min b ((gauge K) ζ) ≤ normMax (gauge K) * (1 + ‖ζ‖) ^ (-(d : ℝ)) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hx : 1 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  have hx0 : 0 < 1 + ‖ζ‖ := by linarith
  have hΨ0 : 0 ≤ (gauge K) ζ := hΨ.nonneg ζ
  have hΛ : (gauge K) ζ ≤ normMax (gauge K) * ‖ζ‖ := hΨ.le_normMax_mul ζ
  have hΛ0 : 0 ≤ normMax (gauge K) := hΨ.normMax_nonneg
  have h1 : chi d ‖ζ‖ * min b ((gauge K) ζ) ≤ chi d ‖ζ‖ * (normMax (gauge K) * ‖ζ‖) :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hΛ) (chi_nonneg _)
  have h2 : (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * ‖ζ‖ ≤ (1 + ‖ζ‖) ^ (-(d : ℝ)) := by
    calc (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * ‖ζ‖
        ≤ (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * (1 + ‖ζ‖) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hx0.le _)
      _ = (1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ) + 1) := (Real.rpow_add_one hx0.ne' _).symm
      _ ≤ (1 + ‖ζ‖) ^ (-(d : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc chi d ‖ζ‖ * min b ((gauge K) ζ) ≤ chi d ‖ζ‖ * (normMax (gauge K) * ‖ζ‖) := h1
    _ = normMax (gauge K) * ((1 + ‖ζ‖) ^ (2 - 2 * (d : ℝ)) * ‖ζ‖) := by rw [chi_norm]; ring
    _ ≤ normMax (gauge K) * (1 + ‖ζ‖) ^ (-(d : ℝ)) := mul_le_mul_of_nonneg_left h2 hΛ0

/-- Far from the origin the integrand of the radial estimate is at most `b |ζ|^{2-2d}`. -/
private lemma chi_mul_min_le_far (hd : 1 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    {b : ℝ} (hb : 0 < b) {ζ : EuclideanSpace ℝ (Fin d)} (hζ : 0 < ‖ζ‖) :
    chi d ‖ζ‖ * min b ((gauge K) ζ) ≤ b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) ≤ ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) :=
    Real.rpow_le_rpow_of_nonpos hζ (by linarith) (by linarith)
  rw [chi_norm, show 2 - 2 * (d : ℝ) = -(2 * (d : ℝ) - 2) by ring]
  calc (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) * min b ((gauge K) ζ)
      ≤ (1 + ‖ζ‖) ^ (-(2 * (d : ℝ) - 2)) * b :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg (by linarith [hζ]) _)
    _ ≤ ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) * b := mul_le_mul_of_nonneg_right h1 hb.le
    _ = b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) := by ring

/-- The radial estimate `∫ χ(|ζ|) min(b, ψ ζ) dζ ≤ σ_d (Λ log(1 + T) + 1)` with `T = max 1 b` and
`σ_d = d ω_d`. -/
private lemma integral_chi_mul_min_le (hd : 3 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hΨ : Adm K) {b : ℝ} (hb : 0 < b) :
    ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b ((gauge K) ζ) ≤
      d * unitBallVolume d * (normMax (gauge K) * Real.log (1 + max 1 b) + 1) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set T : ℝ := max 1 b with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hTb : b ≤ T := le_max_right _ _
  have hTpos : 0 < T := by linarith
  have hΛ0 : 0 ≤ normMax (gauge K) := hΨ.normMax_nonneg
  have hω := unitBallVolume_pos d
  set f : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => chi d ‖ζ‖ * min b ((gauge K) ζ) with hf
  have hfm : Measurable f :=
    (measurable_chi.comp measurable_norm).mul
      (measurable_const.min (hΨ.continuous).measurable)
  have hf0 : ∀ ζ, 0 ≤ f ζ := fun ζ =>
    mul_nonneg (chi_nonneg _) (le_min hb.le (hΨ.nonneg ζ))
  obtain ⟨hI1, hJ1⟩ :=
    CERW.Generic.Kernel.integrableOn_ball_one_add_norm_rpow_and_integral_le (d := d)
      (by omega) hTpos
  obtain ⟨hI2, hJ2⟩ :=
    CERW.Generic.Kernel.integrableOn_compl_ball_rpow_neg_and_integral_eq (d := d)
      (s := 2 * (d : ℝ) - 2) (ρ := T) (by omega) (by linarith) hTpos
  have hfb : IntegrableOn f (Metric.ball 0 T) :=
    (hI1.const_mul (normMax (gauge K))).mono' hfm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball fun ζ _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ζ)]
        exact chi_mul_min_le_near hd hΨ b ζ)
  have hfc : IntegrableOn f (Metric.ball 0 T)ᶜ :=
    (hI2.const_mul b).mono' hfm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_ball.compl fun ζ hζ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ζ)]
        have hζT : T ≤ ‖ζ‖ := by
          rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hζ
          exact hζ
        exact chi_mul_min_le_far (by omega) hb (by linarith))
  have hfint : Integrable f := by
    have := hfb.union hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have hA : ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ ≤
      normMax (gauge K) * (d * unitBallVolume d * Real.log (1 + T)) := by
    calc ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ
        ≤ ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T,
            normMax (gauge K) * (1 + ‖ζ‖) ^ (-(d : ℝ)) :=
          setIntegral_mono_on hfb (hI1.const_mul _) measurableSet_ball fun ζ _ =>
            chi_mul_min_le_near hd hΨ b ζ
      _ = normMax (gauge K) * ∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T,
            (1 + ‖ζ‖) ^ (-(d : ℝ)) := integral_const_mul _ _
      _ ≤ normMax (gauge K) * (d * unitBallVolume d * Real.log (1 + T)) :=
          mul_le_mul_of_nonneg_left hJ1 hΛ0
  have hexp : (d : ℝ) - (2 * (d : ℝ) - 2) ≤ -1 := by linarith
  have hbT : b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ 1 := by
    have h1 : T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ T ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT1 hexp
    rw [Real.rpow_neg_one] at h1
    calc b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) ≤ T * T⁻¹ :=
          mul_le_mul hTb h1 (Real.rpow_nonneg hTpos.le _) hTpos.le
      _ = 1 := mul_inv_cancel₀ hTpos.ne'
  have hB : ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ ≤ d * unitBallVolume d := by
    have hdiv : (1 : ℝ) ≤ 2 * (d : ℝ) - 2 - d := by linarith
    calc ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ
        ≤ ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ,
            b * ‖ζ‖ ^ (-(2 * (d : ℝ) - 2)) :=
          setIntegral_mono_on hfc (hI2.const_mul b) measurableSet_ball.compl fun ζ hζ => by
            have hζT : T ≤ ‖ζ‖ := by
              rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hζ
              exact hζ
            exact chi_mul_min_le_far (by omega) hb (by linarith)
      _ = b * (d * unitBallVolume d * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2)) /
            (2 * (d : ℝ) - 2 - d)) := by rw [integral_const_mul, hJ2]
      _ = d * unitBallVolume d * (b * T ^ ((d : ℝ) - (2 * (d : ℝ) - 2))) /
            (2 * (d : ℝ) - 2 - d) := by ring
      _ ≤ d * unitBallVolume d * 1 / (2 * (d : ℝ) - 2 - d) := by
          gcongr
      _ ≤ d * unitBallVolume d := by
          rw [mul_one, div_le_iff₀ (by linarith)]
          have : 0 ≤ (d : ℝ) * unitBallVolume d := by positivity
          calc (d : ℝ) * unitBallVolume d = d * unitBallVolume d * 1 := (mul_one _).symm
            _ ≤ d * unitBallVolume d * (2 * (d : ℝ) - 2 - d) :=
                mul_le_mul_of_nonneg_left hdiv this
  rw [← integral_add_compl measurableSet_ball hfint]
  calc (∫ ζ in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T, f ζ) +
        ∫ ζ in (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) T)ᶜ, f ζ
      ≤ normMax (gauge K) * (d * unitBallVolume d * Real.log (1 + T)) + d * unitBallVolume d :=
        add_le_add hA hB
    _ = d * unitBallVolume d * (normMax (gauge K) * Real.log (1 + T) + 1) := by ring

/-- The kernel sum over times equals the local-time weighted kernel sum over any finite set of
sites containing the departure range. -/
private lemma sum_range_kern_eq (X : ℕ → Site d) (n : ℕ) {S : Finset (Site d)}
    (hS : departureRange X n ⊆ S) (y : Site d) :
    ∑ j ∈ Finset.range n, kern d (X j - y) =
      ∑ x ∈ S, (localTime X n x : ℝ) * kern d (x - y) := by
  rw [CERW.Support.LocalTime.sum_range_eq_sum_localTime X n (fun w => kern d (w - y))]
  refine Finset.sum_subset hS fun x _ hx => ?_
  rw [mem_departureRange_iff, not_lt, Nat.le_zero] at hx
  rw [hx, Nat.cast_zero, zero_mul]

/-- The lattice departure range lies in the lattice ball of radius `2n`. -/
private lemma departureRange_subset_ballFinset_two_mul {X : ℕ → Site d} {n : ℕ}
    (hXn : ∀ j, euclidNorm (X j) ≤ j) :
    departureRange X n ⊆ LatticeProb.ballFinset d (2 * n) := by
  intro x hx
  have h1 := CERW.Support.Occupation.departureRange_subset_ballFinset X n hx
  rw [LatticeProb.mem_ballFinset_iff] at h1 ⊢
  have h2 := maxRadius_le_nat X n hXn
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The lattice step: there are constants `c₀, α₁` depending only on `d` and `C₁` such that the
kernel sum at a site `z` whose cell is near `y₀` satisfies
`c₀ Σ_j k(X_j - z) ≤ 2 Σ_{y} a(y) U(y) + α₁ L`. -/
private lemma kernel_sum_le (hd : 3 ≤ d) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    ∃ c₀ α₁ : ℝ, 0 < c₀ ∧ 0 ≤ α₁ ∧ ∀ (X : ℕ → Site d) (n : ℕ) (U : Site d → ℝ),
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - U y| ≤
          C₁ * (Real.sqrt ((∑ j ∈ Finset.range n, kern d (X j - y)) *
            Real.log ((n : ℝ) + 2)) + Real.log ((n : ℝ) + 2))) →
      ∀ (y₀ : EuclideanSpace ℝ (Fin d)) (z : Site d), ‖toSpace z - y₀‖ ≤ Real.sqrt d / 2 →
        c₀ * ∑ j ∈ Finset.range n, kern d (X j - z) ≤
          2 * ∑ y ∈ LatticeProb.ballFinset d (2 * n), cellWeight d y₀ y * U y +
            α₁ * Real.log ((n : ℝ) + 2) := by
  obtain ⟨K₀, hK₀pos, hK⟩ := CERW.Generic.Lattice.sum_finset_rpow_two_sub_two_mul_le hd
  have hK₀ : ∀ (F : Finset (Site d)) (u : Site d), ∑ y ∈ F, kern d (y - u) ≤ K₀ :=
    fun F u => hK F u
  have hd1 : 1 ≤ d := by omega
  set A₀ : ℝ := 2 * (2 : ℝ) ^ (-(2 - 2 * (d : ℝ))) * K₀ with hA₀
  have hA₀pos : 0 < A₀ := by
    rw [hA₀]
    exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) hK₀pos
  have hsq : 0 < 1 + Real.sqrt d := by linarith [Real.sqrt_nonneg (d : ℝ)]
  set c₁ : ℝ := (1 + Real.sqrt d) ^ (-(2 - 2 * (d : ℝ))) with hc₁
  have hc₁pos : 0 < c₁ := Real.rpow_pos_of_pos hsq _
  set c₀ : ℝ := c₁⁻¹ with hc₀
  have hc₀pos : 0 < c₀ := inv_pos.mpr hc₁pos
  set γ : ℝ := c₀ / (2 * (c₁ * A₀)) with hγ
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hγ' : γ * (c₁ * A₀) ≤ c₀ / 2 := by
    rw [hγ]
    have : 0 < c₁ * A₀ := mul_pos hc₁pos hA₀pos
    field_simp
    exact le_refl _
  refine ⟨c₀, 2 * (C₁ + C₁ ^ 2 / (4 * γ)) * (c₁ * K₀), hc₀pos, by positivity, ?_⟩
  intro X n U hXn hfine y₀ z hz
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  set S : Finset (Site d) := LatticeProb.ballFinset d (2 * n) with hS
  have hAS : departureRange X n ⊆ S := departureRange_subset_ballFinset_two_mul hXn
  have hℓ0 : ∀ y : Site d, 0 ≤ (localTime X n y : ℝ) := fun y => Nat.cast_nonneg _
  have hw := fun y => cellWeight_bounds hd hz y
  have hfine' : ∀ y ∈ S, (localTime X n y : ℝ) ≤ U y +
      C₁ * (Real.sqrt ((∑ x ∈ S, (localTime X n x : ℝ) * kern d (x - y)) * L) + L) := by
    intro y hy
    rw [hS, LatticeProb.mem_ballFinset_iff] at hy
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h := hfine y (by linarith)
    rw [← sum_range_kern_eq X n hAS y] at *
    have := (abs_le.mp h).2
    linarith
  have habs := absorb_sum (S := S) (z := z) (c₀ := c₀) (c₁ := c₁) (K₀ := K₀) (A₀ := A₀)
    (C₁ := C₁) (L := L) (γ := γ) (ℓ := fun y => (localTime X n y : ℝ)) (U := U)
    (a := cellWeight d y₀) hK₀ (fun F x => sum_kern_mul_kern_le hd1 hK₀ F z x) hc₀pos hc₁pos
    hA₀pos.le (fun y => by
      have := hw y
      rw [hc₀]
      exact this) hℓ0 hC₁ hL0 hγpos hγ' hfine'
  have hlow : c₀ * ∑ j ∈ Finset.range n, kern d (X j - z) ≤
      ∑ y ∈ S, cellWeight d y₀ y * (localTime X n y : ℝ) := by
    rw [sum_range_kern_eq X n hAS z, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    calc c₀ * ((localTime X n x : ℝ) * kern d (x - z))
        = (localTime X n x : ℝ) * (c₀ * kern d (z - x)) := by
          rw [kern_sub_comm x z]; ring
      _ ≤ (localTime X n x : ℝ) * cellWeight d y₀ x :=
          mul_le_mul_of_nonneg_left (hw x).1 (hℓ0 x)
      _ = cellWeight d y₀ x * (localTime X n x : ℝ) := by ring
  calc c₀ * ∑ j ∈ Finset.range n, kern d (X j - z)
      ≤ ∑ y ∈ S, cellWeight d y₀ y * (localTime X n y : ℝ) := hlow
    _ ≤ 2 * ∑ y ∈ S, cellWeight d y₀ y * U y +
          2 * ((C₁ + C₁ ^ 2 / (4 * γ)) * L) * (c₁ * K₀) := habs
    _ = 2 * ∑ y ∈ S, cellWeight d y₀ y * U y +
          2 * (C₁ + C₁ ^ 2 / (4 * γ)) * (c₁ * K₀) * L := by ring

/-- The logarithm of `1 + max 1 b` is at most a constant multiple of `log (n + 2)` when
`b ≤ 2 Λ n`. -/
private lemma log_one_add_max_le {Λ b : ℝ} {n : ℕ} (hn : 2 ≤ n) (hb : b ≤ Λ * (2 * n)) :
    Real.log (1 + max 1 b) ≤
      (1 + Real.log (1 + max 1 (2 * Λ))) * Real.log ((n : ℝ) + 2) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set Λ' : ℝ := max 1 (2 * Λ) with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_left _ _
  have hΛ'2 : 2 * Λ ≤ Λ' := le_max_right _ _
  have hn2 : 1 ≤ (n : ℝ) + 2 := by linarith
  have hT : max 1 b ≤ Λ' * ((n : ℝ) + 2) := by
    refine max_le ?_ ?_
    · exact one_le_mul_of_one_le_of_one_le hΛ'1 hn2
    · calc b ≤ Λ * (2 * n) := hb
        _ = (2 * Λ) * n := by ring
        _ ≤ Λ' * n := mul_le_mul_of_nonneg_right hΛ'2 hn0
        _ ≤ Λ' * ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h1 : 1 + max 1 b ≤ (1 + Λ') * ((n : ℝ) + 2) := by
    calc 1 + max 1 b ≤ 1 + Λ' * ((n : ℝ) + 2) := by linarith
      _ ≤ (1 + Λ') * ((n : ℝ) + 2) := by linarith
  have hpos1 : 0 < 1 + max 1 b := by linarith [le_max_left (1 : ℝ) b]
  have hpos2 : 0 < 1 + Λ' := by linarith
  have hpos3 : 0 < (n : ℝ) + 2 := by linarith
  have hL : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn
  have hlog0 : 0 ≤ Real.log (1 + Λ') := Real.log_nonneg (by linarith)
  calc Real.log (1 + max 1 b) ≤ Real.log ((1 + Λ') * ((n : ℝ) + 2)) :=
        Real.log_le_log hpos1 h1
    _ = Real.log (1 + Λ') + Real.log ((n : ℝ) + 2) := Real.log_mul hpos2.ne' hpos3.ne'
    _ ≤ (1 + Real.log (1 + Λ')) * Real.log ((n : ℝ) + 2) := by
        linarith [mul_nonneg hlog0 (sub_nonneg.mpr hL)]

/-- The far-field bound: at a point of the complement of the cells of the ball of radius `2n`,
the potential of `D_n` is at least `-C` for a constant `C`. -/
private lemma neg_le_normPotential_of_not_mem {K : Set (EuclideanSpace ℝ (Fin d))}
    (hΨ : Adm K) (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) {X : ℕ → Site d} {n : ℕ} (hn : 2 ≤ n)
    (hn4 : 4 * Real.sqrt d ≤ n) (hXn : ∀ j, euclidNorm (X j) ≤ j)
    {ζ : EuclideanSpace ℝ (Fin d)}
    (hζ : ζ ∉ ⋃ y ∈ LatticeProb.ballFinset d (2 * n), cell y) :
    -(2 * ε / unitBallVolume d * (2 * normMax (gauge K))) ≤
        normPotential d ε (gauge K) (cellSet X n) ζ := by
  have hω := unitBallVolume_pos d
  have hΛ0 := hΨ.normMax_nonneg
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmax : maxRadius X n ≤ n := maxRadius_le_nat X n hXn
  have hc : cellCenter ζ ∉ LatticeProb.ballFinset d (2 * n) := fun hcS =>
    hζ (Set.mem_iUnion₂.mpr ⟨cellCenter ζ, hcS, mem_cell_cellCenter ζ⟩)
  rw [LatticeProb.mem_ballFinset_iff, not_le] at hc
  have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter ζ)
  have hζn : 2 * (n : ℝ) - Real.sqrt d / 2 < ‖ζ‖ := by
    have h2 : ‖toSpace (cellCenter ζ)‖ ≤ ‖ζ‖ + ‖ζ - toSpace (cellCenter ζ)‖ := by
      calc ‖toSpace (cellCenter ζ)‖ = ‖ζ - (ζ - toSpace (cellCenter ζ))‖ := by
            rw [sub_sub_cancel]
        _ ≤ ‖ζ‖ + ‖ζ - toSpace (cellCenter ζ)‖ := norm_sub_le _ _
    rw [norm_toSpace] at h2
    linarith
  have hfar : ∀ v ∈ cellSet X n, (n : ℝ) / 2 ≤ ‖v - ζ‖ := by
    intro v hv
    have hvn := CERW.Support.Occupation.norm_le_of_mem_cellSet X n hv
    have h3 : ‖ζ‖ - ‖v‖ ≤ ‖ζ - v‖ := norm_sub_norm_le ζ v
    rw [norm_sub_rev] at h3
    linarith [Real.sqrt_nonneg (d : ℝ)]
  have hDfin : volume (cellSet X n) ≠ ⊤ := by
    rw [CERW.Support.Occupation.volume_cellSet]
    exact ENNReal.natCast_ne_top _
  have hvol : (volume (cellSet X n)).toReal ≤ n := by
    rw [CERW.Support.Occupation.volume_cellSet, ENNReal.toReal_natCast]
    exact_mod_cast CERW.Support.Occupation.card_departureRange_le X n
  have hpot := abs_normPotential_le_of_far hΨ hd hε hDfin (R := (n : ℝ) / 2)
    (by linarith) hfar
  have hratio : normMax (gauge K) * (volume (cellSet X n)).toReal / ((n : ℝ) / 2) ≤ 2 *
      normMax (gauge K) := by
    rw [div_le_iff₀ (by linarith)]
    calc normMax (gauge K) * (volume (cellSet X n)).toReal ≤ normMax (gauge K) * n :=
          mul_le_mul_of_nonneg_left hvol hΛ0
      _ = 2 * normMax (gauge K) * ((n : ℝ) / 2) := by ring
  have hc0 : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hbound := hpot.trans (mul_le_mul_of_nonneg_left hratio hc0)
  exact (neg_le_neg_iff.mpr hbound).trans (neg_abs_le _)

/-- The potential step: the `a`-weighted sum of the potential over the lattice ball of radius
`2n` is at most `β L + m U(y₀)`, where `m = ∫ χ(|ζ|) dζ` and `β` depends only on `d, ψ, ε, C₃`. -/
private lemma sum_cellWeight_mul_potential_le (hd : 3 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    (hconv : GaugeConvBound d K ε) {C₃ : ℝ} (hC₃ : 0 ≤ C₃) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → 4 * Real.sqrt d ≤ n →
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε (gauge K) (cellSet X n) y -
            normPotential d ε (gauge K) (cellSet X n) z| ≤
          C₃ * Real.log ((n : ℝ) + 2)) →
      ∀ (b : ℝ) (y₀ : EuclideanSpace ℝ (Fin d)), 0 < b → {v | (gauge K) v < b} ⊆ cellSet X n →
        b ≤ normMax (gauge K) * (maxRadius X n + Real.sqrt d) → (gauge K) y₀ = b →
        ∑ y ∈ LatticeProb.ballFinset d (2 * n),
            cellWeight d y₀ y * normPotential d ε (gauge K) (cellSet X n) (toSpace y) ≤
          β * Real.log ((n : ℝ) + 2) +
            (∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖) *
                normPotential d ε (gauge K) (cellSet X n) y₀ := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hω := unitBallVolume_pos d
  have hΛ0 := hΨ.normMax_nonneg
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => chi_nonneg _
  set Cf : ℝ := 2 * ε / unitBallVolume d * (2 * normMax (gauge K)) with hCf
  have hCf0 : 0 ≤ Cf := by rw [hCf]; positivity
  set CT : ℝ := 1 + Real.log (1 + max 1 (2 * normMax (gauge K))) with hCT
  have hCT0 : 0 ≤ CT := by
    rw [hCT]
    have : 0 ≤ Real.log (1 + max 1 (2 * normMax (gauge K))) :=
      Real.log_nonneg (by linarith [le_max_left (1 : ℝ) (2 * normMax (gauge K))])
    linarith
  refine ⟨2 * d * ε * (d * unitBallVolume d * (normMax (gauge K) * CT + 1)) + (C₃ + Cf) * m,
    by positivity, ?_⟩
  intro X n hn hn4 hXn hmod b y₀ hb hsub hble hy₀
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmax : maxRadius X n ≤ n := maxRadius_le_nat X n hXn
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set D : Set (EuclideanSpace ℝ (Fin d)) := cellSet X n with hD
  have hDmeas : MeasurableSet D := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDbdd : Bornology.IsBounded D :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius X n + Real.sqrt d)).subset
      (CERW.Support.Occupation.cellSet_subset_ball hd1 X n)
  obtain ⟨hint, hle⟩ := hconv (chi d) measurable_chi chi_nonneg ⟨1, chi_le_one hd1⟩
    (integrable_chi_norm hd) D hDmeas hDbdd b hb hsub y₀ hy₀
  set G : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => chi d ‖y₀ - ζ‖ with hG
  set Uf : EuclideanSpace ℝ (Fin d) → ℝ := fun ζ => normPotential d ε (gauge K) D ζ with hUf
  have hG0 : ∀ ζ, 0 ≤ G ζ := fun ζ => chi_nonneg _
  have hGint : Integrable G := (integrable_chi_norm hd).comp_sub_left y₀
  have hGU : Integrable (fun ζ => G ζ * Uf ζ) := by
    have := hint.comp_sub_left y₀
    simpa only [sub_sub_cancel] using this
  have hGUint : ∫ ζ, G ζ * Uf ζ =
      ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * normPotential d ε (gauge K) D (y₀ - ζ) := by
    have := integral_sub_left_eq_self
      (fun ζ : EuclideanSpace ℝ (Fin d) => chi d ‖ζ‖ * normPotential d ε (gauge K) D (y₀ - ζ))
      volume y₀
    simpa only [sub_sub_cancel] using this
  have hGm : ∫ ζ, G ζ = m :=
    integral_sub_left_eq_self (fun ζ : EuclideanSpace ℝ (Fin d) => chi d ‖ζ‖) volume y₀
  have hmod' : ∀ y ∈ LatticeProb.ballFinset d (2 * n), ∀ ζ ∈ cell y,
      Uf (toSpace y) ≤ Uf ζ + C₃ * L := by
    intro y hy ζ hζ
    rw [LatticeProb.mem_ballFinset_iff] at hy
    have h1 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell hζ
    have h2 := hmod (toSpace y) ζ (by rw [norm_toSpace]; linarith) (by
      rw [norm_sub_rev]; linarith)
    have := (abs_le.mp h2).2
    simp only [hUf]
    linarith
  have hfar : ∀ ζ ∉ ⋃ y ∈ LatticeProb.ballFinset d (2 * n), cell y, -Cf ≤ Uf ζ := fun ζ hζ =>
    neg_le_normPotential_of_not_mem hΨ hd2 hε.le hn hn4 hXn hζ
  have hsum := sum_setIntegral_mul_le (S := LatticeProb.ballFinset d (2 * n)) (M := C₃ * L)
    (Cf := Cf) hG0 hGint hGU (mul_nonneg hC₃ (by linarith)) hCf0 hmod' hfar
  have hb2 : b ≤ normMax (gauge K) * (2 * n) := by
    calc b ≤ normMax (gauge K) * (maxRadius X n + Real.sqrt d) := hble
      _ ≤ normMax (gauge K) * (2 * n) := mul_le_mul_of_nonneg_left (by linarith) hΛ0
  have hlog := log_one_add_max_le hn hb2
  have hIB := integral_chi_mul_min_le hd hΨ hb
  have hIB' : ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b ((gauge K) ζ) ≤
      d * unitBallVolume d * ((normMax (gauge K) * CT + 1) * L) := by
    refine hIB.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    calc normMax (gauge K) * Real.log (1 + max 1 b) + 1
        ≤ normMax (gauge K) * (CT * L) + 1 := by
          have := mul_le_mul_of_nonneg_left hlog hΛ0
          linarith
      _ ≤ (normMax (gauge K) * CT + 1) * L := by
          linarith
  have hP : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hstep : 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b ((gauge K) ζ)) ≤
      2 * d * ε * (d * unitBallVolume d * (normMax (gauge K) * CT + 1)) * L := by
    calc 2 * (d : ℝ) * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b ((gauge K) ζ))
        ≤ 2 * d * ε * (d * unitBallVolume d * ((normMax (gauge K) * CT + 1) * L)) :=
          mul_le_mul_of_nonneg_left hIB' hP
      _ = 2 * d * ε * (d * unitBallVolume d * (normMax (gauge K) * CT + 1)) * L := by ring
  have hCfm : Cf * m ≤ Cf * m * L := by
    have := mul_nonneg (mul_nonneg hCf0 hm0) (sub_nonneg.mpr hL1)
    linarith
  calc ∑ y ∈ LatticeProb.ballFinset d (2 * n),
          cellWeight d y₀ y * normPotential d ε (gauge K) D (toSpace y)
      ≤ (∫ ζ, G ζ * Uf ζ) + (C₃ * L + Cf) * ∫ ζ, G ζ := hsum
    _ ≤ (2 * d * ε * (∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ * min b ((gauge K) ζ)) +
          m * normPotential d ε (gauge K) D y₀) + (C₃ * L + Cf) * m := by
        rw [hGm, hGUint]
        linarith
    _ ≤ (2 * d * ε * (d * unitBallVolume d * (normMax (gauge K) * CT + 1)) * L +
          m * normPotential d ε (gauge K) D y₀) + (C₃ * L + Cf) * m := by linarith
    _ ≤ (2 * d * ε * (d * unitBallVolume d * (normMax (gauge K) * CT + 1)) + (C₃ + Cf) * m) * L +
          m * normPotential d ε (gauge K) D y₀ := by linarith

/-- The final absorption: if `H ≤ C₁ √(W L) + (C₁ + C₃) L` and `W ≤ M (H + L)`, with `H ≥ 0`,
then `H ≤ (1 + C₁² M + 2 C₁ + 2 C₃) L`. -/
private lemma le_of_le_sqrt_add {H W L M C₁ C₃ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hC₁ : 0 ≤ C₁)
    (hH0 : 0 ≤ H) (hW : W ≤ M * (H + L))
    (hH : H ≤ C₁ * Real.sqrt (W * L) + (C₁ + C₃) * L) :
    H ≤ (1 + C₁ ^ 2 * M + 2 * C₁ + 2 * C₃) * L := by
  have h1 : Real.sqrt (W * L) ≤ Real.sqrt ((H + L) * (M * L)) := by
    refine Real.sqrt_le_sqrt ?_
    calc W * L ≤ M * (H + L) * L := mul_le_mul_of_nonneg_right hW hL
      _ = (H + L) * (M * L) := by ring
  have h2 := mul_sqrt_le_add (H + L) (M * L) C₁ (1 / 2) (by linarith) (mul_nonneg hM hL) hC₁
    (by norm_num)
  have h3 : C₁ * Real.sqrt (W * L) ≤ C₁ * Real.sqrt ((H + L) * (M * L)) :=
    mul_le_mul_of_nonneg_left h1 hC₁
  have h4 : C₁ ^ 2 * (M * L) / (4 * (1 / 2)) = C₁ ^ 2 * M * L / 2 := by ring
  rw [h4] at h2
  linarith

/-- **The contact bound in dimension `d ≥ 3`.** The potential of the cell set at a contact point
is at most a constant times `log (n + 2)`, given the pointwise local-time bound and the modulus of
the potential on cells. -/
theorem gauge_contact_bound_three_le {d : ℕ} (hd : 3 ≤ d)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ε : ℝ} (hε : 0 < ε)
    (C₁ C₃ : ℝ) (hC₁ : 0 ≤ C₁) (hC₃ : 0 ≤ C₃) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n → 4 * Real.sqrt d ≤ n → X 0 = 0 →
      (∀ j, euclidNorm (X j) ≤ j) →
      (∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - normPotential d ε (gauge K) (cellSet X n) (toSpace y)| ≤
          C₁ * (Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2))) →
      (∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε (gauge K) (cellSet X n) y -
            normPotential d ε (gauge K) (cellSet X n) z| ≤
          C₃ * Real.log ((n : ℝ) + 2)) →
      ∀ y₀ : EuclideanSpace ℝ (Fin d), (gauge K) y₀ = normInnerRadius (gauge K) X n →
        y₀ ∈ closure (cellSet X n)ᶜ →
        normPotential d ε (gauge K) (cellSet X n) y₀ ≤ C * Real.log ((n : ℝ) + 2) := by
  have hΨ : Adm K := ⟨hK, hc, h0⟩
  have hconv : GaugeConvBound d K ε := gauge_convBound (by omega) hK hc h0 hε
  obtain ⟨c₀, α₁, hc₀, hα₁, hlat⟩ := kernel_sum_le hd hC₁
  obtain ⟨β, hβ, hpot⟩ := sum_cellWeight_mul_potential_le hd hΨ hε hconv hC₃
  set m : ℝ := ∫ ζ : EuclideanSpace ℝ (Fin d), chi d ‖ζ‖ with hm
  have hm0 : 0 ≤ m := integral_nonneg fun ζ => chi_nonneg _
  set M : ℝ := (2 * β + α₁ + 2 * m) / c₀ with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine ⟨1 + C₁ ^ 2 * M + 2 * C₁ + 2 * C₃, by positivity, ?_⟩
  intro X n hn hn4 hX0 hXn hfine hmod y₀ hy₀ hcl
  obtain ⟨hbpos, hsub, hble, hy₀n, z, hz0, hzy, hzn⟩ :=
    contact_setup (by omega) hΨ X n (by omega) hX0 hy₀ hcl
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hL1 : 1 ≤ L := CERW.Support.Law.one_le_log_add_two hn
  set H : ℝ := normPotential d ε (gauge K) (cellSet X n) y₀ with hH
  by_cases hH0 : H ≤ 0
  · have : 0 ≤ (1 + C₁ ^ 2 * M + 2 * C₁ + 2 * C₃) * L := by positivity
    linarith
  rw [not_le] at hH0
  have hmax : maxRadius X n ≤ n := maxRadius_le_nat X n hXn
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfz := hfine z (by linarith)
  rw [hz0, Nat.cast_zero, zero_sub, abs_neg] at hfz
  have hmodz := hmod y₀ (toSpace z) (by linarith) (by rw [norm_sub_rev]; linarith)
  have hUz := (abs_le.mp hfz).2
  have hstar : H ≤ C₁ * Real.sqrt ((∑ j ∈ Finset.range n, kern d (X j - z)) * L) +
      (C₁ + C₃) * L := by
    have := (abs_le.mp hmodz).1
    have h2 : H - normPotential d ε (gauge K) (cellSet X n) (toSpace z) ≤ C₃ * L := by
      have := (abs_le.mp hmodz).2
      linarith
    change normPotential d ε (gauge K) (cellSet X n) (toSpace z) ≤
      C₁ * (Real.sqrt ((∑ j ∈ Finset.range n, kern d (X j - z)) * L) + L) at hUz
    linarith
  have hb1 := hlat X n (fun y => normPotential d ε (gauge K) (cellSet X n) (toSpace y)) hXn
      hfine y₀ z hzy
  have hb2 := hpot X n hn hn4 hXn hmod (normInnerRadius (gauge K) X n) y₀ hbpos hsub hble hy₀
  have hW : (∑ j ∈ Finset.range n, kern d (X j - z)) ≤ M * (H + L) := by
    refine le_of_mul_le_mul_left ?_ hc₀
    have h1 : c₀ * (∑ j ∈ Finset.range n, kern d (X j - z)) ≤
        (2 * β + α₁) * L + 2 * m * H := by
      linarith
    have h2 : c₀ * (M * (H + L)) = (2 * β + α₁ + 2 * m) * (H + L) := by
      rw [hM]
      field_simp
    rw [h2]
    have h3 : 0 ≤ (2 * β + α₁) * H := mul_nonneg (by linarith) hH0.le
    have h4 : 0 ≤ 2 * m * L := mul_nonneg (by linarith) (by linarith)
    linarith
  exact le_of_le_sqrt_add (by linarith) hM0 hC₁ hH0.le hW hstar


end HighDimensional

/-!
## The rates of the limit shape

The rate `q_n` and the elementary inequalities between the scales `r_n`, `log n` and the rates of
Proposition 5.1; the arithmetic that turns the contact bound, the mass identity and the layer bound
into the rates of the inner radius and of the local times.
-/

namespace Rates
open CERW

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
/-! ## The rates -/

/-- The rate `q` as a function of `r` and `ℓ = log n`. -/
noncomputable def rateQ (d : ℕ) (r ℓ : ℝ) : ℝ :=
  if d = 2 then Real.sqrt (ℓ / r) else ℓ / r

end Rates
namespace Rates.RateScales
/-- A power of a square root is a power of the radicand: `(√x)^a = x^(a/2)`. -/
private theorem sqrt_rpow_eq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    Real.sqrt x ^ a = x ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

/-- For positive `r` and `ℓ`, `r * (ℓ / r)^a = r^(1 - a) * ℓ^a`. -/
private theorem mul_div_rpow_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) (a : ℝ) :
    r * (ℓ / r) ^ a = r ^ (1 - a) * ℓ ^ a := by
  rw [Real.div_rpow hℓ.le hr.le, Real.rpow_sub hr, Real.rpow_one]
  ring

/-- The exponent `1 - 1/(d+1)` equals `d/(d+1)`. -/
private theorem one_sub_inv_succ (d : ℕ) :
    (1 : ℝ) - 1 / ((d : ℝ) + 1) = (d : ℝ) / ((d : ℝ) + 1) := by
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The exponent `1/(d+1) + 1` equals `(d+2)/(d+1)`. -/
private theorem inv_succ_add_one (d : ℕ) :
    (1 : ℝ) / ((d : ℝ) + 1) + 1 = ((d : ℝ) + 2) / ((d : ℝ) + 1) := by
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The exponent `1/(d+1) - 1` equals `-(d/(d+1))`. -/
private theorem inv_succ_sub_one (d : ℕ) :
    (1 : ℝ) / ((d : ℝ) + 1) - 1 = -((d : ℝ) / ((d : ℝ) + 1)) := by
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- For positive `X`, the quantity `((d+1) n / X)^(1/(d+1))` is
`((d+1)/X)^(1/(d+1)) * n^(1/(d+1))`. -/
private theorem scale_eq_mul (d : ℕ) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    (((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1)) =
      (((d : ℝ) + 1) / X) ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [show ((d : ℝ) + 1) * n / X = ((d : ℝ) + 1) / X * n by ring,
    Real.mul_rpow (div_pos hd1 hX).le (Nat.cast_nonneg n)]

end Rates.RateScales
namespace Rates
open CERW

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
/-- `r q^{1/2}` is the rate of the inner radius in Proposition 5.1. -/
private theorem rate_inner_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    r * rateQ d r ℓ ^ ((1 : ℝ) / 2) =
      if d = 2 then r ^ ((3 : ℝ) / 4) * ℓ ^ ((1 : ℝ) / 4) else (r * ℓ) ^ ((1 : ℝ) / 2) := by
  have hq : 0 ≤ ℓ / r := div_nonneg hℓ.le hr.le
  by_cases h2 : d = 2
  · simp only [rateQ, if_pos h2]
    rw [RateScales.sqrt_rpow_eq hq, RateScales.mul_div_rpow_eq hr hℓ]
    norm_num
  · simp only [rateQ, if_neg h2]
    rw [RateScales.mul_div_rpow_eq hr hℓ, Real.mul_rpow hr.le hℓ.le]
    norm_num

/-- `r q^{1/(d+1)}` is the rate of the local times in Proposition 5.1. -/
private theorem rate_local_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) =
      if d = 2 then r ^ ((5 : ℝ) / 6) * ℓ ^ ((1 : ℝ) / 6)
      else r ^ ((d : ℝ) / (d + 1)) * ℓ ^ ((1 : ℝ) / (d + 1)) := by
  have hq : 0 ≤ ℓ / r := div_nonneg hℓ.le hr.le
  by_cases h2 : d = 2
  · have hd2 : (d : ℝ) = 2 := by exact_mod_cast h2
    simp only [rateQ, if_pos h2]
    rw [RateScales.sqrt_rpow_eq hq, RateScales.mul_div_rpow_eq hr hℓ, hd2]
    norm_num
  · simp only [rateQ, if_neg h2]
    rw [RateScales.mul_div_rpow_eq hr hℓ, RateScales.one_sub_inv_succ]

/-- `r q^{1/(d+1)} log n` is the rate of the outer radius in Proposition 5.1. -/
private theorem rate_outer_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ =
      if d = 2 then r ^ ((5 : ℝ) / 6) * ℓ ^ ((7 : ℝ) / 6)
      else r ^ ((d : ℝ) / (d + 1)) * ℓ ^ (((d : ℝ) + 2) / (d + 1)) := by
  rw [rate_local_eq hr hℓ]
  by_cases h2 : d = 2
  · simp only [if_pos h2]
    rw [mul_assoc, ← Real.rpow_add_one hℓ.ne']
    norm_num
  · simp only [if_neg h2]
    rw [mul_assoc, ← Real.rpow_add_one hℓ.ne', RateScales.inv_succ_add_one]

/-- The scale `r_n = ((d+1) n / X)^{1/(d+1)}` tends to infinity. -/
private theorem tendsto_scale (d : ℕ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun n : ℕ => (((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1))) atTop atTop := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have he : (0 : ℝ) < (1 : ℝ) / ((d : ℝ) + 1) := div_pos one_pos hd1
  have hlin : Tendsto (fun n : ℕ => ((d : ℝ) + 1) * n / X) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hd1).atTop_div_const hX
  exact (tendsto_rpow_atTop he).comp hlin

/-- Every real power of `log n` is negligible against the scale `r_n`. -/
private theorem tendsto_log_rpow_div_scale (d : ℕ) {X : ℝ} (hX : 0 < X) (K : ℝ) :
    Tendsto (fun n : ℕ => Real.log n ^ K / (((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1)))
      atTop (𝓝 0) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have he : (0 : ℝ) < (1 : ℝ) / ((d : ℝ) + 1) := div_pos one_pos hd1
  have hbase : Tendsto (fun n : ℕ => Real.log n ^ K / (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)))
      atTop (𝓝 0) :=
    ((isLittleO_log_rpow_rpow_atTop K he).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have hmul := hbase.const_mul ((((d : ℝ) + 1) / X) ^ ((1 : ℝ) / ((d : ℝ) + 1)))⁻¹
  rw [mul_zero] at hmul
  refine hmul.congr (fun n => ?_)
  rw [RateScales.scale_eq_mul d hX n]
  ring

/-- The scale is small against `n`: `r_n / n → 0`. -/
private theorem tendsto_scale_div_self (d : ℕ) (hd : 1 ≤ d) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun n : ℕ => (((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1)) / n) atTop (𝓝 0) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hde : (0 : ℝ) < (d : ℝ) / ((d : ℝ) + 1) := div_pos (Nat.cast_pos.mpr hd) hd1
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ (-((d : ℝ) / ((d : ℝ) + 1)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hde).comp tendsto_natCast_atTop_atTop
  have hmul := hbase.const_mul ((((d : ℝ) + 1) / X) ^ ((1 : ℝ) / ((d : ℝ) + 1)))
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [RateScales.scale_eq_mul d hX n, mul_div_assoc, ← Real.rpow_sub_one hn0.ne',
    RateScales.inv_succ_sub_one]

end Rates
namespace Rates.RateInequalities
variable {d : ℕ}

/-- The rate is positive for positive `r` and `ℓ`. -/
private lemma rateQ_pos (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) : 0 < rateQ d r ℓ := by
  unfold rateQ
  split_ifs
  · exact Real.sqrt_pos.2 (div_pos hℓ hr)
  · exact div_pos hℓ hr

/-- The rate is at most `1` once `ℓ ≤ r`. -/
private lemma rateQ_le_one (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓr : ℓ ≤ r) :
    rateQ d r ℓ ≤ 1 := by
  have h : ℓ / r ≤ 1 := (div_le_one hr).2 hℓr
  unfold rateQ
  split_ifs
  · exact Real.sqrt_le_one.2 h
  · exact h

/-- The rate dominates `ℓ / r` once `ℓ ≤ r`. -/
private lemma div_le_rateQ (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) :
    ℓ / r ≤ rateQ d r ℓ := by
  have h0 : 0 ≤ ℓ / r := (div_pos hℓ hr).le
  have h1 : ℓ / r ≤ 1 := (div_le_one hr).2 hℓr
  unfold rateQ
  split_ifs
  · exact (Real.le_sqrt h0 h0).2 (pow_le_of_le_one h0 h1 two_ne_zero)
  · exact le_rfl

/-- The scale regime: `M ℓ^(d+5) ≤ r` with `M ≥ 1` and `ℓ ≥ 1` gives `ℓ ^ (d+5) ≤ r`,
`ℓ ^ 3 ≤ r` and `ℓ ≤ r`. -/
private lemma regime {d : ℕ} (hd : 2 ≤ d) {ℓ r M : ℝ} (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ)
    (h : M * ℓ ^ (d + 5) ≤ r) : ℓ ^ (d + 5) ≤ r ∧ ℓ ^ 3 ≤ r ∧ ℓ ≤ r := by
  have hpos : 0 ≤ ℓ ^ (d + 5) := pow_nonneg (by linarith) _
  have h1 : ℓ ^ (d + 5) ≤ r := (le_mul_of_one_le_left hpos hM).trans h
  have h2 : ℓ ^ 3 ≤ ℓ ^ (d + 5) := pow_le_pow_right₀ hℓ (by omega)
  have h3 : ℓ ≤ ℓ ^ 3 := le_self_pow₀ hℓ (by norm_num)
  exact ⟨h1, h2.trans h1, h3.trans (h2.trans h1)⟩

/-- Taking the power `1 / (d + 1)` undoes raising to the power `d + 1`. -/
private lemma pow_succ_rpow_inv (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have h : ((d + 1 : ℕ) : ℝ) * ((1 : ℝ) / (d + 1)) = 1 := by
    push_cast
    field_simp
  rw [h, Real.rpow_one]

/-- The square of the half power of the rate is the rate. -/
private lemma rpow_half_sq (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    (rateQ d r ℓ ^ ((1 : ℝ) / 2)) ^ 2 = rateQ d r ℓ := by
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (rateQ_pos d hr hℓ).le

/-- The half power of the rate is at most the `1 / (d + 1)` power of the rate. -/
private lemma rpow_half_le_rpow_inv (d : ℕ) (hd : 1 ≤ d) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ)
    (hℓr : ℓ ≤ r) :
    rateQ d r ℓ ^ ((1 : ℝ) / 2) ≤ rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) + 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact Real.rpow_le_rpow_of_exponent_ge (rateQ_pos d hr hℓ) (rateQ_le_one d hr hℓr)
    (one_div_le_one_div_of_le (by norm_num) hd')

/-- The fluctuation scale is at most `r` times the half power of the rate. -/
private lemma fluct_le {r ℓ : ℝ} (hr : 0 < r) (hℓ : 1 ≤ ℓ) (hℓ3 : ℓ ^ 3 ≤ r) :
    (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) ≤
      r * rateQ d r ℓ ^ ((1 : ℝ) / 2) := by
  have hℓ0 : 0 < ℓ := by linarith
  by_cases hd2 : d = 2
  · rw [if_pos hd2]
    have hq : rateQ d r ℓ = Real.sqrt (ℓ / r) := by simp [rateQ, hd2]
    rw [hq, ← Real.sqrt_eq_rpow]
    have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
    have hp2 : Real.sqrt (Real.sqrt (ℓ / r)) ^ 2 = Real.sqrt (ℓ / r) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have hp4 : Real.sqrt (Real.sqrt (ℓ / r)) ^ 4 = ℓ / r := by
      calc Real.sqrt (Real.sqrt (ℓ / r)) ^ 4
          = (Real.sqrt (Real.sqrt (ℓ / r)) ^ 2) ^ 2 := by ring
        _ = ℓ / r := by rw [hp2]; exact Real.sq_sqrt (div_pos hℓ0 hr).le
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num)
      (mul_nonneg hr.le (Real.sqrt_nonneg _)) ?_
    have hl : (Real.sqrt r * ℓ) ^ 4 = r ^ 2 * ℓ ^ 4 := by
      calc (Real.sqrt r * ℓ) ^ 4 = (Real.sqrt r ^ 2) ^ 2 * ℓ ^ 4 := by ring
        _ = r ^ 2 * ℓ ^ 4 := by rw [hsr]
    have hrr : (r * Real.sqrt (Real.sqrt (ℓ / r))) ^ 4 = r ^ 3 * ℓ := by
      rw [mul_pow, hp4]
      field_simp
    rw [hl, hrr]
    calc r ^ 2 * ℓ ^ 4 = (r ^ 2 * ℓ) * ℓ ^ 3 := by ring
      _ ≤ (r ^ 2 * ℓ) * r := mul_le_mul_of_nonneg_left hℓ3 (by positivity)
      _ = r ^ 3 * ℓ := by ring
  · rw [if_neg hd2]
    have hq : rateQ d r ℓ = ℓ / r := by simp [rateQ, hd2]
    rw [hq, ← Real.sqrt_eq_rpow]
    apply le_of_eq
    calc Real.sqrt (r * ℓ) = Real.sqrt (r ^ 2 * (ℓ / r)) := by
          congr 1
          field_simp
      _ = r * Real.sqrt (ℓ / r) := by rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]

/-- Mean value bound `y^(n+1) - x^(n+1) ≤ (n+1) (y - x) y^n` for `0 ≤ x ≤ y`. -/
private lemma pow_succ_sub_pow_succ_le (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y ^ (n + 1) - x ^ (n + 1) ≤ ((n : ℝ) + 1) * (y - x) * y ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : x ^ (k + 1) ≤ y ^ (k + 1) := pow_le_pow_left₀ hx hxy _
    have h2 : 0 ≤ y - x := sub_nonneg.2 hxy
    have h3 : (y - x) * x ^ (k + 1) ≤ (y - x) * y ^ (k + 1) :=
      mul_le_mul_of_nonneg_left h1 h2
    have hy : 0 ≤ y := hx.trans hxy
    have h4 : y * (y ^ (k + 1) - x ^ (k + 1)) ≤ y * (((k : ℝ) + 1) * (y - x) * y ^ k) :=
      mul_le_mul_of_nonneg_left ih hy
    calc y ^ (k + 1 + 1) - x ^ (k + 1 + 1)
        = y * (y ^ (k + 1) - x ^ (k + 1)) + (y - x) * x ^ (k + 1) := by ring
      _ ≤ y * (((k : ℝ) + 1) * (y - x) * y ^ k) + (y - x) * y ^ (k + 1) := add_le_add h4 h3
      _ = (((k + 1 : ℕ) : ℝ) + 1) * (y - x) * y ^ (k + 1) := by push_cast; ring

/-- Mean value bound `y^n - x^n ≤ n (y - x) y^(n-1)` for `0 ≤ x ≤ y` and `n ≥ 1`. -/
private lemma pow_sub_pow_le_mul {n : ℕ} (hn : 1 ≤ n) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y ^ n - x ^ n ≤ n * (y - x) * y ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using pow_succ_sub_pow_succ_le k hx hxy

/-- Bound on the shell term: `(b + s)^d - b^d ≤ d s (K^(d-1) r^(d-1))` when `b + s ≤ K r`. -/
private lemma shell_bound {d : ℕ} (hd : 1 ≤ d) {b s K r : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hK : b + s ≤ K * r) :
    (b + s) ^ d - b ^ d ≤ d * s * (K ^ (d - 1) * r ^ (d - 1)) := by
  have h1 := pow_sub_pow_le_mul hd hb (le_add_of_nonneg_right hs : b ≤ b + s)
  have h2 : (b + s) ^ (d - 1) ≤ (K * r) ^ (d - 1) :=
    pow_le_pow_left₀ (add_nonneg hb hs) hK _
  have h3 : (d : ℝ) * s * (b + s) ^ (d - 1) ≤ d * s * (K * r) ^ (d - 1) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg (Nat.cast_nonneg d) hs)
  rw [add_sub_cancel_left] at h1
  calc (b + s) ^ d - b ^ d ≤ d * s * (b + s) ^ (d - 1) := by
        have : (d : ℝ) * s * (b + s) ^ (d - 1) = d * (b + s - b) * (b + s) ^ (d - 1) := by ring
        rw [this, ← add_sub_cancel_left (a := b) (b := s)]
        simpa using h1
    _ ≤ d * s * (K * r) ^ (d - 1) := h3
    _ = d * s * (K ^ (d - 1) * r ^ (d - 1)) := by rw [mul_pow]

/-- The volume of the shell is at most `(V d (C_R+1)^(d-1) + C_I C_c) r^d p`. -/
private lemma ev_bound {d : ℕ} (hd : 1 ≤ d) {V C_R C_c C_I r p b I Ev : ℝ} (hV : 0 < V)
    (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) (hb : 0 < b) (hbR : b ≤ C_R * r)
    (hI : I ≤ C_I * C_c * (r ^ (d + 1) * p ^ 2))
    (hEv : Ev ≤ V * ((b + r * p) ^ d - b ^ d) + I / (r * p)) :
    Ev ≤ (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c) * (r ^ d * p) := by
  have hs : 0 < r * p := mul_pos hr hp
  have hK : b + r * p ≤ (C_R + 1) * r :=
    calc b + r * p ≤ C_R * r + r := add_le_add hbR (mul_le_of_le_one_right hr.le hp1)
      _ = (C_R + 1) * r := by ring
  have h1 := shell_bound hd hb.le hs.le hK
  have hrd : r * r ^ (d - 1) = r ^ d := mul_pow_sub_one (by omega) r
  have h2 : V * ((b + r * p) ^ d - b ^ d) ≤ V * d * (C_R + 1) ^ (d - 1) * (r ^ d * p) :=
    calc V * ((b + r * p) ^ d - b ^ d)
        ≤ V * (d * (r * p) * ((C_R + 1) ^ (d - 1) * r ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left h1 hV.le
      _ = V * d * (C_R + 1) ^ (d - 1) * (r ^ d * p) := by rw [← hrd]; ring
  have h3 : I / (r * p) ≤ C_I * C_c * (r ^ d * p) := by
    rw [div_le_iff₀ hs]
    calc I ≤ C_I * C_c * (r ^ (d + 1) * p ^ 2) := hI
      _ = C_I * C_c * (r ^ d * p) * (r * p) := by ring
  calc Ev ≤ V * ((b + r * p) ^ d - b ^ d) + I / (r * p) := hEv
    _ ≤ V * d * (C_R + 1) ^ (d - 1) * (r ^ d * p) + C_I * C_c * (r ^ d * p) :=
        add_le_add h2 h3
    _ = (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c) * (r ^ d * p) := by ring

/-- For `0 ≤ x ≤ y`: `y^n (y - x) ≤ y^(n+1) - x^(n+1)`. -/
private lemma pow_succ_sub_ge (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y ^ n * (y - x) ≤ y ^ (n + 1) - x ^ (n + 1) := by
  have h1 : x ^ n ≤ y ^ n := pow_le_pow_left₀ hx hxy n
  have h2 : x * x ^ n ≤ x * y ^ n := mul_le_mul_of_nonneg_left h1 hx
  rw [pow_succ, pow_succ]
  linarith

/-- For `r > 0` and `b ≥ 0`: `r^d |r - b| ≤ |r^(d+1) - b^(d+1)|`. -/
private lemma pow_mul_abs_sub_le (d : ℕ) {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) :
    r ^ d * |r - b| ≤ |r ^ (d + 1) - b ^ (d + 1)| := by
  rcases le_total b r with h | h
  · have h1 := pow_succ_sub_ge d hb h
    rw [abs_of_nonneg (sub_nonneg.2 h),
      abs_of_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hb h _))]
    exact h1
  · have h1 := pow_succ_sub_ge d hr.le h
    have h2 : r ^ d ≤ b ^ d := pow_le_pow_left₀ hr.le h d
    rw [abs_of_nonpos (sub_nonpos.2 h),
      abs_of_nonpos (sub_nonpos.2 (pow_le_pow_left₀ hr.le h _)), neg_sub, neg_sub]
    calc r ^ d * (b - r) ≤ b ^ d * (b - r) := mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 h)
      _ ≤ b ^ (d + 1) - r ^ (d + 1) := h1

/-- The comparison of the norm volume with the inner radius gives `|b - r| ≤ C r p`. -/
private lemma cmp_bound {d : ℕ} (hd : 1 ≤ d) {ε V C_m C_e C_δ C_Ev : ℝ} (hε : 0 < ε)
    (hV : 0 < V) (hC_m : 0 < C_m) (hC_e : 0 < C_e) (hC_δ : 0 < C_δ)
    {r p b Ev δ w nn : ℝ} (hr : 0 < r) (hb : 0 ≤ b)
    (hnn : nn = 2 * ε * d * V * r ^ (d + 1) / (d + 1)) (hw : w ≤ r * p)
    (hδ : δ ≤ C_δ * w) (hEv : Ev ≤ C_Ev * (r ^ d * p))
    (hcmp : |nn - 2 * ε * (d * V * b ^ (d + 1) / (d + 1))| ≤ C_m * r ^ d * δ + C_e * r * Ev) :
    |b - r| ≤ ((C_m * C_δ + C_e * C_Ev) / (2 * ε * d * V / (d + 1))) * (r * p) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 2 * ε * d * V / (d + 1) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    exact div_pos (mul_pos (mul_pos (mul_pos two_pos hε) hd') hV) (by positivity)
  have hcast : nn - 2 * ε * (d * V * b ^ (d + 1) / (d + 1)) = κ * (r ^ (d + 1) - b ^ (d + 1)) := by
    rw [hnn, hκdef]
    ring
  rw [hcast, abs_mul, abs_of_pos hκ] at hcmp
  have hδr : δ ≤ C_δ * (r * p) := hδ.trans (mul_le_mul_of_nonneg_left hw hC_δ.le)
  have h2 : C_m * r ^ d * δ + C_e * r * Ev ≤
      (C_m * C_δ + C_e * C_Ev) * (r ^ d * (r * p)) :=
    calc C_m * r ^ d * δ + C_e * r * Ev
        ≤ C_m * r ^ d * (C_δ * (r * p)) + C_e * r * (C_Ev * (r ^ d * p)) :=
          add_le_add (mul_le_mul_of_nonneg_left hδr (by positivity))
            (mul_le_mul_of_nonneg_left hEv (by positivity))
      _ = (C_m * C_δ + C_e * C_Ev) * (r ^ d * (r * p)) := by ring
  have h3 : r ^ d * (κ * |b - r|) ≤ r ^ d * ((C_m * C_δ + C_e * C_Ev) * (r * p)) :=
    calc r ^ d * (κ * |b - r|) = κ * (r ^ d * |r - b|) := by rw [abs_sub_comm]; ring
      _ ≤ κ * |r ^ (d + 1) - b ^ (d + 1)| :=
          mul_le_mul_of_nonneg_left (pow_mul_abs_sub_le d hr hb) hκ.le
      _ ≤ C_m * r ^ d * δ + C_e * r * Ev := hcmp
      _ ≤ (C_m * C_δ + C_e * C_Ev) * (r ^ d * (r * p)) := h2
      _ = r ^ d * ((C_m * C_δ + C_e * C_Ev) * (r * p)) := by ring
  have h4 : κ * |b - r| ≤ (C_m * C_δ + C_e * C_Ev) * (r * p) :=
    le_of_mul_le_mul_left h3 (pow_pos hr d)
  rw [← hκdef, div_mul_eq_mul_div, le_div_iff₀ hκ]
  linarith

/-- The upper bound for the local time mass in terms of the rate. -/
private lemma mass_bound {d : ℕ} {C_I C_c r q H I : ℝ} (hC_I : 0 < C_I) (hr : 0 < r)
    (hI : I ≤ C_I * r ^ d * H) (hH : H ≤ C_c * r * q) :
    I ≤ C_I * C_c * (r ^ (d + 1) * q) :=
  calc I ≤ C_I * r ^ d * H := hI
    _ ≤ C_I * r ^ d * (C_c * r * q) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = C_I * C_c * (r ^ (d + 1) * q) := by ring

/-- The power `1 / (d + 1)` of a bounded quantity. -/
private lemma rpow_inv_le_of_le (d : ℕ) {I c r q : ℝ} (hI : 0 ≤ I) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hq : 0 ≤ q) (h : I ≤ c * (r ^ (d + 1) * q)) :
    I ^ ((1 : ℝ) / (d + 1)) ≤ c ^ ((1 : ℝ) / (d + 1)) * (r * q ^ ((1 : ℝ) / (d + 1))) := by
  have he : (0 : ℝ) ≤ (1 : ℝ) / (d + 1) := by positivity
  calc I ^ ((1 : ℝ) / (d + 1)) ≤ (c * (r ^ (d + 1) * q)) ^ ((1 : ℝ) / (d + 1)) :=
        Real.rpow_le_rpow hI h he
    _ = c ^ ((1 : ℝ) / (d + 1)) * ((r ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) *
          q ^ ((1 : ℝ) / (d + 1))) := by
        rw [Real.mul_rpow hc (mul_nonneg (pow_nonneg hr _) hq),
          Real.mul_rpow (pow_nonneg hr _) hq]
    _ = c ^ ((1 : ℝ) / (d + 1)) * (r * q ^ ((1 : ℝ) / (d + 1))) := by
        rw [pow_succ_rpow_inv d hr]

/-- The square of `q ℓ^(d+1)` is at most `ℓ^(d+5) / r`. -/
private lemma rate_mul_pow_sq_le (hd : 2 ≤ d) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 1 ≤ ℓ)
    (hℓr : ℓ ^ (d + 5) ≤ r) :
    (rateQ d r ℓ * ℓ ^ (d + 1)) ^ 2 ≤ ℓ ^ (d + 5) / r := by
  have hℓ0 : 0 < ℓ := by linarith
  by_cases hd2 : d = 2
  · subst hd2
    have hq : rateQ 2 r ℓ = Real.sqrt (ℓ / r) := by simp [rateQ]
    rw [hq, mul_pow, Real.sq_sqrt (div_pos hℓ0 hr).le]
    apply le_of_eq
    ring
  · have hq : rateQ d r ℓ = ℓ / r := by simp [rateQ, hd2]
    rw [hq]
    have h1 : ℓ / r * ℓ ^ (d + 1) ≤ ℓ ^ (d + 5) / r := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hr.le
      calc ℓ * ℓ ^ (d + 1) = ℓ ^ (d + 2) := by ring
        _ ≤ ℓ ^ (d + 5) := pow_le_pow_right₀ hℓ (by omega)
    have h2 : ℓ ^ (d + 5) / r ≤ 1 := (div_le_one hr).2 hℓr
    have h3 : 0 ≤ ℓ / r * ℓ ^ (d + 1) := by positivity
    exact (pow_le_of_le_one h3 (h1.trans h2) two_ne_zero).trans h1

/-- The product of the `1 / (d + 1)` power of the rate with `ℓ` is small in the regime
`M ℓ^(d+5) ≤ r` with `M` large. -/
private lemma rate_local_mul_le (hd : 2 ≤ d) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r ℓ : ℝ, 1 ≤ ℓ → M * ℓ ^ (d + 5) ≤ r →
      rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ ≤ θ := by
  have hθ' : 0 < θ ^ (d + 1) := pow_pos hθ _
  refine ⟨1 / (θ ^ (d + 1)) ^ 2 + 1, by
    have : 0 ≤ 1 / (θ ^ (d + 1)) ^ 2 := by positivity
    linarith, ?_⟩
  intro r ℓ hℓ hM
  have hM1 : 1 ≤ 1 / (θ ^ (d + 1)) ^ 2 + 1 := by
    have : 0 ≤ 1 / (θ ^ (d + 1)) ^ 2 := by positivity
    linarith
  obtain ⟨hℓ5, -, hℓr⟩ := regime hd hM1 hℓ hM
  have hℓ0 : 0 < ℓ := by linarith
  have hr : 0 < r := by linarith
  have hsq := rate_mul_pow_sq_le hd hr hℓ hℓ5
  have hMθ : 1 ≤ (θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2 + 1) := by
    have h0 : (θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2) = 1 := by field_simp
    have h1 : 0 ≤ (θ ^ (d + 1)) ^ 2 := by positivity
    calc (1 : ℝ) = (θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2) := h0.symm
      _ ≤ (θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2 + 1) := by
          rw [mul_add, mul_one]
          linarith
  have hpos : 0 ≤ ℓ ^ (d + 5) := pow_nonneg hℓ0.le _
  have h2 : ℓ ^ (d + 5) / r ≤ (θ ^ (d + 1)) ^ 2 := by
    rw [div_le_iff₀ hr]
    calc ℓ ^ (d + 5) = 1 * ℓ ^ (d + 5) := (one_mul _).symm
      _ ≤ ((θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2 + 1)) * ℓ ^ (d + 5) :=
          mul_le_mul_of_nonneg_right hMθ hpos
      _ = (θ ^ (d + 1)) ^ 2 * ((1 / (θ ^ (d + 1)) ^ 2 + 1) * ℓ ^ (d + 5)) := by ring
      _ ≤ (θ ^ (d + 1)) ^ 2 * r := mul_le_mul_of_nonneg_left hM (by positivity)
  have hq0 : 0 ≤ rateQ d r ℓ := (rateQ_pos d hr hℓ0).le
  have hz : rateQ d r ℓ * ℓ ^ (d + 1) ≤ θ ^ (d + 1) :=
    le_of_pow_le_pow_left₀ two_ne_zero hθ'.le (hsq.trans h2)
  have hy : 0 ≤ rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hq0 _
  refine le_of_pow_le_pow_left₀ (n := d + 1) (Nat.succ_ne_zero d) hθ.le ?_
  rw [mul_pow, CERW.Support.Geometry.rpow_inv_succ_pow d hq0]
  exact hz

/-- The product `r q^(1/(d+1))` is at least `1` when `r, ℓ ≥ 1` and `ℓ ≤ r`. -/
private lemma one_le_mul_rpow (d : ℕ) {r ℓ : ℝ} (hr : 1 ≤ r) (hℓ : 1 ≤ ℓ) (hℓr : ℓ ≤ r) :
    1 ≤ r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) := by
  have hr0 : 0 < r := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hq0 : 0 ≤ rateQ d r ℓ := (rateQ_pos d hr0 hℓ0).le
  have hq : ℓ / r ≤ rateQ d r ℓ := div_le_rateQ d hr0 hℓ0 hℓr
  have hy : 0 ≤ rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hq0 _
  have h1 : 1 ≤ (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) := by
    rw [mul_pow, CERW.Support.Geometry.rpow_inv_succ_pow d hq0]
    calc (1 : ℝ) ≤ r ^ d * ℓ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr) hℓ
      _ = r ^ (d + 1) * (ℓ / r) := by
          field_simp
          ring
      _ ≤ r ^ (d + 1) * rateQ d r ℓ := mul_le_mul_of_nonneg_left hq (by positivity)
  exact (one_le_pow_iff_of_nonneg (mul_nonneg hr0.le hy) (Nat.succ_ne_zero d)).1 h1

/-- The pure real-variable form of the outer-radius smallness conditions. -/
private lemma outer_core {K₁ C₀ η Λsq E θ r ℓ x : ℝ} (hK₁ : 0 < K₁) (hC₀ : 0 < C₀)
    (hη : 0 < η) (hΛsq : 0 < Λsq) (hE : 0 < E) (hθ : 0 < θ)
    (hθs : K₁ * (1 + C₀) * θ * (η + Λsq) ≤ 1 / 4) (hr : 0 < r) (hℓ : 0 ≤ ℓ) (hx : 1 ≤ x)
    (hxℓ : x * ℓ ≤ r * θ) :
    η * (K₁ * (1 + C₀ * x) * ℓ) ≤ r / 2 ∧ K₁ * (1 + C₀ * x) * ℓ * Λsq < r / 2 ∧
      E * (K₁ * (1 + C₀ * x) * ℓ) ≤ E * (K₁ * (1 + C₀)) * (x * ℓ) := by
  have hA : 0 < K₁ * (1 + C₀) := by positivity
  have hτ1 : K₁ * (1 + C₀ * x) * ℓ ≤ K₁ * (1 + C₀) * (x * ℓ) := by
    have h : 1 + C₀ * x ≤ (1 + C₀) * x := by
      have e : (1 + C₀) * x = x + C₀ * x := by ring
      linarith
    calc K₁ * (1 + C₀ * x) * ℓ ≤ K₁ * ((1 + C₀) * x) * ℓ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hK₁.le) hℓ
      _ = K₁ * (1 + C₀) * (x * ℓ) := by ring
  have hτ2 : K₁ * (1 + C₀ * x) * ℓ ≤ K₁ * (1 + C₀) * (r * θ) :=
    hτ1.trans (mul_le_mul_of_nonneg_left hxℓ hA.le)
  have hκ : 0 ≤ K₁ * (1 + C₀) * θ := by positivity
  have hκη : K₁ * (1 + C₀) * θ * η ≤ 1 / 4 := by
    have h1 : 0 ≤ K₁ * (1 + C₀) * θ * Λsq := mul_nonneg hκ hΛsq.le
    have h2 : K₁ * (1 + C₀) * θ * (η + Λsq) =
        K₁ * (1 + C₀) * θ * η + K₁ * (1 + C₀) * θ * Λsq := mul_add _ _ _
    linarith
  have hκΛ : K₁ * (1 + C₀) * θ * Λsq ≤ 1 / 4 := by
    have h1 : 0 ≤ K₁ * (1 + C₀) * θ * η := mul_nonneg hκ hη.le
    have h2 : K₁ * (1 + C₀) * θ * (η + Λsq) =
        K₁ * (1 + C₀) * θ * η + K₁ * (1 + C₀) * θ * Λsq := mul_add _ _ _
    linarith
  refine ⟨?_, ?_, ?_⟩
  · calc η * (K₁ * (1 + C₀ * x) * ℓ) ≤ η * (K₁ * (1 + C₀) * (r * θ)) :=
          mul_le_mul_of_nonneg_left hτ2 hη.le
      _ = r * (K₁ * (1 + C₀) * θ * η) := by ring
      _ ≤ r * (1 / 4) := mul_le_mul_of_nonneg_left hκη hr.le
      _ ≤ r / 2 := by linarith
  · calc K₁ * (1 + C₀ * x) * ℓ * Λsq ≤ K₁ * (1 + C₀) * (r * θ) * Λsq :=
          mul_le_mul_of_nonneg_right hτ2 hΛsq.le
      _ = r * (K₁ * (1 + C₀) * θ * Λsq) := by ring
      _ ≤ r * (1 / 4) := mul_le_mul_of_nonneg_left hκΛ hr.le
      _ < r / 2 := by linarith
  · calc E * (K₁ * (1 + C₀ * x) * ℓ) ≤ E * (K₁ * (1 + C₀) * (x * ℓ)) :=
          mul_le_mul_of_nonneg_left hτ1 hE.le
      _ = E * (K₁ * (1 + C₀)) * (x * ℓ) := by ring

end Rates.RateInequalities
namespace Rates
open CERW

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
/-- The inner radius and the local mass are controlled by the rates, from the shell bound, the
volume comparison and the fluctuation bound on the boundary layer. -/
private theorem inner_rates_arith (hd : 2 ≤ d) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V)
    {C_R C_c C_δ C_I C_m C_e : ℝ} (hC_R : 0 < C_R) (hC_c : 0 < C_c) (hC_δ : 0 < C_δ)
    (hC_I : 0 < C_I) (hC_m : 0 < C_m) (hC_e : 0 < C_e) :
    ∃ C r₀ M : ℝ, 0 < C ∧ 0 < M ∧ ∀ r ℓ b I Ev H δ nn : ℝ, r₀ ≤ r → 1 ≤ ℓ →
      M * ℓ ^ (d + 5) ≤ r →
      nn = 2 * ε * d * V * r ^ (d + 1) / (d + 1) →
      0 < b → b ≤ C_R * r →
      0 ≤ I → I ≤ C_I * r ^ d * H →
      0 ≤ H → H ≤ C_c * r * rateQ d r ℓ →
      0 ≤ Ev → (∀ s : ℝ, 0 < s → Ev ≤ V * ((b + s) ^ d - b ^ d) + I / s) →
      0 ≤ δ → δ ≤ C_δ * (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) →
      |nn - 2 * ε * (d * V * b ^ (d + 1) / (d + 1))| ≤ C_m * r ^ d * δ + C_e * r * Ev →
      |b - r| ≤ C * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) ∧
        I ≤ C * (r ^ (d + 1) * rateQ d r ℓ) := by
  have hCI : 0 < C_I * C_c := mul_pos hC_I hC_c
  refine ⟨C_I * C_c + (C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
      (2 * ε * d * V / (d + 1)), 1, 1, ?_, one_pos, ?_⟩
  · have hd' : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
    positivity
  · intro r ℓ b I Ev H δ nn hr hℓ hM hnn hb hbR hI0 hI hH0 hH hEv0 hEv hδ0 hδ hcmp
    obtain ⟨-, hℓ3, hℓr⟩ := RateInequalities.regime hd le_rfl hℓ hM
    have hr0 : 0 < r := by linarith
    have hℓ0 : 0 < ℓ := by linarith
    have hq0 : 0 < rateQ d r ℓ := RateInequalities.rateQ_pos d hr0 hℓ0
    have hq1 : rateQ d r ℓ ≤ 1 := RateInequalities.rateQ_le_one d hr0 hℓr
    have hp0 : 0 < rateQ d r ℓ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hq0 _
    have hp2 : (rateQ d r ℓ ^ ((1 : ℝ) / 2)) ^ 2 = rateQ d r ℓ :=
      RateInequalities.rpow_half_sq d hr0 hℓ0
    have hp1 : rateQ d r ℓ ^ ((1 : ℝ) / 2) ≤ 1 := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_one.2 hq1
    have hw := RateInequalities.fluct_le (d := d) hr0 hℓ hℓ3
    have hmass := RateInequalities.mass_bound (d := d) hC_I hr0 hI hH
    have hmass' : I ≤ C_I * C_c * (r ^ (d + 1) * (rateQ d r ℓ ^ ((1 : ℝ) / 2)) ^ 2) := by
      rw [hp2]
      exact hmass
    have hEvb := RateInequalities.ev_bound (by omega) hV hr0 hp0 hp1 hb hbR hmass'
      (hEv (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) (mul_pos hr0 hp0))
    have hcb := RateInequalities.cmp_bound (by omega) hε hV hC_m hC_e hC_δ hr0 hb.le hnn hw
      hδ hEvb hcmp
    constructor
    · calc |b - r| ≤ ((C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
            (2 * ε * d * V / (d + 1))) * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) := hcb
        _ ≤ (C_I * C_c + (C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
            (2 * ε * d * V / (d + 1))) * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCI.le) (mul_nonneg hr0.le hp0.le)
    · calc I ≤ C_I * C_c * (r ^ (d + 1) * rateQ d r ℓ) := hmass
        _ ≤ (C_I * C_c + (C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
            (2 * ε * d * V / (d + 1))) * (r ^ (d + 1) * rateQ d r ℓ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hd' : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
          have : 0 ≤ (C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
              (2 * ε * d * V / (d + 1)) := by positivity
          exact le_add_of_nonneg_right this

/-- The profile error is controlled by `r q^(1/(d+1))`, from the inner-radius and mass bounds. -/
private theorem profile_arith (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {C_L C_I' C_b C_δ : ℝ} (hC_L : 0 < C_L) (hC_I' : 0 < C_I') (hC_b : 0 < C_b)
    (hC_δ : 0 < C_δ) :
    ∃ C r₀ M : ℝ, 0 < C ∧ 0 < M ∧ ∀ r ℓ b I δ : ℝ, r₀ ≤ r → 1 ≤ ℓ →
      M * ℓ ^ (d + 5) ≤ r →
      0 ≤ I → I ≤ C_I' * (r ^ (d + 1) * rateQ d r ℓ) →
      |b - r| ≤ C_b * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) →
      0 ≤ δ → δ ≤ C_δ * (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) →
      δ + C_L * I ^ ((1 : ℝ) / (d + 1)) + 2 * d * ε * |b - r| ≤
        C * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) := by
  refine ⟨C_δ + C_L * C_I' ^ ((1 : ℝ) / (d + 1)) + 2 * d * ε * C_b, 1, 1, ?_, one_pos, ?_⟩
  · have : 0 < C_I' ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hC_I' _
    positivity
  · intro r ℓ b I δ hr hℓ hM hI0 hI hb hδ0 hδ
    obtain ⟨-, hℓ3, hℓr⟩ := RateInequalities.regime hd le_rfl hℓ hM
    have hr0 : 0 < r := by linarith
    have hℓ0 : 0 < ℓ := by linarith
    have hq0 : 0 < rateQ d r ℓ := RateInequalities.rateQ_pos d hr0 hℓ0
    have hp_y := RateInequalities.rpow_half_le_rpow_inv d (by omega) hr0 hℓ0 hℓr
    have hw := RateInequalities.fluct_le (d := d) hr0 hℓ hℓ3
    have hry : 0 ≤ r := hr0.le
    have h1 : δ ≤ C_δ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) :=
      hδ.trans (mul_le_mul_of_nonneg_left
        (hw.trans (mul_le_mul_of_nonneg_left hp_y hry)) hC_δ.le)
    have h2 : I ^ ((1 : ℝ) / (d + 1)) ≤
        C_I' ^ ((1 : ℝ) / (d + 1)) * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) :=
      RateInequalities.rpow_inv_le_of_le d hI0 hC_I'.le hry hq0.le hI
    have h3 : |b - r| ≤ C_b * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) :=
      hb.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp_y hry) hC_b.le)
    have hc1 : (0 : ℝ) ≤ 2 * d * ε := by positivity
    calc δ + C_L * I ^ ((1 : ℝ) / (d + 1)) + 2 * d * ε * |b - r|
        ≤ C_δ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) +
          C_L * (C_I' ^ ((1 : ℝ) / (d + 1)) * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) +
          2 * d * ε * (C_b * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) :=
          add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left h2 hC_L.le))
            (mul_le_mul_of_nonneg_left h3 hc1)
      _ = (C_δ + C_L * C_I' ^ ((1 : ℝ) / (d + 1)) + 2 * d * ε * C_b) *
          (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) := by ring

/-- The smallness conditions and the size bound for the outer-radius time scale. -/
private theorem outer_arith (hd : 2 ≤ d) {K₁ C₀ η Λsq E : ℝ} (hK₁ : 0 < K₁) (hC₀ : 0 < C₀)
    (hη : 0 < η) (hΛsq : 0 < Λsq) (hE : 0 < E) :
    ∃ C r₀ M : ℝ, 0 < C ∧ 0 < M ∧ ∀ r ℓ : ℝ, r₀ ≤ r → 1 ≤ ℓ → M * ℓ ^ (d + 5) ≤ r →
      η * (K₁ * (1 + C₀ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) * ℓ) ≤ r / 2 ∧
      K₁ * (1 + C₀ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) * ℓ * Λsq < r / 2 ∧
      E * (K₁ * (1 + C₀ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) * ℓ) ≤
        C * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ) := by
  have hA : 0 < K₁ * (1 + C₀) := by positivity
  have hP : 0 < η + Λsq := add_pos hη hΛsq
  have hθ : 0 < 1 / (4 * (K₁ * (1 + C₀)) * (η + Λsq)) := by positivity
  obtain ⟨M, hM1, hM⟩ := RateInequalities.rate_local_mul_le hd hθ
  refine ⟨E * (K₁ * (1 + C₀)), 1, M, by positivity, by linarith, ?_⟩
  intro r ℓ hr hℓ hMr
  obtain ⟨-, -, hℓr⟩ := RateInequalities.regime hd hM1 hℓ hMr
  have hr0 : 0 < r := by linarith
  have hy := hM r ℓ hℓ hMr
  have hx1 := RateInequalities.one_le_mul_rpow d hr hℓ hℓr
  have hxℓ : r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ ≤
      r * (1 / (4 * (K₁ * (1 + C₀)) * (η + Λsq))) := by
    calc r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ
        = r * (rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ) := by ring
      _ ≤ r * (1 / (4 * (K₁ * (1 + C₀)) * (η + Λsq))) :=
          mul_le_mul_of_nonneg_left hy hr0.le
  have hθs : K₁ * (1 + C₀) * (1 / (4 * (K₁ * (1 + C₀)) * (η + Λsq))) * (η + Λsq) ≤ 1 / 4 := by
    apply le_of_eq
    field_simp
  exact RateInequalities.outer_core hK₁ hC₀ hη hΛsq hE hθ hθs hr0 (by linarith) hx1 hxℓ

end Rates
/-!
## Excess, inner radius and potential of the cell set for the gauge

The integral of the cone, the volume of the excess `E = D_n \ {ψ < b}`, the inradius and its contact
point, the splitting of the potential, the excess bound from the contact point and the potential of
the excess from its layers: the deterministic geometry behind the inner radius.
-/


namespace Rates.BallFacts

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- `Λ_ψ > 0` when `d ≥ 1`. -/
private theorem normMax_pos' (hd : 1 ≤ d) (hΨ : Adm K) : 0 < normMax (gauge K) :=
  lt_of_lt_of_le (normMin_gauge_pos_mul_le hΨ.compact hΨ.zero_mem hd).1
    (normMin_gauge_le_normMax_gauge hΨ.compact hΨ.zero_mem hd)

/-- Homogeneity of the sublevel sets. -/
private theorem normSublevel_eq_smul (_hΨ : Adm K) {ρ : ℝ} (hρ : 0 < ρ) :
    {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} =
      ρ • {v : EuclideanSpace ℝ (Fin d) | gauge K v < 1} :=
  gauge_sublevel_eq_smul K hρ

/-- The real volume of a sublevel set is `ρ ^ d` times the volume of the unit ball. -/
private theorem real_volume_sublevel (hd : 1 ≤ d) (hΨ : Adm K) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume.real {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} =
      ρ ^ d * normBallVolume (gauge K) := by
  rw [measureReal_def, volume_gauge_sublevel hΨ.compact hΨ.zero_mem hd hρ]
  exact ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hρ _) ENNReal.toReal_nonneg)

/-- A sublevel set has finite volume. -/
private theorem volume_sublevel_ne_top (hd : 1 ≤ d) (hΨ : Adm K) (ρ : ℝ) :
    volume {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} ≠ ⊤ :=
  ((measure_mono (gauge_sublevel_subset_ball hΨ.compact hΨ.zero_mem hd ρ)).trans_lt
    measure_ball_lt_top).ne

/-- A continuous function is integrable on every bounded set. -/
private theorem integrableOn_of_isBounded {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) {E : Set (EuclideanSpace ℝ (Fin d))} (hEb : Bornology.IsBounded E) :
    IntegrableOn f E volume := by
  obtain ⟨r, hr⟩ := hEb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hr

end Rates.BallFacts

namespace Rates

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}


/-- The sublevel sets are measurable. -/
private theorem measurableSet_normSublevel (hΨ : Adm K) (ρ : ℝ) :
    MeasurableSet {v : EuclideanSpace ℝ (Fin d) | (gauge K) v < ρ} :=
  measurableSet_gauge_sublevel hΨ.convex hΨ.zero_mem ρ

/-- The sublevel set `{ψ < ρ}` lies in the Euclidean ball of radius `ρ / c_ψ`. -/
private theorem normSublevel_subset_ball (hd : 1 ≤ d) (hΨ : Adm K) (ρ : ℝ) :
    {v : EuclideanSpace ℝ (Fin d) | (gauge K) v < ρ} ⊆ Metric.ball 0 (ρ / normMin (gauge K)) :=
  gauge_sublevel_subset_ball hΨ.compact hΨ.zero_mem hd ρ

/-- The Euclidean ball of radius `ρ / Λ_ψ` lies in the sublevel set `{ψ < ρ}`. -/
private theorem ball_subset_normSublevel (hd : 1 ≤ d) (hΨ : Adm K) {ρ : ℝ} :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (ρ / normMax (gauge K)) ⊆ {v | (gauge K) v < ρ} :=
  ball_subset_gauge_sublevel hΨ.compact hΨ.zero_mem hd ρ

end Rates

namespace Rates
open CERW

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
/-- The integral of the cone function `max (b - ψ) 0` over a ball of radius `S ≥ b / c_ψ` is
`|B_ψ| b ^ (d + 1) / (d + 1)`. -/
private theorem integral_cone (hd : 1 ≤ d) (hΨ : Adm K) {b S : ℝ} (hb : 0 ≤ b)
    (hS : b / normMin (gauge K) ≤ S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, max (b - (gauge K) y) 0 =
      normBallVolume (gauge K) * b ^ (d + 1) / (d + 1) := by
  obtain ⟨hc, hle⟩ := hΨ.normMin_pos_mul_le hd
  have hcont : Continuous (gauge K) := hΨ.continuous
  have hnn : ∀ y, 0 ≤ (gauge K) y := hΨ.nonneg
  have hfcont : Continuous fun y : EuclideanSpace ℝ (Fin d) => max (b - (gauge K) y) 0 :=
    (continuous_const.sub hcont).max continuous_const
  have hfzero : ∀ y : EuclideanSpace ℝ (Fin d), S ≤ ‖y‖ → max (b - (gauge K) y) 0 = 0 := by
    intro y hy
    have hby : b ≤ (gauge K) y := by
      calc b = (b / normMin (gauge K)) * normMin (gauge K) := (div_mul_cancel₀ b hc.ne').symm
        _ ≤ ‖y‖ * normMin (gauge K) := mul_le_mul_of_nonneg_right (hS.trans hy) hc.le
        _ = normMin (gauge K) * ‖y‖ := mul_comm _ _
        _ ≤ (gauge K) y := hle y
    exact max_eq_right (by linarith)
  have hint : Integrable fun y : EuclideanSpace ℝ (Fin d) => max (b - (gauge K) y) 0 := by
    refine hfcont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S) ?_)
    intro y hy
    refine hfzero y ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact hy.le
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hfzero y (by
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hy
    exact hy)),
    hint.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun y => le_max_right _ _)]
  have hlayer : ∀ t ∈ Set.Ioi (0 : ℝ),
      volume.real {a : EuclideanSpace ℝ (Fin d) | t < max (b - (gauge K) a) 0} =
        (max (b - t) 0) ^ d * normBallVolume (gauge K) := by
    intro t ht
    have ht0 : 0 < t := ht
    rcases lt_or_ge t b with htb | htb
    · have hset : {a : EuclideanSpace ℝ (Fin d) | t < max (b - (gauge K) a) 0} =
          {a | (gauge K) a < b - t} := by
        ext a
        simp only [Set.mem_setOf_eq, lt_max_iff]
        constructor
        · rintro (h | h)
          · linarith
          · linarith
        · intro h
          exact Or.inl (by linarith)
      rw [hset, BallFacts.real_volume_sublevel hd hΨ (by linarith),
        max_eq_left (by linarith : 0 ≤ b - t)]
    · have hset : {a : EuclideanSpace ℝ (Fin d) | t < max (b - (gauge K) a) 0} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, lt_max_iff, Set.mem_empty_iff_false, iff_false, not_or,
          not_lt]
        exact ⟨by linarith [hnn a], ht0.le⟩
      rw [hset, max_eq_right (by linarith : b - t ≤ 0), zero_pow (by omega)]
      simp
  have hsd : ∫ t in Set.Ioi (0 : ℝ), (max (b - t) 0) ^ d * normBallVolume (gauge K) =
      ∫ t in Set.Ioc (0 : ℝ) b, (max (b - t) 0) ^ d * normBallVolume (gauge K) := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      Set.Ioc_subset_Ioi_self (Filter.Eventually.of_forall fun t ht => ?_)
    have hbt : b < t := by
      by_contra h
      exact ht.2 ⟨ht.1, not_lt.mp h⟩
    rw [max_eq_right (by linarith : b - t ≤ 0), zero_pow (by omega), zero_mul]
  have hcongr : ∫ t in (0 : ℝ)..b, (max (b - t) 0) ^ d * normBallVolume (gauge K) =
      ∫ t in (0 : ℝ)..b, (b - t) ^ d * normBallVolume (gauge K) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hb] at ht
    rw [max_eq_left (by linarith [ht.2])]
  rw [setIntegral_congr_fun measurableSet_Ioi hlayer, hsd, ← intervalIntegral.integral_of_le hb,
    hcongr, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ d) b, sub_self, sub_zero,
    integral_pow, zero_pow (Nat.succ_ne_zero d), sub_zero]
  ring

/-- Volume of a set `E ⊆ {b ≤ ψ}` in terms of the integral of `ψ - b` over `E`: the part of `E`
below level `b + s` lies in a shell of volume `|B_ψ| ((b + s) ^ d - b ^ d)`, and the rest is
controlled by Markov's inequality. -/
private theorem volume_excess_le (hd : 1 ≤ d) (hΨ : Adm K) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b : ℝ} (hb : 0 ≤ b)
    (hEsub : E ⊆ {v | b ≤ (gauge K) v}) {s : ℝ} (hs : 0 < s) :
    (volume E).toReal ≤ normBallVolume (gauge K) * ((b + s) ^ d - b ^ d) +
      (∫ v in E, ((gauge K) v - b)) / s := by
  have hcont : Continuous (gauge K) := hΨ.continuous
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  set A : Set (EuclideanSpace ℝ (Fin d)) := {v | (gauge K) v < b + s} with hA
  set B : Set (EuclideanSpace ℝ (Fin d)) := {v | (gauge K) v < b} with hB
  have hAm : MeasurableSet A := measurableSet_normSublevel hΨ _
  have hBm : MeasurableSet B := measurableSet_normSublevel hΨ _
  have hAfin : volume A ≠ ⊤ := BallFacts.volume_sublevel_ne_top hd hΨ _
  have hAvol : volume.real A = (b + s) ^ d * normBallVolume (gauge K) :=
    BallFacts.real_volume_sublevel hd hΨ (by linarith)
  have hBvol : volume.real B = b ^ d * normBallVolume (gauge K) :=
    BallFacts.real_volume_sublevel hd hΨ hb
  have hsplit : volume.real (E ∩ A) + volume.real (E \ A) = volume.real E :=
    measureReal_inter_add_sdiff hAm hEfin
  have hE₁ : volume.real (E ∩ A) ≤ normBallVolume (gauge K) * ((b + s) ^ d - b ^ d) := by
    have hsub : E ∩ A ⊆ A \ B := fun v hv => ⟨hv.2, fun hvB => by
      have h₁ : b ≤ (gauge K) v := hEsub hv.1
      have h₂ : (gauge K) v < b := hvB
      linarith⟩
    have hBA : B ⊆ A := fun v hv => lt_trans hv (by linarith : b < b + s)
    calc volume.real (E ∩ A) ≤ volume.real (A \ B) := measureReal_mono hsub
          (measure_ne_top_of_subset Set.sdiff_subset hAfin)
      _ = (b + s) ^ d * normBallVolume (gauge K) - b ^ d * normBallVolume (gauge K) := by
          rw [measureReal_sdiff hBA hBm hAfin, hAvol, hBvol]
      _ = normBallVolume (gauge K) * ((b + s) ^ d - b ^ d) := by ring
  have hint : IntegrableOn (fun v => (gauge K) v - b) E volume :=
    BallFacts.integrableOn_of_isBounded (hcont.sub continuous_const) hEb
  have hE₂ : s * volume.real (E \ A) ≤ ∫ v in E, ((gauge K) v - b) := by
    have hE₂m : MeasurableSet (E \ A) := hE.diff hAm
    have hE₂fin : volume (E \ A) ≠ ⊤ := measure_ne_top_of_subset Set.sdiff_subset hEfin
    calc s * volume.real (E \ A) = ∫ _ in E \ A, s := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ v in E \ A, ((gauge K) v - b) := by
          refine setIntegral_mono_on (integrableOn_const hE₂fin)
            (hint.mono_set Set.sdiff_subset) hE₂m fun v hv => ?_
          have : b + s ≤ (gauge K) v := not_lt.mp hv.2
          linarith
      _ ≤ ∫ v in E, ((gauge K) v - b) := by
          refine setIntegral_mono_set hint ?_ (Set.sdiff_subset.eventuallyLE)
          rw [Filter.EventuallyLE, ae_restrict_iff' hE]
          refine Filter.Eventually.of_forall fun v hv => ?_
          have : b ≤ (gauge K) v := hEsub hv
          simp only [Pi.zero_apply]
          linarith
  have hE₂' : volume.real (E \ A) ≤ (∫ v in E, ((gauge K) v - b)) / s := by
    rw [le_div_iff₀ hs, mul_comm]
    exact hE₂
  have hreal : (volume E).toReal = volume.real E := rfl
  rw [hreal, ← hsplit]
  exact add_le_add hE₁ hE₂'

/-! ## The inner radius and the contact point -/

/-- The cell set of a path started at the origin, run for at least one step, contains the ball
of radius `1 / 2`: it contains the cell of the origin. -/
private theorem ball_subset_cellSet (X : ℕ → Site d) (n : ℕ) (hX0 : X 0 = 0) (hn : 1 ≤ n) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) ⊆ cellSet X n := by
  intro v hv
  have h0 : (0 : Site d) ∈ departureRange X n :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), hX0⟩
  refine Set.mem_iUnion₂.mpr ⟨0, h0, fun i => ?_⟩
  have hcoord : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  have hv' : ‖v‖ < 1 / 2 := mem_ball_zero_iff.mp hv
  have habs := abs_lt.mp (lt_of_le_of_lt hcoord hv')
  simp only [Pi.zero_apply, Int.cast_zero]
  constructor <;> linarith [habs.1, habs.2]

/-- The inner radius `inf_{y ∉ D} ψ(y)` of a bounded set containing a ball about the origin is
positive, the sublevel set of `ψ` at that radius lies in `D`, and the infimum is attained in the
closure of the complement. -/
private theorem inradius_facts (hd : 1 ≤ d) (hΨ : Adm K) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDb : Bornology.IsBounded D) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ D) :
    0 < sInf ((gauge K) '' Dᶜ) ∧ {v | (gauge K) v < sInf ((gauge K) '' Dᶜ)} ⊆ D ∧
      ∃ y₀ : EuclideanSpace ℝ (Fin d), (gauge K) y₀ = sInf ((gauge K) '' Dᶜ) ∧ y₀ ∈ closure Dᶜ := by
  obtain ⟨hc, hle⟩ := hΨ.normMin_pos_mul_le hd
  have hcont : Continuous (gauge K) := hΨ.continuous
  have hnn : ∀ y, 0 ≤ (gauge K) y := hΨ.nonneg
  have hne : (Dᶜ).Nonempty := by
    haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
    rw [Set.nonempty_compl]
    rintro rfl
    exact NormedSpace.unbounded_univ ℝ _ hDb
  have hbdd : BddBelow ((gauge K) '' Dᶜ) := ⟨0, by rintro _ ⟨y, _, rfl⟩; exact hnn y⟩
  have hge : ∀ y ∈ Dᶜ, sInf ((gauge K) '' Dᶜ) ≤ (gauge K) y := fun y hy =>
    csInf_le hbdd (Set.mem_image_of_mem (gauge K) hy)
  have hpos : 0 < sInf ((gauge K) '' Dᶜ) := by
    refine lt_of_lt_of_le (mul_pos hc hρ) (le_csInf (hne.image (gauge K)) ?_)
    rintro _ ⟨y, hy, rfl⟩
    have hyρ : ρ ≤ ‖y‖ := by
      by_contra h
      exact hy (hball (mem_ball_zero_iff.mpr (not_le.mp h)))
    calc normMin (gauge K) * ρ ≤ normMin (gauge K) * ‖y‖ := mul_le_mul_of_nonneg_left hyρ hc.le
      _ ≤ (gauge K) y := hle y
  refine ⟨hpos, fun v hv => ?_, ?_⟩
  · by_contra hvD
    exact absurd (hge v hvD) (not_le.mpr hv)
  · set Kc : Set (EuclideanSpace ℝ (Fin d)) := closure Dᶜ ∩
      {y | (gauge K) y ≤ sInf ((gauge K) '' Dᶜ) + 1} with hK
    have hKclosed : IsClosed Kc := isClosed_closure.inter (isClosed_le hcont continuous_const)
    have hKsub : Kc ⊆ Metric.closedBall 0 ((sInf ((gauge K) '' Dᶜ) + 1) / normMin (gauge K)) := by
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc]
      calc ‖y‖ * normMin (gauge K) = normMin (gauge K) * ‖y‖ := mul_comm _ _
        _ ≤ (gauge K) y := hle y
        _ ≤ sInf ((gauge K) '' Dᶜ) + 1 := hy.2
    have hKcpt : IsCompact Kc := (isCompact_closedBall _ _).of_isClosed_subset hKclosed hKsub
    have hlt : ∀ η : ℝ, 0 < η → ∃ y ∈ Dᶜ, (gauge K) y < sInf ((gauge K) '' Dᶜ) + η := fun η hη => by
      obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image (gauge K))
        (by linarith : sInf ((gauge K) '' Dᶜ) < sInf ((gauge K) '' Dᶜ) + η)
      exact ⟨y, hy, hlt⟩
    obtain ⟨y₁, hy₁, hy₁lt⟩ := hlt 1 one_pos
    have hKne : Kc.Nonempty := ⟨y₁, subset_closure hy₁, hy₁lt.le⟩
    obtain ⟨y₀, hy₀K, hmin⟩ := hKcpt.exists_isMinOn hKne hcont.continuousOn
    have hclosed : closure Dᶜ ⊆ {y | sInf ((gauge K) '' Dᶜ) ≤ (gauge K) y} :=
      closure_minimal hge (isClosed_le continuous_const hcont)
    have hy₀ge : sInf ((gauge K) '' Dᶜ) ≤ (gauge K) y₀ := hclosed hy₀K.1
    refine ⟨y₀, le_antisymm ?_ hy₀ge, hy₀K.1⟩
    by_contra hgt
    have hgt' : sInf ((gauge K) '' Dᶜ) < (gauge K) y₀ := not_le.mp hgt
    obtain ⟨y, hy, hylt⟩ := hlt (min (((gauge K) y₀ - sInf ((gauge K) '' Dᶜ)) / 2) 1)
      (lt_min (by linarith) one_pos)
    have hyK : y ∈ Kc := ⟨subset_closure hy, (hylt.trans_le (by
      linarith [min_le_right (((gauge K) y₀ - sInf ((gauge K) '' Dᶜ)) / 2) 1])).le⟩
    have h₁ := isMinOn_iff.mp hmin y hyK
    linarith [min_le_left (((gauge K) y₀ - sInf ((gauge K) '' Dᶜ)) / 2) 1]

/-- The inner radius `inf_{y ∉ D} ψ(y)` of a set `D ⊆ B(0, R)` containing a ball about the
origin is at most `Λ_ψ R`. -/
private theorem inradius_le (hd : 1 ≤ d) (hΨ : Adm K) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDb : Bornology.IsBounded D) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ D) {R : ℝ}
    (hDR : D ⊆ Metric.ball 0 R) : sInf ((gauge K) '' Dᶜ) ≤ normMax (gauge K) * R := by
  obtain ⟨hpos, hsub, -⟩ := inradius_facts hd hΨ hDb hρ hball
  have hΛ := BallFacts.normMax_pos' hd hΨ
  have hR : 0 < R := by
    have h0 := hDR (hball (Metric.mem_ball_self hρ))
    rwa [mem_ball_zero_iff, norm_zero] at h0
  have hcontain : Metric.ball (0 : EuclideanSpace ℝ (Fin d))
      (sInf ((gauge K) '' Dᶜ) / normMax (gauge K)) ⊆
      Metric.ball 0 R := (ball_subset_normSublevel hd hΨ).trans (hsub.trans hDR)
  have hle : sInf ((gauge K) '' Dᶜ) / normMax (gauge K) ≤ R := by
    by_contra h
    have hlt : R < sInf ((gauge K) '' Dᶜ) / normMax (gauge K) := not_le.mp h
    set u : EuclideanSpace ℝ (Fin d) := coordVec (⟨0, by omega⟩ : Fin d) with hu
    have hun : ‖u‖ = 1 := by simp [hu, coordVec, PiLp.norm_single]
    set t : ℝ := (R + sInf ((gauge K) '' Dᶜ) / normMax (gauge K)) / 2 with ht
    have hyn : ‖t • u‖ = t := by
      rw [norm_smul, hun, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hmem : t • u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d))
        (sInf ((gauge K) '' Dᶜ) / normMax (gauge K)) := by
      rw [mem_ball_zero_iff, hyn]
      linarith
    have := mem_ball_zero_iff.mp (hcontain hmem)
    rw [hyn] at this
    linarith
  rw [div_le_iff₀ hΛ] at hle
  linarith

end Rates
namespace Rates.PotentialSplit
open CERW CERW.Generic.Kernel

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
/-- A measurable field weighted by the Newtonian kernel has a measurable integrand. -/
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
          rw [mul_div_assoc, CERW.Support.Geometry.div_pow_eq_rpow_sub hw d]

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

/-- On a set of finite volume the integrand `∇ψ(v) · (v - y) |v - y|^{-d}` of the potential of a
norm is integrable. -/
private lemma integrableOn_gradientIntegrand (hd : 1 ≤ d) (hΨ : Adm K)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d) D :=
  integrableOn_fieldIntegrand hd (measurable_gradient (gauge K)) (hΨ.norm_gradient_le) hD hDfin y

/-- Splitting the potential of a norm over a measurable subset of finite volume. -/
private lemma normPotential_sdiff (hd : 1 ≤ d) (hΨ : Adm K) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε (gauge K) D y = normPotential d ε (gauge K) A y +
        normPotential d ε (gauge K) (D \ A) y := by
  have hF := integrableOn_gradientIntegrand hd hΨ hD hDfin y
  have hFA := hF.mono_set hAD
  have hFE := hF.mono_set (Set.sdiff_subset : D \ A ⊆ D)
  have hsplit : ∫ v in D, inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d =
      (∫ v in A, inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d) +
      (∫ v in D \ A, inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d) := by
    conv_lhs => rw [← Set.union_sdiff_cancel hAD]
    exact setIntegral_union Set.disjoint_sdiff_right (hD.diff hA) hFA hFE
  unfold normPotential
  rw [hsplit]
  ring

/-- A norm is integrable (minus a constant) on every bounded set. -/
private lemma integrableOn_sub_const (hΨ : Adm K) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hEb : Bornology.IsBounded E) (b : ℝ) : IntegrableOn (fun v => (gauge K) v - b) E := by
  obtain ⟨r, hr⟩ := hEb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hc : ContinuousOn (fun v => (gauge K) v - b) (Metric.closedBall 0 r) :=
    ((hΨ.continuous).sub continuous_const).continuousOn
  exact (hc.integrableOn_compact (isCompact_closedBall 0 r)).mono_set hr

/-- The potential of a set `E ⊆ {b ≤ ψ}` is at most `2dεa` plus the geometric bound for the part of
`E` where `ψ > b + a`, whose volume is at most `(∫_E (ψ - b)) / a`. -/
private lemma abs_potential_le_layer_add_tail (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ}
    (hε : 0 < ε) {Cg : ℝ} (hCg0 : 0 ≤ Cg)
    (hCg : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |normPotential d ε (gauge K) D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d))
    {b : ℝ} (hb : 0 ≤ b) {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hEb : Bornology.IsBounded E) (hEsub : E ⊆ {v | b ≤ (gauge K) v}) (y : EuclideanSpace ℝ (Fin d))
    {a : ℝ} (ha : 0 < a) :
    |normPotential d ε (gauge K) E y| ≤
      2 * d * ε * a + Cg * ε * ((∫ v in E, ((gauge K) v - b)) / a) ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  have hΨc : Continuous (gauge K) := hΨ.continuous
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  have hE₁m : MeasurableSet (E ∩ {v | (gauge K) v ≤ b + a}) :=
    hE.inter (measurableSet_le hΨc.measurable measurable_const)
  have hsplit := normPotential_sdiff hd1 hΨ (ε := ε) hE₁m hE hEfin Set.inter_subset_left y
  have h1 : |normPotential d ε (gauge K) (E ∩ {v | (gauge K) v ≤ b + a}) y| ≤ 2 * d * ε * a :=
    gauge_layer_potential hd hΨ.compact hΨ.convex hΨ.zero_mem hε hb ha hE₁m
        (fun v hv => ⟨hEsub hv.1, hv.2⟩) y
  have hE₂m : MeasurableSet (E \ (E ∩ {v | (gauge K) v ≤ b + a})) := hE.diff hE₁m
  have hE₂sub : E \ (E ∩ {v | (gauge K) v ≤ b + a}) ⊆ E := Set.sdiff_subset
  have hE₂b : Bornology.IsBounded (E \ (E ∩ {v | (gauge K) v ≤ b + a})) := hEb.subset hE₂sub
  have hE₂fin : volume (E \ (E ∩ {v | (gauge K) v ≤ b + a})) ≠ ⊤ := hE₂b.measure_lt_top.ne
  have h2 := hCg _ hE₂m hE₂b y
  have hint : IntegrableOn (fun v => (gauge K) v - b) E := integrableOn_sub_const hΨ hEb b
  have hmarkov : a * (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal ≤ ∫ v in E,
      ((gauge K) v - b) := by
    calc a * (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal
        = ∫ _v in E \ (E ∩ {v | (gauge K) v ≤ b + a}), a := by
          rw [setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
      _ ≤ ∫ v in E \ (E ∩ {v | (gauge K) v ≤ b + a}), ((gauge K) v - b) := by
          refine setIntegral_mono_on (integrableOn_const hE₂fin) (hint.mono_set hE₂sub) hE₂m ?_
          intro v hv
          have hlt : b + a < (gauge K) v := by
            by_contra hcon
            exact hv.2 ⟨hv.1, not_lt.mp hcon⟩
          linarith
      _ ≤ ∫ v in E, ((gauge K) v - b) := by
          refine setIntegral_mono_set hint ?_ (Set.sdiff_subset : _ ⊆ E).eventuallyLE
          filter_upwards [ae_restrict_mem hE] with v hv
          exact sub_nonneg.mpr (hEsub hv)
  have hvol : (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal ≤
      (∫ v in E, ((gauge K) v - b)) / a := by
    rw [le_div_iff₀ ha, mul_comm]
    exact hmarkov
  have hexp : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have h3 : (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal ^ ((1 : ℝ) / d) ≤
      ((∫ v in E, ((gauge K) v - b)) / a) ^ ((1 : ℝ) / d) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hvol hexp
  have h4 : Cg * ε * (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal ^ ((1 : ℝ) / d) ≤
      Cg * ε * ((∫ v in E, ((gauge K) v - b)) / a) ^ ((1 : ℝ) / d) :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg hCg0 hε.le)
  calc |normPotential d ε (gauge K) E y|
      = |normPotential d ε (gauge K) (E ∩ {v | (gauge K) v ≤ b + a}) y +
          normPotential d ε (gauge K) (E \ (E ∩ {v | (gauge K) v ≤ b + a})) y| := by rw [← hsplit]
    _ ≤ |normPotential d ε (gauge K) (E ∩ {v | (gauge K) v ≤ b + a}) y| +
          |normPotential d ε (gauge K) (E \ (E ∩ {v | (gauge K) v ≤ b + a})) y| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 (h2.trans h4)

end Rates.PotentialSplit
namespace Rates
open CERW

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
/-- Splitting the potential of a norm over a measurable subset of finite volume:
`U_D = U_A + U_{D \ A}` for `A ⊆ D`. -/
private theorem normPotential_sdiff_eq (hd : 1 ≤ d) (hΨ : Adm K) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε (gauge K) D y = normPotential d ε (gauge K) A y +
        normPotential d ε (gauge K) (D \ A) y :=
  PotentialSplit.normPotential_sdiff hd hΨ hA hD hDfin hAD y

/-- The excess `∫_{D \ {ψ < b}} (ψ - b)` of a set `D` containing `{ψ < b}` is at most
`(ω_d / (2ε)) (R₁ + R₂)^d U_D(y₀)` at a point `y₀` with `ψ(y₀) = b`: the subgradient inequality at
`y₀` makes `∇ψ(v) · (v - y₀) ≥ ψ(v) - b` on `D \ {ψ < b}`. -/
theorem excess_le_potential (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {b R₁ R₂ : ℝ} (hb : 0 < b) (hDR : D ⊆ Metric.ball 0 R₁)
    (hsub : {v | (gauge K) v < b} ⊆ D) {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : (gauge K) y₀ = b)
    (hy₀R : ‖y₀‖ ≤ R₂) :
    ∫ v in D \ {v | (gauge K) v < b}, ((gauge K) v - b) ≤
      unitBallVolume d / (2 * ε) * (R₁ + R₂) ^ d * normPotential d ε (gauge K) D y₀ := by
  have hd1 : 1 ≤ d := by omega
  have hΨc : Continuous (gauge K) := hΨ.continuous
  have hSm : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | (gauge K) v < b} :=
    measurableSet_lt hΨc.measurable measurable_const
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDR
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hEm : MeasurableSet (D \ {v | (gauge K) v < b}) := hD.diff hSm
  have hEb : Bornology.IsBounded (D \ {v | (gauge K) v < b}) := hDb.subset Set.sdiff_subset
  have hEfin : volume (D \ {v | (gauge K) v < b}) ≠ ⊤ := hEb.measure_lt_top.ne
  have hsplit := PotentialSplit.normPotential_sdiff hd1 hΨ (ε := ε) hSm hD hDfin hsub y₀
  rw [gauge_ball_potential hd hΨ.compact hΨ.convex hΨ.zero_mem ε hb y₀, hy₀, sub_self, max_self,
      mul_zero, zero_add] at hsplit
  have hR₁ : 0 < R₁ := by
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ {v | (gauge K) v < b} := by
      show (gauge K) 0 < b
      rw [hΨ.map_zero]
      exact hb
    simpa using hDR (hsub h0)
  have hR : 0 < R₁ + R₂ := add_pos_of_pos_of_nonneg hR₁ ((norm_nonneg y₀).trans hy₀R)
  have hpt : ∀ᵐ v ∂(volume.restrict (D \ {v | (gauge K) v < b})),
      ((gauge K) v - b) / (R₁ + R₂) ^ d ≤ inner ℝ (gradient (gauge K) v) (v - y₀) /
          ‖v - y₀‖ ^ d := by
    filter_upwards [ae_restrict_mem hEm,
      ae_restrict_of_ae (hΨ.ae_differentiableAt)] with v hvE hvdiff
    by_cases hv0 : v = y₀
    · rw [hv0]
      simp [hy₀]
    · have hvb : b ≤ (gauge K) v := not_lt.mp hvE.2
      have hsg := hΨ.gradient_isSubgradient hvdiff y₀
      have hneg : inner ℝ (gradient (gauge K) v) (y₀ - v) =
          -inner ℝ (gradient (gauge K) v) (v - y₀) := by
        rw [← inner_neg_right, neg_sub]
      have hin : (gauge K) v - b ≤ inner ℝ (gradient (gauge K) v) (v - y₀) := by
        rw [hy₀] at hsg
        linarith
      have hvR : ‖v‖ < R₁ := by simpa using hDR hvE.1
      have hnorm : ‖v - y₀‖ ≤ R₁ + R₂ :=
        (norm_sub_le v y₀).trans (by linarith)
      have hpos : 0 < ‖v - y₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv0)
      calc ((gauge K) v - b) / (R₁ + R₂) ^ d
          ≤ inner ℝ (gradient (gauge K) v) (v - y₀) / (R₁ + R₂) ^ d :=
            div_le_div_of_nonneg_right hin (pow_nonneg hR.le d)
        _ ≤ inner ℝ (gradient (gauge K) v) (v - y₀) / ‖v - y₀‖ ^ d :=
            div_le_div_of_nonneg_left (by linarith) (pow_pos hpos d)
              (pow_le_pow_left₀ hpos.le hnorm d)
  have hint1 : IntegrableOn (fun v => ((gauge K) v - b) / (R₁ + R₂) ^ d)
      (D \ {v | (gauge K) v < b}) :=
    (PotentialSplit.integrableOn_sub_const hΨ hEb b).div_const _
  have hint2 := PotentialSplit.integrableOn_gradientIntegrand hd1 hΨ hEm hEfin y₀
  have hle := setIntegral_mono_ae_restrict hint1 hint2 hpt
  rw [integral_div] at hle
  have hPpos : 0 < (R₁ + R₂) ^ d := pow_pos hR d
  have hω := unitBallVolume_pos d
  rw [hsplit]
  unfold normPotential
  rw [div_le_iff₀ hPpos] at hle
  calc ∫ v in D \ {v | (gauge K) v < b}, ((gauge K) v - b)
      ≤ (∫ v in D \ {v | (gauge K) v < b}, inner ℝ (gradient (gauge K) v) (v - y₀) / ‖v - y₀‖ ^ d) *
        (R₁ + R₂) ^ d := hle
    _ = _ := by
        field_simp

/-- The potential of a bounded measurable set `E ⊆ {b ≤ ψ}` is at most `C (∫_E (ψ - b))^{1/(d+1)}`
in absolute value: the layer `{ψ ≤ b + a}` contributes at most `2dεa` and the rest has volume at
most `(∫_E (ψ - b)) / a`; take `a = (∫_E (ψ - b))^{1/(d+1)}`. -/
theorem abs_potential_excess_le (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℝ}, 0 ≤ b → ∀ {E : Set (EuclideanSpace ℝ (Fin d))},
      MeasurableSet E → Bornology.IsBounded E → E ⊆ {v | b ≤ (gauge K) v} →
      ∀ y : EuclideanSpace ℝ (Fin d),
        |normPotential d ε (gauge K) E y| ≤ C *
            (∫ v in E, ((gauge K) v - b)) ^ ((1 : ℝ) / (d + 1)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  obtain ⟨Cg, hCg, hgeo⟩ := gauge_potential_geometry hd hΨ.compact hΨ.convex hΨ.zero_mem
  have hCg' : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |normPotential d ε (gauge K) D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d) :=
    fun D hD hDb y => (hgeo ε hε.le D hD hDb).1 y
  refine ⟨2 * d * ε + Cg * ε + 1, by positivity, ?_⟩
  intro b hb E hE hEb hEsub y
  have hI0 : 0 ≤ ∫ v in E, ((gauge K) v - b) :=
    setIntegral_nonneg hE (fun v hv => sub_nonneg.mpr (hEsub hv))
  have key := fun a (ha : 0 < a) =>
    PotentialSplit.abs_potential_le_layer_add_tail hd hΨ hε hCg.le hCg' hb hE hEb hEsub y ha
  generalize (∫ v in E, ((gauge K) v - b)) = I at hI0 key ⊢
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity), mul_zero]
    refine _root_.le_of_forall_pos_le_add fun δ hδ => ?_
    have hc : 0 < 2 * (d : ℝ) * ε := by positivity
    have hk := key (δ / (2 * d * ε)) (by positivity)
    rw [← h0, zero_div, Real.zero_rpow (one_div_ne_zero hdpos.ne'), mul_zero, add_zero,
      mul_div_cancel₀ _ hc.ne'] at hk
    linarith
  · obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = I ^ ((1 : ℝ) / (d + 1)) := ⟨_, rfl⟩
    have ha : 0 < a := by
      rw [ha_def]
      exact Real.rpow_pos_of_pos hpos _
    have hIa : a ^ (d + 1) = I := by
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      have : (1 : ℝ) / (d + 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [this, Real.rpow_one]
    have hdiv : I / a = a ^ d := by
      rw [← hIa, pow_succ, mul_div_cancel_right₀ _ ha.ne']
    have hrt : (a ^ d) ^ ((1 : ℝ) / d) = a := by
      rw [one_div]
      exact Real.pow_rpow_inv_natCast ha.le (by omega)
    have hk := key a ha
    rw [hdiv, hrt] at hk
    rw [← ha_def]
    calc |normPotential d ε (gauge K) E y| ≤ 2 * d * ε * a + Cg * ε * a := hk
      _ = (2 * d * ε + Cg * ε) * a := by ring
      _ ≤ (2 * d * ε + Cg * ε + 1) * a :=
          mul_le_mul_of_nonneg_right (by linarith) ha.le

end Rates
/-!
## The mass identity for the potential of the gauge

The spherical average of the potential of a bounded set (`eq:newton`) by Fubini and the kernel
average, with Euler's relation `∇ψ(v) · v = ψ(v)`, and the mass identity `∫_{B(0,S)} U_D = 2ε ∫_D ψ`
that determines the inradius from the local-time approximation of the potential.
-/

namespace SphereAverage

open CERW.Generic.Kernel CERW.Support.Geometry Convolution

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- The field potential's integrand, as a function of the sphere point `θ` and the position `v`,
is integrable for the product of the sphere measure and Lebesgue measure restricted to a measurable
set of finite volume. -/
private lemma integrable_fieldPair (hd : 1 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (s : ℝ) :
    Integrable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
        EuclideanSpace ℝ (Fin d) =>
      inner ℝ (g p.2) (p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))) /
        ‖p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))‖ ^ d)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict D)) := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hmeas : Measurable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
      EuclideanSpace ℝ (Fin d) =>
      inner ℝ (g p.2) (p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))) /
        ‖p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))‖ ^ d) := by
    have hsub : Measurable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
        EuclideanSpace ℝ (Fin d) => p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))) :=
      measurable_snd.sub ((measurable_subtype_coe.comp measurable_fst).const_smul s)
    exact ((hg.comp measurable_snd).inner hsub).div (hsub.norm.pow_const d)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun θ =>
    integrableOn_fieldIntegrand hd hg hΛ hD hDfin (s • (θ : EuclideanSpace ℝ (Fin d))), ?_⟩
  refine Integrable.mono' (integrable_const (Λ * (d * unitBallVolume d *
    ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d))))
    hmeas.norm.aestronglyMeasurable.integral_prod_right' ?_
  refine Filter.Eventually.of_forall fun θ => ?_
  obtain ⟨hint, hle⟩ := integrableOn_and_setIntegral_le hd hD hDfin
    (s • (θ : EuclideanSpace ℝ (Fin d)))
  have hint' := integrableOn_fieldIntegrand hd hg hΛ hD hDfin (s • (θ : EuclideanSpace ℝ (Fin d)))
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hle hΛ0)
  rw [← integral_const_mul]
  refine setIntegral_mono hint'.norm (hint.const_mul Λ) fun v => ?_
  rw [Real.norm_eq_abs]
  exact abs_fieldIntegrand_le (hΛ v) v _

/-- Lebesgue-almost every point is nonzero and has norm different from a given radius. -/
private lemma ae_ne_zero_and_norm_ne (hd : 2 ≤ d) (s : ℝ) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ≠ 0 ∧ ‖v‖ ≠ s := by
  haveI : NeZero d := ⟨by omega⟩
  have h0 : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ≠ 0 := by
    rw [ae_iff]
    simp
  have h1 : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ‖v‖ ≠ s := by
    rw [ae_iff]
    have := Measure.addHaar_sphere (volume : Measure (EuclideanSpace ℝ (Fin d))) 0 s
    simpa [Metric.sphere] using this
  filter_upwards [h0, h1] with v hv0 hv1 using ⟨hv0, hv1⟩

/-- The spherical integral of a field potential of `D` at radius `s` is the weighted exterior
integral of the field's radial component, by Fubini and the kernel average. -/
private lemma integral_sphere_fieldPotential (hd : 2 ≤ d) (ε : ℝ)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) {s : ℝ} (hs : 0 < s) :
    ∫ θ, (2 * ε / unitBallVolume d *
        ∫ v in D, inner ℝ (g v) (v - s • (θ : EuclideanSpace ℝ (Fin d))) /
          ‖v - s • (θ : EuclideanSpace ℝ (Fin d))‖ ^ d)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * ε / unitBallVolume d * ∫ v in D,
        (if s < ‖v‖ then d * unitBallVolume d * (inner ℝ (g v) v / ‖v‖ ^ d) else 0) := by
  have hnull := ae_ne_zero_and_norm_ne hd s
  rw [integral_const_mul]
  congr 1
  rw [integral_integral_swap (integrable_fieldPair (by omega) hg hΛ hD hDfin s)]
  refine setIntegral_congr_ae hD (hnull.mono fun v hv _ => ?_)
  have h := integral_sphere_inner_newtonField_vec hd hv.1 hs hv.2 (g v)
  simp_rw [inner_newtonField] at h
  exact h

/-- `eq:newton` for a norm: the spherical integral of the norm potential of `D` at radius `s` is
`σ_d` times the exterior integral of `ψ(v)/|v|^d`, using Euler's relation `∇ψ(v) · v = ψ(v)`. -/
private lemma integral_sphere_normPotential (hd : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hΨ : Adm K) (ε : ℝ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDb : Bornology.IsBounded D) {s : ℝ} (hs : 0 < s) :
    ∫ θ, normPotential d ε (gauge K) D (s • (θ : EuclideanSpace ℝ (Fin d)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * ε / unitBallVolume d * (d * unitBallVolume d *
        ∫ v in D ∩ {v | s < ‖v‖}, (gauge K) v / ‖v‖ ^ d) := by
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hset : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖} :=
    measurableSet_lt measurable_const measurable_norm
  have h1 := integral_sphere_fieldPotential hd ε (measurable_gradient (gauge K))
    (hΨ.norm_gradient_le) hD hDfin hs
  unfold normPotential
  rw [h1]
  congr 1
  have heuler : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ∈ D →
      (if s < ‖v‖ then d * unitBallVolume d * (inner ℝ (gradient (gauge K) v) v / ‖v‖ ^ d) else 0) =
        {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖}.indicator
          (fun v => d * unitBallVolume d * ((gauge K) v / ‖v‖ ^ d)) v := by
    filter_upwards [hΨ.ae_differentiableAt] with v hv _
    rw [(hΨ.subgradient_euler (hΨ.gradient_isSubgradient hv)).1, Set.indicator_apply]
    rfl
  rw [setIntegral_congr_ae hD heuler, setIntegral_indicator hset, integral_const_mul]
end SphereAverage

namespace Rates.MassIdentity
open MeasureTheory
open CERW

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
/-- The radial integral of the exchanged weight: for `0 ≤ t ≤ S`,
`∫_0^S 1{r < t} r^{d-1} dr = t^d / d`. -/
private lemma integral_Ioo_indicator_pow (hd : 1 ≤ d) {S t : ℝ} (ht0 : 0 ≤ t) (htS : t ≤ S) :
    ∫ r in Set.Ioo 0 S, (Set.Iio t).indicator (fun r : ℝ => r ^ (d - 1)) r = t ^ d / d := by
  rw [setIntegral_indicator measurableSet_Iio, Set.Ioo_inter_Iio, min_eq_right htS,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht0, integral_pow]
  have h1 : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have h2 : ((d - 1 : ℕ) : ℝ) + 1 = d := by
    rw [Nat.cast_sub hd, Nat.cast_one, sub_add_cancel]
  rw [h1, h2, zero_pow (by omega), sub_zero]

/-- The exchanged weight `r ↦ 1{r < |v|} r^{d-1} ψ(v) |v|^{-d}` integrates over `(0, S)` to
`ψ(v)/d` whenever `|v| ≤ S`. -/
private lemma integral_Ioo_exchange_weighted (hd : 2 ≤ d) (hΨ : Adm K) {S : ℝ}
    (v : EuclideanSpace ℝ (Fin d)) (hvS : ‖v‖ ≤ S) :
    ∫ r in Set.Ioo 0 S, (if r < ‖v‖ then r ^ (d - 1) * ((gauge K) v / ‖v‖ ^ d) else 0) =
        (gauge K) v / d := by
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 : (gauge K) 0 = 0 := hΨ.map_zero
    simp [h0]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hind : ∀ r : ℝ, (if r < ‖v‖ then r ^ (d - 1) * ((gauge K) v / ‖v‖ ^ d) else 0) =
      ((gauge K) v / ‖v‖ ^ d) * (Set.Iio ‖v‖).indicator (fun r : ℝ => r ^ (d - 1)) r := by
    intro r
    by_cases hr : r < ‖v‖
    · simp only [hr, if_true, Set.indicator_of_mem (Set.mem_Iio.mpr hr)]
      ring
    · simp only [hr, if_false, Set.indicator_of_notMem (mt Set.mem_Iio.mp hr), mul_zero]
  simp_rw [hind]
  rw [integral_const_mul, integral_Ioo_indicator_pow (by omega) (norm_nonneg v) hvS]
  have hne : ‖v‖ ^ d ≠ 0 := pow_ne_zero d hvpos.ne'
  field_simp

/-- The exchanged weight is jointly integrable over `(0, S) × D`. -/
private lemma integrable_exchange_weighted (hd : 2 ≤ d) (hΨ : Adm K)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (S : ℝ) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      if p.1 < ‖p.2‖ then p.1 ^ (d - 1) * ((gauge K) p.2 / ‖p.2‖ ^ d) else 0)
      ((volume.restrict (Set.Ioo 0 S)).prod (volume.restrict D)) := by
  have hd1 : 1 ≤ d := by omega
  have hΨm : Measurable (gauge K) := (hΨ.continuous).measurable
  have hmeas : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      if p.1 < ‖p.2‖ then p.1 ^ (d - 1) * ((gauge K) p.2 / ‖p.2‖ ^ d) else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd.norm)
      ((measurable_fst.pow_const _).mul ((hΨm.comp measurable_snd).div
        (measurable_snd.norm.pow_const _))) measurable_const
  have hker : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ))) D := by
    simpa using (CERW.Generic.Kernel.integrableOn_and_setIntegral_le (d := d) hd1 hD hDfin 0).1
  have hbound : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      S ^ (d - 1) * (normMax (gauge K) * ‖p.2‖ ^ (1 - (d : ℝ))))
      ((volume.restrict (Set.Ioo 0 S)).prod (volume.restrict D)) := by
    have hc : Integrable (fun _ : ℝ => S ^ (d - 1)) (volume.restrict (Set.Ioo 0 S)) :=
      integrable_const _
    exact hc.mul_prod (hker.const_mul (normMax (gauge K)))
  refine hbound.mono' hmeas.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (measurableSet_Ioo.prod hD) fun p hp => ?_
  have hnn : 0 ≤ ‖p.2‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hΛ : 0 ≤ normMax (gauge K) :=
    (lt_of_lt_of_le (hΨ.normMin_pos_mul_le hd1).1
      (normMin_gauge_le_normMax_gauge hΨ.compact hΨ.zero_mem hd1)).le
  split_ifs with hlt
  · have hvpos : 0 < ‖p.2‖ := lt_of_le_of_lt hp.1.1.le hlt
    have hΨle : (gauge K) p.2 ≤ normMax (gauge K) * ‖p.2‖ := hΨ.le_normMax_mul p.2
    have hΨ0 : 0 ≤ (gauge K) p.2 := hΨ.nonneg p.2
    have hdiv : (gauge K) p.2 / ‖p.2‖ ^ d ≤ normMax (gauge K) * ‖p.2‖ ^ (1 - (d : ℝ)) := by
      rw [← CERW.Support.Geometry.div_pow_eq_rpow_sub hvpos d, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hΨle (pow_pos hvpos d).le
    have hdiv0 : 0 ≤ (gauge K) p.2 / ‖p.2‖ ^ d := div_nonneg hΨ0 (pow_pos hvpos d).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hp.1.1.le _) hdiv0)]
    exact mul_le_mul (pow_le_pow_left₀ hp.1.1.le hp.1.2.le _) hdiv hdiv0
      (pow_nonneg (hp.1.1.le.trans hp.1.2.le) _)
  · rw [norm_zero]
    exact mul_nonneg (pow_nonneg (hp.1.2.le.trans' hp.1.1.le) _) (mul_nonneg hΛ hnn)

/-- The radial average of the spherical mean: for `D ⊆ B(0, S)`,
`∫_0^S r^{d-1} ∫_{D ∩ {|v| > r}} ψ(v) |v|^{-d} dv dr = d⁻¹ ∫_D ψ`, by Tonelli. -/
private lemma integral_Ioo_pow_mul_weighted (hd : 2 ≤ d) (hΨ : Adm K)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) {S : ℝ}
    (hDS : D ⊆ Metric.ball 0 S) :
    ∫ r in Set.Ioo 0 S, r ^ (d - 1) * ∫ v in D ∩ {v | r < ‖v‖}, (gauge K) v / ‖v‖ ^ d =
      (d : ℝ)⁻¹ * ∫ v in D, (gauge K) v := by
  have hDfin : volume D ≠ ⊤ := (measure_mono hDS |>.trans_lt measure_ball_lt_top).ne
  have hpt : ∀ r : ℝ, r ^ (d - 1) * ∫ v in D ∩ {v | r < ‖v‖}, (gauge K) v / ‖v‖ ^ d =
      ∫ v in D, (if r < ‖v‖ then r ^ (d - 1) * ((gauge K) v / ‖v‖ ^ d) else 0) := by
    intro r
    have hset : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | r < ‖v‖} :=
      measurableSet_lt measurable_const measurable_norm
    have hind : ∀ v : EuclideanSpace ℝ (Fin d),
        (if r < ‖v‖ then r ^ (d - 1) * ((gauge K) v / ‖v‖ ^ d) else 0) =
          {v : EuclideanSpace ℝ (Fin d) | r < ‖v‖}.indicator
            (fun v => r ^ (d - 1) * ((gauge K) v / ‖v‖ ^ d)) v := fun v => by
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    simp_rw [hind]
    rw [setIntegral_indicator hset, integral_const_mul, Set.inter_comm]
  simp_rw [hpt]
  rw [integral_integral_swap (integrable_exchange_weighted hd hΨ hD hDfin S)]
  rw [setIntegral_congr_fun hD fun v hv => integral_Ioo_exchange_weighted hd hΨ v
    (mem_ball_zero_iff.mp (hDS hv)).le, integral_div, inv_mul_eq_div]

/-- `eq:massidentity` for the norm potential: for a bounded measurable `D ⊆ B(0, S)`,
`∫_{B(0,S)} U_D = 2ε ∫_D ψ(v) dv`, by the spherical means of `U_D`. -/
private theorem integral_ball_eq (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {S : ℝ} (hDS : D ⊆ Metric.ball 0 S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, normPotential d ε (gauge K) D y =
      2 * ε * ∫ v in D, (gauge K) v := by
  have hd1 : 1 ≤ d := by omega
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDS
  have hω := unitBallVolume_pos d
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact this.ne'
  obtain ⟨Cd, hCd0, hgeo⟩ := gauge_potential_geometry hd hΨ.compact hΨ.convex hΨ.zero_mem
  have hhol := (hgeo ε hε.le D hD hDb).2
  have hsph : ∀ s : ℝ, 0 < s → ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      normPotential d ε (gauge K) D (s • (θ : EuclideanSpace ℝ (Fin d)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      d * unitBallVolume d * (2 * ε / unitBallVolume d *
        ∫ v in D ∩ {v | s < ‖v‖}, (gauge K) v / ‖v‖ ^ d) := fun s hs => by
    rw [SphereAverage.integral_sphere_normPotential hd hΨ ε hD hDb hs]
    ring
  have hcont : Continuous (normPotential d ε (gauge K) D) :=
    CERW.Support.Geometry.continuous_of_holder_half (by positivity) hhol
  have hint : IntegrableOn (normPotential d ε (gauge K) D) (Metric.ball 0 S) :=
    (hcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
      Metric.ball_subset_closedBall
  have hpolar := CERW.Generic.Newton.integral_eq_integral_Ioi_sphere hd1
    ((integrable_indicator_iff measurableSet_ball).2 hint)
  rw [integral_indicator measurableSet_ball] at hpolar
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      r ^ (d - 1) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S).indicator (normPotential d ε (gauge K) D)
          (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      (Set.Iio S).indicator (fun r : ℝ => r ^ (d - 1) * ∫ θ : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin d)) 1, normPotential d ε (gauge K) D
          (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) r := by
    intro r hr
    have hnorm : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := fun θ => by
      have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
        rw [← dist_zero_right]
        exact Metric.mem_sphere.mp θ.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hθ, mul_one]
    by_cases hrS : r < S
    · rw [Set.indicator_of_mem (Set.mem_Iio.mpr hrS)]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      exact Set.indicator_of_mem (mem_ball_zero_iff.mpr (by rw [hnorm θ]; exact hrS)) _
    · rw [Set.indicator_of_notMem (mt Set.mem_Iio.mp hrS)]
      have hz : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S).indicator (normPotential d ε (gauge K) D)
            (r • (θ : EuclideanSpace ℝ (Fin d))) = 0 := fun θ =>
        Set.indicator_of_notMem (fun h => hrS (by rw [← hnorm θ]; exact mem_ball_zero_iff.mp h)) _
      simp [hz]
  rw [hpolar, setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  have hsph' : ∀ r ∈ Set.Ioo (0 : ℝ) S,
      r ^ (d - 1) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        normPotential d ε (gauge K) D (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * ε * d * (r ^ (d - 1) * ∫ v in D ∩ {v | r < ‖v‖}, (gauge K) v / ‖v‖ ^ d) := by
    intro r hr
    rw [hsph r hr.1]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hsph', integral_const_mul,
    integral_Ioo_pow_mul_weighted hd hΨ hD hDS]
  field_simp

/-- The cell-center map is measurable. -/
private theorem measurable_cellCenter :
    Measurable (cellCenter : EuclideanSpace ℝ (Fin d) → Site d) := by
  rw [measurable_pi_iff]
  intro i
  exact Measurable.floor
    (((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))).add_const (1 / 2))

/-- The cell local time is measurable. -/
private theorem measurable_cellLocalTime (X : ℕ → Site d) (n : ℕ) :
    Measurable (cellLocalTime X n) :=
  (measurable_of_countable (fun x : Site d => (localTime X n x : ℝ))).comp measurable_cellCenter

/-- `|n - ∫_{B(0,S)} U_{D_n}| ≤ ω_d S^d δ` when `D_n ⊆ B(0, S)` and `|ℓ̃_n - U_{D_n}| ≤ δ`
there, for the norm potential. -/
private theorem abs_sub_integral_ball_le (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ}
    (hε : 0 < ε) (X : ℕ → Site d) (n : ℕ)
    {S δ : ℝ} (hS : 0 < S) (hDS : cellSet X n ⊆ Metric.ball 0 S)
    (happrox : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime X n y - normPotential d ε (gauge K) (cellSet X n) y| ≤ δ) :
    |(n : ℝ) - ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        normPotential d ε (gauge K) (cellSet X n) y| ≤ unitBallVolume d * S ^ d * δ := by
  have hDmeas : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDb : Bornology.IsBounded (cellSet X n) := Metric.isBounded_ball.subset hDS
  have hballfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) < ⊤ :=
    measure_ball_lt_top
  have hballmeas : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) :=
    measurableSet_ball
  have hcellint : ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      cellLocalTime X n y = n :=
    CERW.Support.Occupation.setIntegral_cellLocalTime_of_subset X n hballmeas hDS
  obtain ⟨Cd, hCd0, hgeo⟩ := gauge_potential_geometry hd hΨ.compact hΨ.convex hΨ.zero_mem
  have hholder : ∀ y z, |normPotential d ε (gauge K) (cellSet X n) y -
      normPotential d ε (gauge K) (cellSet X n) z| ≤
      Cd * ε * (volume (cellSet X n)).toReal ^ ((1 : ℝ) / (2 * d)) *
        ‖y - z‖ ^ ((1 : ℝ) / 2) := (hgeo ε hε.le _ hDmeas hDb).2
  have hcont : Continuous (normPotential d ε (gauge K) (cellSet X n)) :=
    CERW.Support.Geometry.continuous_of_holder_half (by positivity) hholder
  have hpotint : IntegrableOn (normPotential d ε (gauge K) (cellSet X n))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) :=
    ((hcont.continuousOn).integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
        Metric.ball_subset_closedBall
  have hcellint_on : IntegrableOn (cellLocalTime X n)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) := by
    refine IntegrableOn.of_bound hballfin
      (measurable_cellLocalTime X n).aestronglyMeasurable.restrict (maxLocalTime X n : ℝ) ?_
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (cellLocalTime_nonneg X n v)]
    show (localTime X n (cellCenter v) : ℝ) ≤ (maxLocalTime X n : ℝ)
    exact_mod_cast localTime_le_maxLocalTime X n (cellCenter v)
  have hsub := integral_sub hcellint_on hpotint
  have hmain : ‖∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        (cellLocalTime X n y - normPotential d ε (gauge K) (cellSet X n) y)‖
        = |(n : ℝ) - ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
            normPotential d ε (gauge K) (cellSet X n) y| := by
    rw [hsub, hcellint, Real.norm_eq_abs]
  have hbound : ‖∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        (cellLocalTime X n y - normPotential d ε (gauge K) (cellSet X n) y)‖
        ≤ δ * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal :=
    norm_setIntegral_le_of_norm_le_const hballfin fun y hy => by
      rw [Real.norm_eq_abs]
      exact happrox y hy
  have hvol : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal =
      S ^ d * unitBallVolume d := by
    rw [Measure.addHaar_ball_of_pos (μ := volume) (0 : EuclideanSpace ℝ (Fin d)) hS,
      finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hfinal : δ * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal =
      unitBallVolume d * S ^ d * δ := by
    rw [hvol]
    ring
  rw [← hmain]
  exact hbound.trans_eq hfinal

end Rates.MassIdentity
namespace Rates
open CERW

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
/-! ## The mass identity -/

/-- `eq:massidentity` for the norm potential: `∫_{B(0,S)} U_D = 2ε ∫_D ψ` for a measurable
`D ⊆ B(0, S)`. -/
theorem integral_ball_normPotential (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {S : ℝ} (hDS : D ⊆ Metric.ball 0 S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, normPotential d ε (gauge K) D y =
      2 * ε * ∫ v in D, (gauge K) v :=
  MassIdentity.integral_ball_eq hd hΨ hε hD hDS

/-- The mass error for the norm potential: `|n - 2ε ∫_{D_n} ψ| ≤ ω_d S^d δ` when
`D_n ⊆ B(0, S)` and `|ℓ̃_n - U_{D_n}| ≤ δ` there. -/
private theorem abs_sub_integral_normPotential_le (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ}
    (hε : 0 < ε) (X : ℕ → Site d) (n : ℕ)
    {S δ : ℝ} (hS : 0 < S) (hDS : cellSet X n ⊆ Metric.ball 0 S)
    (happrox : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime X n y - normPotential d ε (gauge K) (cellSet X n) y| ≤ δ) :
    |(n : ℝ) - 2 * ε * ∫ v in cellSet X n, (gauge K) v| ≤ unitBallVolume d * S ^ d * δ := by
  have hDmeas : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  rw [← integral_ball_normPotential hd hΨ hε hDmeas hDS]
  exact MassIdentity.abs_sub_integral_ball_le hd hΨ hε X n hS hDS happrox

/-- The mass of a sublevel set of the norm: `∫_{ψ < b} ψ = d ω_ψ b^{d+1}/(d+1)`, from the
mass identity with `ε = 1` and the explicit potential of the sublevel set. -/
private theorem integral_normSublevel_self (hd : 2 ≤ d) (hΨ : Adm K)
    {b : ℝ} (hb : 0 < b) :
    ∫ v in {v : EuclideanSpace ℝ (Fin d) | (gauge K) v < b}, (gauge K) v =
      d * normBallVolume (gauge K) * b ^ (d + 1) / (d + 1) := by
  have hd1 : 1 ≤ d := by omega
  have hmass := integral_ball_normPotential hd hΨ one_pos (measurableSet_normSublevel hΨ b)
    (normSublevel_subset_ball hd1 hΨ b)
  have hcone := integral_cone hd1 hΨ hb.le (le_refl (b / normMin (gauge K)))
  have hpot : ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / normMin (gauge K)),
      normPotential d 1 (gauge K) {v | (gauge K) v < b} y =
      2 * d * ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / normMin (gauge K)),
        max (b - (gauge K) y) 0 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun y _ => ?_
    rw [gauge_ball_potential hd hΨ.compact hΨ.convex hΨ.zero_mem 1 hb y]
    ring
  rw [hpot, hcone] at hmass
  have hd0 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp at hmass ⊢
  linarith

end Rates
/-!
## The inner radius and the local-time profile for the gauge

The deterministic geometry of the inner radius: the contact bound controls the excess
`∫_E (ψ - b)`, the mass identity controls `b`, and the layer bound controls the profile; combined
with the rates it gives the inner radius and the local-time profile of Proposition 5.1.
-/

namespace Rates
open CERW

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
/-! ## The geometry of the inner radius -/

/-- The deterministic geometry of the inner radius: the contact bound controls the excess
`∫_E (ψ - b)`, the mass identity controls `b`, and the layer bound controls the profile. -/
theorem inner_geometry (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C_L : ℝ, 0 < C_L ∧ ∀ (X : ℕ → Site d) (n : ℕ), X 0 = 0 → 1 ≤ n →
      ∀ {R δ H : ℝ}, cellSet X n ⊆ Metric.ball 0 R →
      (∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R,
        |cellLocalTime X n y - normPotential d ε (gauge K) (cellSet X n) y| ≤ δ) →
      (∀ y₀ : EuclideanSpace ℝ (Fin d), (gauge K) y₀ = normInnerRadius (gauge K) X n →
        y₀ ∈ closure (cellSet X n)ᶜ → normPotential d ε (gauge K) (cellSet X n) y₀ ≤ H) →
      0 < normInnerRadius (gauge K) X n ∧ normInnerRadius (gauge K) X n ≤ normMax (gauge K) * R ∧
      0 ≤ (∫ v in cellSet X n \ {v | (gauge K) v < normInnerRadius (gauge K) X n},
          ((gauge K) v - normInnerRadius (gauge K) X n)) ∧
      ∫ v in cellSet X n \ {v | (gauge K) v < normInnerRadius (gauge K) X n},
          ((gauge K) v - normInnerRadius (gauge K) X n) ≤
        unitBallVolume d / (2 * ε) * ((1 + normMax (gauge K) / normMin (gauge K)) * R) ^ d * H ∧
      (∀ s : ℝ, 0 < s →
        (volume (cellSet X n \ {v | (gauge K) v < normInnerRadius (gauge K) X n})).toReal ≤
          normBallVolume (gauge K) *
              ((normInnerRadius (gauge K) X n + s) ^ d - normInnerRadius (gauge K) X n ^ d) +
            (∫ v in cellSet X n \ {v | (gauge K) v < normInnerRadius (gauge K) X n},
              ((gauge K) v - normInnerRadius (gauge K) X n)) / s) ∧
      |(n : ℝ) - 2 * ε * (d * normBallVolume (gauge K) * normInnerRadius (gauge K) X n ^ (d + 1) /
          (d + 1))| ≤
        unitBallVolume d * R ^ d * δ + 2 * ε * normMax (gauge K) * R *
          (volume (cellSet X n \ {v | (gauge K) v < normInnerRadius (gauge K) X n})).toReal ∧
      ∀ y : EuclideanSpace ℝ (Fin d),
        |cellLocalTime X n y - 2 * d * ε * max (normInnerRadius (gauge K) X n - (gauge K) y) 0| ≤
          δ + C_L * (∫ v in cellSet X n \ {v | (gauge K) v < normInnerRadius (gauge K) X n},
            ((gauge K) v - normInnerRadius (gauge K) X n)) ^ ((1 : ℝ) / (d + 1)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C_L, hCL, hCLb⟩ := abs_potential_excess_le hd hΨ hε
  refine ⟨C_L, hCL, ?_⟩
  intro X n hX0 hn R δ H hDR happrox hcon
  set D : Set (EuclideanSpace ℝ (Fin d)) := cellSet X n with hD
  set b : ℝ := normInnerRadius (gauge K) X n with hb
  have hbdef : b = sInf ((gauge K) '' Dᶜ) := rfl
  have hDmeas : MeasurableSet D := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDR
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hball0 : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) ⊆ D :=
    ball_subset_cellSet X n hX0 hn
  obtain ⟨hb0, hsub, y₀, hy₀, hy₀cl⟩ :=
    inradius_facts hd1 hΨ hDb (ρ := 1 / 2) (by norm_num) hball0
  rw [← hbdef] at hb0 hsub hy₀
  have hbR : b ≤ normMax (gauge K) * R := by
    rw [hbdef]
    exact inradius_le hd1 hΨ hDb (ρ := 1 / 2) (by norm_num) hball0 hDR
  have hR0 : 0 < R := by
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D :=
      hball0 (by rw [Metric.mem_ball, dist_self]; norm_num)
    have := hDR h0
    rwa [Metric.mem_ball, dist_self] at this
  obtain ⟨hc0, hcle⟩ := hΨ.normMin_pos_mul_le hd1
  have hΛc : 0 < normMax (gauge K) := lt_of_lt_of_le hc0
      (normMin_gauge_le_normMax_gauge hΨ.compact hΨ.zero_mem hd1)
  have hy₀R : ‖y₀‖ ≤ normMax (gauge K) / normMin (gauge K) * R := by
    have h1 : normMin (gauge K) * ‖y₀‖ ≤ b := hy₀ ▸ hcle y₀
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    calc ‖y₀‖ * normMin (gauge K) = normMin (gauge K) * ‖y₀‖ := mul_comm _ _
      _ ≤ b := h1
      _ ≤ normMax (gauge K) * R := hbR
  set E : Set (EuclideanSpace ℝ (Fin d)) := D \ {v | (gauge K) v < b} with hE
  have hEmeas : MeasurableSet E := hDmeas.diff (measurableSet_normSublevel hΨ b)
  have hEb : Bornology.IsBounded E := hDb.subset Set.sdiff_subset
  have hEsub : E ⊆ {v | b ≤ (gauge K) v} := fun v hv => (not_lt.mp hv.2 : b ≤ (gauge K) v)
  set I : ℝ := ∫ v in E, ((gauge K) v - b) with hI
  have hΨcont : Continuous (gauge K) := hΨ.continuous
  have hΨint : IntegrableOn (gauge K) D :=
    (hΨcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R)).mono_set
      (hDR.trans Metric.ball_subset_closedBall)
  have hI0 : 0 ≤ I := setIntegral_nonneg hEmeas fun v hv => sub_nonneg.mpr (hEsub hv)
  have hexc := excess_le_potential hd hΨ hε hDmeas (b := b) (R₁ := R)
    (R₂ := normMax (gauge K) / normMin (gauge K) * R) hb0 hDR hsub hy₀ hy₀R
  have hH := hcon y₀ hy₀ hy₀cl
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hcoef : 0 ≤ unitBallVolume d / (2 * ε) *
      (R + normMax (gauge K) / normMin (gauge K) * R) ^ d := by
    positivity
  have hrew : (1 + normMax (gauge K) / normMin (gauge K)) * R = R + normMax (gauge K) /
      normMin (gauge K) * R := by ring
  have hmass := abs_sub_integral_normPotential_le hd hΨ hε X n hR0 hDR happrox
  have hsplit : ∫ v in D, (gauge K) v = (∫ v in {v | (gauge K) v < b}, (gauge K) v) + ∫ v in E,
      (gauge K) v := by
    have hunion : D = {v | (gauge K) v < b} ∪ E := (Set.union_sdiff_cancel hsub).symm
    conv_lhs => rw [hunion]
    exact setIntegral_union (Set.disjoint_sdiff_right) hEmeas
      (hΨint.mono_set hsub) (hΨint.mono_set Set.sdiff_subset)
  have hball_int := integral_normSublevel_self hd hΨ hb0
  have hEΨ0 : 0 ≤ ∫ v in E, (gauge K) v :=
    setIntegral_nonneg hEmeas fun v _ => hΨ.nonneg v
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hDfin (measure_mono Set.sdiff_subset)
  have hEΨle : ∫ v in E, (gauge K) v ≤ normMax (gauge K) * R * (volume E).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := E)
      (f := (gauge K)) (C := normMax (gauge K) * R) (lt_top_iff_ne_top.mpr hEfin) (fun v hv => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hΨ.nonneg v)]
        have h1 := hΨ.le_normMax_mul v
        have h2 : ‖v‖ ≤ R := by
          have := hDR hv.1
          rw [mem_ball_zero_iff] at this
          exact this.le
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hΛc.le))
    rw [Real.norm_eq_abs, abs_of_nonneg hEΨ0, measureReal_def] at this
    linarith [this]
  refine ⟨hb0, hbR, hI0, ?_, ?_, ?_, ?_⟩
  · rw [hrew]
    calc I ≤ unitBallVolume d / (2 * ε) * (R + normMax (gauge K) / normMin (gauge K) * R) ^ d *
          normPotential d ε (gauge K) D y₀ := hexc
      _ ≤ unitBallVolume d / (2 * ε) * (R + normMax (gauge K) / normMin (gauge K) * R) ^ d * H :=
          mul_le_mul_of_nonneg_left hH hcoef
  · intro s hs
    exact volume_excess_le hd1 hΨ hEmeas hEb hb0.le hEsub hs
  · have h1 : (n : ℝ) - 2 * ε * (d * normBallVolume (gauge K) * b ^ (d + 1) / (d + 1)) =
        ((n : ℝ) - 2 * ε * ∫ v in D, (gauge K) v) + 2 * ε * ∫ v in E, (gauge K) v := by
      rw [hsplit, hball_int]
      ring
    rw [h1]
    calc |((n : ℝ) - 2 * ε * ∫ v in D, (gauge K) v) + 2 * ε * ∫ v in E, (gauge K) v|
        ≤ |(n : ℝ) - 2 * ε * ∫ v in D, (gauge K) v| + |2 * ε * ∫ v in E,
            (gauge K) v| := abs_add_le _ _
      _ ≤ unitBallVolume d * R ^ d * δ + 2 * ε * normMax (gauge K) * R * (volume E).toReal := by
          rw [abs_of_nonneg (by positivity : 0 ≤ 2 * ε * ∫ v in E, (gauge K) v)]
          have h2 : 2 * ε * ∫ v in E, (gauge K) v ≤ 2 * ε *
              (normMax (gauge K) * R * (volume E).toReal) :=
            mul_le_mul_of_nonneg_left hEΨle (by positivity)
          have h3 : 2 * ε * (normMax (gauge K) * R * (volume E).toReal) =
              2 * ε * normMax (gauge K) * R * (volume E).toReal := by ring
          linarith [hmass]
  · intro y
    have hδ0 : 0 ≤ δ := by
      have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R :=
        by rw [Metric.mem_ball, dist_self]; exact hR0
      exact (abs_nonneg _).trans (happrox 0 h0)
    have hIp : 0 ≤ I ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hI0 _
    by_cases hyD : y ∈ D
    · have hyball : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R := hDR hyD
      have hloc := happrox y hyball
      have hsp := normPotential_sdiff_eq (ε := ε) hd1 hΨ
        (measurableSet_normSublevel hΨ b) hDmeas hDfin hsub y
      have hUb := gauge_ball_potential hd hΨ.compact hΨ.convex hΨ.zero_mem ε hb0 y
      have hUE := hCLb hb0.le hEmeas hEb hEsub y
      rw [hUb] at hsp
      have hsplit' : cellLocalTime X n y - 2 * d * ε * max (b - (gauge K) y) 0 =
          (cellLocalTime X n y - normPotential d ε (gauge K) D y) +
              normPotential d ε (gauge K) E y := by
        rw [hsp]
        ring
      rw [hsplit']
      calc |(cellLocalTime X n y - normPotential d ε (gauge K) D y) +
          normPotential d ε (gauge K) E y|
          ≤ |cellLocalTime X n y - normPotential d ε (gauge K) D y| +
              |normPotential d ε (gauge K) E y| :=
            abs_add_le _ _
        _ ≤ δ + C_L * I ^ ((1 : ℝ) / (d + 1)) := add_le_add hloc hUE
    · have hloc0 : cellLocalTime X n y = 0 :=
        CERW.Support.Occupation.cellLocalTime_eq_zero_of_not_mem X n hyD
      have hbdd : BddBelow ((gauge K) '' Dᶜ) :=
        ⟨0, by
          rintro _ ⟨v, -, rfl⟩
          exact hΨ.nonneg v⟩
      have hby : b ≤ (gauge K) y := by
        rw [hbdef]
        exact csInf_le hbdd ⟨y, hyD, rfl⟩
      have hmax : max (b - (gauge K) y) 0 = 0 := max_eq_right (by linarith)
      rw [hloc0, hmax]
      simp only [mul_zero, sub_zero, abs_zero]
      exact add_nonneg hδ0 (mul_nonneg hCL.le hIp)

/-! ## The inner radius and the local time profile -/

/-- The rate `q` is nonnegative. -/
private lemma rateQ_nonneg (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 ≤ ℓ) : 0 ≤ rateQ d r ℓ := by
  unfold rateQ
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact div_nonneg hℓ hr.le

/-- The approximation error of the local times is at most a constant times the scale `√r ℓ`
(in the plane) or `√(r ℓ)` (in higher dimension), once `M ≤ C r` and `1 ≤ ℓ ≤ r`. -/
private lemma approx_error_le (d : ℕ) {C_loc C_co M r ℓ : ℝ} (hC_loc : 0 ≤ C_loc)
    (hC_co : 0 ≤ C_co) (hM : M ≤ C_co * r) (hr : 1 ≤ r) (hℓ : 1 ≤ ℓ) (hℓr : ℓ ≤ r) :
    C_loc * ℓ + C_loc * (if d = 2 then Real.sqrt M * ℓ else Real.sqrt (M * ℓ)) ≤
      C_loc * (1 + Real.sqrt C_co) *
        (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) := by
  have hℓ0 : 0 ≤ ℓ := by linarith
  split_ifs with h2
  · have h1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
    have hsq : Real.sqrt M ≤ Real.sqrt C_co * Real.sqrt r := by
      rw [← Real.sqrt_mul hC_co]
      exact Real.sqrt_le_sqrt hM
    have a1 : ℓ ≤ Real.sqrt r * ℓ := le_mul_of_one_le_left hℓ0 h1
    have a2 : Real.sqrt M * ℓ ≤ Real.sqrt C_co * Real.sqrt r * ℓ :=
      mul_le_mul_of_nonneg_right hsq hℓ0
    calc C_loc * ℓ + C_loc * (Real.sqrt M * ℓ)
        ≤ C_loc * (Real.sqrt r * ℓ) + C_loc * (Real.sqrt C_co * Real.sqrt r * ℓ) :=
          add_le_add (mul_le_mul_of_nonneg_left a1 hC_loc)
            (mul_le_mul_of_nonneg_left a2 hC_loc)
      _ = C_loc * (1 + Real.sqrt C_co) * (Real.sqrt r * ℓ) := by ring
  · have a1 : ℓ ≤ Real.sqrt (r * ℓ) := by
      refine (le_abs_self ℓ).trans (Real.abs_le_sqrt ?_)
      calc ℓ ^ 2 = ℓ * ℓ := sq ℓ
        _ ≤ r * ℓ := mul_le_mul_of_nonneg_right hℓr hℓ0
    have hsq : Real.sqrt (M * ℓ) ≤ Real.sqrt C_co * Real.sqrt (r * ℓ) := by
      rw [← Real.sqrt_mul hC_co]
      refine Real.sqrt_le_sqrt ?_
      calc M * ℓ ≤ C_co * r * ℓ := mul_le_mul_of_nonneg_right hM hℓ0
        _ = C_co * (r * ℓ) := by ring
    calc C_loc * ℓ + C_loc * Real.sqrt (M * ℓ)
        ≤ C_loc * Real.sqrt (r * ℓ) + C_loc * (Real.sqrt C_co * Real.sqrt (r * ℓ)) :=
          add_le_add (mul_le_mul_of_nonneg_left a1 hC_loc)
            (mul_le_mul_of_nonneg_left hsq hC_loc)
      _ = C_loc * (1 + Real.sqrt C_co) * Real.sqrt (r * ℓ) := by ring

/-- The inner radius and the local time profile: the geometry of the inner radius combined with
the rates. -/
theorem inner_rates (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε) {C_co C_loc C_c : ℝ}
    (hC_co : 0 < C_co)
    (hC_loc : 0 < C_loc) (hC_c : 0 < C_c) :
    ∃ C_in C_lt r₀ M : ℝ, 0 < C_in ∧ 0 < C_lt ∧ 0 < M ∧
      ∀ (X : ℕ → Site d) (n : ℕ) (r : ℝ), X 0 = 0 → 2 ≤ n →
        r₀ ≤ r → 1 ≤ Real.log n → M * Real.log n ^ (d + 5) ≤ r → (C_co + 1) * r ≤ 2 * n →
        (n : ℝ) = 2 * ε * d * normBallVolume (gauge K) * r ^ (d + 1) / (d + 1) →
        maxRadius X n ≤ C_co * r → (maxLocalTime X n : ℝ) ≤ C_co * r →
        (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
          |cellLocalTime X n y - normPotential d ε (gauge K) (cellSet X n) y| ≤
            C_loc * Real.log n + C_loc * (if d = 2
              then Real.sqrt (maxLocalTime X n) * Real.log n
              else Real.sqrt (maxLocalTime X n * Real.log n))) →
        (∀ y₀ : EuclideanSpace ℝ (Fin d), (gauge K) y₀ = normInnerRadius (gauge K) X n →
          y₀ ∈ closure (cellSet X n)ᶜ →
          normPotential d ε (gauge K) (cellSet X n) y₀ ≤ C_c * r * rateQ d r (Real.log n)) →
        |normInnerRadius (gauge K) X n - r| ≤ C_in * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / 2)) ∧
        ∀ y : EuclideanSpace ℝ (Fin d),
          |cellLocalTime X n y - 2 * d * ε * max (r - (gauge K) y) 0| ≤
            C_lt * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume (gauge K) := normBallVolume_gauge_pos hΨ.compact hΨ.convex
      hΨ.zero_mem
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  obtain ⟨hc0, hcle⟩ := hΨ.normMin_pos_mul_le hd1
  have hΛ : 0 < normMax (gauge K) := lt_of_lt_of_le hc0
      (normMin_gauge_le_normMax_gauge hΨ.compact hΨ.zero_mem hd1)
  obtain ⟨C_L, hCL, hgeoC⟩ := inner_geometry hd hΨ hε
  set Kc : ℝ := C_co + 1 with hK
  have hK0 : 0 < Kc := by linarith
  set C_δ : ℝ := C_loc * (1 + Real.sqrt C_co) with hCδ
  have hCδ0 : 0 < C_δ := mul_pos hC_loc (by linarith [Real.sqrt_nonneg C_co])
  have hCI0 : 0 < unitBallVolume d / (2 * ε) *
      ((1 + normMax (gauge K) / normMin (gauge K)) * Kc) ^ d := by
    positivity
  obtain ⟨C₁, r₁, M₁, hC₁, hM₁, harith⟩ := inner_rates_arith hd hε hV
    (C_R := normMax (gauge K) * Kc) (C_c := C_c) (C_δ := C_δ)
    (C_I := unitBallVolume d / (2 * ε) * ((1 + normMax (gauge K) / normMin (gauge K)) * Kc) ^ d)
    (C_m := unitBallVolume d * Kc ^ d) (C_e := 2 * ε * normMax (gauge K) * Kc)
    (mul_pos hΛ hK0) hC_c hCδ0 hCI0 (mul_pos hω (pow_pos hK0 d))
    (mul_pos (mul_pos (mul_pos two_pos hε) hΛ) hK0)
  obtain ⟨C₂, r₂, M₂, hC₂, hM₂, hprof⟩ := profile_arith hd hε hCL hC₁ hC₁ hCδ0
  refine ⟨C₁, C₂, max (max r₁ r₂) (max 1 (Real.sqrt d)), max (max M₁ M₂) 1, hC₁, hC₂,
    lt_max_of_lt_right one_pos, ?_⟩
  intro X n r hX0 hn hr hℓ hMℓ hK2n hnr hH hMloc happrox hcon
  set ℓ : ℝ := Real.log n with hℓdef
  have hr1 : 1 ≤ r :=
    le_trans (le_trans (le_max_left 1 _) (le_max_right _ _)) hr
  have hrd : Real.sqrt d ≤ r :=
    le_trans (le_trans (le_max_right 1 _) (le_max_right _ _)) hr
  have hr₁ : r₁ ≤ r := le_trans (le_trans (le_max_left r₁ r₂) (le_max_left _ _)) hr
  have hr₂ : r₂ ≤ r := le_trans (le_trans (le_max_right r₁ r₂) (le_max_left _ _)) hr
  have hr0 : 0 < r := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hpowℓ : 0 ≤ ℓ ^ (d + 5) := pow_nonneg hℓ0 _
  have hℓpow : ℓ ^ (d + 5) ≤ r :=
    calc ℓ ^ (d + 5) = 1 * ℓ ^ (d + 5) := (one_mul _).symm
      _ ≤ max (max M₁ M₂) 1 * ℓ ^ (d + 5) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpowℓ
      _ ≤ r := hMℓ
  have hℓr : ℓ ≤ r := (le_self_pow₀ hℓ (by omega)).trans hℓpow
  have hM₁ℓ : M₁ * ℓ ^ (d + 5) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left M₁ M₂) (le_max_left _ _)) hpowℓ) hMℓ
  have hM₂ℓ : M₂ * ℓ ^ (d + 5) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right M₁ M₂) (le_max_left _ _)) hpowℓ) hMℓ
  have hDR : cellSet X n ⊆ Metric.ball 0 (Kc * r) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 X n).trans
      (Metric.ball_subset_ball (by
        have : Kc * r = C_co * r + 1 * r := by rw [hK]; ring
        linarith))
  set δ : ℝ := C_loc * ℓ + C_loc * (if d = 2
      then Real.sqrt (maxLocalTime X n) * ℓ else Real.sqrt (maxLocalTime X n * ℓ)) with hδdef
  have hδapp : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (Kc * r),
      |cellLocalTime X n y - normPotential d ε (gauge K) (cellSet X n) y| ≤ δ := by
    intro y hy
    rw [mem_ball_zero_iff] at hy
    exact happrox y (by linarith)
  have hδ0 : 0 ≤ δ := by
    refine add_nonneg (mul_nonneg hC_loc.le hℓ0) (mul_nonneg hC_loc.le ?_)
    split_ifs
    · exact mul_nonneg (Real.sqrt_nonneg _) hℓ0
    · exact Real.sqrt_nonneg _
  have hδle : δ ≤ C_δ * (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) :=
    approx_error_le d hC_loc.le hC_co.le hMloc hr1 hℓ hℓr
  have hqnn : 0 ≤ rateQ d r ℓ := rateQ_nonneg d hr0 hℓ0
  obtain ⟨hb0, hbR, hI0, hexc, hshell, hmass, hprof'⟩ :=
    hgeoC X n hX0 (by omega) (R := Kc * r) (δ := δ) (H := C_c * r * rateQ d r ℓ) hDR hδapp hcon
  set b : ℝ := normInnerRadius (gauge K) X n with hb
  set E : Set (EuclideanSpace ℝ (Fin d)) := cellSet X n \ {v | (gauge K) v < b} with hE
  set I : ℝ := ∫ v in E, ((gauge K) v - b) with hI
  set Ev : ℝ := (volume E).toReal with hEv
  have hbR' : b ≤ normMax (gauge K) * Kc * r := by
    calc b ≤ normMax (gauge K) * (Kc * r) := hbR
      _ = normMax (gauge K) * Kc * r := by ring
  have hexc' : I ≤ unitBallVolume d / (2 * ε) *
      ((1 + normMax (gauge K) / normMin (gauge K)) * Kc) ^ d * r ^ d *
      (C_c * r * rateQ d r ℓ) := by
    calc I ≤ unitBallVolume d / (2 * ε) *
        ((1 + normMax (gauge K) / normMin (gauge K)) * (Kc * r)) ^ d *
          (C_c * r * rateQ d r ℓ) := hexc
      _ = unitBallVolume d / (2 * ε) *
          ((1 + normMax (gauge K) / normMin (gauge K)) * Kc) ^ d * r ^ d *
          (C_c * r * rateQ d r ℓ) := by
          rw [show (1 + normMax (gauge K) / normMin (gauge K)) * (Kc * r) =
            ((1 + normMax (gauge K) / normMin (gauge K)) * Kc) * r by ring, mul_pow]
          ring
  have hmass' : |(n : ℝ) - 2 * ε * (d * normBallVolume (gauge K) * b ^ (d + 1) / (d + 1))| ≤
      unitBallVolume d * Kc ^ d * r ^ d * δ + 2 * ε * normMax (gauge K) * Kc * r * Ev := by
    calc _ ≤ unitBallVolume d * (Kc * r) ^ d * δ + 2 * ε * normMax (gauge K) * (Kc * r) *
        Ev := hmass
      _ = _ := by rw [mul_pow]; ring
  obtain ⟨hbrate, hIrate⟩ := harith r ℓ b I Ev (C_c * r * rateQ d r ℓ) δ (n : ℝ) hr₁ hℓ hM₁ℓ
    hnr hb0 hbR' hI0 hexc' (mul_nonneg (mul_nonneg hC_c.le hr0.le) hqnn) le_rfl
    ENNReal.toReal_nonneg hshell hδ0 hδle hmass'
  have hprofC := hprof r ℓ b I δ hr₂ hℓ hM₂ℓ hI0 hIrate hbrate hδ0 hδle
  refine ⟨hbrate, fun y => ?_⟩
  have h1 := hprof' y
  have hmx : |max (b - (gauge K) y) 0 - max (r - (gauge K) y) 0| ≤ |b - r| := by
    have := abs_max_sub_max_le_abs (b - (gauge K) y) (r - (gauge K) y) 0
    rwa [show (b - (gauge K) y) - (r - (gauge K) y) = b - r by ring] at this
  have hcoef : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hsplit : cellLocalTime X n y - 2 * d * ε * max (r - (gauge K) y) 0 =
      (cellLocalTime X n y - 2 * d * ε * max (b - (gauge K) y) 0) +
        2 * d * ε * (max (b - (gauge K) y) 0 - max (r - (gauge K) y) 0) := by ring
  rw [hsplit]
  calc |(cellLocalTime X n y - 2 * d * ε * max (b - (gauge K) y) 0) +
        2 * d * ε * (max (b - (gauge K) y) 0 - max (r - (gauge K) y) 0)|
      ≤ |cellLocalTime X n y - 2 * d * ε * max (b - (gauge K) y) 0| +
        |2 * d * ε * (max (b - (gauge K) y) 0 - max (r - (gauge K) y) 0)| := abs_add_le _ _
    _ ≤ (δ + C_L * I ^ ((1 : ℝ) / (d + 1))) + 2 * d * ε * |b - r| := by
        refine add_le_add h1 ?_
        rw [abs_mul, abs_of_nonneg hcoef]
        exact mul_le_mul_of_nonneg_left hmx hcoef
    _ ≤ C₂ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) := by linarith

end Rates
/-!
## The outer crossing lemma for the gauge

`lem:outer-crossing` for a deterministic path of the walk with a drift field `ξ` that is a selection
of subgradients of the gauge of a compact convex body: the ramp martingales, the level inequality,
the recurrence along every second level and the last-entrance crossing. The argument involves the
drift only through the bound `ε |ξ_i(z)| ≤ 1/d`, which the two-sided coordinate bounds of the gauge
give.
-/

namespace Outer

section Ramp

variable {d : ℕ}

/-- The embedding of lattice sites is additive. -/
private lemma toSpace_add (x y : Site d) : toSpace (x + y) = toSpace x + toSpace y := by
  ext i
  simp [toSpace]

/-- A unit step changes a projection `q · z` by at most `‖q‖`. -/
private lemma abs_inner_toSpace_le (q : EuclideanSpace ℝ (Fin d)) {e : Site d}
    (he : e ∈ unitSteps d) : |inner ℝ q (toSpace e)| ≤ ‖q‖ := by
  calc |inner ℝ q (toSpace e)| ≤ ‖q‖ * ‖toSpace e‖ := abs_real_inner_le_norm _ _
    _ = ‖q‖ := by
      rw [norm_toSpace, CERW.Support.Law.euclidNorm_of_mem_unitSteps he, mul_one]

/-- A nearest-neighbour path started at the origin satisfies `‖x_j‖ ≤ j`. -/
private lemma norm_toSpace_le_index (x : ℕ → Site d) (hx0 : x 0 = 0)
    (hstep : ∀ j, x (j + 1) - x j ∈ unitSteps d) (j : ℕ) : ‖toSpace (x j)‖ ≤ j := by
  induction j with
  | zero => simp [hx0, CERW.Support.Occupation.toSpace_zero]
  | succ j ih =>
    have h1 : toSpace (x (j + 1)) = toSpace (x j) + toSpace (x (j + 1) - x j) := by
      rw [← toSpace_add]
      congr 1
      abel
    rw [h1]
    calc ‖toSpace (x j) + toSpace (x (j + 1) - x j)‖
        ≤ ‖toSpace (x j)‖ + ‖toSpace (x (j + 1) - x j)‖ := norm_add_le _ _
      _ ≤ ((j + 1 : ℕ) : ℝ) := by
          rw [norm_toSpace (x (j + 1) - x j),
            CERW.Support.Law.euclidNorm_of_mem_unitSteps (hstep j)]
          push_cast
          linarith

/-- The ramp `z ↦ (q · z - a)₊`. -/
private noncomputable def ramp (q : EuclideanSpace ℝ (Fin d)) (a : ℝ) (z : Site d) : ℝ :=
  max (inner ℝ q (toSpace z) - a) 0

/-- One unit step changes the ramp by at most `‖q‖`. -/
private lemma abs_ramp_step_le (q : EuclideanSpace ℝ (Fin d)) (a : ℝ) (z : Site d) {e : Site d}
    (he : e ∈ unitSteps d) : |ramp q a (z + e) - ramp q a z| ≤ ‖q‖ := by
  unfold ramp
  calc |max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0|
      ≤ |(inner ℝ q (toSpace (z + e)) - a) - (inner ℝ q (toSpace z) - a)| :=
        abs_max_sub_max_le_abs _ _ _
    _ = |inner ℝ q (toSpace e)| := by
        rw [toSpace_add, inner_add_right]
        congr 1
        ring
    _ ≤ ‖q‖ := abs_inner_toSpace_le q he

/-- At `z` with `q · z ≥ a + Λ` the ramp is linear across every unit step. -/
private lemma ramp_step_of_top {q : EuclideanSpace ℝ (Fin d)} {a Λ : ℝ} (hq : ‖q‖ ≤ Λ)
    {z e : Site d} (he : e ∈ unitSteps d) (hz : a + Λ ≤ inner ℝ q (toSpace z)) :
    ramp q a (z + e) - ramp q a z = inner ℝ q (toSpace e) := by
  have h2 := abs_le.mp ((abs_inner_toSpace_le q he).trans hq)
  unfold ramp
  rw [toSpace_add, inner_add_right, max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

/-- At `z` with `q · z ≤ a - Λ` the ramp vanishes after every unit step. -/
private lemma ramp_step_of_bottom {q : EuclideanSpace ℝ (Fin d)} {a Λ : ℝ} (hq : ‖q‖ ≤ Λ)
    {z e : Site d} (he : e ∈ unitSteps d) (hz : inner ℝ q (toSpace z) ≤ a - Λ) :
    ramp q a (z + e) - ramp q a z = 0 := by
  have h2 := abs_le.mp ((abs_inner_toSpace_le q he).trans hq)
  unfold ramp
  rw [toSpace_add, inner_add_right, max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- Above the level `a + Λ`, the mean increment of the ramp is minus `ε q · ξ` at a first
departure from a nonzero site and zero otherwise. -/
private lemma stepMean_ramp_of_top {q : EuclideanSpace ℝ (Fin d)} {a Λ : ℝ} (hq : ‖q‖ ≤ Λ)
    (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (j : ℕ)
    (hz : a + Λ ≤ inner ℝ q (toSpace (x j))) :
    stepMean (driftStepProb d ε ξ) (ramp q a) x j =
      -(if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then
        ε * inner ℝ q (ξ (x j)) else 0) := by
  unfold stepMean
  have hterm : ∀ e ∈ unitSteps d,
      driftStepProb d ε ξ x j e * (ramp q a (x j + e) - ramp q a (x j)) =
        inner ℝ q (driftStepProb d ε ξ x j e • toSpace e) := by
    intro e he
    rw [ramp_step_of_top hq he hz, real_inner_smul_right]
  rw [Finset.sum_congr rfl hterm, ← inner_sum]
  by_cases h : x j ≠ 0 ∧ x j ∉ (Finset.range j).image x
  · have hsum : ∑ e ∈ unitSteps d, driftStepProb d ε ξ x j e • toSpace e =
        -(ε • ξ (x j)) := by
      simp only [driftStepProb, if_pos h]
      exact CERW.Support.Drift.sum_driftFirstStep_smul ε (ξ (x j))
    rw [hsum, if_pos h, inner_neg_right, real_inner_smul_right]
  · have hsum : ∑ e ∈ unitSteps d, driftStepProb d ε ξ x j e • toSpace e = 0 := by
      simp only [driftStepProb, if_neg h]
      exact CERW.Support.Law.sum_srwStep_smul
    rw [hsum, if_neg h, inner_zero_right, neg_zero]

/-- Below the level `a - Λ`, the mean increment of the ramp is zero. -/
private lemma stepMean_ramp_of_bottom {q : EuclideanSpace ℝ (Fin d)} {a Λ : ℝ} (hq : ‖q‖ ≤ Λ)
    (p : (ℕ → Site d) → ℕ → Site d → ℝ) (x : ℕ → Site d) (j : ℕ)
    (hz : inner ℝ q (toSpace (x j)) ≤ a - Λ) : stepMean p (ramp q a) x j = 0 := by
  unfold stepMean
  refine Finset.sum_eq_zero fun e he => ?_
  rw [ramp_step_of_bottom hq he hz, mul_zero]

/-- The mean increment of the ramp is at most `‖q‖` in absolute value, for nonnegative step
probabilities that sum to one. -/
private lemma abs_stepMean_ramp_le (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (p : (ℕ → Site d) → ℕ → Site d → ℝ) (x : ℕ → Site d) (j : ℕ) (hp : ∀ e, 0 ≤ p x j e)
    (hp1 : ∑ e ∈ unitSteps d, p x j e = 1) : |stepMean p (ramp q a) x j| ≤ ‖q‖ := by
  unfold stepMean
  calc |∑ e ∈ unitSteps d, p x j e * (ramp q a (x j + e) - ramp q a (x j))|
      ≤ ∑ e ∈ unitSteps d, |p x j e * (ramp q a (x j + e) - ramp q a (x j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ unitSteps d, p x j e * ‖q‖ := by
        refine Finset.sum_le_sum fun e he => ?_
        rw [abs_mul, abs_of_nonneg (hp e)]
        exact mul_le_mul_of_nonneg_left (abs_ramp_step_le q a (x j) he) (hp e)
    _ = ‖q‖ := by rw [← Finset.sum_mul, hp1, one_mul]

/-- The number of sites `z` of the departure range with `q · z > a`. -/
private noncomputable def aboveCount (q : EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ)
    (a : ℝ) : ℕ :=
  ((departureRange x n).filter (fun z => a < inner ℝ q (toSpace z))).card

/-- Raising the level can only remove sites. -/
private lemma aboveCount_anti (q : EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ)
    {a a' : ℝ} (h : a ≤ a') : aboveCount q x n a' ≤ aboveCount q x n a := by
  unfold aboveCount
  refine Finset.card_le_card fun z hz => ?_
  simp only [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, lt_of_le_of_lt h hz.2⟩

/-- The comparison of neighboring levels (`eq:norm-linear` before the absorption): at a level
`a` past which every site has local time at most `S` and drift at least `α` in the direction `q`,
the Dynkin martingale of the ramp controls the number of sites above `a + Λ`. -/
private lemma level_inequality {ε α C₁ Λ lg : ℝ} (hd : 1 ≤ d) (hε : 0 < ε) (hα : 0 < α)
    (hΛ : 0 < Λ) (hlg : 0 ≤ lg) (hC₁ : 0 ≤ C₁)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ Λ) (x : ℕ → Site d) (hx0 : x 0 = 0) (n : ℕ)
    {a : ℝ} (ha : 0 ≤ a) {S : ℕ}
    (hS : ∀ z ∈ departureRange x n, a - Λ < inner ℝ q (toSpace z) → localTime x n z ≤ S)
    (hα' : ∀ j < n, a + Λ ≤ inner ℝ q (toSpace (x j)) → α ≤ inner ℝ q (ξ (x j)))
    (hM : |dynkinMart (driftStepProb d ε ξ) (ramp q a) x n| ≤
      C₁ * (Real.sqrt (lg * ∑ z ∈ (departureRange x n).filter
        (fun z => a - Λ < inner ℝ q (toSpace z)), (localTime x n z : ℝ)) + lg)) :
    ε * α * (aboveCount q x n (a + Λ) : ℝ) ≤
      Λ * S * ((aboveCount q x n (a - Λ) : ℝ) - aboveCount q x n (a + Λ)) +
        C₁ * (Real.sqrt (lg * (S * aboveCount q x n (a - Λ))) + lg) := by
  have hεα : 0 < ε * α := mul_pos hε hα
  -- the Dynkin identity for the ramp
  have hmart : -∑ j ∈ Finset.range n, stepMean (driftStepProb d ε ξ) (ramp q a) x j ≤
      |dynkinMart (driftStepProb d ε ξ) (ramp q a) x n| := by
    have h0 : ramp q a (x 0) = 0 := by
      unfold ramp
      rw [hx0, CERW.Support.Occupation.toSpace_zero, inner_zero_right]
      exact max_eq_right (by linarith)
    have h1 : 0 ≤ ramp q a (x n) := le_max_right _ _
    have hdef : dynkinMart (driftStepProb d ε ξ) (ramp q a) x n =
        ramp q a (x n) - ramp q a (x 0) -
          ∑ j ∈ Finset.range n, stepMean (driftStepProb d ε ξ) (ramp q a) x j := rfl
    rw [hdef, h0]
    have := le_abs_self (ramp q a (x n) - 0 -
      ∑ j ∈ Finset.range n, stepMean (driftStepProb d ε ξ) (ramp q a) x j)
    linarith
  -- the pointwise lower bound for minus the mean increments
  have hpt : ∀ j ∈ Finset.range n,
      ε * α * (if x j ∉ (Finset.range j).image x then
          (if a + Λ ≤ inner ℝ q (toSpace (x j)) then (1 : ℝ) else 0) else 0) -
        Λ * (if a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ
          then (1 : ℝ) else 0) ≤
        -stepMean (driftStepProb d ε ξ) (ramp q a) x j := by
    intro j hj
    by_cases htop : a + Λ ≤ inner ℝ q (toSpace (x j))
    · have hx_ne : x j ≠ 0 := by
        intro h
        rw [h, CERW.Support.Occupation.toSpace_zero, inner_zero_right] at htop
        linarith
      have hmid : ¬ (a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ) :=
        fun h => absurd h.2 (not_lt.mpr htop)
      rw [stepMean_ramp_of_top hq ε ξ x j htop, if_neg hmid, if_pos htop]
      by_cases hf : x j ∉ (Finset.range j).image x
      · rw [if_pos hf, if_pos ⟨hx_ne, hf⟩]
        have := mul_le_mul_of_nonneg_left (hα' j (Finset.mem_range.mp hj) htop) hε.le
        linarith
      · rw [if_neg hf, if_neg (fun h => hf h.2)]
        simp
    · by_cases hbot : inner ℝ q (toSpace (x j)) ≤ a - Λ
      · have hmid : ¬ (a - Λ < inner ℝ q (toSpace (x j)) ∧
            inner ℝ q (toSpace (x j)) < a + Λ) :=
          fun h => absurd h.1 (not_lt.mpr hbot)
        rw [stepMean_ramp_of_bottom hq _ x j hbot, if_neg hmid, if_neg htop]
        simp
      · have hmid : a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ :=
          ⟨not_le.mp hbot, not_le.mp htop⟩
        rw [if_pos hmid, if_neg htop, ite_self, mul_zero]
        have hp0 : ∀ e, 0 ≤ driftStepProb d ε ξ x j e :=
          CERW.Support.Drift.driftStepProb_nonneg hε.le hξ x j
        have habs := abs_stepMean_ramp_le q a (driftStepProb d ε ξ) x j hp0
          (CERW.Support.Drift.sum_driftStepProb hd ε ξ x j)
        have := le_abs_self (stepMean (driftStepProb d ε ξ) (ramp q a) x j)
        simp only [Finset.mem_range] at hj
        linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_neg_distrib] at hsum
  -- the count of first departures above the level
  have hF : (aboveCount q x n (a + Λ) : ℝ) ≤ ∑ j ∈ Finset.range n,
      (if x j ∉ (Finset.range j).image x then
          (if a + Λ ≤ inner ℝ q (toSpace (x j)) then (1 : ℝ) else 0) else 0) := by
    rw [CERW.Support.Occupation.sum_fresh_eq_sum_departureRange x n
      (fun z => if a + Λ ≤ inner ℝ q (toSpace z) then (1 : ℝ) else 0), Finset.sum_boole]
    unfold aboveCount
    refine Nat.cast_le.mpr (Finset.card_le_card fun z hz => ?_)
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.le⟩
  -- the count of times spent strictly between the levels
  have hcard : ((departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z) ∧
        inner ℝ q (toSpace z) < a + Λ)).card + aboveCount q x n (a + Λ) ≤
      aboveCount q x n (a - Λ) := by
    unfold aboveCount
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card fun z hz => ?_
      simp only [Finset.mem_union, Finset.mem_filter] at hz ⊢
      rcases hz with ⟨h1, h2, _⟩ | ⟨h1, h2⟩
      · exact ⟨h1, h2⟩
      · exact ⟨h1, by linarith⟩
    · rw [Finset.disjoint_filter]
      intro z _ h1 h2
      exact absurd h2 (not_lt.mpr h1.2.le)
  have hG : ((∑ j ∈ Finset.range n,
      (if a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ
        then (1 : ℝ) else 0)) : ℝ) ≤ S * ((departureRange x n).filter
          (fun z => a - Λ < inner ℝ q (toSpace z) ∧ inner ℝ q (toSpace z) < a + Λ)).card := by
    rw [Finset.sum_boole]
    have hle := Finset.card_le_mul_card_image_of_maps_to
      (s := (Finset.range n).filter (fun j => a - Λ < inner ℝ q (toSpace (x j)) ∧
        inner ℝ q (toSpace (x j)) < a + Λ)) (f := x)
      (t := (departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z) ∧
        inner ℝ q (toSpace z) < a + Λ))
      (fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp only [Finset.mem_filter, departureRange, Finset.mem_image, Finset.mem_range]
        exact ⟨⟨j, hj.1, rfl⟩, hj.2⟩) S (fun z hz => by
        simp only [Finset.mem_filter] at hz
        refine le_trans (Finset.card_le_card fun j hj => ?_) (hS z hz.1 hz.2.1)
        simp only [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1.1, hj.2⟩)
    exact_mod_cast hle
  -- the martingale term
  have hsumS : ∑ z ∈ (departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z)),
      (localTime x n z : ℝ) ≤ S * aboveCount q x n (a - Λ) := by
    calc ∑ z ∈ (departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z)),
          (localTime x n z : ℝ)
        ≤ ∑ _z ∈ (departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z)),
            (S : ℝ) := by
          refine Finset.sum_le_sum fun z hz => ?_
          simp only [Finset.mem_filter] at hz
          exact_mod_cast hS z hz.1 hz.2
      _ = S * aboveCount q x n (a - Λ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          rfl
  have hM' : C₁ * (Real.sqrt (lg * ∑ z ∈ (departureRange x n).filter
        (fun z => a - Λ < inner ℝ q (toSpace z)), (localTime x n z : ℝ)) + lg) ≤
      C₁ * (Real.sqrt (lg * (S * aboveCount q x n (a - Λ))) + lg) := by
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsumS hlg)
    linarith
  have hcard' : ((((departureRange x n).filter
        (fun z => a - Λ < inner ℝ q (toSpace z) ∧ inner ℝ q (toSpace z) < a + Λ)).card : ℕ) : ℝ)
      ≤ (aboveCount q x n (a - Λ) : ℝ) - aboveCount q x n (a + Λ) := by
    have : (((departureRange x n).filter
        (fun z => a - Λ < inner ℝ q (toSpace z) ∧ inner ℝ q (toSpace z) < a + Λ)).card : ℝ) +
        aboveCount q x n (a + Λ) ≤ aboveCount q x n (a - Λ) := by exact_mod_cast hcard
    linarith
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have h1 : Λ * ((∑ j ∈ Finset.range n,
      (if a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ
        then (1 : ℝ) else 0))) ≤ Λ * S * ((aboveCount q x n (a - Λ) : ℝ) -
          aboveCount q x n (a + Λ)) := by
    calc Λ * (∑ j ∈ Finset.range n, (if a - Λ < inner ℝ q (toSpace (x j)) ∧
            inner ℝ q (toSpace (x j)) < a + Λ then (1 : ℝ) else 0))
        ≤ Λ * (S * ((departureRange x n).filter
          (fun z => a - Λ < inner ℝ q (toSpace z) ∧ inner ℝ q (toSpace z) < a + Λ)).card) :=
          mul_le_mul_of_nonneg_left hG hΛ.le
      _ ≤ Λ * (S * ((aboveCount q x n (a - Λ) : ℝ) - aboveCount q x n (a + Λ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard' hS0) hΛ.le
      _ = Λ * S * ((aboveCount q x n (a - Λ) : ℝ) - aboveCount q x n (a + Λ)) := by ring
  have h2 := mul_le_mul_of_nonneg_left hF hεα.le
  linarith [hmart, hM, hM']

/-- The compensated path `Z_t = X_t + ε Σ_{j<t} I_j ξ(X_j)`, where `I_j` marks a first
departure. -/
private noncomputable def compensatedPath (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  toSpace (x t) + ε • ∑ j ∈ Finset.range t, if x j ∉ departureRange x j then ξ (x j) else 0

/-- If every first departure in `[s, t)` has nonnegative drift in the direction `u`, then the
increment of `u · X` over `[s, t)` obeys the bound on the increments of the compensated path. -/
private lemma inner_sub_le_of_drift {ε : ℝ} (hε : 0 ≤ ε) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) {n : ℕ} {C Λ lg : ℝ} {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ ≤ Λ)
    (hZ : ∀ s t : ℕ, s < t → t ≤ n →
      ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ ≤ C * Real.sqrt ((t - s : ℝ) * lg))
    {s t : ℕ} (hst : s < t) (htn : t ≤ n)
    (hxi : ∀ j : ℕ, s ≤ j → j < t → x j ∉ departureRange x j → 0 ≤ inner ℝ u (ξ (x j))) :
    inner ℝ u (toSpace (x t) - toSpace (x s)) ≤ Λ * (C * Real.sqrt ((t - s : ℝ) * lg)) := by
  set f : ℕ → EuclideanSpace ℝ (Fin d) := fun j =>
    if x j ∉ departureRange x j then ξ (x j) else 0 with hf
  have hsum : ∑ j ∈ Finset.range t, f j =
      ∑ j ∈ Finset.range s, f j + ∑ j ∈ Finset.Ico s t, f j :=
    (Finset.sum_range_add_sum_Ico f hst.le).symm
  have hZeq : compensatedPath ε ξ x t - compensatedPath ε ξ x s =
      (toSpace (x t) - toSpace (x s)) + ε • ∑ j ∈ Finset.Ico s t, f j := by
    simp only [compensatedPath, ← hf, hsum, smul_add]
    abel
  have hT : 0 ≤ inner ℝ u (∑ j ∈ Finset.Ico s t, f j) := by
    rw [inner_sum]
    refine Finset.sum_nonneg fun j hj => ?_
    by_cases hdep : x j ∉ departureRange x j
    · simp only [hf, if_pos hdep]
      exact hxi j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2 hdep
    · simp only [hf, if_neg hdep, inner_zero_right, le_refl]
  have hinner : inner ℝ u (compensatedPath ε ξ x t - compensatedPath ε ξ x s) =
      inner ℝ u (toSpace (x t) - toSpace (x s)) +
        ε * inner ℝ u (∑ j ∈ Finset.Ico s t, f j) := by
    rw [hZeq, inner_add_right, real_inner_smul_right]
  have hεT : 0 ≤ ε * inner ℝ u (∑ j ∈ Finset.Ico s t, f j) := mul_nonneg hε hT
  have hΛ : 0 ≤ Λ := (norm_nonneg u).trans hu
  calc inner ℝ u (toSpace (x t) - toSpace (x s))
      ≤ inner ℝ u (compensatedPath ε ξ x t - compensatedPath ε ξ x s) := by linarith
    _ ≤ ‖u‖ * ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ := real_inner_le_norm _ _
    _ ≤ Λ * ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ :=
        mul_le_mul_of_nonneg_right hu (norm_nonneg _)
    _ ≤ Λ * (C * Real.sqrt ((t - s : ℝ) * lg)) :=
        mul_le_mul_of_nonneg_left (hZ s t hst htn) hΛ

/-- A path that finishes above the level `ā + Λ` and spends few steps above `ā`, at sites of
small local time, gains little above `ā`: its last entrance into `{q · z > ā}` is followed by a
crossing whose duration is at most the number of sites times the largest local time. -/
private lemma top_bound {ε : ℝ} (hε : 0 ≤ ε) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    {q : EuclideanSpace ℝ (Fin d)} {Λ : ℝ} (hΛ : 0 < Λ) (hq : ‖q‖ ≤ Λ) (x : ℕ → Site d)
    (hx0 : x 0 = 0) (hstep : ∀ j, x (j + 1) - x j ∈ unitSteps d) {n : ℕ} {C₁ lg : ℝ}
    (hC₁ : 0 ≤ C₁) (hlg : 0 ≤ lg)
    (hZ : ∀ s t : ℕ, s < t → t ≤ n →
      ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ ≤ C₁ * Real.sqrt ((t - s : ℝ) * lg))
    {σ : ℕ} (hσn : σ ≤ n) {ā : ℝ} (hā : 0 ≤ ā) (hT : ā + Λ < inner ℝ q (toSpace (x σ)))
    (hxi : ∀ j < σ, ā < inner ℝ q (toSpace (x j)) → x j ∉ departureRange x j →
      0 ≤ inner ℝ q (ξ (x j)))
    {S : ℕ} (hS : ∀ z ∈ departureRange x n, ā < inner ℝ q (toSpace z) → localTime x n z ≤ S) :
    inner ℝ q (toSpace (x σ)) ≤
      ā + Λ + Λ * (C₁ * Real.sqrt (S * aboveCount q x n ā * lg)) := by
  have hσ0 : 0 < σ := by
    rcases Nat.eq_zero_or_pos σ with h | h
    · rw [h, hx0, CERW.Support.Occupation.toSpace_zero, inner_zero_right] at hT
      linarith
    · exact h
  have hstepq : ∀ j, inner ℝ q (toSpace (x (j + 1))) ≤ inner ℝ q (toSpace (x j)) + Λ := by
    intro j
    have h1 : toSpace (x (j + 1)) = toSpace (x j) + toSpace (x (j + 1) - x j) := by
      rw [← toSpace_add]
      congr 1
      abel
    rw [h1, inner_add_right]
    have := abs_inner_toSpace_le q (hstep j)
    have := (abs_le.mp (this.trans hq)).2
    linarith
  obtain ⟨s, hs0, hsσ, hfs, hfj⟩ := CERW.Support.Crossing.exists_last_entrance
    (f := fun j => inner ℝ q (toSpace (x j)) / Λ) (b := ā / Λ) (τ := σ)
    (by
      rw [hx0, CERW.Support.Occupation.toSpace_zero, inner_zero_right, zero_div]
      exact div_nonneg hā hΛ.le)
    (fun j => by
      rw [div_le_iff₀ hΛ, add_mul, one_mul, div_mul_cancel₀ _ hΛ.ne']
      exact hstepq j) hσ0
  have hxs : inner ℝ q (toSpace (x s)) ≤ ā + Λ := by
    have := hfs
    rw [div_le_iff₀ hΛ, add_mul, one_mul, div_mul_cancel₀ _ hΛ.ne'] at this
    exact this
  have hxj : ∀ j, s ≤ j → j < σ → ā < inner ℝ q (toSpace (x j)) := fun j h1 h2 =>
    (div_lt_div_iff_of_pos_right hΛ).mp (hfj j h1 h2)
  have hsσ' : s < σ := by
    rcases hsσ.lt_or_eq with h | h
    · exact h
    · rw [h] at hxs
      linarith
  have hdrift := inner_sub_le_of_drift hε ξ x hq hZ hsσ' hσn
    (fun j h1 h2 h3 => hxi j h2 (hxj j h1 h2) h3)
  -- the duration of the crossing
  have hdur : σ - s ≤ S * aboveCount q x n ā := by
    have hle := Finset.card_le_mul_card_image_of_maps_to (s := Finset.Ico s σ) (f := x)
      (t := (departureRange x n).filter (fun z => ā < inner ℝ q (toSpace z)))
      (fun j hj => by
        rw [Finset.mem_Ico] at hj
        simp only [Finset.mem_filter, departureRange, Finset.mem_image, Finset.mem_range]
        exact ⟨⟨j, by omega, rfl⟩, hxj j hj.1 hj.2⟩) S (fun z hz => by
        simp only [Finset.mem_filter] at hz
        refine le_trans (Finset.card_le_card fun j hj => ?_) (hS z hz.1 hz.2)
        simp only [Finset.mem_filter, Finset.mem_Ico] at hj
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hj.2⟩)
    rw [Nat.card_Ico] at hle
    exact hle
  have hdur' : ((σ : ℝ) - s) * lg ≤ S * aboveCount q x n ā * lg := by
    have : ((σ : ℝ) - s) ≤ S * aboveCount q x n ā := by
      have h := (Nat.cast_le (α := ℝ)).mpr hdur
      rwa [Nat.cast_sub hsσ'.le, Nat.cast_mul] at h
    exact mul_le_mul_of_nonneg_right this hlg
  have hsqrt : Real.sqrt (((σ : ℝ) - s) * lg) ≤ Real.sqrt (S * aboveCount q x n ā * lg) :=
    Real.sqrt_le_sqrt hdur'
  have hsplit : inner ℝ q (toSpace (x σ)) =
      inner ℝ q (toSpace (x s)) + inner ℝ q (toSpace (x σ) - toSpace (x s)) := by
    rw [inner_sub_right]
    ring
  have hfin : Λ * (C₁ * Real.sqrt (((σ : ℝ) - s) * lg)) ≤
      Λ * (C₁ * Real.sqrt (S * aboveCount q x n ā * lg)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt hC₁) hΛ.le
  linarith

/-- `log n ≥ 1/2` for `n ≥ 2`. -/
private lemma half_le_log {n : ℕ} (hn : 2 ≤ n) : 1 / 2 ≤ Real.log n := by
  have h1 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have h2 := Real.log_two_gt_d9
  linarith

/-- A sequence contracted at each step by the factor `1 - 1/(2 (A L + 1))` up to an additive
error `O(L log n)` is of order `L log n` after `O(L log n)` steps, when it starts below `n`. -/
private lemma exists_small_level {A B L : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hL : 1 ≤ L) {n : ℕ}
    (hn : 2 ≤ n) (u : ℕ → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hun : u 0 ≤ n)
    (hrec : ∀ i, u (i + 1) ≤ A * L * (u i - u (i + 1)) +
      B * Real.sqrt (L * u i * Real.log n) + B * Real.log n) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ (2 * A + 4) * L * Real.log n ∧
      u k ≤ (B ^ 2 + 2 * B + 2) * L * Real.log n := by
  set lg : ℝ := Real.log n with hlg
  have hlg2 : 1 / 2 ≤ lg := half_le_log hn
  have hlg0 : 0 < lg := by linarith
  set c : ℝ := A * L + 1 with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ A * L := mul_nonneg hA.le (by linarith)
    linarith
  have hc0 : 0 < c := by linarith
  set E : ℝ := (B ^ 2 / 2 + B) * L * lg with hE
  have hE0 : 0 ≤ E := by positivity
  set ρ : ℝ := 1 - 1 / (2 * c) with hρ
  have hρ0 : 0 ≤ ρ := by
    have : 1 / (2 * c) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  -- one step of the contraction
  have hstep : ∀ i, u (i + 1) ≤ ρ * u i + E / c := by
    intro i
    have h1 := hrec i
    have hsq : B * Real.sqrt (L * u i * lg) ≤ (u i + B ^ 2 * L * lg) / 2 := by
      have hLl : 0 ≤ L * lg := by positivity
      have hsplit : Real.sqrt (L * u i * lg) = Real.sqrt (L * lg) * Real.sqrt (u i) := by
        rw [← Real.sqrt_mul hLl]
        congr 1
        ring
      have ht : (B * Real.sqrt (L * lg)) ^ 2 = B ^ 2 * L * lg := by
        rw [mul_pow, Real.sq_sqrt hLl]
        ring
      have hs : Real.sqrt (u i) ^ 2 = u i := Real.sq_sqrt (hu0 i)
      have hprod : B * Real.sqrt (L * u i * lg) =
          (B * Real.sqrt (L * lg)) * Real.sqrt (u i) := by
        rw [hsplit]
        ring
      rw [hprod]
      linarith [sq_nonneg (B * Real.sqrt (L * lg) - Real.sqrt (u i))]
    have hLlg : lg ≤ L * lg := by
      have := mul_le_mul_of_nonneg_right hL hlg0.le
      linarith
    have hBl : B * lg ≤ B * L * lg := by
      have := mul_le_mul_of_nonneg_left hLlg hB
      linarith
    have hmain : c * u (i + 1) ≤ (c - 1 / 2) * u i + E := by
      rw [hc, hE]
      linarith
    rw [← sub_nonneg] at hmain ⊢
    have : ρ * u i + E / c - u (i + 1) = ((c - 1 / 2) * u i + E - c * u (i + 1)) / c := by
      rw [hρ]
      field_simp
    rw [this]
    exact div_nonneg hmain hc0.le
  -- iteration
  have hiter : ∀ k : ℕ, u k ≤ ρ ^ k * u 0 + 2 * E := by
    intro k
    induction k with
    | zero => simp only [pow_zero, one_mul]; linarith
    | succ k ih =>
        have h1 := hstep k
        have h2 : ρ * u k ≤ ρ * (ρ ^ k * u 0 + 2 * E) := mul_le_mul_of_nonneg_left ih hρ0
        have hkey : ρ * (2 * E) + E / c = 2 * E := by
          rw [hρ]
          field_simp
          ring
        rw [pow_succ]
        linarith [hkey, h1, h2]
  -- the choice of the number of steps
  set k : ℕ := ⌈2 * c * lg⌉₊ with hk
  have hk1 : 1 ≤ k := by
    rw [hk]
    exact Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Nat.ceil_eq_zero, not_le]
      positivity)
  have hkge : 2 * c * lg ≤ k := Nat.le_ceil _
  have hρk : ρ ^ k * u 0 ≤ 1 := by
    have hexp : ρ ≤ Real.exp (-(1 / (2 * c))) := by
      have := Real.add_one_le_exp (-(1 / (2 * c)))
      rw [hρ]
      linarith
    have hpow : ρ ^ k ≤ Real.exp (-(1 / (2 * c))) ^ k := pow_le_pow_left₀ hρ0 hexp k
    have hexp2 : Real.exp (-(1 / (2 * c))) ^ k = Real.exp (-(1 / (2 * c)) * k) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    have hlow : lg ≤ 1 / (2 * c) * k := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      linarith
    have hexp3 : Real.exp (-(1 / (2 * c)) * k) ≤ Real.exp (-lg) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hexp4 : Real.exp (-lg) = (n : ℝ)⁻¹ := by
      rw [hlg, Real.exp_neg, Real.exp_log (by exact_mod_cast (by omega : 0 < n))]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    calc ρ ^ k * u 0 ≤ (n : ℝ)⁻¹ * n := by
          apply mul_le_mul _ hun (hu0 0) (by positivity)
          calc ρ ^ k ≤ _ := hpow
            _ = _ := hexp2
            _ ≤ _ := hexp3
            _ = _ := hexp4
      _ = 1 := inv_mul_cancel₀ hnpos.ne'
  refine ⟨k, hk1, ?_, ?_⟩
  · have hk2 : (k : ℝ) < 2 * c * lg + 1 := Nat.ceil_lt_add_one (by positivity)
    have hLlg : lg ≤ L * lg := by
      have := mul_le_mul_of_nonneg_right hL hlg0.le
      linarith
    rw [hc] at hk2
    linarith
  · have := hiter k
    have h2 : 2 * E = (B ^ 2 + 2 * B) * L * lg := by rw [hE]; ring
    have hLlg : lg ≤ L * lg := by
      have := mul_le_mul_of_nonneg_right hL hlg0.le
      linarith
    linarith

/-- The recurrence for the level counts: divide the level inequality by `ε α`, using
`S ≤ L` and `u' ≤ u`. -/
private lemma recurrence_step {ε α C₁ Λ S L lg ui un A B : ℝ} (hεα : 0 < ε * α)
    (hΛ : 0 < Λ) (hlg : 0 ≤ lg) (hC₁ : 0 ≤ C₁) (hSL : S ≤ L) (hui : 0 ≤ ui)
    (hdiff : un ≤ ui) (hA : A = Λ / (ε * α)) (hB : B = C₁ / (ε * α))
    (hlev : ε * α * un ≤ Λ * S * (ui - un) +
      C₁ * (Real.sqrt (lg * (S * ui)) + lg)) :
    un ≤ A * L * (ui - un) + B * Real.sqrt (L * ui * lg) + B * lg := by
  have hd0 : 0 ≤ ui - un := sub_nonneg.mpr hdiff
  have h1 : Λ * S * (ui - un) ≤ Λ * L * (ui - un) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSL hΛ.le) hd0
  have h2 : Real.sqrt (lg * (S * ui)) ≤ Real.sqrt (L * ui * lg) := by
    refine Real.sqrt_le_sqrt ?_
    rw [mul_comm lg]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSL hui) hlg
  have h3 := mul_le_mul_of_nonneg_left (add_le_add_right h2 lg) hC₁
  have hlev' : ε * α * un ≤ Λ * L * (ui - un) + C₁ * (Real.sqrt (L * ui * lg) + lg) := by
    linarith
  have hAe : A * (ε * α) = Λ := by rw [hA]; exact div_mul_cancel₀ _ hεα.ne'
  have hBe : B * (ε * α) = C₁ := by rw [hB]; exact div_mul_cancel₀ _ hεα.ne'
  have key : (A * L * (ui - un) + B * Real.sqrt (L * ui * lg) + B * lg) * (ε * α) =
      Λ * L * (ui - un) + C₁ * (Real.sqrt (L * ui * lg) + lg) := by
    calc (A * L * (ui - un) + B * Real.sqrt (L * ui * lg) + B * lg) * (ε * α)
        = (A * (ε * α)) * L * (ui - un) + (B * (ε * α)) * (Real.sqrt (L * ui * lg) + lg) := by
          ring
      _ = _ := by rw [hAe, hBe]
  refine le_of_mul_le_mul_right ?_ hεα
  rw [key]
  linarith

/-- The arithmetic of the last step: the level `ā` and the crossing bound combine into the
estimate `T ≤ max {T - h, b} + C L log n`. -/
private lemma final_arithmetic {T h b m a₀ Λ K₁ K₂ C₁ L lg k Y : ℝ} (hΛ : 0 < Λ)
    (hC₁ : 0 ≤ C₁) (hL : 1 ≤ L) (hlg : 1 / 2 ≤ lg)
    (hm : m ≤ max (T - h) b + Λ) (ha₀ : a₀ < m + Λ) (hkK : k ≤ K₁ * L * lg)
    (hYb : Y ≤ (K₂ + 1) * (L * lg))
    (hT : T ≤ a₀ - Λ + 2 * k * Λ + Λ + Λ * (C₁ * Y)) :
    T ≤ max (T - h) b + (4 * Λ + 2 * K₁ * Λ + Λ * C₁ * (K₂ + 1)) * L * lg := by
  have hLl : 1 / 2 ≤ L * lg := by
    have := mul_le_mul_of_nonneg_right hL (by linarith : 0 ≤ lg)
    linarith
  have h1 : 2 * k * Λ ≤ 2 * K₁ * Λ * (L * lg) := by
    have := mul_le_mul_of_nonneg_left hkK (by positivity : (0 : ℝ) ≤ 2 * Λ)
    linarith
  have h2 : 2 * Λ ≤ 4 * Λ * (L * lg) := by
    have := mul_le_mul_of_nonneg_left hLl hΛ.le
    linarith
  have h3 : Λ * (C₁ * Y) ≤ Λ * C₁ * (K₂ + 1) * (L * lg) := by
    have := mul_le_mul_of_nonneg_left hYb (mul_nonneg hΛ.le hC₁)
    linarith
  have hexp : (4 * Λ + 2 * K₁ * Λ + Λ * C₁ * (K₂ + 1)) * L * lg =
      4 * Λ * (L * lg) + 2 * K₁ * Λ * (L * lg) + Λ * C₁ * (K₂ + 1) * (L * lg) := by ring
  rw [hexp]
  linarith

/-- The square root in the crossing duration bound is at most `(K₂ + 1) L log n`. -/
private lemma sqrt_crossing_bound {S L lg u K₂ : ℝ} (hS : S ≤ L) (hS0 : 0 ≤ S) (hu : 0 ≤ u)
    (hlg : 0 ≤ lg) (hK₂ : 0 ≤ K₂) (huK : u ≤ K₂ * (L * lg)) :
    Real.sqrt (S * u * lg) ≤ (K₂ + 1) * (L * lg) := by
  have hL : 0 ≤ L := hS0.trans hS
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : S * u * lg ≤ L * (K₂ * (L * lg)) * lg :=
    mul_le_mul_of_nonneg_right (mul_le_mul hS huK hu hL) hlg
  have h2 : K₂ ≤ (K₂ + 1) ^ 2 := by nlinarith [sq_nonneg (K₂ + 1 / 2)]
  calc S * u * lg ≤ L * (K₂ * (L * lg)) * lg := h1
    _ = K₂ * (L * lg) ^ 2 := by ring
    _ ≤ (K₂ + 1) ^ 2 * (L * lg) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = ((K₂ + 1) * (L * lg)) ^ 2 := by ring

/-- The outer crossing estimate for a path and a direction `q`, in terms of a bound `Λ ≥ ‖q‖`
and the explicit inequalities of the hypotheses. -/
private lemma outer_crossing_core {d : ℕ} (hd : 1 ≤ d) {ε α C₁ Λ : ℝ} (hε : 0 < ε) (hα : 0 < α)
    (hC₁ : 0 < C₁) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) → ∀ n : ℕ, 2 ≤ n →
      ∀ q : EuclideanSpace ℝ (Fin d), ‖q‖ ≤ Λ →
      ∀ x : ℕ → Site d, x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) →
      (∀ s t : ℕ, s < t → t ≤ n → ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ ≤
        C₁ * Real.sqrt ((t - s : ℝ) * Real.log n)) →
      (∀ k : ℕ, k ≤ n →
        |dynkinMart (driftStepProb d ε ξ) (ramp q (k * Λ)) x n| ≤
          C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
            (fun z => k * Λ - Λ < inner ℝ q (toSpace z)), (localTime x n z : ℝ)) +
              Real.log n)) →
      ∀ j₀ : ℕ, j₀ ≤ n → ∀ h : ℝ, 0 < h →
      (∀ j ≤ n, inner ℝ q (toSpace (x j₀)) - h < inner ℝ q (toSpace (x j)) →
        α ≤ inner ℝ q (ξ (x j))) →
      ∀ b : ℝ, 0 ≤ b →
        inner ℝ q (toSpace (x j₀)) ≤ max (inner ℝ q (toSpace (x j₀)) - h) b +
          C * (1 + ((((departureRange x n).filter
            (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) *
              Real.log n := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Λ / (ε * α) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = C₁ / (ε * α) := ⟨_, rfl⟩
  have hεα : 0 < ε * α := mul_pos hε hα
  have hA : 0 < A := by rw [hAdef]; positivity
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = 2 * A + 4 := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂def⟩ : ∃ K₂ : ℝ, K₂ = B ^ 2 + 2 * B + 2 := ⟨_, rfl⟩
  have hK₁ : 0 < K₁ := by rw [hK₁def]; linarith
  have hK₂ : 0 < K₂ := by rw [hK₂def]; positivity
  refine ⟨4 * Λ + 2 * K₁ * Λ + Λ * C₁ * (K₂ + 1), by positivity, ?_⟩
  intro ξ hξ n hn q hq x hx0 hstep hZ hmart j₀ hj₀ h hh hα' b hb
  have hlg2 : 1 / 2 ≤ Real.log n := half_le_log hn
  have hlg0 : 0 ≤ Real.log n := by linarith
  -- the largest local time above `b`
  have hSloc : ∀ z ∈ departureRange x n, b ≤ inner ℝ q (toSpace z) → localTime x n z ≤
      ((departureRange x n).filter (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) :=
    fun z hz hbz => Finset.le_sup (f := localTime x n) (Finset.mem_filter.mpr ⟨hz, hbz⟩)
  generalize ((departureRange x n).filter
    (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) = S at hSloc ⊢
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 1 + S := ⟨_, rfl⟩
  rw [← hLdef]
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hSL : (S : ℝ) ≤ L := by rw [hLdef]; linarith
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = inner ℝ q (toSpace (x j₀)) := ⟨_, rfl⟩
  rw [← hTdef] at hα' ⊢
  have hproj : ∀ j : ℕ, inner ℝ q (toSpace (x j)) ≤ Λ * j := fun j =>
    calc inner ℝ q (toSpace (x j)) ≤ ‖q‖ * ‖toSpace (x j)‖ := real_inner_le_norm _ _
      _ ≤ Λ * j := mul_le_mul hq (norm_toSpace_le_index x hx0 hstep j) (norm_nonneg _) hΛ.le
  -- the first level above `max {T - h, b + Λ}` on the grid `Λ ℕ`
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = max (T - h) (b + Λ) := ⟨_, rfl⟩
  have hTm : T - h ≤ m := hmdef ▸ le_max_left _ _
  have hbm : b + Λ ≤ m := hmdef ▸ le_max_right _ _
  have hmax : m ≤ max (T - h) b + Λ := by
    rw [hmdef]
    exact max_le (by linarith [le_max_left (T - h) b]) (by linarith [le_max_right (T - h) b])
  obtain ⟨k₀, hk₀def⟩ : ∃ k₀ : ℕ, k₀ = ⌈m / Λ⌉₊ := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = k₀ * Λ := ⟨_, rfl⟩
  have hma₀ : m ≤ a₀ := by
    have := Nat.le_ceil (m / Λ)
    rw [← hk₀def, div_le_iff₀ hΛ] at this
    rwa [ha₀]
  have ha₀m : a₀ < m + Λ := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ m / Λ from div_nonneg (by linarith) hΛ.le)
    rw [← hk₀def] at h1
    have h2 := mul_lt_mul_of_pos_right h1 hΛ
    rw [add_mul, div_mul_cancel₀ _ hΛ.ne', one_mul] at h2
    rwa [ha₀]
  have ha₀nn : 0 ≤ a₀ := by linarith
  -- the number of sites above the levels `a₀ - Λ + 2 i Λ`
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ i : ℕ,
      u i = (aboveCount q x n (a₀ - Λ + 2 * i * Λ) : ℝ) := ⟨fun i => _, fun i => rfl⟩
  have hu0 : ∀ i, 0 ≤ u i := fun i => by rw [hu]; exact Nat.cast_nonneg _
  have hun : u 0 ≤ n := by
    rw [hu]
    have h1 : aboveCount q x n (a₀ - Λ + 2 * ((0 : ℕ) : ℝ) * Λ) ≤ n :=
      (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp))
    exact_mod_cast h1
  have hu_anti : ∀ i, u (i + 1) ≤ u i := fun i => by
    rw [hu, hu]
    refine Nat.cast_le.mpr (aboveCount_anti q x n ?_)
    push_cast
    linarith
  have hrec : ∀ i : ℕ, u (i + 1) ≤
      A * L * (u i - u (i + 1)) + B * Real.sqrt (L * u i * Real.log n) + B * Real.log n := by
    intro i
    have hlo : a₀ ≤ ((k₀ + 2 * i : ℕ) : ℝ) * Λ := by
      push_cast
      rw [ha₀]
      have : 0 ≤ 2 * (i : ℝ) * Λ := by positivity
      linarith
    have hul : a₀ - Λ + 2 * (i : ℝ) * Λ = ((k₀ + 2 * i : ℕ) : ℝ) * Λ - Λ := by
      push_cast
      rw [ha₀]
      ring
    have huh : a₀ - Λ + 2 * ((i + 1 : ℕ) : ℝ) * Λ = ((k₀ + 2 * i : ℕ) : ℝ) * Λ + Λ := by
      push_cast
      rw [ha₀]
      ring
    by_cases hk : k₀ + 2 * i ≤ n
    · have hlev := level_inequality hd hε hα hΛ hlg0 hC₁.le hξ hq x hx0 n
        (a := ((k₀ + 2 * i : ℕ) : ℝ) * Λ) (by positivity) (S := S)
        (fun z hz hzq => hSloc z hz (by linarith))
        (fun j hj hjq => hα' j hj.le (by linarith)) (hmart _ hk)
      rw [← hul, ← huh, ← hu, ← hu] at hlev
      exact recurrence_step hεα hΛ hlg0 hC₁.le hSL (hu0 i) (hu_anti i) hAdef hBdef hlev
    · have hzero : u i = 0 := by
        rw [hu, hul]
        have : aboveCount q x n (((k₀ + 2 * i : ℕ) : ℝ) * Λ - Λ) = 0 := by
          refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun z hz => ?_)
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
          rw [Finset.mem_range] at hj
          rw [not_lt]
          refine (hproj j).trans ?_
          have h1 : (n : ℝ) ≤ ((k₀ + 2 * i : ℕ) : ℝ) - 1 := by
            have : n + 1 ≤ k₀ + 2 * i := by omega
            have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((k₀ + 2 * i : ℕ) : ℝ) := Nat.cast_le.mpr this
            linarith [(Nat.cast_add_one n : ((n + 1 : ℕ) : ℝ) = n + 1)]
          have h2 : (j : ℝ) ≤ n := by exact_mod_cast hj.le
          have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) hΛ.le
          linarith
        rw [this]
        simp
      have hzero' : u (i + 1) = 0 := le_antisymm (hzero ▸ hu_anti i) (hu0 _)
      rw [hzero, hzero']
      simp only [sub_self, mul_zero, zero_mul, Real.sqrt_zero, zero_add]
      exact mul_nonneg hB hlg0
  -- the level at which few sites remain
  obtain ⟨k, hk1, hkK, hukK⟩ := exists_small_level hA hB hL1 hn u hu0 hun hrec
  rw [← hK₁def] at hkK
  rw [← hK₂def] at hukK
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hbar : a₀ + Λ ≤ a₀ - Λ + 2 * (k : ℝ) * Λ := by
    have := mul_nonneg (sub_nonneg.mpr hk1') hΛ.le
    linarith
  have hL0 : 0 ≤ L := by linarith
  by_cases hcase : T ≤ a₀ - Λ + 2 * (k : ℝ) * Λ + Λ
  · refine final_arithmetic (Y := 0) hΛ hC₁.le hL1 hlg2 hmax ha₀m hkK ?_ ?_
    · exact mul_nonneg (by linarith) (mul_nonneg hL0 hlg0)
    · rw [mul_zero, mul_zero, add_zero]
      exact hcase
  · have htop := top_bound hε.le ξ hΛ hq x hx0 hstep hC₁.le hlg0 hZ hj₀
      (ā := a₀ - Λ + 2 * (k : ℝ) * Λ) (by linarith)
      (by rw [← hTdef]; exact not_le.mp hcase)
      (fun j hj hjq _ => by
        have := hα' j (by omega) (by linarith)
        linarith)
      (S := S) (fun z hz hzq => hSloc z hz (by linarith))
    rw [← hTdef] at htop
    have hukS : (aboveCount q x n (a₀ - Λ + 2 * (k : ℝ) * Λ) : ℝ) ≤ K₂ * (L * Real.log n) := by
      rw [← hu k]
      linarith
    exact final_arithmetic hΛ hC₁.le hL1 hlg2 hmax ha₀m hkK
      (sqrt_crossing_bound hSL hS0 (Nat.cast_nonneg _) hlg0 hK₂.le hukS) htop

end Ramp
/-- **The outer crossing lemma** (`lem:outer-crossing`) for the gauge of a compact convex body with
the origin in its interior and the two-sided ellipticity condition: a path of the walk with a
subgradient selection `ξ` as drift field, that satisfies the vector bound and the linear martingale
bound in the direction `q`, and that has drift at least `α` in the direction `q` above `T - h`,
reaches the height `T` at most `C L_b log n` above `max {T - h, b}`, where `L_b` is one more than
the largest local time above `b`. -/
theorem gauge_outer_crossing {d : ℕ} (hd : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {α : ℝ} (hα : 0 < α) {C₁ : ℝ} (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ n : ℕ, 2 ≤ n → ∀ q : EuclideanSpace ℝ (Fin d), ‖q‖ ≤ normMax (gauge K) →
      ∀ x : ℕ → Site d, x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) →
        let Λ : ℝ := normMax (gauge K)
        let Z : ℕ → EuclideanSpace ℝ (Fin d) := fun t => toSpace (x t) + ε •
          ∑ j ∈ Finset.range t, if x j ∉ departureRange x j then ξ (x j) else 0
        (∀ s t : ℕ, s < t → t ≤ n →
          ‖Z t - Z s‖ ≤ C₁ * Real.sqrt ((t - s : ℝ) * Real.log n)) →
        (∀ k : ℕ, k ≤ n →
          |dynkinMart (driftStepProb d ε ξ)
              (fun z => max (inner ℝ q (toSpace z) - k * Λ) 0) x n|
            ≤ C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
                  (fun z => k * Λ - Λ < inner ℝ q (toSpace z)),
                  (localTime x n z : ℝ)) + Real.log n)) →
        ∀ j₀ : ℕ, j₀ ≤ n →
        (∀ j ≤ n, inner ℝ q (toSpace (x j)) ≤ inner ℝ q (toSpace (x j₀))) →
        let T : ℝ := inner ℝ q (toSpace (x j₀))
        ∀ h : ℝ, 0 < h →
        (∀ j ≤ n, T - h < inner ℝ q (toSpace (x j)) → α ≤ inner ℝ q (ξ (x j))) →
        ∀ b : ℝ, 0 ≤ b →
          T ≤ max (T - h) b + C * (1 + ((((departureRange x n).filter
              (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ))
                * Real.log n := by
  have hd1 : 1 ≤ d := by omega
  have hΛ : 0 < normMax (gauge K) :=
    lt_of_lt_of_le (normMin_gauge_pos_mul_le hK h0 hd1).1
      (normMin_gauge_le_normMax_gauge hK h0 hd1)
  obtain ⟨C, hC, hmain⟩ := outer_crossing_core hd1 hε hα hC₁ hΛ
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hξ0 n hn q hq x hx0 hstep Λ Z hZ hmart j₀ hj₀ hmax T h hh hα' b hb
  exact hmain ξ (drift_coord_bound_gauge hε.le hell hξ hξ0) n hn q hq x hx0 hstep hZ hmart j₀ hj₀
    h hh hα' b hb

end Outer

/-!
## The outer radius from the nearest point of `{ψ ≤ r}`

The deterministic outer-radius argument for the gauge of a compact convex body: the Euclidean
nearest point `Π(x)` of the closed convex set `{ψ ≤ r}`, the direction `u = (x - Π x)/|x - Π x|` of
the point farthest from this set, and the outer crossing lemma in the direction `Λ_ψ u` give
`max_{j ≤ n} ψ(X_j) ≤ r + C (1 + L_b) log n`, where `L_b` bounds the local times of the sites with
`ψ ≥ r`. The point `Π(x)` is an arbitrary nearest point; only the variational inequality
`(x - Π x) · (y - Π x) ≤ 0` for `y ∈ {ψ ≤ r}` is used. Nothing here uses evenness.
-/

namespace Projection

/-- The outer-normal direction `Λ_ψ (z - P z)/|z - P z|` at `z`, for a nearest-point map `P`. -/
noncomputable def projDir {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  normMax (gauge K) • (‖z - P z‖⁻¹ • (z - P z))

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- A nearest-point map onto the closed convex set `{ψ ≤ r}` exists, with the variational
inequality that characterizes the nearest point. -/
theorem exists_nearestPoint (hΨ : Adm K) {r : ℝ} (hr : 0 < r) :
    ∃ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x, gauge K (P x) ≤ r) ∧
        ∀ x y, gauge K y ≤ r → inner ℝ (x - P x) (y - P x) ≤ 0 := by
  set s : Set (EuclideanSpace ℝ (Fin d)) := {y | gauge K y ≤ r} with hs
  have hne : s.Nonempty := ⟨0, by simp [hs, hr.le]⟩
  have hclosed : IsClosed s := isClosed_le hΨ.continuous continuous_const
  have hconv : Convex ℝ s := by
    have := (convexOn_gauge hΨ.convex hΨ.zero_mem).convex_le r
    simpa [hs] using this
  choose v hv hxv using exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv
  exact ⟨v, fun x => hv x, fun x y hy =>
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hv x)).1 (hxv x) y hy⟩

/-- A point `P x` with the variational inequality is at least as close to `x` as every point `y`
of `{ψ ≤ r}`. -/
private theorem norm_sub_nearest_le {r : ℝ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP2 : ∀ x y, gauge K y ≤ r → inner ℝ (x - P x) (y - P x) ≤ 0)
    {x y : EuclideanSpace ℝ (Fin d)} (hy : gauge K y ≤ r) : ‖x - P x‖ ≤ ‖x - y‖ := by
  have h := hP2 x y hy
  have e := norm_sub_sq_real (x - P x) (y - P x)
  have e2 : x - P x - (y - P x) = x - y := by abel
  rw [e2] at e
  have h2 : ‖x - P x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [e]
    nlinarith [sq_nonneg ‖y - P x‖]
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq h2 (norm_nonneg _))

/-- A point `y` with `ψ(y) > r` is at positive distance from its nearest point `P y`, and every
subgradient `ξ` of `ψ` at `y` has `ξ · (y - P y)/|y - P y| ≥ c_ψ`: the subgradient inequality at
`P y` gives `ξ · (y - P y) ≥ ψ(y) - r`, and `|y - P y| ≤ |y - (r/ψ(y)) y| ≤ (ψ(y) - r)/c_ψ`. -/
theorem normMin_le_inner_proj (hΨ : Adm K) (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP1 : ∀ x, gauge K (P x) ≤ r)
    (hP2 : ∀ x y, gauge K y ≤ r → inner ℝ (x - P x) (y - P x) ≤ 0)
    {y : EuclideanSpace ℝ (Fin d)} (hy : r < gauge K y) {ξ : EuclideanSpace ℝ (Fin d)}
    (hξ : IsSubgradient (gauge K) y ξ) :
    0 < ‖y - P y‖ ∧ normMin (gauge K) ≤ inner ℝ ξ (‖y - P y‖⁻¹ • (y - P y)) := by
  have hyP : y ≠ P y := fun h => by
    have := hP1 y
    rw [← h] at this
    linarith
  have hw : 0 < ‖y - P y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyP)
  refine ⟨hw, ?_⟩
  obtain ⟨hc, hcle⟩ := hΨ.normMin_pos_mul_le hd
  have hψpos : 0 < gauge K y := lt_trans hr hy
  have h1 : gauge K y - r ≤ inner ℝ ξ (y - P y) := by
    have h := hξ (P y)
    have e : inner ℝ ξ (P y - y) = - inner ℝ ξ (y - P y) := by
      rw [← inner_neg_right, neg_sub]
    rw [e] at h
    linarith [hP1 y]
  set z : EuclideanSpace ℝ (Fin d) := (r / gauge K y) • y with hz
  have hψz : gauge K z = r := by
    rw [hz, hΨ.smul_nonneg (div_nonneg hr.le hψpos.le), div_mul_cancel₀ _ hψpos.ne']
  have hwle : ‖y - P y‖ ≤ ‖y - z‖ := norm_sub_nearest_le hP2 hψz.le
  have hr1 : r / gauge K y ≤ 1 := (div_le_one hψpos).mpr hy.le
  have hyz : y - z = (1 - r / gauge K y) • y := by rw [hz, sub_smul, one_smul]
  have hnyz : ‖y - z‖ = (1 - r / gauge K y) * ‖y‖ := by
    rw [hyz, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hr1)]
  have hy_le : ‖y‖ ≤ gauge K y / normMin (gauge K) := by
    rw [le_div_iff₀ hc, mul_comm]
    exact hcle y
  have hw2 : ‖y - P y‖ ≤ (gauge K y - r) / normMin (gauge K) := by
    calc ‖y - P y‖ ≤ ‖y - z‖ := hwle
      _ = (1 - r / gauge K y) * ‖y‖ := hnyz
      _ ≤ (1 - r / gauge K y) * (gauge K y / normMin (gauge K)) :=
          mul_le_mul_of_nonneg_left hy_le (sub_nonneg.mpr hr1)
      _ = (gauge K y - r) / normMin (gauge K) := by
          field_simp
  have hw3 : normMin (gauge K) * ‖y - P y‖ ≤ gauge K y - r := by
    rw [le_div_iff₀ hc] at hw2
    linarith
  rw [real_inner_smul_right, inv_mul_eq_div, le_div_iff₀ hw]
  linarith

/-- The outer-normal direction at a point off its nearest point has norm `Λ_ψ`. -/
private theorem norm_projDir (hΨ : Adm K) {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ P x) : ‖projDir K P x‖ = normMax (gauge K) := by
  have hw : 0 < ‖x - P x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  rw [projDir, norm_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw.ne', mul_one,
    Real.norm_of_nonneg hΨ.normMax_nonneg]

/-- The outer-normal direction has inner product `Λ_ψ |x - P x|` with `x - P x`. -/
private theorem inner_projDir_self
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ≠ P x) : inner ℝ (projDir K P x) (x - P x) = normMax (gauge K) * ‖x - P x‖ := by
  have hw : 0 < ‖x - P x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  rw [projDir, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

/-- Every `z` with `ψ(z) ≤ r` has `q · z ≤ β` for `q = Λ_ψ (x - P x)/|x - P x|` and
`β = q · P x`. -/
private theorem inner_projDir_le (hΨ : Adm K) {r : ℝ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP2 : ∀ x y, gauge K y ≤ r → inner ℝ (x - P x) (y - P x) ≤ 0)
    (x : EuclideanSpace ℝ (Fin d)) {z : EuclideanSpace ℝ (Fin d)} (hz : gauge K z ≤ r) :
    inner ℝ (projDir K P x) z ≤ inner ℝ (projDir K P x) (P x) := by
  have h := hP2 x z hz
  rw [inner_sub_right] at h
  simp only [projDir, real_inner_smul_left]
  have h' : inner ℝ (x - P x) z ≤ inner ℝ (x - P x) (P x) := by linarith
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr (norm_nonneg _))) hΨ.normMax_nonneg

/-- Beyond the level `β`, every point is outside `{ψ < r}`: if `q · z ≥ β` then `ψ(z) ≥ r`
(otherwise `z + tu` lies in `{ψ ≤ r}` for a small `t > 0` and `q · (z + tu) > β`). -/
private theorem le_gauge_of_inner_ge (hΨ : Adm K) (hd : 1 ≤ d) {r : ℝ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP2 : ∀ x y, gauge K y ≤ r → inner ℝ (x - P x) (y - P x) ≤ 0)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ P x)
    {z : EuclideanSpace ℝ (Fin d)}
    (hz : inner ℝ (projDir K P x) (P x) ≤ inner ℝ (projDir K P x) z) :
    r ≤ gauge K z := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hw : 0 < ‖x - P x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hΛ : 0 < normMax (gauge K) :=
    lt_of_lt_of_le (hΨ.normMin_pos_mul_le hd).1
      (normMin_gauge_le_normMax_gauge hΨ.compact hΨ.zero_mem hd)
  set u : EuclideanSpace ℝ (Fin d) := ‖x - P x‖⁻¹ • (x - P x) with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw.ne']
  have hψu : 0 ≤ gauge K u := hΨ.nonneg u
  set t : ℝ := (r - gauge K z) / (gauge K u + 1) with ht
  have htpos : 0 < t := div_pos (by linarith) (by linarith)
  have hψt : gauge K (z + t • u) ≤ r := by
    have h1 := hΨ.add_le z (t • u)
    rw [hΨ.smul_nonneg htpos.le] at h1
    have h2 : t * gauge K u ≤ r - gauge K z := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have h3 := inner_projDir_le hΨ hP2 x hψt
  rw [inner_add_right, real_inner_smul_right] at h3
  have h4 : inner ℝ (projDir K P x) u = normMax (gauge K) := by
    rw [projDir, real_inner_smul_left, real_inner_self_eq_norm_sq, hun]
    ring
  rw [h4] at h3
  have := mul_pos htpos hΛ
  nlinarith [hz]

end Projection

/-!
## The deterministic outer radius from a nearest-point crossing

At a visited site `y` with `q · y > T - θ Λ_ψ w`, every subgradient of `ψ` at `y` has a component
at least `Λ_ψ c_ψ / 2` in the direction `q`, and the outer crossing lemma in the direction `q`
then bounds the largest distance `w` of a visited site from `{ψ ≤ r}`.
-/

namespace Projection

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- The drift has a positive component in the direction of the farthest point. If `x` is a point
at the largest distance `w = |x - P x| > 0` from `{ψ ≤ r}`, `q = Λ_ψ (x - P x)/w`,
`β = q · P x`, then every `y` with `|y - P y| ≤ w` and `q · y > β + (1 - θ) Λ_ψ w`, where
`θ = c_ψ² / (8 Λ_ψ²)`, has `Λ_ψ c_ψ / 2 ≤ q · ξ` for every subgradient `ξ` of `ψ` at `y`. -/
theorem drift_sign (hΨ : Adm K) (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP1 : ∀ x, gauge K (P x) ≤ r)
    (hP2 : ∀ x y, gauge K y ≤ r → inner ℝ (x - P x) (y - P x) ≤ 0)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ P x)
    {y : EuclideanSpace ℝ (Fin d)} (hyw : ‖y - P y‖ ≤ ‖x - P x‖) {ξ : EuclideanSpace ℝ (Fin d)}
    (hξ : IsSubgradient (gauge K) y ξ)
    (hy : inner ℝ (projDir K P x) (P x) +
        (1 - normMin (gauge K) ^ 2 / (8 * normMax (gauge K) ^ 2)) *
          (normMax (gauge K) * ‖x - P x‖) < inner ℝ (projDir K P x) y) :
    normMax (gauge K) * normMin (gauge K) / 2 ≤ inner ℝ (projDir K P x) ξ := by
  obtain ⟨hc, hcle⟩ := hΨ.normMin_pos_mul_le hd
  have hcΛ : normMin (gauge K) ≤ normMax (gauge K) :=
    normMin_gauge_le_normMax_gauge hΨ.compact hΨ.zero_mem hd
  have hΛ : 0 < normMax (gauge K) := lt_of_lt_of_le hc hcΛ
  have hwpos : 0 < ‖x - P x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  set Λ := normMax (gauge K) with hΛdef
  set c := normMin (gauge K) with hcdef
  set w : ℝ := ‖x - P x‖ with hw
  set θ : ℝ := c ^ 2 / (8 * Λ ^ 2) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 8 := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_self_le_mul_self hc.le hcΛ]
  set u : EuclideanSpace ℝ (Fin d) := w⁻¹ • (x - P x) with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
  set q : EuclideanSpace ℝ (Fin d) := projDir K P x with hq
  have hqu : q = Λ • u := rfl
  have hF1 : ∀ z, gauge K z ≤ r → inner ℝ q z ≤ inner ℝ q (P x) := fun z hz =>
    inner_projDir_le hΨ hP2 x hz
  have hpos : 0 < (1 - θ) * (Λ * w) := by
    have : 0 < 1 - θ := by linarith
    positivity
  have hyr : r < gauge K y := by
    by_contra h
    have := hF1 y (not_lt.mp h)
    linarith
  obtain ⟨hwy, hcv⟩ := normMin_le_inner_proj hΨ hd hr hP1 hP2 hyr hξ
  set wy : ℝ := ‖y - P y‖ with hwydef
  set v : EuclideanSpace ℝ (Fin d) := wy⁻¹ • (y - P y) with hv
  have hcv' : c ≤ inner ℝ ξ v := hcv
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwy.ne']
  have hyv : y - P y = wy • v := by rw [hv, smul_inv_smul₀ hwy.ne']
  have h1 : inner ℝ q y - inner ℝ q (P x) ≤ inner ℝ q (y - P y) := by
    rw [inner_sub_right]
    linarith [hF1 (P y) (hP1 y)]
  have h2 : inner ℝ q (y - P y) = Λ * wy * inner ℝ u v := by
    rw [hyv, hqu, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right]
    ring
  have h3 : (1 - θ) * Λ * wy < Λ * wy * inner ℝ u v := by
    have h5 : (1 - θ) * Λ * wy ≤ (1 - θ) * Λ * w :=
      mul_le_mul_of_nonneg_left hyw (by
        have : 0 < 1 - θ := by linarith
        positivity)
    linarith
  have h4 : 1 - θ < inner ℝ u v := by
    have hpos2 : 0 < Λ * wy := mul_pos hΛ hwy
    have : (Λ * wy) * (1 - θ) < (Λ * wy) * inner ℝ u v := by linarith
    exact lt_of_mul_lt_mul_left this hpos2.le
  have h5 : ‖u - v‖ ^ 2 < (c / (2 * Λ)) ^ 2 := by
    rw [norm_sub_sq_real, hun, hvn]
    have : (c / (2 * Λ)) ^ 2 = 2 * θ := by
      rw [hθ]
      field_simp
      ring
    rw [this]
    linarith
  have h6 : ‖u - v‖ < c / (2 * Λ) := by
    by_contra h
    replace h := not_lt.mp h
    nlinarith [norm_nonneg (u - v), div_pos hc (by positivity : 0 < 2 * Λ)]
  have hξn : ‖ξ‖ ≤ Λ := norm_le_normMax_of_isSubgradient hΨ.compact hΨ.zero_mem hξ
  have h7 : inner ℝ q ξ = Λ * (inner ℝ ξ v + inner ℝ (u - v) ξ) := by
    rw [hqu, real_inner_smul_left, inner_sub_left, real_inner_comm v ξ]
    ring
  have h8 : - (c / 2) ≤ inner ℝ (u - v) ξ := by
    have h9 : ‖u - v‖ * ‖ξ‖ ≤ c / (2 * Λ) * Λ :=
      mul_le_mul h6.le hξn (norm_nonneg _) (by positivity)
    have h10 : c / (2 * Λ) * Λ = c / 2 := by field_simp
    have h11 := abs_real_inner_le_norm (u - v) ξ
    have h12 := neg_abs_le (inner ℝ (u - v) ξ)
    linarith
  rw [h7]
  have : c / 2 ≤ inner ℝ ξ v + inner ℝ (u - v) ξ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this hΛ.le]

end Projection

/-!
## The outer radius of the range of the walk

The deterministic implication behind the outer bound of the limit shape: if the visited sites are
bounded by the Euclidean distance `w` from `{ψ ≤ r}`, then `ψ ≤ r + Λ_ψ w` on them, and the crossing
in the direction of the outer normal at the farthest visited site bounds `Λ_ψ w` by a multiple
of `(1 + L) log n`, where `L` bounds the local times of the sites with `ψ ≥ r`.
-/

namespace Projection

/-- **Deterministic outer radius.** For the literal gauge `ψ` of a compact convex body with the
origin in its interior, a subgradient field `ξ`, a nearest-point map `P` onto `{ψ ≤ r}` (that is,
with the variational inequality `(z - P z) · (y - P z) ≤ 0` for `ψ(y) ≤ r`), a nearest-neighbour
path `x` of length `n`, a bound on the compensated path, the linear ramp-martingale bound in the
direction `Λ_ψ (z - P z)/|z - P z|` at each visited site `z` with `ψ(z) > r`, and a local-time
bound `L` on the sites with `ψ ≥ r`, one has `max_{j ≤ n} ψ(X_j) ≤ r + C (1 + L) log n`. -/
theorem gauge_outer_radius_of_crossing {d : ℕ} (hd : 2 ≤ d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {C₁ : ℝ} (hC₁ : 0 < C₁) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ n : ℕ, 2 ≤ n → ∀ x : ℕ → Site d, x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) →
      ∀ r : ℝ, 0 < r → ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        (∀ z, gauge K (P z) ≤ r) →
        (∀ z y, gauge K y ≤ r → inner ℝ (z - P z) (y - P z) ≤ 0) →
        let Z : ℕ → EuclideanSpace ℝ (Fin d) := fun t => toSpace (x t) + ε •
          ∑ j ∈ Finset.range t, if x j ∉ departureRange x j then ξ (x j) else 0
        (∀ s t : ℕ, s < t → t ≤ n →
          ‖Z t - Z s‖ ≤ C₁ * Real.sqrt ((t - s : ℝ) * Real.log n)) →
        (∀ j ≤ n, r < gauge K (toSpace (x j)) → ∀ k : ℕ, k ≤ n →
          |dynkinMart (driftStepProb d ε ξ)
              (fun z => max (inner ℝ (projDir K P (toSpace (x j))) (toSpace z) -
                k * normMax (gauge K)) 0) x n|
            ≤ C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
                  (fun z => k * normMax (gauge K) - normMax (gauge K) <
                    inner ℝ (projDir K P (toSpace (x j))) (toSpace z)),
                  (localTime x n z : ℝ)) + Real.log n)) →
        ∀ L : ℝ, 0 ≤ L →
          (∀ z : Site d, r ≤ gauge K (toSpace z) → (localTime x n z : ℝ) ≤ L) →
          normMaxRadius (gauge K) x n ≤ r + C * (1 + L) * Real.log n := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc, hcle⟩ := hΨ.normMin_pos_mul_le hd1
  have hcΛ : normMin (gauge K) ≤ normMax (gauge K) :=
    normMin_gauge_le_normMax_gauge hΨ.compact hΨ.zero_mem hd1
  have hΛ : 0 < normMax (gauge K) := lt_of_lt_of_le hc hcΛ
  have hα : 0 < normMax (gauge K) * normMin (gauge K) / 2 := by positivity
  obtain ⟨C, hC, hmain⟩ :=
    Outer.gauge_outer_crossing hd hΨ.compact hΨ.zero_mem hε hell hα hC₁
  have hθ : 0 < normMin (gauge K) ^ 2 / (8 * normMax (gauge K) ^ 2) := by positivity
  refine ⟨C / (normMin (gauge K) ^ 2 / (8 * normMax (gauge K) ^ 2)), by positivity, ?_⟩
  intro ξ hξ hξ0 n hn x hx0 hstep r hr P hP1 hP2 Z hZ hmart L hL hloc
  set Λ := normMax (gauge K) with hΛdef
  set c := normMin (gauge K) with hcdef
  set θ : ℝ := c ^ 2 / (8 * Λ ^ 2) with hθdef
  have hθ1 : θ ≤ 1 / 8 := by
    rw [hθdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_self_le_mul_self hc.le hcΛ]
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun j => ‖toSpace (x j) - P (toSpace (x j))‖) ⟨0, by simp⟩
  have hj₀ : j₀ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₀mem)
  set xs : EuclideanSpace ℝ (Fin d) := toSpace (x j₀) with hxs
  set w : ℝ := ‖xs - P xs‖ with hwdef
  have hdist : ∀ j ≤ n, ‖toSpace (x j) - P (toSpace (x j))‖ ≤ w := fun j hj =>
    hj₀max j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hup : ∀ j ≤ n, gauge K (toSpace (x j)) ≤ r + Λ * w := by
    intro j hj
    have h1 : gauge K (toSpace (x j)) ≤
        gauge K (P (toSpace (x j))) + gauge K (toSpace (x j) - P (toSpace (x j))) := by
      have := hΨ.add_le (P (toSpace (x j))) (toSpace (x j) - P (toSpace (x j)))
      have e : P (toSpace (x j)) + (toSpace (x j) - P (toSpace (x j))) = toSpace (x j) := by abel
      rwa [e] at this
    have h2 := hΨ.le_normMax_mul (toSpace (x j) - P (toSpace (x j)))
    have h3 := mul_le_mul_of_nonneg_left (hdist j hj) hΛ.le
    have h4 := hP1 (toSpace (x j))
    linarith
  have hC' : 0 ≤ C / θ * (1 + L) * Real.log n := by positivity
  have key : Λ * w ≤ C / θ * (1 + L) * Real.log n := by
    rcases eq_or_lt_of_le (norm_nonneg (xs - P xs)) with hw0 | hwpos
    · have : Λ * w = 0 := by rw [hwdef, ← hw0, mul_zero]
      linarith
    · have hwpos' : 0 < w := hwpos
      have hxP : xs ≠ P xs := sub_ne_zero.mp (norm_pos_iff.mp hwpos)
      set q : EuclideanSpace ℝ (Fin d) := projDir K P xs with hq
      have hqn : ‖q‖ = Λ := norm_projDir hΨ hxP
      have hF1 : ∀ z, gauge K z ≤ r → inner ℝ q z ≤ inner ℝ q (P xs) := fun z hz =>
        inner_projDir_le hΨ hP2 xs hz
      have hβ : 0 ≤ inner ℝ q (P xs) := by
        have := hF1 0 (by rw [hΨ.map_zero]; exact hr.le)
        simpa using this
      have hT : inner ℝ q xs = inner ℝ q (P xs) + Λ * w := by
        have h1 : inner ℝ q (xs - P xs) = Λ * w := inner_projDir_self hxP
        rw [inner_sub_right] at h1
        linarith
      have hmax : ∀ j ≤ n, inner ℝ q (toSpace (x j)) ≤ inner ℝ q xs := by
        intro j hj
        have h1 : inner ℝ q (toSpace (x j) - P (toSpace (x j))) ≤
            ‖q‖ * ‖toSpace (x j) - P (toSpace (x j))‖ := real_inner_le_norm _ _
        rw [inner_sub_right] at h1
        have h2 := hF1 (P (toSpace (x j))) (hP1 _)
        have h3 := mul_le_mul_of_nonneg_left (hdist j hj) hΛ.le
        rw [hqn] at h1
        linarith
      have hpos : 0 < (1 - θ) * (Λ * w) := by
        have : 0 < 1 - θ := by linarith
        positivity
      have hh : 0 < θ * Λ * w := by positivity
      have hα' : ∀ j ≤ n, inner ℝ q xs - θ * Λ * w < inner ℝ q (toSpace (x j)) →
          Λ * c / 2 ≤ inner ℝ q (ξ (x j)) := by
        intro j hj hy
        have hy' : inner ℝ q (P xs) + (1 - θ) * (Λ * w) < inner ℝ q (toSpace (x j)) := by
          rw [hT] at hy
          linarith
        have hx0' : x j ≠ 0 := by
          intro h0
          rw [h0] at hy'
          have e : toSpace (0 : Site d) = 0 := by
            ext i
            simp [toSpace]
          rw [e, inner_zero_right] at hy'
          linarith
        exact drift_sign hΨ hd1 hr hP1 hP2 hxP (hdist j hj) (hξ _ hx0') hy'
      have hrxs : r < gauge K xs := by
        by_contra h
        have := hF1 xs (not_lt.mp h)
        linarith
      have hsup : ((((departureRange x n).filter
          (fun z => inner ℝ q (P xs) ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ) ≤
          L := by
        rcases ((departureRange x n).filter
            (fun z => inner ℝ q (P xs) ≤ inner ℝ q (toSpace z))).eq_empty_or_nonempty with he | hne
        · rw [he]
          simpa using hL
        · obtain ⟨z, hz, hzsup⟩ := Finset.exists_mem_eq_sup _ hne (localTime x n)
          rw [hzsup]
          exact hloc z (le_gauge_of_inner_ge hΨ hd1 hP2 hxP (Finset.mem_filter.mp hz).2)
      have hcross : inner ℝ q xs ≤ max (inner ℝ q xs - θ * Λ * w) (inner ℝ q (P xs)) +
          C * (1 + ((((departureRange x n).filter
            (fun z => inner ℝ q (P xs) ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) *
              Real.log n :=
        hmain ξ hξ hξ0 n hn q hqn.le x hx0 hstep hZ (hmart j₀ hj₀ hrxs) j₀ hj₀ hmax
          (θ * Λ * w) hh hα' (inner ℝ q (P xs)) hβ
      have hmaxeq : max (inner ℝ q xs - θ * Λ * w) (inner ℝ q (P xs)) =
          inner ℝ q xs - θ * Λ * w := by
        apply max_eq_left
        rw [hT]
        linarith
      have hsup' : C * (1 + ((((departureRange x n).filter
            (fun z => inner ℝ q (P xs) ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) *
              Real.log n ≤ C * (1 + L) * Real.log n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC.le) hlog
      have hθΛw : θ * (Λ * w) ≤ C * (1 + L) * Real.log n := by linarith
      calc Λ * w = (θ * (Λ * w)) / θ := by field_simp
        _ ≤ C * (1 + L) * Real.log n / θ := div_le_div_of_nonneg_right hθΛw hθ.le
        _ = C / θ * (1 + L) * Real.log n := by ring
  unfold normMaxRadius
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  linarith [hup j hjn]

end Projection

/-!
## The cell modulus of the potential of the gauge

For `D ⊆ B(0, R)` with `R ≥ 1` and `y, z` with `|y| ≤ 2R` and `|y - z| ≤ √d`, the potentials of a
bounded measurable field differ by at most `C ε log (R + 2)`; the field here is a gradient of the
gauge, bounded by `Λ_ψ`. Along a path, the cell set lies in the ball of radius `n + √d`, which gives
the modulus at the scale `log (n + 2)`.
-/

namespace CellModulus

open CERW.Generic.Kernel CERW.Support.Geometry

variable {d : ℕ}

/-- The integrand `g(v) · (v - y) |v - y|^{-d}` of the potential of the field `g`. -/
private noncomputable def fieldIntegrand (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (y v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ (g v) (v - y) / ‖v - y‖ ^ d

/-- The far-field constant `2^d + 2 d 3^{d-1}`. -/
private def farFieldConstant (d : ℕ) : ℝ := (2 : ℝ) ^ d + 2 * (d : ℝ) * 3 ^ (d - 1)

/-- The potential of a norm is the integral of the field integrand of its gradient. -/
private lemma normPotential_eq_integral (d : ℕ) (ε : ℝ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin d))) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ D y
      = 2 * ε / unitBallVolume d * ∫ v in D, fieldIntegrand (gradient Ψ) y v :=
  rfl

/-- The gradient of a function on `ℝ^d` is measurable. -/
private lemma measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- A measurable field weighted by the Newtonian kernel has a measurable integrand. -/
private lemma measurable_fieldIntegrand {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (y : EuclideanSpace ℝ (Fin d)) :
    Measurable (fieldIntegrand g y) := by
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
    measurable_id.sub measurable_const
  exact (hg.inner hsub).div (hsub.norm.pow_const d)

/-- The integrand of the field potential is at most `Λ` times the Newtonian kernel `|v - y|^{1-d}`
when the field has norm at most `Λ`. -/
private lemma abs_fieldIntegrand_le {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {Λ : ℝ} (hg : ∀ v, ‖g v‖ ≤ Λ) (v y : EuclideanSpace ℝ (Fin d)) :
    |fieldIntegrand g y v| ≤ Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
  have hξ := hg v
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hξ
  rcases eq_or_ne v y with rfl | hne
  · simp only [fieldIntegrand, sub_self, inner_zero_right, zero_div, abs_zero]
    exact mul_nonneg hΛ (Real.rpow_nonneg (norm_nonneg _) _)
  · have hw : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < ‖v - y‖ ^ d := pow_pos hw d
    have h1 : |inner ℝ (g v) (v - y)| ≤ ‖g v‖ * ‖v - y‖ := abs_real_inner_le_norm _ _
    have h2 : ‖g v‖ * ‖v - y‖ ≤ Λ * ‖v - y‖ := mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    calc |fieldIntegrand g y v|
        = |inner ℝ (g v) (v - y)| / ‖v - y‖ ^ d := by
          rw [fieldIntegrand, abs_div, abs_of_nonneg hden.le]
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
    IntegrableOn (fieldIntegrand g y) D := by
  obtain ⟨hint, _⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  refine (hint.const_mul Λ).mono' (measurable_fieldIntegrand hg y).aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs]
  exact abs_fieldIntegrand_le hΛ v y

/-- The difference of two field-potential integrands is at most `Λ` times the norm of the
difference of the Newtonian fields when the field has norm at most `Λ`. -/
private lemma abs_fieldIntegrand_sub_le {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {Λ : ℝ} (hg : ∀ v, ‖g v‖ ≤ Λ) (v y z : EuclideanSpace ℝ (Fin d)) :
    |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * ‖newtonField (v - y) - newtonField (v - z)‖ := by
  simp only [fieldIntegrand]
  rw [← inner_newtonField (g v) (v - y), ← inner_newtonField (g v) (v - z), ← inner_sub_right]
  calc |inner ℝ (g v) (newtonField (v - y) - newtonField (v - z))|
      ≤ ‖g v‖ * ‖newtonField (v - y) - newtonField (v - z)‖ := abs_real_inner_le_norm _ _
    _ ≤ Λ * ‖newtonField (v - y) - newtonField (v - z)‖ :=
        mul_le_mul_of_nonneg_right (hg v) (norm_nonneg _)

/-- Integral of `|v - z|^{-d}` over an annulus centred at `z`, obtained from the corresponding
integral at the origin by translation. -/
private lemma integrableOn_annulus_sub_rpow_neg_and_integral_eq (hd : 1 ≤ d)
    (z : EuclideanSpace ℝ (Fin d)) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    IntegrableOn (fun v => ‖v - z‖ ^ (-(d : ℝ))) (Metric.ball z R \ Metric.ball z ρ) ∧
      ∫ v in Metric.ball z R \ Metric.ball z ρ, ‖v - z‖ ^ (-(d : ℝ))
        = d * unitBallVolume d * Real.log (R / ρ) := by
  obtain ⟨hint, hval⟩ := integrableOn_annulus_norm_rpow_and_integral_eq (d := d) hd hρ hρR
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) z
  have hemb := measurableEmbedding_subRight z
  have hset : Metric.ball z R \ Metric.ball z ρ
      = (fun v : EuclideanSpace ℝ (Fin d) => v - z) ⁻¹'
          (Metric.ball 0 R \ Metric.ball 0 ρ) := by
    ext v
    simp only [Set.mem_sdiff, Set.mem_preimage, mem_ball_iff_norm, sub_zero]
  rw [hset]
  refine ⟨?_, ?_⟩
  · exact (hmp.integrableOn_comp_preimage hemb (f := fun v => ‖v‖ ^ (-(d : ℝ)))).mpr hint
  · rw [hmp.setIntegral_preimage_emb hemb (fun v => ‖v‖ ^ (-(d : ℝ))), hval]

/-- Near-field bound: the difference of the field integrands over `D ∩ B(z, 2√d)` is at most
`Λ · 5 d ω_d √d`. -/
private lemma setIntegral_abs_fieldIntegrand_sub_le_near (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y z : EuclideanSpace ℝ (Fin d))
    (hyz : ‖y - z‖ ≤ Real.sqrt d) :
    ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
        |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d) := by
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hsubY : D ∩ Metric.ball z (2 * Real.sqrt d) ⊆ Metric.ball y (3 * Real.sqrt d) := by
    intro v hv
    have hvz : ‖v - z‖ < 2 * Real.sqrt d := by
      have h := hv.2
      rwa [Metric.mem_ball, dist_eq_norm] at h
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖v - y‖ ≤ ‖v - z‖ + ‖z - y‖ := by
          rw [show v - y = (v - z) + (z - y) by abel]
          exact norm_add_le _ _
      _ = ‖v - z‖ + ‖y - z‖ := by rw [norm_sub_rev z y]
      _ < 2 * Real.sqrt d + Real.sqrt d := by linarith
      _ = 3 * Real.sqrt d := by ring
  obtain ⟨hintY, hvalY⟩ :=
    integrableOn_ball_and_integral_eq (d := d) hd1 y (ρ := 3 * Real.sqrt d) (by positivity)
  obtain ⟨hintZ, hvalZ⟩ :=
    integrableOn_ball_and_integral_eq (d := d) hd1 z (ρ := 2 * Real.sqrt d) (by positivity)
  have hgy : IntegrableOn (fun v => ‖v - y‖ ^ (1 - (d : ℝ)))
      (D ∩ Metric.ball z (2 * Real.sqrt d)) := hintY.mono_set hsubY
  have hgz : IntegrableOn (fun v => ‖v - z‖ ^ (1 - (d : ℝ)))
      (D ∩ Metric.ball z (2 * Real.sqrt d)) :=
    hintZ.mono_set Set.inter_subset_right
  have hsum : IntegrableOn
      (fun v => Λ * (‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ))))
      (D ∩ Metric.ball z (2 * Real.sqrt d)) := (hgy.add hgz).const_mul Λ
  have hfyD : IntegrableOn (fieldIntegrand g y) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin y
  have hfzD : IntegrableOn (fieldIntegrand g z) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin z
  have hfs : IntegrableOn (fun v => |fieldIntegrand g y v - fieldIntegrand g z v|)
      (D ∩ Metric.ball z (2 * Real.sqrt d)) :=
    ((hfyD.mono_set Set.inter_subset_left).sub (hfzD.mono_set Set.inter_subset_left)).abs
  calc
    ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
        |fieldIntegrand g y v - fieldIntegrand g z v|
        ≤ ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
            Λ * (‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ))) := by
          refine setIntegral_mono_on hfs hsum (hD.inter measurableSet_ball) (fun v _ => ?_)
          refine (abs_fieldIntegrand_sub_le hΛ v y z).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ hΛ0
          calc ‖newtonField (v - y) - newtonField (v - z)‖
              ≤ ‖newtonField (v - y)‖ + ‖newtonField (v - z)‖ := norm_sub_le _ _
            _ = ‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ)) := by
                rw [norm_newtonField hd, norm_newtonField hd]
      _ = Λ * ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
            (‖v - y‖ ^ (1 - (d : ℝ)) + ‖v - z‖ ^ (1 - (d : ℝ))) := integral_const_mul _ _
      _ = Λ * ((∫ v in D ∩ Metric.ball z (2 * Real.sqrt d), ‖v - y‖ ^ (1 - (d : ℝ)))
            + ∫ v in D ∩ Metric.ball z (2 * Real.sqrt d), ‖v - z‖ ^ (1 - (d : ℝ))) := by
          rw [integral_add hgy hgz]
      _ ≤ Λ * ((∫ v in Metric.ball y (3 * Real.sqrt d), ‖v - y‖ ^ (1 - (d : ℝ)))
            + ∫ v in Metric.ball z (2 * Real.sqrt d), ‖v - z‖ ^ (1 - (d : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hΛ0
          · exact setIntegral_mono_set hintY
              (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg _) _))
              hsubY.eventuallyLE
          · exact setIntegral_mono_set hintZ
              (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg (norm_nonneg _) _))
              Set.inter_subset_right.eventuallyLE
      _ = Λ * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d) := by
          rw [hvalY, hvalZ]
          ring

/-- The far-field set `D \ B(z, 2√d)` lies in the annulus `B(z, (3 + √d)(R + 2)) \ B(z, 2√d)`. -/
private lemma sdiff_ball_subset_annulus {R : ℝ} (hR : 1 ≤ R) {d : ℕ} (hd1 : 1 ≤ d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hDsub : D ⊆ Metric.ball 0 R)
    (y z : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 2 * R) (hyz : ‖y - z‖ ≤ Real.sqrt d) :
    D \ Metric.ball z (2 * Real.sqrt d) ⊆
      Metric.ball z ((3 + Real.sqrt d) * (R + 2)) \ Metric.ball z (2 * Real.sqrt d) := by
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  intro v hv
  refine ⟨?_, hv.2⟩
  have hvD : v ∈ D := hv.1
  have hvR : ‖v‖ < R := by
    have := hDsub hvD
    rwa [Metric.mem_ball, dist_zero_right] at this
  have hz : ‖z‖ ≤ 2 * R + Real.sqrt d := by
    calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      _ = ‖y - z‖ + ‖y‖ := by rw [norm_sub_rev]
      _ ≤ Real.sqrt d + 2 * R := by linarith
      _ = 2 * R + Real.sqrt d := by ring
  have hlt : ‖v - z‖ < (3 + Real.sqrt d) * (R + 2) := by
    have htri : ‖v - z‖ ≤ ‖v‖ + ‖z‖ := norm_sub_le _ _
    nlinarith [hvR, hz, hRpos, hδpos]
  rwa [Metric.mem_ball, dist_eq_norm]

/-- Pointwise far-field bound: for `‖v - z‖ ≥ 2√d` the difference of the field integrands is at
most `Λ A_d √d ‖v - z‖^{-d}`. -/
private lemma abs_fieldIntegrand_sub_le_far (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) (y z v : EuclideanSpace ℝ (Fin d))
    (hyz : ‖y - z‖ ≤ Real.sqrt d) (hvz : 2 * Real.sqrt d ≤ ‖v - z‖) :
    |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) := by
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hA : 0 ≤ farFieldConstant d := by
    rw [farFieldConstant]; positivity
  have h2δpos : 0 < 2 * Real.sqrt d := by positivity
  have hsub : 2 * ‖(v - y) - (v - z)‖ ≤ ‖v - z‖ := by
    have h1 : (v - y) - (v - z) = z - y := by abel
    rw [h1, norm_sub_rev]
    linarith
  have hK := norm_newtonField_sub_le (a := v - y) (b := v - z) hsub
  have hneg : 0 < ‖v - z‖ := lt_of_lt_of_le h2δpos hvz
  have hnum : farFieldConstant d * ‖(v - y) - (v - z)‖
      ≤ farFieldConstant d * Real.sqrt d := by
    have hle : ‖(v - y) - (v - z)‖ ≤ Real.sqrt d := by
      rw [show (v - y) - (v - z) = z - y by abel, norm_sub_rev]
      exact hyz
    exact mul_le_mul_of_nonneg_left hle hA
  have hden : (0 : ℝ) < ‖v - z‖ ^ d := pow_pos hneg d
  calc |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * ‖newtonField (v - y) - newtonField (v - z)‖ := abs_fieldIntegrand_sub_le hΛ v y z
    _ ≤ Λ * (farFieldConstant d * ‖(v - y) - (v - z)‖ / ‖v - z‖ ^ d) :=
        mul_le_mul_of_nonneg_left hK hΛ0
    _ = Λ * ((farFieldConstant d * ‖(v - y) - (v - z)‖) / ‖v - z‖ ^ d) := by ring
    _ ≤ Λ * ((farFieldConstant d * Real.sqrt d) / ‖v - z‖ ^ d) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hden.le) hΛ0
    _ = Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) := by
        rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, div_eq_mul_inv]
        ring

/-- Far-field bound: the difference of the field integrands over `D \ B(z, 2√d)` is at most
`Λ A_d √d σ_d log(((3 + √d)(R + 2))/(2√d))`. -/
private lemma setIntegral_abs_fieldIntegrand_sub_le_far (hd : 2 ≤ d) {R : ℝ} (hR : 1 ≤ R)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hDsub : D ⊆ Metric.ball 0 R)
    (y z : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 2 * R)
    (hyz : ‖y - z‖ ≤ Real.sqrt d) :
    ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
        |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * farFieldConstant d * Real.sqrt d
        * ((d : ℝ) * unitBallVolume d
          * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hA : 0 ≤ farFieldConstant d := by
    rw [farFieldConstant]; positivity
  have h2δpos : 0 < 2 * Real.sqrt d := by positivity
  have h2δR' : 2 * Real.sqrt d ≤ (3 + Real.sqrt d) * (R + 2) := by
    nlinarith [hR, hδpos]
  have hsubset := sdiff_ball_subset_annulus hR hd1 hDsub y z hy hyz
  obtain ⟨hannInt, hannVal⟩ :=
    integrableOn_annulus_sub_rpow_neg_and_integral_eq (d := d) hd1 z
      (ρ := 2 * Real.sqrt d) (R := (3 + Real.sqrt d) * (R + 2)) h2δpos h2δR'
  have hbig : IntegrableOn
      (fun v => Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)))
      (Metric.ball z ((3 + Real.sqrt d) * (R + 2)) \ Metric.ball z (2 * Real.sqrt d)) :=
    hannInt.const_mul (Λ * farFieldConstant d * Real.sqrt d)
  have hsmall : IntegrableOn
      (fun v => Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)))
      (D \ Metric.ball z (2 * Real.sqrt d)) := hbig.mono_set hsubset
  have hfyD : IntegrableOn (fieldIntegrand g y) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin y
  have hfzD : IntegrableOn (fieldIntegrand g z) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin z
  have hfs : IntegrableOn (fun v => |fieldIntegrand g y v - fieldIntegrand g z v|)
      (D \ Metric.ball z (2 * Real.sqrt d)) :=
    ((hfyD.mono_set Set.sdiff_subset).sub (hfzD.mono_set Set.sdiff_subset)).abs
  have hpt : ∀ v ∈ D \ Metric.ball z (2 * Real.sqrt d),
      |fieldIntegrand g y v - fieldIntegrand g z v|
        ≤ Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) := by
    intro v hv
    have hvz : 2 * Real.sqrt d ≤ ‖v - z‖ := by
      have hnot : ¬ ‖v - z‖ < 2 * Real.sqrt d := by
        intro hlt
        exact hv.2 (by rwa [Metric.mem_ball, dist_eq_norm])
      linarith
    exact abs_fieldIntegrand_sub_le_far hd hΛ y z v hyz hvz
  have hfar1 : ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
        |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
          Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) :=
    setIntegral_mono_on hfs hsmall (hD.diff measurableSet_ball) hpt
  have hcnn : 0 ≤ Λ * farFieldConstant d * Real.sqrt d := by positivity
  have hfar2 : ∫ v in D \ Metric.ball z (2 * Real.sqrt d),
          Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ))
      ≤ ∫ v in Metric.ball z ((3 + Real.sqrt d) * (R + 2)) \ Metric.ball z (2 * Real.sqrt d),
          Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ)) :=
    setIntegral_mono_set hbig
      (Filter.Eventually.of_forall
        (fun v => mul_nonneg hcnn (Real.rpow_nonneg (norm_nonneg _) _)))
      hsubset.eventuallyLE
  have hfar3 : ∫ v in Metric.ball z ((3 + Real.sqrt d) * (R + 2))
          \ Metric.ball z (2 * Real.sqrt d),
          Λ * farFieldConstant d * Real.sqrt d * ‖v - z‖ ^ (-(d : ℝ))
      = Λ * farFieldConstant d * Real.sqrt d
          * ((d : ℝ) * unitBallVolume d
            * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
    rw [integral_const_mul, hannVal]
  exact hfar1.trans (hfar2.trans (le_of_eq hfar3))

/-- Arithmetic bound: for nonnegative `δ` and `A`, `M ≥ 0` and `L ≥ 1`, if `Lf ≤ M + L`, then
`5 δ + A δ Lf ≤ (5 + A (1 + M)) δ L`. -/
private lemma add_mul_le_mul_log {δ A M L Lf : ℝ} (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hL : 1 ≤ L) (hlog : Lf ≤ M + L) :
    5 * δ + A * δ * Lf ≤ (5 + A * (1 + M)) * δ * L := by
  have h1 : 5 * δ ≤ 5 * δ * L := by nlinarith
  have h2 : A * δ * Lf ≤ A * δ * (M + L) :=
    mul_le_mul_of_nonneg_left hlog (mul_nonneg hA hδ)
  have h4 : A * δ * M ≤ A * δ * M * L := by
    have hAM : 0 ≤ A * δ * M := mul_nonneg (mul_nonneg hA hδ) hM
    nlinarith
  nlinarith [h1, h2, h4]

/-- The logarithm of the far-field radius ratio is at most `log (3 + √d) + log (R + 2)`. -/
private lemma log_far_ratio_le {d : ℕ} (hd1 : 1 ≤ d) {R : ℝ} (hR : 1 ≤ R) :
    Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))
      ≤ Real.log (3 + Real.sqrt d) + Real.log (R + 2) := by
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hle : ((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d) ≤ (3 + Real.sqrt d) * (R + 2) :=
    div_le_self (by positivity) (by linarith [hδ1])
  calc Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))
      ≤ Real.log ((3 + Real.sqrt d) * (R + 2)) := Real.log_le_log (by positivity) hle
    _ = Real.log (3 + Real.sqrt d) + Real.log (R + 2) :=
        Real.log_mul (by positivity) (by linarith)

/-- For `R ≥ 1`, `log (R + 2) ≥ 1`. -/
private lemma one_le_log_add_two {R : ℝ} (hR : 1 ≤ R) : 1 ≤ Real.log (R + 2) := by
  have hexp : Real.exp 1 ≤ R + 2 := by
    have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have h := Real.log_le_log (Real.exp_pos 1) hexp
  rwa [Real.log_exp] at h

/-- The coefficient identity: `(2ε/w) (Λ (5 d w δ) + Λ A δ (d w Lf)) = 2 ε d Λ (5 δ + A δ Lf)`. -/
private lemma coefficient_identity {w ε Λ A δ Lf : ℝ} (n : ℝ) (hw : w ≠ 0) :
    (2 * ε / w) * (Λ * (5 * n * w * δ) + Λ * A * δ * (n * w * Lf))
      = 2 * ε * n * Λ * (5 * δ + A * δ * Lf) := by
  field_simp

/-- `eq:cellmodulus` for a bounded measurable field: for `D ⊆ B(0, R)` with `R ≥ 1`, and `y, z`
with `|y| ≤ 2R` and `|y - z| ≤ √d`, the potentials of the field differ by at most `C ε log(R + 2)`,
where `C` depends only on `d` and the bound `Λ` of the field. -/
private lemma exists_fieldPotential_cell_modulus (hd : 2 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g y v)
          - 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g z v)|
          ≤ C * ε * Real.log (R + 2) := by
  have hd1 : 1 ≤ d := by omega
  have hd1R : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hδ1 : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1R
  have hδpos : 0 < Real.sqrt d := lt_of_lt_of_le zero_lt_one hδ1
  have hδnn : 0 ≤ Real.sqrt d := hδpos.le
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hAnn : 0 ≤ farFieldConstant d := by
    rw [farFieldConstant]; positivity
  have hlogM : 0 ≤ Real.log (3 + Real.sqrt d) := Real.log_nonneg (by linarith [hδpos])
  refine ⟨2 * (d : ℝ) * Λ * Real.sqrt d
    * (5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d))), ?_, ?_⟩
  · have h5 : 0 ≤ 5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)) := by
      have h6 : 0 ≤ farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)) :=
        mul_nonneg hAnn (by linarith)
      linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hΛ0)
      hδnn) h5
  intro ε hε R hR D hD hDsub y z hy hyz
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hDfin : volume D ≠ ⊤ := by
    have hle : volume D ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
      measure_mono hDsub
    exact ne_of_lt (lt_of_le_of_lt hle measure_ball_lt_top)
  have hcoef : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hfyD : IntegrableOn (fieldIntegrand g y) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin y
  have hfzD : IntegrableOn (fieldIntegrand g z) D :=
    integrableOn_fieldIntegrand hd1 hg hΛ hD hDfin z
  have hU : 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g y v)
        - 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g z v)
      = (2 * ε / unitBallVolume d)
        * ∫ v in D, (fieldIntegrand g y v - fieldIntegrand g z v) := by
    rw [← mul_sub, ← integral_sub hfyD hfzD]
  have habsInt : |∫ v in D, (fieldIntegrand g y v - fieldIntegrand g z v)|
      ≤ ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v| := by
    have h := norm_integral_le_integral_norm (μ := volume.restrict D)
      (fun v => fieldIntegrand g y v - fieldIntegrand g z v)
    simpa only [Real.norm_eq_abs] using h
  have habsU : |2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g y v)
        - 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g z v)|
      ≤ (2 * ε / unitBallVolume d)
        * ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v| := by
    rw [hU, abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left habsInt hcoef
  have hfsD : IntegrableOn (fun v => |fieldIntegrand g y v - fieldIntegrand g z v|) D :=
    (hfyD.sub hfzD).abs
  have hsplit : ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v|
      = (∫ v in D ∩ Metric.ball z (2 * Real.sqrt d),
          |fieldIntegrand g y v - fieldIntegrand g z v|)
        + (∫ v in D \ Metric.ball z (2 * Real.sqrt d),
          |fieldIntegrand g y v - fieldIntegrand g z v|) :=
    (integral_inter_add_sdiff (μ := volume) (s := D) (t := Metric.ball z (2 * Real.sqrt d))
      measurableSet_ball hfsD).symm
  have hnear := setIntegral_abs_fieldIntegrand_sub_le_near (d := d) hd hg hΛ hD hDfin y z hyz
  have hfar := setIntegral_abs_fieldIntegrand_sub_le_far (d := d) hd hR hg hΛ hD hDfin hDsub
    y z hy hyz
  have hintD : ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v|
      ≤ Λ * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d)
        + Λ * farFieldConstant d * Real.sqrt d
          * ((d : ℝ) * unitBallVolume d
            * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) := by
    rw [hsplit]
    exact add_le_add hnear hfar
  have hbase : 5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
        * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))
      ≤ (5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
        * Real.sqrt d * Real.log (R + 2) :=
    add_mul_le_mul_log hδnn hAnn hlogM (one_le_log_add_two hR) (log_far_ratio_le hd1 hR)
  have hcoefnn : 0 ≤ 2 * ε * (d : ℝ) * Λ := by positivity
  calc |2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g y v)
        - 2 * ε / unitBallVolume d * (∫ v in D, fieldIntegrand g z v)|
      ≤ (2 * ε / unitBallVolume d)
        * ∫ v in D, |fieldIntegrand g y v - fieldIntegrand g z v| := habsU
    _ ≤ (2 * ε / unitBallVolume d)
        * (Λ * (5 * (d : ℝ) * unitBallVolume d * Real.sqrt d)
          + Λ * farFieldConstant d * Real.sqrt d
            * ((d : ℝ) * unitBallVolume d
              * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d)))) :=
        mul_le_mul_of_nonneg_left hintD hcoef
    _ = 2 * ε * (d : ℝ) * Λ
        * (5 * Real.sqrt d + farFieldConstant d * Real.sqrt d
          * Real.log (((3 + Real.sqrt d) * (R + 2)) / (2 * Real.sqrt d))) :=
        coefficient_identity (d : ℝ) hω.ne'
    _ ≤ 2 * ε * (d : ℝ) * Λ
        * ((5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
          * Real.sqrt d * Real.log (R + 2)) :=
        mul_le_mul_of_nonneg_left hbase hcoefnn
    _ = 2 * (d : ℝ) * Λ * Real.sqrt d
          * (5 + farFieldConstant d * (1 + Real.log (3 + Real.sqrt d)))
          * ε * Real.log (R + 2) := by ring


variable {K : Set (EuclideanSpace ℝ (Fin d))}

/-- **The cell modulus of the potential of the gauge.** For `D ⊆ B(0, R)` with `R ≥ 1`, and `y, z`
with `|y| ≤ 2R` and `|y - z| ≤ √d`, `|U_D(y) - U_D(z)| ≤ C ε log (R + 2)`, with `C` depending only
on `d` and `ψ = gauge K`. -/
theorem gauge_normPotential_cell_modulus (hd : 2 ≤ d) (hΨ : Adm K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ R : ℝ, 1 ≤ R →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → D ⊆ Metric.ball 0 R →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * R → ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε (gauge K) D y - normPotential d ε (gauge K) D z| ≤
          C * ε * Real.log (R + 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_fieldPotential_cell_modulus hd (measurable_gradient (gauge K))
    hΨ.norm_gradient_le
  refine ⟨C, hC0, fun ε hε R hR D hD hDsub y z hy hyz => ?_⟩
  simp only [normPotential_eq_integral]
  exact hC ε hε R hR D hD hDsub y z hy hyz

end CellModulus

/-!
## The contact bound in the rate form

The planar and the higher dimensional contact bounds, combined with the cell modulus of the
potential along a path, give for every `d ≥ 2` the potential of the cell set at a contact point of
the inradius as `C r q`, where `q` is the rate `√(log n / r)` in the plane and `log n / r` for
`d ≥ 3`.
-/

namespace Rates

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- `r √(a/r) = √(r a)` for `r > 0`. -/
private lemma mul_sqrt_div_eq {r a : ℝ} (hr : 0 < r) :
    r * Real.sqrt (a / r) = Real.sqrt (r * a) := by
  have h : r * a = r ^ 2 * (a / r) := by
    field_simp
  rw [h, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]

/-- For `n ≥ 2`, `log(n + 2) ≤ 2 log n`. -/
private lemma log_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by linarith) h1
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- For `n ≥ 2` the logarithm `log n` is positive. -/
private lemma log_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.log_pos (by linarith)

/-- **The cell modulus along a path.** The cell set of a path with `|X_j| ≤ j` lies in the ball of
radius `n + √d`, so the cell modulus of the potential holds at the scale `log (n + 2)`. -/
theorem gauge_cell_modulus_of_path (hd : 2 ≤ d) (hΨ : Adm K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ (X : ℕ → Site d) (n : ℕ), 2 ≤ n →
      (∀ j, euclidNorm (X j) ≤ j) →
      ∀ y z : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * ((n : ℝ) + Real.sqrt d) →
        ‖y - z‖ ≤ Real.sqrt d →
        |normPotential d ε (gauge K) (cellSet X n) y -
            normPotential d ε (gauge K) (cellSet X n) z| ≤
          (C * ε) * Real.log ((n : ℝ) + 2) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C_mod, hCmod, hmod⟩ := CellModulus.gauge_normPotential_cell_modulus hd hΨ
  have hl0 : 0 ≤ Real.log (1 + Real.sqrt d) :=
    Real.log_nonneg (by linarith [Real.sqrt_nonneg (d : ℝ)])
  refine ⟨C_mod * (1 + Real.log (1 + Real.sqrt d)), by positivity, ?_⟩
  intro ε hε X n hn hXn y z hy hyz
  have hsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd1)
  have hball : cellSet X n ⊆ Metric.ball 0 ((n : ℝ) + Real.sqrt d) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 X n).trans
      (Metric.ball_subset_ball (by linarith [maxRadius_le_nat X n hXn]))
  have hR : (1 : ℝ) ≤ (n : ℝ) + Real.sqrt d := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1 := hmod ε hε _ hR (cellSet X n) (CERW.Support.Occupation.measurableSet_cellSet X n)
    hball y z hy hyz
  have hL1 : 1 ≤ Real.log ((n : ℝ) + 2) := CERW.Support.Law.one_le_log_add_two hn
  have hlog : Real.log ((n : ℝ) + Real.sqrt d + 2) ≤
      (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (n : ℝ) + Real.sqrt d + 2 ≤ (1 + Real.sqrt d) * ((n : ℝ) + 2) := by
      nlinarith
    calc Real.log ((n : ℝ) + Real.sqrt d + 2)
        ≤ Real.log ((1 + Real.sqrt d) * ((n : ℝ) + 2)) :=
          Real.log_le_log (by positivity) h2
      _ = Real.log (1 + Real.sqrt d) + Real.log ((n : ℝ) + 2) :=
          Real.log_mul (by positivity) (by positivity)
      _ ≤ (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by
          nlinarith
  have hCe : 0 ≤ C_mod * ε := mul_nonneg hCmod hε
  calc _ ≤ C_mod * ε * Real.log ((n : ℝ) + Real.sqrt d + 2) := h1
    _ ≤ C_mod * ε * ((1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlog hCe
    _ = _ := by ring

/-- **The contact bound in the rate form, for every `d ≥ 2`.** On a path with `|X_j| ≤ j`, the
pointwise local-time bound and the crude bound on the cell local times, the coarse bounds
`H_n, M_n ≤ C r`, the potential of the cell set at a contact point `y₀` of the inradius is at most
`C_c r q`, where `q = √(log n / r)` if `d = 2` and `q = log n / r` otherwise. -/
theorem gauge_contact_rate (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    (C₁ C_loc C_co : ℝ) (hC₁ : 0 ≤ C₁) (hC_loc : 0 ≤ C_loc) (hC_co : 0 ≤ C_co) :
    ∃ C_c : ℝ, 0 < C_c ∧ ∀ (X : ℕ → Site d) (n : ℕ) (r : ℝ), 2 ≤ n → X 0 = 0 →
      (∀ j, euclidNorm (X j) ≤ j) → 0 < r →
      (d = 2 → 1 ≤ r ∧ Real.log ((n : ℝ) + 2) ^ 4 ≤ r ∧ 3 * C_co * r + 6 * Real.sqrt d ≤ n) →
      (3 ≤ d → 4 * Real.sqrt d ≤ n) →
      maxRadius X n ≤ C_co * r → (maxLocalTime X n : ℝ) ≤ C_co * r →
      (∀ y : Site d, euclidNorm y ≤ 3 * n →
        |(localTime X n y : ℝ) - normPotential d ε (gauge K) (cellSet X n) (toSpace y)| ≤
          C₁ * (Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2))) →
      (∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ 2 * n →
        |cellLocalTime X n v - normPotential d ε (gauge K) (cellSet X n) v| ≤
          C_loc * Real.log n + C_loc * (if d = 2
            then Real.sqrt (maxLocalTime X n) * Real.log n
            else Real.sqrt (maxLocalTime X n * Real.log n))) →
      ∀ y₀ : EuclideanSpace ℝ (Fin d), gauge K y₀ = normInnerRadius (gauge K) X n →
        y₀ ∈ closure (cellSet X n)ᶜ →
        normPotential d ε (gauge K) (cellSet X n) y₀ ≤ C_c * r * rateQ d r (Real.log n) := by
  obtain ⟨C_pm, hCpm, hpm⟩ := gauge_cell_modulus_of_path hd hΨ
  have hC₃ : 0 ≤ C_pm * ε := mul_nonneg hCpm hε.le
  by_cases hd2 : d = 2
  · obtain ⟨C_G, hCG, hG⟩ := Planar.gauge_contact_bound_two hd2 hΨ.compact hΨ.convex
      hΨ.zero_mem hε C₁ C_loc (C_pm * ε) C_co C_co hC₁ hC_loc hC₃ hC_co hC_co
    refine ⟨2 * C_G, by positivity, ?_⟩
    intro X n r hn hX0 hXn hr h2 _ hRad hLT hfine hcrude y₀ hy₀ hcl
    obtain ⟨hr1, hrlog, hlarge⟩ := h2 hd2
    rw [if_pos hd2] at hcrude
    have hU := hG X n r hn hX0 hXn hr1 hrlog hlarge hLT hRad hfine hcrude
      (hpm ε hε.le X n hn hXn) y₀ hy₀ hcl
    have hlogn := log_pos_of_two_le hn
    have hL := log_add_two_le hn
    have hsq : Real.sqrt (r * Real.log ((n : ℝ) + 2)) ≤ 2 * Real.sqrt (r * Real.log n) := by
      have h4 : r * Real.log ((n : ℝ) + 2) ≤ 2 ^ 2 * (r * Real.log n) := by
        have : r * Real.log ((n : ℝ) + 2) ≤ r * (2 * Real.log n) :=
          mul_le_mul_of_nonneg_left hL hr.le
        nlinarith [mul_nonneg hr.le hlogn.le]
      calc Real.sqrt (r * Real.log ((n : ℝ) + 2))
          ≤ Real.sqrt (2 ^ 2 * (r * Real.log n)) := Real.sqrt_le_sqrt h4
        _ = 2 * Real.sqrt (r * Real.log n) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hqn : rateQ d r (Real.log n) = Real.sqrt (Real.log n / r) := by
      unfold rateQ
      rw [if_pos hd2]
    rw [hqn]
    calc normPotential d ε (gauge K) (cellSet X n) y₀
        ≤ C_G * Real.sqrt (r * Real.log ((n : ℝ) + 2)) := hU
      _ ≤ C_G * (2 * Real.sqrt (r * Real.log n)) := mul_le_mul_of_nonneg_left hsq hCG.le
      _ = 2 * C_G * Real.sqrt (r * Real.log n) := by ring
      _ = 2 * C_G * r * Real.sqrt (Real.log n / r) := by
          rw [mul_assoc (2 * C_G) r, mul_sqrt_div_eq hr]
  · have hd3 : 3 ≤ d := by omega
    obtain ⟨C_H, hCH, hH⟩ := HighDimensional.gauge_contact_bound_three_le hd3 hΨ.compact hΨ.convex
      hΨ.zero_mem hε C₁ (C_pm * ε) hC₁ hC₃
    refine ⟨2 * C_H, by positivity, ?_⟩
    intro X n r hn hX0 hXn hr _ h4 _ _ hfine _ y₀ hy₀ hcl
    have hU := hH X n hn (h4 hd3) hX0 hXn hfine (hpm ε hε.le X n hn hXn) y₀ hy₀ hcl
    have hlogn := log_pos_of_two_le hn
    have hL := log_add_two_le hn
    have hqn : rateQ d r (Real.log n) = Real.log n / r := by
      unfold rateQ
      rw [if_neg hd2]
    rw [hqn]
    calc normPotential d ε (gauge K) (cellSet X n) y₀
        ≤ C_H * Real.log ((n : ℝ) + 2) := hU
      _ ≤ C_H * (2 * Real.log n) := mul_le_mul_of_nonneg_left hL hCH.le
      _ = 2 * C_H * r * (Real.log n / r) := by
          field_simp

end Rates

/-!
## The deterministic rates of the limit shape

On a path of the walk that satisfies the coarse bounds, the pointwise and the crude local-time
bounds, the compensated-path bound and the linear martingale bounds in the directions of the nearest
point projections onto `{ψ ≤ r}`, the inner radius, the outer radius and the profile of the local
times of the walk with the literal gauge `ψ` of a compact convex body have the rates of the limit
shape. These are the deterministic implications behind the rates: the events themselves are the
statements of the probabilistic estimates for the walk.
-/

namespace Rates

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- **The inner radius and the profile from the events.** Under the coarse bounds, the pointwise
local-time bound and the crude bound on the cell local times, the inner radius of the cell set of a
path is `r + O(r q^{1/2})`, and the local times are within `O(r q^{1/(d+1)})` of the cone
`2 d ε (r - ψ)_+`, where `r` is the scale `n = (2 d ε |K| / (d + 1)) r^{d+1}`. -/
theorem gauge_inner_rates_of_events (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    {C_co C_F C_loc : ℝ} (hC_co : 0 < C_co) (hC_F : 0 ≤ C_F) (hC_loc : 0 < C_loc) :
    ∃ C_in C_lt r₀ M : ℝ, 0 < C_in ∧ 0 < C_lt ∧ 0 < M ∧
      ∀ (X : ℕ → Site d) (n : ℕ) (r : ℝ), X 0 = 0 → (∀ j, X (j + 1) - X j ∈ unitSteps d) →
        r₀ ≤ r → 1 ≤ Real.log n → M * Real.log n ^ (d + 5) ≤ r →
        (n : ℝ) = 2 * ε * d * normBallVolume (gauge K) * r ^ (d + 1) / (d + 1) →
        maxRadius X n ≤ C_co * r → (maxLocalTime X n : ℝ) ≤ C_co * r →
        (∀ y : Site d, euclidNorm y ≤ 3 * n →
          |(localTime X n y : ℝ) - normPotential d ε (gauge K) (cellSet X n) (toSpace y)| ≤
            C_F * (Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (X j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
              Real.log ((n : ℝ) + 2))) →
        (∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ 2 * n →
          |cellLocalTime X n v - normPotential d ε (gauge K) (cellSet X n) v| ≤
            C_loc * Real.log n + C_loc * (if d = 2
              then Real.sqrt (maxLocalTime X n) * Real.log n
              else Real.sqrt (maxLocalTime X n * Real.log n))) →
        |normInnerRadius (gauge K) X n - r| ≤
            C_in * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / 2)) ∧
          ∀ y : EuclideanSpace ℝ (Fin d),
            |cellLocalTime X n y - 2 * d * ε * max (r - gauge K y) 0| ≤
              C_lt * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume (gauge K) :=
    normBallVolume_gauge_pos hΨ.compact hΨ.convex hΨ.zero_mem
  have hsd : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr (by exact_mod_cast hd1)
  set a : ℝ := 2 * ε * d * normBallVolume (gauge K) / (d + 1) with ha
  have ha0 : 0 < a := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    positivity
  obtain ⟨C_c, hC_c, hcon⟩ := gauge_contact_rate hd hΨ hε C_F C_loc C_co hC_F hC_loc.le hC_co.le
  obtain ⟨C_in, C_lt, r₀, M, hC_in, hC_lt, hM, hin⟩ := inner_rates hd hΨ hε hC_co hC_loc hC_c
  refine ⟨C_in, C_lt, max r₀ (max 1 ((3 * C_co + 6 * Real.sqrt d) / a)), max M 16, hC_in, hC_lt,
    lt_max_of_lt_left hM, ?_⟩
  intro X n r hX0 hstep hr hℓ hMr hnr hRad hLT hfine hcrude
  have hr₀ : r₀ ≤ r := (le_max_left _ _).trans hr
  have hr1 : 1 ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hr
  have hr2 : (3 * C_co + 6 * Real.sqrt d) / a ≤ r :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hr
  have hr0 : 0 < r := by linarith
  have hℓpow : 1 ≤ Real.log n ^ (d + 5) := one_le_pow₀ hℓ
  have hM' : M * Real.log n ^ (d + 5) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hMr
  have hM16 : 16 * Real.log n ^ (d + 5) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)) hMr
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num at hℓ
    · exact h
  have hnR : Real.exp 1 ≤ (n : ℝ) := by
    rwa [Real.le_log_iff_exp_le (by exact_mod_cast hn0)] at hℓ
  have hn2 : 2 ≤ n := by
    have h2 : (2 : ℝ) ≤ n := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hnR
    exact_mod_cast h2
  have hXn : ∀ j, euclidNorm (X j) ≤ j :=
    CERW.Support.Occupation.euclidNorm_le_of_steps X hX0 hstep
  have hna : (n : ℝ) = a * r ^ (d + 1) := by rw [hnr, ha]; ring
  have hnbig : (3 * C_co + 6 * Real.sqrt d) * r ≤ n := by
    have h1 : 3 * C_co + 6 * Real.sqrt d ≤ r * a := (div_le_iff₀ ha0).mp hr2
    have h2 : r ≤ r ^ d := le_self_pow₀ hr1 (by omega)
    have h3 : r * r ≤ r ^ (d + 1) := by rw [pow_succ]; nlinarith
    have h4 : (3 * C_co + 6 * Real.sqrt d) * r ≤ (r * a) * r :=
      mul_le_mul_of_nonneg_right h1 hr0.le
    rw [hna]
    nlinarith [mul_le_mul_of_nonneg_left h3 ha0.le]
  have hℓ2 : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := log_add_two_le hn2
  have hlogcond : Real.log ((n : ℝ) + 2) ^ 4 ≤ r := by
    have hl0 : 0 ≤ Real.log ((n : ℝ) + 2) := by linarith [Real.log_nonneg (show (1 : ℝ) ≤ n + 2 by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)]
    have h1 : Real.log ((n : ℝ) + 2) ^ 4 ≤ (2 * Real.log n) ^ 4 :=
      pow_le_pow_left₀ hl0 hℓ2 4
    have h2 : (2 * Real.log n) ^ 4 = 16 * Real.log n ^ 4 := by ring
    have h3 : Real.log n ^ 4 ≤ Real.log n ^ (d + 5) := pow_le_pow_right₀ hℓ (by omega)
    nlinarith
  have hcontact := hcon X n r hn2 hX0 hXn hr0
    (fun _ => ⟨hr1, hlogcond, by nlinarith
        [mul_le_mul_of_nonneg_left hr1 (Real.sqrt_nonneg (d : ℝ))]⟩)
    (fun _ => by nlinarith [mul_le_mul_of_nonneg_left hr1 (Real.sqrt_nonneg (d : ℝ))])
    hRad hLT hfine hcrude
  exact hin X n r hX0 hn2 hr₀ hℓ hM' (by nlinarith) hnr hRad hLT hcrude hcontact

/-- **The outer radius from the profile.** If the visited sites with `ψ ≥ r` have local times at
most `C_lt r q^{1/(d+1)}`, then, under the compensated-path bound and the linear martingale bounds
in the directions of a nearest-point projection onto `{ψ ≤ r}`, the outer radius of the path is at
most `r + C r q^{1/(d+1)} log n`. The subgradient selection `ξ` is arbitrary. -/
theorem gauge_outer_rates (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {C₁ C_lt : ℝ} (hC₁ : 0 < C₁) (hC_lt : 0 < C_lt) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ n : ℕ, 2 ≤ n → ∀ x : ℕ → Site d, x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) →
      ∀ r : ℝ, 1 ≤ r → 1 ≤ Real.log n → Real.log n ≤ r →
      ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        (∀ z, gauge K (P z) ≤ r) →
        (∀ z y, gauge K y ≤ r → inner ℝ (z - P z) (y - P z) ≤ 0) →
        let Z : ℕ → EuclideanSpace ℝ (Fin d) := fun t => toSpace (x t) + ε •
          ∑ j ∈ Finset.range t, if x j ∉ departureRange x j then ξ (x j) else 0
        (∀ s t : ℕ, s < t → t ≤ n →
          ‖Z t - Z s‖ ≤ C₁ * Real.sqrt ((t - s : ℝ) * Real.log n)) →
        (∀ j ≤ n, r < gauge K (toSpace (x j)) → ∀ k : ℕ, k ≤ n →
          |dynkinMart (driftStepProb d ε ξ)
              (fun z => max (inner ℝ (Projection.projDir K P (toSpace (x j))) (toSpace z) -
                k * normMax (gauge K)) 0) x n|
            ≤ C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
                  (fun z => k * normMax (gauge K) - normMax (gauge K) <
                    inner ℝ (Projection.projDir K P (toSpace (x j))) (toSpace z)),
                  (localTime x n z : ℝ)) + Real.log n)) →
        (∀ z : Site d, r ≤ gauge K (toSpace z) →
          (localTime x n z : ℝ) ≤
            C_lt * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)))) →
        normMaxRadius (gauge K) x n - r ≤
          C * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)) * Real.log n) := by
  obtain ⟨C_out, hCout, hout⟩ := Projection.gauge_outer_radius_of_crossing hd hΨ hε hell hC₁
  refine ⟨C_out * (1 + C_lt), by positivity, ?_⟩
  intro ξ hξ hξ0 n hn x hx0 hstep r hr hℓ hℓr P hP1 hP2 Z hZ hmart hprof
  have hr0 : 0 < r := by linarith
  have hℓ0 : 0 < Real.log n := by linarith
  have hρ1 : 1 ≤ r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)) :=
    RateInequalities.one_le_mul_rpow d hr hℓ hℓr
  set ρ : ℝ := r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)) with hρ
  have hL : 0 ≤ C_lt * ρ := by positivity
  have h := hout ξ hξ hξ0 n hn x hx0 hstep r hr0 P hP1 hP2 hZ hmart (C_lt * ρ) hL hprof
  have h1 : 1 + C_lt * ρ ≤ (1 + C_lt) * ρ := by nlinarith
  have h2 : C_out * (1 + C_lt * ρ) * Real.log n ≤ C_out * ((1 + C_lt) * ρ) * Real.log n :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCout.le) hℓ0.le
  calc normMaxRadius (gauge K) x n - r ≤ C_out * (1 + C_lt * ρ) * Real.log n := by linarith
    _ ≤ C_out * ((1 + C_lt) * ρ) * Real.log n := h2
    _ = C_out * (1 + C_lt) * (ρ * Real.log n) := by ring

end Rates

/-!
## The three rates together

The inner radius, the outer radius and the local-time profile of a path of the walk with the literal
gauge `ψ` of a compact convex body, on the events of the probabilistic estimates, with one constant.
-/

namespace Rates

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- **The conclusion of the rates theorem (deterministic core of Proposition 5.1).** The scale `r`
of `n = (2 d ε |K|/(d + 1)) r^{d+1}`, with `r` large compared with `log n`: a path `x` of the walk
with the literal gauge `ψ` of `K` and an arbitrary selection `ξ` of subgradients that satisfies the
coarse bounds `H_n, M_n ≤ C r`, the pointwise and the crude local-time bounds, the compensated-path
bound and the linear martingale bounds in the directions of a nearest-point projection `P` onto
`{ψ ≤ r}`, has inner radius `r + O(r q^{1/2})`, outer radius `r + O(r q^{1/(d+1)} log n)` and local
times within `O(r q^{1/(d+1)})` of `2 d ε (r - ψ)_+`, with one constant `C`. -/
def ShapeRatesOfEvents (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ε C_co C_F C_loc C₁ : ℝ) :
    Prop :=
  ∃ C r₀ M : ℝ, 0 < C ∧ 0 < M ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (x : ℕ → Site d) (n : ℕ) (r : ℝ), x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) →
        r₀ ≤ r → 1 ≤ Real.log n → M * Real.log n ^ (d + 5) ≤ r →
        (n : ℝ) = 2 * ε * d * normBallVolume (gauge K) * r ^ (d + 1) / (d + 1) →
        maxRadius x n ≤ C_co * r → (maxLocalTime x n : ℝ) ≤ C_co * r →
        (∀ y : Site d, euclidNorm y ≤ 3 * n →
          |(localTime x n y : ℝ) - normPotential d ε (gauge K) (cellSet x n) (toSpace y)| ≤
            C_F * (Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
              Real.log ((n : ℝ) + 2))) →
        (∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ 2 * n →
          |cellLocalTime x n v - normPotential d ε (gauge K) (cellSet x n) v| ≤
            C_loc * Real.log n + C_loc * (if d = 2
              then Real.sqrt (maxLocalTime x n) * Real.log n
              else Real.sqrt (maxLocalTime x n * Real.log n))) →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          (∀ z, gauge K (P z) ≤ r) →
          (∀ z y, gauge K y ≤ r → inner ℝ (z - P z) (y - P z) ≤ 0) →
          let Z : ℕ → EuclideanSpace ℝ (Fin d) := fun t => toSpace (x t) + ε •
            ∑ j ∈ Finset.range t, if x j ∉ departureRange x j then ξ (x j) else 0
          (∀ s t : ℕ, s < t → t ≤ n →
            ‖Z t - Z s‖ ≤ C₁ * Real.sqrt ((t - s : ℝ) * Real.log n)) →
          (∀ j ≤ n, r < gauge K (toSpace (x j)) → ∀ k : ℕ, k ≤ n →
            |dynkinMart (driftStepProb d ε ξ)
                (fun z => max (inner ℝ (Projection.projDir K P (toSpace (x j))) (toSpace z) -
                  k * normMax (gauge K)) 0) x n|
              ≤ C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
                    (fun z => k * normMax (gauge K) - normMax (gauge K) <
                      inner ℝ (Projection.projDir K P (toSpace (x j))) (toSpace z)),
                    (localTime x n z : ℝ)) + Real.log n)) →
          |normInnerRadius (gauge K) x n - r| ≤
              C * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / 2)) ∧
            normMaxRadius (gauge K) x n - r ≤
              C * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)) * Real.log n) ∧
            ∀ y : EuclideanSpace ℝ (Fin d),
              |cellLocalTime x n y - 2 * d * ε * max (r - gauge K y) 0| ≤
                C * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)))

/-- **The rates of the limit shape from the events.** For the literal gauge `ψ` of a compact
convex body `K` with the origin in its interior and a drift `ε` with `ε ψ(±e_i) < 1/d`, the
conclusion `ShapeRatesOfEvents` holds for all positive coarse, pointwise and crude constants and
every compensated-path and martingale constant. -/
theorem gauge_shape_rates_of_events (hd : 2 ≤ d) (hΨ : Adm K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {C_co C_F C_loc C₁ : ℝ} (hC_co : 0 < C_co) (hC_F : 0 ≤ C_F) (hC_loc : 0 < C_loc)
    (hC₁ : 0 < C₁) :
    ShapeRatesOfEvents d K ε C_co C_F C_loc C₁ := by
  unfold ShapeRatesOfEvents
  obtain ⟨C_in, C_lt, r₀, M, hC_in, hC_lt, hM, hin⟩ :=
    gauge_inner_rates_of_events hd hΨ hε hC_co hC_F hC_loc
  obtain ⟨C_ob, hC_ob, hob⟩ := gauge_outer_rates hd hΨ hε hell hC₁ hC_lt
  refine ⟨max (max C_in C_lt) C_ob, r₀, max M 1, lt_max_of_lt_left (lt_max_of_lt_left hC_in),
    lt_max_of_lt_right one_pos, ?_⟩
  intro ξ hξ hξ0 x n r hx0 hstep hr hℓ hMr hnr hRad hLT hfine hcrude P hP1 hP2 Z hZ hmart
  have hℓpow : Real.log n ≤ Real.log n ^ (d + 5) := le_self_pow₀ hℓ (by omega)
  have hℓr : Real.log n ≤ r :=
    hℓpow.trans (le_trans (le_mul_of_one_le_left (by linarith) (le_max_right _ _)) hMr)
  have hr1 : 1 ≤ r := hℓ.trans hℓr
  have hr0 : 0 < r := by linarith
  have hℓ0 : 0 < Real.log n := by linarith
  have hM' : M * Real.log n ^ (d + 5) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hMr
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num at hℓ
    · exact h
  have hnR : Real.exp 1 ≤ (n : ℝ) := by
    rwa [Real.le_log_iff_exp_le (by exact_mod_cast hn0)] at hℓ
  have hn2 : 2 ≤ n := by
    have h2 : (2 : ℝ) ≤ n := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hnR
    exact_mod_cast h2
  obtain ⟨hinner, hprofile⟩ := hin x n r hx0 hstep hr hℓ hM' hnr hRad hLT hfine hcrude
  have hprof : ∀ z : Site d, r ≤ gauge K (toSpace z) →
      (localTime x n z : ℝ) ≤ C_lt * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
    intro z hz
    have h := hprofile (toSpace z)
    rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell z), max_eq_right (by linarith), mul_zero,
      sub_zero, abs_of_nonneg (Nat.cast_nonneg _)] at h
    exact h
  have hfin := hob ξ hξ hξ0 n hn2 x hx0 hstep r hr1 hℓ hℓr P hP1 hP2 hZ hmart hprof
  have hq := rateQ_nonneg d hr0 hℓ0.le
  have hCin : C_in ≤ max (max C_in C_lt) C_ob := (le_max_left _ _).trans (le_max_left _ _)
  have hClt : C_lt ≤ max (max C_in C_lt) C_ob := (le_max_right _ _).trans (le_max_left _ _)
  have hCob : C_ob ≤ max (max C_in C_lt) C_ob := le_max_right _ _
  refine ⟨?_, ?_, ?_⟩
  · exact hinner.trans (mul_le_mul_of_nonneg_right hCin
      (mul_nonneg hr0.le (Real.rpow_nonneg hq _)))
  · exact hfin.trans (mul_le_mul_of_nonneg_right hCob
      (mul_nonneg (mul_nonneg hr0.le (Real.rpow_nonneg hq _)) hℓ0.le))
  · intro y
    exact (hprofile y).trans (mul_le_mul_of_nonneg_right hClt
      (mul_nonneg hr0.le (Real.rpow_nonneg hq _)))

end Rates

/-!
## The rates at the nonsymmetric bodies `cutDisc` and `cornerTriangle`

The cut disc `{|y| ≤ 2, y₀ ≥ -1}` and the triangle with vertices `(-1,-1)`, `(2,-1)`, `(-1,2)` are
compact convex bodies with the origin in their interior whose gauges are not even; the second has
corners. At `ε = 1/4`, the condition `ε ψ(±e_i) < 1/2` holds for both, and the rates theorem applies
to the literal gauge, with every constant of the events arbitrary.
-/

namespace Rates

/-- `cutDisc` is a compact convex body with the origin in its interior. -/
theorem adm_cutDisc : Adm cutDisc :=
  ⟨isCompact_cutDisc, convex_cutDisc, zero_mem_interior_cutDisc⟩

/-- `cornerTriangle` is a compact convex body with the origin in its interior. -/
theorem adm_cornerTriangle : Adm cornerTriangle :=
  ⟨isCompact_cornerTriangle, convex_cornerTriangle, zero_mem_interior_cornerTriangle⟩

/-- At `ε = 1/4` the asymmetric ellipticity condition `ε ψ(±e_i) < 1/d` holds for
`cornerTriangle`, whose gauge is `ψ(y) = max {-y₀, -y₁, y₀ + y₁}`. -/
theorem cornerTriangle_ellipticity (i : Fin 2) :
    (1 / 4 : ℝ) * gauge cornerTriangle (coordVec i) < 1 / ((2 : ℕ) : ℝ) ∧
      (1 / 4 : ℝ) * gauge cornerTriangle (-coordVec i) < 1 / ((2 : ℕ) : ℝ) := by
  rw [gauge_cornerTriangle_eq, gauge_cornerTriangle_eq]
  fin_cases i <;> simp [coordVec] <;> norm_num

/-- The convolution bound of the gauge of `cutDisc` at `ε = 1/4`. -/
theorem cutDisc_convBound : GaugeConvBound 2 cutDisc (1 / 4) :=
  gauge_convBound (le_refl 2) isCompact_cutDisc convex_cutDisc zero_mem_interior_cutDisc
    (by norm_num)

/-- The convolution bound of the gauge of `cornerTriangle` at `ε = 1/4`. -/
theorem cornerTriangle_convBound : GaugeConvBound 2 cornerTriangle (1 / 4) :=
  gauge_convBound (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
    zero_mem_interior_cornerTriangle (by norm_num)

/-- **The rates at `cutDisc`.** The conclusion of the rates theorem for the walk with drift
opposite to subgradients of the gauge of the cut disc, at `ε = 1/4`. -/
theorem cutDisc_shape_rates {C_co C_F C_loc C₁ : ℝ} (hC_co : 0 < C_co) (hC_F : 0 ≤ C_F)
    (hC_loc : 0 < C_loc) (hC₁ : 0 < C₁) :
    ShapeRatesOfEvents 2 cutDisc (1 / 4) C_co C_F C_loc C₁ :=
  gauge_shape_rates_of_events (le_refl 2) adm_cutDisc (by norm_num) cutDisc_ellipticity hC_co hC_F
    hC_loc hC₁

/-- **The rates at `cornerTriangle`.** The conclusion of the rates theorem for the walk with drift
opposite to subgradients of the gauge of the triangle with corners, at `ε = 1/4`. -/
theorem cornerTriangle_shape_rates {C_co C_F C_loc C₁ : ℝ} (hC_co : 0 < C_co) (hC_F : 0 ≤ C_F)
    (hC_loc : 0 < C_loc) (hC₁ : 0 < C₁) :
    ShapeRatesOfEvents 2 cornerTriangle (1 / 4) C_co C_F C_loc C₁ :=
  gauge_shape_rates_of_events (le_refl 2) adm_cornerTriangle (by norm_num)
    cornerTriangle_ellipticity hC_co hC_F hC_loc hC₁

end Rates

end CERW.Support.Norm.GaugeContactShape
