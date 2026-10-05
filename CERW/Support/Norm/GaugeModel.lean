import CERW.Support.Norm.MinkowskiGauge
import CERW.Support.Drift.Existence
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Rademacher

/-!
# The walk with a drift opposite to subgradients of an asymmetric gauge

The end of the norm section of the paper: for a compact convex set `K ⊆ ℝ^d` with the origin in its
interior, the Minkowski functional `ψ_K = gauge K` is convex and positively homogeneous but need
not be even, and the walk that steps from a first departure at `x ≠ 0` to `x ± e_i` with
probability `1/(2d) ∓ (ε/2) ξ_i(x)`, for a subgradient `ξ(x)` of `ψ_K` at `x`, exists whenever
`ε max {ψ_K(e_i), ψ_K(-e_i)} < 1/d`.

This file composes `MinkowskiGauge` with the trajectory-existence theorem for a drift field
(`CERW.Support.Drift.exists_isDriftCERW`), without `IsNorm`: the drift field is the subgradient
selection of `MinkowskiGauge`, the bound `ε |ξ_i(z)| ≤ 1/d` of that theorem is the two-sided
coordinate bound together with the ellipticity condition, and the walk is a probability space with
a process satisfying `IsDriftCERW`. It is consumed at the planar body `cutDisc` with `ε = 1/4`,
where the first-departure probabilities at `±e₀` are computed and differ.

It also records the analytic facts about `ψ_K` that the norm potential and cell estimates use and
that follow from the geometry of the body alone: the radial comparison constants `c_ψ`, `Λ_ψ` of the
Euclidean sphere, the Lipschitz bound, the bound on subgradients and gradients, and measurability
of the gradient. Each statement is for the literal `gauge K` with explicit hypotheses
`IsCompact K`, `Convex ℝ K`, `0 ∈ interior K` where they are needed, and none uses evenness.
-/

open Set Metric Topology MeasureTheory
open scoped Pointwise

namespace CERW.Support.Norm.GaugeModel

open CERW LatticeProb CERW.Support.Norm.MinkowskiGauge

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Radial comparison constants on the Euclidean sphere -/

/-- The basis vector `e_i` has norm one. -/
private lemma norm_coordVec (i : Fin d) : ‖(coordVec i : EuclideanSpace ℝ (Fin d))‖ = 1 := by
  simp [coordVec]

/-- Positive homogeneity written through the unit vector: `ψ_K(x) = |x| ψ_K(x/|x|)` for `x ≠ 0`. -/
private lemma gauge_eq_mul_gauge_unit (K : Set (EuclideanSpace ℝ (Fin d)))
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    gauge K x = ‖x‖ * gauge K (‖x‖⁻¹ • x) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_inv_smul₀ hn]
  conv_lhs => rw [h]
  rw [gauge_smul_nonneg K (norm_nonneg x)]

/-- The normalization `x/|x|` of a nonzero vector lies on the Euclidean unit sphere. -/
private lemma unit_mem_sphere {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- The image of the Euclidean unit sphere under `ψ_K` is bounded above. -/
private lemma gauge_image_bddAbove (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    BddAbove (gauge K '' sphere (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  obtain ⟨c, C, -, -, h⟩ := exists_gauge_comparison hK h0
  refine ⟨C, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have := (h u).2
  rwa [mem_sphere_zero_iff_norm.mp hu, mul_one] at this

/-- The image of the Euclidean unit sphere under `ψ_K` is bounded below by `0`. -/
private lemma gauge_image_bddBelow (K : Set (EuclideanSpace ℝ (Fin d))) :
    BddBelow (gauge K '' sphere (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨u, -, rfl⟩
  exact gauge_nonneg u

/-- `Λ_ψ = max_{|u| = 1} ψ_K(u)` is nonnegative. -/
theorem normMax_gauge_nonneg (K : Set (EuclideanSpace ℝ (Fin d))) : 0 ≤ normMax (gauge K) := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨u, -, rfl⟩
  exact gauge_nonneg u

/-- `ψ_K(x) ≤ Λ_ψ |x|` for every `x`, with `Λ_ψ` the largest value of `ψ_K` on the sphere. -/
theorem gauge_le_normMax_mul (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    (x : EuclideanSpace ℝ (Fin d)) : gauge K x ≤ normMax (gauge K) * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hle : gauge K (‖x‖⁻¹ • x) ≤ normMax (gauge K) :=
      le_csSup (gauge_image_bddAbove hK h0) (mem_image_of_mem _ (unit_mem_sphere hx))
    calc gauge K x = ‖x‖ * gauge K (‖x‖⁻¹ • x) := gauge_eq_mul_gauge_unit K hx
      _ ≤ ‖x‖ * normMax (gauge K) := mul_le_mul_of_nonneg_left hle (norm_nonneg x)
      _ = normMax (gauge K) * ‖x‖ := mul_comm _ _

/-- `c_ψ = min_{|u| = 1} ψ_K(u)` is positive and `c_ψ |x| ≤ ψ_K(x)` for every `x`, when `d ≥ 1`. -/
theorem normMin_gauge_pos_mul_le (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) :
    0 < normMin (gauge K) ∧
      ∀ x : EuclideanSpace ℝ (Fin d), normMin (gauge K) * ‖x‖ ≤ gauge K x := by
  obtain ⟨c, C, hc, -, h⟩ := exists_gauge_comparison hK h0
  have hmem : coordVec (⟨0, by omega⟩ : Fin d) ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    mem_sphere_zero_iff_norm.mpr (norm_coordVec _)
  have hlow : c ≤ normMin (gauge K) := by
    refine le_csInf ((Set.nonempty_of_mem hmem).image _) ?_
    rintro _ ⟨u, hu, rfl⟩
    have := (h u).1
    rwa [mem_sphere_zero_iff_norm.mp hu, mul_one] at this
  refine ⟨lt_of_lt_of_le hc hlow, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hle : normMin (gauge K) ≤ gauge K (‖x‖⁻¹ • x) :=
      csInf_le (gauge_image_bddBelow K) (mem_image_of_mem _ (unit_mem_sphere hx))
    calc normMin (gauge K) * ‖x‖ ≤ gauge K (‖x‖⁻¹ • x) * ‖x‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg x)
      _ = ‖x‖ * gauge K (‖x‖⁻¹ • x) := mul_comm _ _
      _ = gauge K x := (gauge_eq_mul_gauge_unit K hx).symm

/-- `c_ψ ≤ Λ_ψ`, when `d ≥ 1`. -/
theorem normMin_gauge_le_normMax_gauge (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) :
    normMin (gauge K) ≤ normMax (gauge K) := by
  have hmem : coordVec (⟨0, by omega⟩ : Fin d) ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    mem_sphere_zero_iff_norm.mpr (norm_coordVec _)
  exact (csInf_le (gauge_image_bddBelow K) (mem_image_of_mem _ hmem)).trans
    (le_csSup (gauge_image_bddAbove hK h0) (mem_image_of_mem _ hmem))

/-! ### The Lipschitz bound -/

/-- The reverse triangle inequality without evenness: `ψ_K(x) - ψ_K(y) ≤ ψ_K(x - y)`. -/
theorem gauge_sub_le (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    (x y : EuclideanSpace ℝ (Fin d)) : gauge K x - gauge K y ≤ gauge K (x - y) := by
  have h := gauge_subadditive hc h0 (x - y) y
  rw [sub_add_cancel] at h
  linarith

/-- `ψ_K` is Lipschitz for the Euclidean norm with the constant `Λ_ψ`:
`|ψ_K(x) - ψ_K(y)| ≤ Λ_ψ |x - y|`. -/
theorem abs_gauge_sub_le (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (x y : EuclideanSpace ℝ (Fin d)) :
    |gauge K x - gauge K y| ≤ normMax (gauge K) * ‖x - y‖ := by
  rw [abs_sub_le_iff]
  constructor
  · exact (gauge_sub_le hc h0 x y).trans (gauge_le_normMax_mul hK h0 _)
  · have := (gauge_sub_le hc h0 y x).trans (gauge_le_normMax_mul hK h0 (y - x))
    rwa [norm_sub_rev] at this

/-- `ψ_K` is Lipschitz with the constant `Λ_ψ`. -/
theorem lipschitzWith_gauge (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    LipschitzWith (Real.toNNReal (normMax (gauge K))) (gauge K) := by
  refine LipschitzWith.of_dist_le' fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm]
  exact abs_gauge_sub_le hK hc h0 x y

/-! ### Differentiability, gradients and subgradients -/

/-- `ψ_K` is differentiable at almost every point (Rademacher). -/
theorem ae_differentiableAt_gauge (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ (gauge K) v :=
  (lipschitzWith_gauge hK hc h0).ae_differentiableAt

/-- Where `ψ_K` is differentiable, its gradient is a subgradient: convexity of `ψ_K` along the
segment from `v` to `y` gives `ψ_K(y) ≥ ψ_K(v) + ∇ψ_K(v) · (y - v)`. -/
theorem gradient_isSubgradient_gauge (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {v : EuclideanSpace ℝ (Fin d)}
    (hv : DifferentiableAt ℝ (gauge K) v) : IsSubgradient (gauge K) v (gradient (gauge K) v) := by
  intro y
  let w : EuclideanSpace ℝ (Fin d) := y - v
  let path : ℝ → EuclideanSpace ℝ (Fin d) := fun t => v + t • w
  have hconv : ConvexOn ℝ Set.univ (gauge K ∘ path) := by
    have h := (convexOn_gauge hc h0).comp_affineMap (AffineMap.lineMap v (v + w))
    have hfun : (gauge K ∘ ⇑(AffineMap.lineMap v (v + w))) = (gauge K ∘ path) := by
      funext t
      simp only [Function.comp_apply, path]
      rw [AffineMap.lineMap_apply_module']
      congr 1
      module
    rwa [hfun] at h
  have hpath : HasDerivAt path w 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • w) w 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).smul_const w
    simpa [path] using h1.const_add v
  have hderiv : HasDerivAt (gauge K ∘ path) ((fderiv ℝ (gauge K) v) w) 0 := by
    have hc' := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hv.hasGradientAt.hasFDerivAt hpath
      (by simp [path])
    simpa only [Function.comp_apply, InnerProductSpace.toDual_apply_apply, toDual_gradient]
      using hc'
  have hslope := hconv.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num) hderiv
  rw [slope_def_field] at hslope
  have hmain : (gauge K ∘ path) 0 + (fderiv ℝ (gauge K) v) w ≤ (gauge K ∘ path) 1 := by
    simp only [Function.comp_apply]
    norm_num at hslope
    linarith
  have hrewrite : (fderiv ℝ (gauge K) v) w = inner ℝ (gradient (gauge K) v) w := by
    rw [← toDual_gradient]
    rfl
  rw [hrewrite] at hmain
  simpa [Function.comp_apply, path, w] using hmain

/-- The gradient of any function on `ℝ^d` is measurable. -/
theorem measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- A subgradient of `ψ_K` has Euclidean norm at most `Λ_ψ`: `|ξ|² = ξ · ξ ≤ ψ_K(ξ) ≤ Λ_ψ |ξ|`. -/
theorem norm_le_normMax_of_isSubgradient (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {x ξ : EuclideanSpace ℝ (Fin d)}
    (h : IsSubgradient (gauge K) x ξ) : ‖ξ‖ ≤ normMax (gauge K) := by
  have h1 := ((isSubgradient_gauge_iff K).mp h).2 ξ
  have h2 := gauge_le_normMax_mul hK h0 ξ
  rw [real_inner_self_eq_norm_mul_norm] at h1
  have h3 : ‖ξ‖ * ‖ξ‖ ≤ normMax (gauge K) * ‖ξ‖ := h1.trans h2
  rcases (norm_nonneg ξ).eq_or_lt with hz | hpos
  · rw [← hz]
    exact normMax_gauge_nonneg K
  · exact le_of_mul_le_mul_right h3 hpos

/-- A subgradient `p` of `ψ_K` at `z ≠ 0` has Euclidean norm at least `c_ψ`. -/
theorem normMin_le_norm_of_isSubgradient (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d)
    {z p : EuclideanSpace ℝ (Fin d)} (hp : IsSubgradient (gauge K) z p) (hz : z ≠ 0) :
    normMin (gauge K) ≤ ‖p‖ := by
  have h1 := ((isSubgradient_gauge_iff K).mp hp).1
  have h2 := (normMin_gauge_pos_mul_le hK h0 hd).2 z
  have h3 : inner ℝ p z ≤ ‖p‖ * ‖z‖ := real_inner_le_norm p z
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h4 : normMin (gauge K) * ‖z‖ ≤ ‖p‖ * ‖z‖ := by linarith
  exact le_of_mul_le_mul_right h4 hz0

/-- Euler's relation with `c_ψ`: a subgradient `ξ` of `ψ_K` at `x` has `ξ · x ≥ c_ψ |x|`. -/
theorem normMin_mul_le_inner_of_isSubgradient (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d)
    {x ξ : EuclideanSpace ℝ (Fin d)} (h : IsSubgradient (gauge K) x ξ) :
    normMin (gauge K) * ‖x‖ ≤ inner ℝ ξ x := by
  rw [((isSubgradient_gauge_iff K).mp h).1]
  exact (normMin_gauge_pos_mul_le hK h0 hd).2 x

/-- The gradient of `ψ_K` has Euclidean norm at most `Λ_ψ` everywhere: where `ψ_K` is
differentiable it is a subgradient, and elsewhere it is `0`. -/
theorem norm_gradient_gauge_le (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (v : EuclideanSpace ℝ (Fin d)) :
    ‖gradient (gauge K) v‖ ≤ normMax (gauge K) := by
  by_cases hv : DifferentiableAt ℝ (gauge K) v
  · exact norm_le_normMax_of_isSubgradient hK h0 (gradient_isSubgradient_gauge hc h0 hv)
  · have hz : gradient (gauge K) v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [hz, norm_zero]
    exact normMax_gauge_nonneg K

/-- Euler's relation for the gradient: where `ψ_K` is differentiable, `∇ψ_K(v) · v = ψ_K(v)`. -/
theorem inner_gradient_gauge_self (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {v : EuclideanSpace ℝ (Fin d)}
    (hv : DifferentiableAt ℝ (gauge K) v) : inner ℝ (gradient (gauge K) v) v = gauge K v :=
  ((isSubgradient_gauge_iff K).mp (gradient_isSubgradient_gauge hc h0 hv)).1

/-! ### Sublevel sets and the volume of the unit ball -/

/-- The sublevel sets `{ψ_K < ρ}` are measurable. -/
theorem measurableSet_gauge_sublevel (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (ρ : ℝ) :
    MeasurableSet {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} :=
  measurableSet_lt (continuous_gauge hc (mem_interior_iff_mem_nhds.mp h0)).measurable
    measurable_const

/-- The sublevel set `{ψ_K < ρ}` lies in the Euclidean ball of radius `ρ / c_ψ`. -/
theorem gauge_sublevel_subset_ball (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) (ρ : ℝ) :
    {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} ⊆ ball 0 (ρ / normMin (gauge K)) := by
  obtain ⟨hc, hle⟩ := normMin_gauge_pos_mul_le hK h0 hd
  intro v hv
  rw [mem_ball_zero_iff, lt_div_iff₀ hc]
  calc ‖v‖ * normMin (gauge K) = normMin (gauge K) * ‖v‖ := mul_comm _ _
    _ ≤ gauge K v := hle v
    _ < ρ := hv

/-- The Euclidean ball of radius `ρ / Λ_ψ` lies in the sublevel set `{ψ_K < ρ}`. -/
theorem ball_subset_gauge_sublevel (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) (ρ : ℝ) :
    ball (0 : EuclideanSpace ℝ (Fin d)) (ρ / normMax (gauge K)) ⊆ {v | gauge K v < ρ} := by
  have hΛ : 0 < normMax (gauge K) :=
    lt_of_lt_of_le (normMin_gauge_pos_mul_le hK h0 hd).1
      (normMin_gauge_le_normMax_gauge hK h0 hd)
  intro v hv
  rw [mem_ball_zero_iff, lt_div_iff₀ hΛ] at hv
  calc gauge K v ≤ normMax (gauge K) * ‖v‖ := gauge_le_normMax_mul hK h0 v
    _ = ‖v‖ * normMax (gauge K) := mul_comm _ _
    _ < ρ := hv

/-- Homogeneity of the sublevel sets: `{ψ_K < ρ} = ρ • {ψ_K < 1}` for `ρ > 0`. -/
theorem gauge_sublevel_eq_smul (K : Set (EuclideanSpace ℝ (Fin d))) {ρ : ℝ} (hρ : 0 < ρ) :
    {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} =
      ρ • {v : EuclideanSpace ℝ (Fin d) | gauge K v < 1} := by
  ext v
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hρ.ne']
  simp only [Set.mem_setOf_eq]
  rw [gauge_smul_nonneg K (inv_nonneg.mpr hρ.le), inv_mul_lt_iff₀ hρ, mul_one]

/-- The unit ball `{ψ_K < 1}` has finite volume. -/
theorem volume_gauge_unitBall_ne_top (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) :
    volume {v : EuclideanSpace ℝ (Fin d) | gauge K v < 1} ≠ ⊤ :=
  ((measure_mono (gauge_sublevel_subset_ball hK h0 hd 1)).trans_lt measure_ball_lt_top).ne

/-- The volume of the sublevel set `{ψ_K < ρ}` is `ρ ^ d` times the volume `|B_ψ| = |K|` of the unit
ball of `ψ_K`, for `ρ ≥ 0`. -/
theorem volume_gauge_sublevel (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} =
      ENNReal.ofReal (ρ ^ d * normBallVolume (gauge K)) := by
  rcases hρ.eq_or_lt with rfl | hρ
  · have hempty : {v : EuclideanSpace ℝ (Fin d) | gauge K v < 0} = ∅ := by
      ext v
      simpa using gauge_nonneg v
    rw [hempty, measure_empty, zero_pow (by omega), zero_mul, ENNReal.ofReal_zero]
  · have hfin := volume_gauge_unitBall_ne_top hK h0 hd
    rw [gauge_sublevel_eq_smul K hρ, Measure.addHaar_smul_of_nonneg _ hρ.le,
      finrank_euclideanSpace_fin, normBallVolume, ← ENNReal.ofReal_toReal hfin,
      ← ENNReal.ofReal_mul (pow_nonneg hρ.le _)]
    simp [ENNReal.toReal_nonneg]

/-- The volume `|B_ψ|` of the unit ball of `ψ_K`, which replaces `|B_Ψ|` in the radius `r_n`, is
positive. -/
theorem normBallVolume_gauge_pos (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) : 0 < normBallVolume (gauge K) := by
  rw [normBallVolume_gauge hK hc h0]
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  exact ENNReal.toReal_pos
    ((Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin d)) hr).trans_le
      (measure_mono hrK)).ne' hK.measure_lt_top.ne

/-! ### Rays and bounded sublevel sets -/

/-- The sublevel sets `{ψ_K < ρ}` are bounded. -/
theorem isBounded_gauge_sublevel (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) (ρ : ℝ) :
    Bornology.IsBounded {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} :=
  isBounded_ball.subset (gauge_sublevel_subset_ball hK h0 hd ρ)

/-- Restricted to a line through `y` in a unit direction, `ψ_K` is Lipschitz in the parameter. -/
theorem lipschitzWith_gauge_ray (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (y : EuclideanSpace ℝ (Fin d))
    {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ‖ = 1) :
    LipschitzWith (Real.toNNReal (normMax (gauge K))) (fun t : ℝ => gauge K (y + t • θ)) := by
  refine LipschitzWith.of_dist_le_mul fun s u => ?_
  rw [Real.dist_eq, Real.dist_eq]
  have h := abs_gauge_sub_le hK hc h0 (y + s • θ) (y + u • θ)
  have hn : ‖(y + s • θ) - (y + u • θ)‖ = |s - u| := by
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hθ, mul_one, Real.norm_eq_abs]
  rw [hn] at h
  exact h.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (abs_nonneg _))

/-- Restricted to a line, `ψ_K` is convex in the parameter. -/
theorem convexOn_gauge_ray (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (y θ : EuclideanSpace ℝ (Fin d)) :
    ConvexOn ℝ Set.univ (fun t : ℝ => gauge K (y + t • θ)) := by
  have h := (convexOn_gauge hc h0).comp_affineMap (AffineMap.lineMap y (y + θ))
  have hfun : (gauge K ∘ ⇑(AffineMap.lineMap y (y + θ))) = (fun t : ℝ => gauge K (y + t • θ)) := by
    funext t
    simp only [Function.comp_apply]
    rw [AffineMap.lineMap_apply_module']
    congr 1
    module
  rwa [hfun] at h

/-- Along a ray from `y` in the direction `θ`, `ψ_K` grows at least linearly:
`ψ_K(y + tθ) ≥ t ψ_K(θ) - ψ_K(-y)` for `t ≥ 0`. The value at `-y`, not at `y`, appears, because
`ψ_K` is not even. -/
theorem gauge_ray_coercive (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    (y θ : EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    t * gauge K θ - gauge K (-y) ≤ gauge K (y + t • θ) := by
  have h := gauge_subadditive hc h0 (y + t • θ) (-y)
  rw [show y + t • θ + -y = t • θ by abel, gauge_smul_nonneg K ht] at h
  linarith

/-! ### A subgradient selection as a drift field -/

/-- The zero vector is a subgradient of `ψ_K` at the origin. -/
theorem isSubgradient_zero_gauge (K : Set (EuclideanSpace ℝ (Fin d))) :
    IsSubgradient (gauge K) 0 0 := by
  intro y
  rw [gauge_zero, sub_zero, inner_zero_left, zero_add]
  exact gauge_nonneg y

/-- The origin of `ℤ^d` embeds as the origin of `ℝ^d`. -/
private lemma toSpace_zero_eq : toSpace (0 : Site d) = 0 := by
  ext i
  simp [toSpace]

/-- At every site there is a subgradient: `ξ x` for `x ≠ 0`, and `0` at the origin. -/
theorem isSubgradient_selection {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    (x : Site d) : IsSubgradient (gauge K) (toSpace x) (ξ x) := by
  by_cases hx : x = 0
  · subst hx
    rw [hξ0, toSpace_zero_eq]
    exact isSubgradient_zero_gauge K
  · exact hξ x hx

/-- A drift field of subgradients of `ψ_K` has norm at most `Λ_ψ`. -/
theorem norm_selection_le (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    (x : Site d) : ‖ξ x‖ ≤ normMax (gauge K) :=
  norm_le_normMax_of_isSubgradient hK h0 (isSubgradient_selection hξ hξ0 x)

/-! ### The walk with drift opposite to subgradients of `ψ_K` -/

/-- The ellipticity bound `ε |ξ_i(z)| ≤ 1/d` of the existence theorem for a drift field, from the
two-sided coordinate bounds of a subgradient of `ψ_K` and the asymmetric ellipticity condition
`ε ψ_K(±e_i) < 1/d`. -/
theorem drift_coord_bound_gauge {ε : ℝ} (hε : 0 ≤ ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0) :
    ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) := by
  intro z i
  by_cases hz : z = 0
  · rw [hz, hξ0]
    simp only [PiLp.zero_apply, abs_zero, mul_zero]
    positivity
  · obtain ⟨hlo, hhi⟩ := coord_bounds_of_isSubgradient K (hξ z hz) i
    obtain ⟨h1, h2⟩ := hell i
    have e1 : ε * ξ z i ≤ ε * gauge K (coordVec i) := mul_le_mul_of_nonneg_left hhi hε
    have e2 : ε * (-gauge K (-coordVec i)) ≤ ε * ξ z i := mul_le_mul_of_nonneg_left hlo hε
    rw [← abs_of_nonneg hε, ← abs_mul]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The centrally excited random walk with drift opposite to any subgradient selection of `ψ_K`
exists: with `ε max {ψ_K(e_i), ψ_K(-e_i)} < 1/d` there are a probability space and a process on it
satisfying `IsDriftCERW μ ε ξ X`. This is `exists_isDriftCERW`, whose hypothesis is supplied by the
two-sided coordinate bounds; no norm is assumed. -/
theorem exists_isDriftCERW_of_selection (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X :=
  CERW.Support.Drift.exists_isDriftCERW hd hε (drift_coord_bound_gauge hε hell hξ hξ0)

/-- Walk data for the compact convex body `K`: a subgradient selection of `ψ_K` with `ξ 0 = 0`
(Hahn–Banach, `exists_isSubgradient_selection`) and, under `ε max {ψ_K(e_i), ψ_K(-e_i)} < 1/d`,
a walk with that drift field. -/
theorem exists_isDriftCERW_gauge (hd : 1 ≤ d) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ)) :
    ∃ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X := by
  obtain ⟨ξ, hξ, hξ0⟩ := exists_isSubgradient_selection hc h0
  exact ⟨ξ, hξ, hξ0, exists_isDriftCERW_of_selection hd hε hell hξ hξ0⟩

/-! ### The planar body `cutDisc` with `ε = 1/4` -/

/-- The walk with drift opposite to subgradients of the gauge of `cutDisc`, at `ε = 1/4`: every
hypothesis is proved, the gauge is not a norm, and the walk data (selection, probability space,
process) exist. -/
theorem cutDisc_isDriftCERW :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cutDisc) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4) ξ X :=
  exists_isDriftCERW_gauge (by norm_num) convex_cutDisc zero_mem_interior_cutDisc (by norm_num)
    cutDisc_ellipticity

/-! ### Forced subgradients and first-departure probabilities of `cutDisc` -/

/-- The inner product with the basis vector `e_i` is the `i`-th coordinate. -/
private lemma inner_coordVec' (ξ : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    inner ℝ ξ (coordVec i) = ξ i := by
  simp [coordVec, EuclideanSpace.inner_single_right]

/-- The unit step `e_i` of `ℤ^d` embeds as the basis vector `e_i` of `ℝ^d`. -/
private lemma toSpace_unit_eq (i : Fin d) : toSpace (unit i) = coordVec i := by
  ext k
  simp [toSpace, coordVec, LatticeProb.unit, Pi.single_apply, eq_comm]

/-- The embedding of `ℤ^d` commutes with negation. -/
private lemma toSpace_neg_eq (x : Site d) : toSpace (-x) = -toSpace x := by
  ext k
  simp [toSpace]

/-- The squared Euclidean norm in the plane. -/
private lemma norm_sq_two (y : EuclideanSpace ℝ (Fin 2)) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- The gauge of `cutDisc` in closed form: `ψ(y) = max {|y|/2, -y₀}`, because
`t • cutDisc = {|y| ≤ 2t, y₀ ≥ -t}`. -/
theorem gauge_cutDisc_eq (y : EuclideanSpace ℝ (Fin 2)) :
    gauge cutDisc y = max (‖y‖ / 2) (-(y 0)) := by
  refine le_antisymm ?_ (max_le ?_ (neg_apply_zero_le_gauge_cutDisc y))
  · rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
      set M := max (‖y‖ / 2) (-(y 0)) with hM
      have hM1 : ‖y‖ / 2 ≤ M := le_max_left _ _
      have hM2 : -(y 0) ≤ M := le_max_right _ _
      have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM1
      have hmem : M⁻¹ • y ∈ cutDisc := by
        refine ⟨?_, ?_⟩
        · rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hMpos.le,
            inv_mul_le_iff₀ hMpos]
          linarith
        · show (-1 : ℝ) ≤ M⁻¹ * y 0
          have h := mul_le_mul_of_nonneg_left (neg_le.mp hM2) (inv_nonneg.mpr hMpos.le)
          rwa [mul_neg, inv_mul_cancel₀ hMpos.ne'] at h
      have h := (gauge_le_one_iff isCompact_cutDisc convex_cutDisc zero_mem_interior_cutDisc
        _).mpr hmem
      rw [gauge_smul_nonneg _ (inv_nonneg.mpr hMpos.le), inv_mul_le_iff₀ hMpos] at h
      linarith
  · exact (gauge_bounds_of_ball_subset one_pos two_pos ball_subset_cutDisc
      cutDisc_subset_closedBall y).1

/-- The subgradient of the gauge of `cutDisc` at `e₀` is forced: it is `e₀ / 2`. -/
theorem eq_of_isSubgradient_unit {ξ : EuclideanSpace ℝ (Fin 2)}
    (h : IsSubgradient (gauge cutDisc) (coordVec 0) ξ) : ξ = (1 / 2 : ℝ) • coordVec 0 := by
  obtain ⟨hEu, hle⟩ := (isSubgradient_gauge_iff cutDisc).mp h
  rw [gauge_cutDisc_coordVec_zero, inner_coordVec'] at hEu
  have key : ∀ s : ℝ, s * ξ 1 ≤ s ^ 2 / 4 := by
    intro s
    have h1 := hle (coordVec 0 + s • coordVec 1)
    rw [gauge_cutDisc_eq, inner_add_right, real_inner_smul_right, inner_coordVec',
      inner_coordVec', hEu] at h1
    have hy0 : (coordVec 0 + s • coordVec 1 : EuclideanSpace ℝ (Fin 2)) 0 = 1 := by
      simp [coordVec]
    have hy1 : (coordVec 0 + s • coordVec 1 : EuclideanSpace ℝ (Fin 2)) 1 = s := by
      simp [coordVec]
    have hn := norm_sq_two (coordVec 0 + s • coordVec 1)
    rw [hy0, hy1] at hn
    have hbound : ‖(coordVec 0 + s • coordVec 1 : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 + s ^ 2 / 2 :=
      (le_abs_self _).trans (abs_le_of_sq_le_sq (by rw [hn]; nlinarith [sq_nonneg (s ^ 2)])
        (by positivity))
    have hnn := norm_nonneg (coordVec 0 + s • coordVec 1 : EuclideanSpace ℝ (Fin 2))
    rw [hy0, max_eq_left (by linarith)] at h1
    linarith
  have hξ1 : ξ 1 = 0 := by
    refine le_antisymm ?_ ?_
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      have h2 : 4 * ε * ξ 1 ≤ 4 * ε * (0 + ε) := by nlinarith [key (4 * ε)]
      exact le_of_mul_le_mul_left h2 (by positivity)
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      have h2 : 4 * ε * 0 ≤ 4 * ε * (ξ 1 + ε) := by nlinarith [key (-(4 * ε))]
      exact le_of_mul_le_mul_left h2 (by positivity)
  ext i
  fin_cases i
  · simpa [coordVec] using hEu
  · simpa [coordVec] using hξ1

/-- The subgradient of the gauge of `cutDisc` at `-e₀` is forced: it is `-e₀`. -/
theorem eq_of_isSubgradient_neg_unit {ξ : EuclideanSpace ℝ (Fin 2)}
    (h : IsSubgradient (gauge cutDisc) (-coordVec 0) ξ) : ξ = -coordVec 0 := by
  obtain ⟨hEu, hle⟩ := (isSubgradient_gauge_iff cutDisc).mp h
  rw [gauge_cutDisc_neg_coordVec_zero, inner_neg_right, inner_coordVec'] at hEu
  have key : ∀ s : ℝ, s ^ 2 ≤ 1 → s * ξ 1 ≤ 0 := by
    intro s hs
    have h1 := hle (-coordVec 0 + s • coordVec 1)
    rw [gauge_cutDisc_eq, inner_add_right, real_inner_smul_right, inner_neg_right,
      inner_coordVec', inner_coordVec'] at h1
    have hy0 : (-coordVec 0 + s • coordVec 1 : EuclideanSpace ℝ (Fin 2)) 0 = -1 := by
      simp [coordVec]
    have hy1 : (-coordVec 0 + s • coordVec 1 : EuclideanSpace ℝ (Fin 2)) 1 = s := by
      simp [coordVec]
    have hn := norm_sq_two (-coordVec 0 + s • coordVec 1)
    rw [hy0, hy1] at hn
    have hbound : ‖(-coordVec 0 + s • coordVec 1 : EuclideanSpace ℝ (Fin 2))‖ ≤ 2 :=
      (le_abs_self _).trans (abs_le_of_sq_le_sq (by rw [hn]; nlinarith) (by norm_num))
    rw [hy0, max_eq_right (by linarith)] at h1
    linarith
  have hξ1 : ξ 1 = 0 := le_antisymm (by simpa using key 1 (by norm_num))
    (by simpa using key (-1) (by norm_num))
  ext i
  fin_cases i
  · simp [coordVec]
    linarith
  · simpa [coordVec] using hξ1

/-- Two steps of the walk: the probability that the path starts `0, a, b`, for a nonzero site `a`,
is the simple random walk probability of the step `a` times the first-departure probability at `a`
of the step `b - a`. -/
theorem cylinder_prob_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) {a : Site d} (ha : a ≠ 0) (b : Site d) :
    μ {ω | X 0 ω = 0 ∧ X 1 ω = a ∧ X 2 ω = b} =
      ENNReal.ofReal (CERW.srwStep d a) * ENNReal.ofReal (driftFirstStep d ε (ξ a) (b - a)) := by
  classical
  set x : ℕ → Site d := fun j => if j = 0 then 0 else if j = 1 then a else b with hx
  have hset : {ω | X 0 ω = 0 ∧ X 1 ω = a ∧ X 2 ω = b} = {ω | ∀ j ≤ 1 + 1, X j ω = x j} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1, h2⟩ j hj
      interval_cases j
      · simpa [hx] using h0
      · simpa [hx] using h1
      · simpa [hx] using h2
    · intro h
      exact ⟨by simpa [hx] using h 0 (by omega), by simpa [hx] using h 1 (by omega),
        by simpa [hx] using h 2 (by omega)⟩
  have hX0 : μ {ω | ∀ j ≤ 0, X j ω = x j} = 1 := by
    have hset0 : {ω | ∀ j ≤ 0, X j ω = x j} = {ω | X 0 ω ≠ 0}ᶜ := by
      ext ω
      simp [hx]
    rw [hset0, prob_compl_eq_one_iff]
    · exact hX.start
    · exact hX.measurable 0 (MeasurableSet.of_discrete : MeasurableSet ({0}ᶜ : Set (Site d)))
  have h1 : μ {ω | ∀ j ≤ 1, X j ω = x j} =
      ENNReal.ofReal (CERW.srwStep d a) := by
    have := hX.step 0 x
    rw [hX0, one_mul] at this
    have e : driftStepProb d ε ξ x 0 (x (0 + 1) - x 0) = CERW.srwStep d a := by
      simp [driftStepProb, hx]
    rw [e] at this
    exact this
  have h2 := hX.step 1 x
  rw [h1] at h2
  have e2 : driftStepProb d ε ξ x 1 (x (1 + 1) - x 1) = driftFirstStep d ε (ξ a) (b - a) := by
    simp [driftStepProb, hx, ha]
  rw [e2] at h2
  rw [hset]
  exact h2

/-- The first-departure probabilities of the walk with drift opposite to subgradients of the gauge
of `cutDisc`, at `ε = 1/4`, are forced by the geometry and differ between `e₀` and `-e₀`:
from `e₀` the step `+e₀` has probability `3/16` and the step `-e₀` has `5/16`; from `-e₀` the step
`+e₀` has `3/8` and the step `-e₀` has `1/8`. For every walk with a subgradient selection as drift
field, the path probabilities of the first two steps are therefore
`P(0, e₀, 2e₀) = 3/64`, `P(0, e₀, 0) = 5/64`, `P(0, -e₀, 0) = 3/32`, `P(0, -e₀, -2e₀) = 1/32`. -/
theorem cutDisc_cylinder_probs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ξ : Site 2 → EuclideanSpace ℝ (Fin 2)}
    (hξ : ∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cutDisc) (toSpace x) (ξ x))
    {X : ℕ → Ω → Site 2} (hX : IsDriftCERW μ (1 / 4) ξ X) :
    μ {ω | X 0 ω = 0 ∧ X 1 ω = unit 0 ∧ X 2 ω = unit 0 + unit 0} = ENNReal.ofReal (3 / 64) ∧
    μ {ω | X 0 ω = 0 ∧ X 1 ω = unit 0 ∧ X 2 ω = 0} = ENNReal.ofReal (5 / 64) ∧
    μ {ω | X 0 ω = 0 ∧ X 1 ω = -unit 0 ∧ X 2 ω = 0} = ENNReal.ofReal (3 / 32) ∧
    μ {ω | X 0 ω = 0 ∧ X 1 ω = -unit 0 ∧ X 2 ω = -unit 0 + -unit 0} = ENNReal.ofReal (1 / 32) := by
  have hp : ξ (unit 0) = (1 / 2 : ℝ) • coordVec 0 := by
    have := hξ (unit 0) (unit_ne_zero 0)
    rw [toSpace_unit_eq] at this
    exact eq_of_isSubgradient_unit this
  have hn : ξ (-unit 0) = -coordVec 0 := by
    have := hξ (-unit 0) (neg_ne_zero.mpr (unit_ne_zero 0))
    rw [toSpace_neg_eq, toSpace_unit_eq] at this
    exact eq_of_isSubgradient_neg_unit this
  have hp0 : ((1 / 2 : ℝ) • coordVec 0 : EuclideanSpace ℝ (Fin 2)) 0 = 1 / 2 := by
    simp [coordVec]
  have hn0 : (-coordVec 0 : EuclideanSpace ℝ (Fin 2)) 0 = -1 := by simp [coordVec]
  have hs : CERW.srwStep 2 (unit 0) = 1 / 4 := by
    rw [CERW.Support.Law.srwStep_unit]; norm_num
  have hs' : CERW.srwStep 2 (-unit 0) = 1 / 4 := by
    rw [CERW.Support.Law.srwStep_neg_unit]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cylinder_prob_two hX (unit_ne_zero 0), hs, hp, add_sub_cancel_left,
      CERW.Support.Drift.driftFirstStep_unit, hp0, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · rw [cylinder_prob_two hX (unit_ne_zero 0), hs, hp, zero_sub,
      CERW.Support.Drift.driftFirstStep_neg_unit, hp0, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · rw [cylinder_prob_two hX (neg_ne_zero.mpr (unit_ne_zero 0)), hs', hn, zero_sub, neg_neg,
      CERW.Support.Drift.driftFirstStep_unit, hn0, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  · rw [cylinder_prob_two hX (neg_ne_zero.mpr (unit_ne_zero 0)), hs', hn, add_sub_cancel_left,
      CERW.Support.Drift.driftFirstStep_neg_unit, hn0, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num

/-- The actual nonsymmetric walk: a probability space and a process with a subgradient selection of
the gauge of `cutDisc` as drift field at `ε = 1/4`, together with the four two-step path
probabilities of `cutDisc_cylinder_probs`. -/
theorem cutDisc_walk :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cutDisc) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4) ξ X ∧
        μ {ω | X 0 ω = 0 ∧ X 1 ω = unit 0 ∧ X 2 ω = unit 0 + unit 0} = ENNReal.ofReal (3 / 64) ∧
        μ {ω | X 0 ω = 0 ∧ X 1 ω = -unit 0 ∧ X 2 ω = -unit 0 + -unit 0} =
          ENNReal.ofReal (1 / 32) := by
  obtain ⟨ξ, hξ, hξ0, Ω, hΩ, μ, hμ, X, hX⟩ := cutDisc_isDriftCERW
  exact ⟨ξ, hξ, hξ0, Ω, hΩ, μ, hμ, X, hX, (cutDisc_cylinder_probs hξ hX).1,
    (cutDisc_cylinder_probs hξ hX).2.2.2⟩

end CERW.Support.Norm.GaugeModel
