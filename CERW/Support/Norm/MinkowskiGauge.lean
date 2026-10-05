import CERW.Model.Norm
import CERW.Support.Drift.KernelValues
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Measure

/-!
# The Minkowski functional of an asymmetric convex body

The closing remark of the norm section of the paper. The proofs for a norm `Ψ` use the symmetry
`Ψ(-x) = Ψ(x)` only to bound the coordinates of the subgradients. For a compact convex set
`K ⊆ ℝ^d` with the origin in its interior, the Minkowski functional
`ψ_K(x) = inf {t > 0 : x ∈ t K}` is convex, positively homogeneous, positive away from the origin
and comparable to the Euclidean norm, but it need not be even; its subgradients satisfy the
two-sided bounds `-ψ_K(-e_i) ≤ ξ_i ≤ ψ_K(e_i)`, and the first-departure probabilities
`1/(2d) ∓ (ε/2) ξ_i` are positive when `ε max {ψ_K(e_i), ψ_K(-e_i)} < 1/d`.

The functional is Mathlib's `gauge K`, whose definition `sInf {t | 0 < t ∧ x ∈ t • K}` is the one
above. Nothing here uses evenness or absolute homogeneity: the statements of the section on positive
homogeneity hold for every set `K` and use only `ψ_K(t x) = t ψ_K(x)` for `t ≥ 0`, and `ψ_K` is not
an `IsNorm` function in general (the last section gives a concrete planar body, a disc cut by a
half-plane, with `ψ(e₀) = 1/2 ≠ 1 = ψ(-e₀)`, and a subgradient of it that violates the symmetric
bound `|ξ_i| ≤ ψ(e_i)`).

This is support for the asymmetric extension. The statements about the walk with a norm, whose
hypothesis is `IsNorm Ψ`, are not restated here for `ψ_K`.
-/

open Set Metric Topology MeasureTheory
open scoped Pointwise

namespace CERW.Support.Norm.MinkowskiGauge

open CERW LatticeProb

variable {d : ℕ}

/-! ### The functional is the infimum `inf {t > 0 : x ∈ t K}` -/

/-- The Minkowski functional of `K` is, by definition, `x ↦ inf {t > 0 : x ∈ t K}`. -/
theorem gauge_eq_sInf (K : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    gauge K x = sInf {t : ℝ | 0 < t ∧ x ∈ t • K} :=
  rfl

/-- If the origin is an interior point of `K`, the set of `t > 0` with `x ∈ t K` is nonempty and
`ψ_K(x)` is its greatest lower bound, so the infimum is not the junk value of `sInf ∅`. -/
theorem isGLB_gauge {K : Set (EuclideanSpace ℝ (Fin d))}
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (x : EuclideanSpace ℝ (Fin d)) :
    IsGLB {t : ℝ | 0 < t ∧ x ∈ t • K} (gauge K x) :=
  isGLB_csInf (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)).gauge_set_nonempty
    ⟨0, fun _ ht => ht.1.le⟩

/-! ### Positive homogeneity and the subgradient inequalities (every set `K`) -/

/-- Positive homogeneity of the Minkowski functional of any set: `ψ_K(t x) = t ψ_K(x)` for
`t ≥ 0`. No symmetry of `K` is used. -/
theorem gauge_smul_nonneg (K : Set (EuclideanSpace ℝ (Fin d))) {t : ℝ} (ht : 0 ≤ t)
    (x : EuclideanSpace ℝ (Fin d)) : gauge K (t • x) = t * gauge K x := by
  rw [gauge_smul_of_nonneg ht, smul_eq_mul]

/-- The inner product with the basis vector `e_i` is the `i`-th coordinate. -/
private lemma inner_coordVec (ξ : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    inner ℝ ξ (coordVec i) = ξ i := by
  simp [coordVec, EuclideanSpace.inner_single_right]

/-- Euler's relation for a positively homogeneous functional: `ξ` is a subgradient of `ψ_K` at
`x` exactly when `ξ · x = ψ_K(x)` and `ξ · y ≤ ψ_K(y)` for every `y`. Holds for every set `K`. -/
theorem isSubgradient_gauge_iff (K : Set (EuclideanSpace ℝ (Fin d)))
    {x ξ : EuclideanSpace ℝ (Fin d)} :
    IsSubgradient (gauge K) x ξ ↔
      inner ℝ ξ x = gauge K x ∧ ∀ y, inner ℝ ξ y ≤ gauge K y := by
  constructor
  · intro h
    have key : ∀ y, gauge K x + inner ℝ ξ y - inner ℝ ξ x ≤ gauge K y := by
      intro y
      have hh := h y
      rw [inner_sub_right] at hh
      linarith
    have hlow : gauge K x ≤ inner ℝ ξ x := by
      have h0 := key 0
      rw [inner_zero_right, gauge_zero] at h0
      linarith
    have hhigh : inner ℝ ξ x ≤ gauge K x := by
      have h2 := key ((2 : ℝ) • x)
      rw [real_inner_smul_right, gauge_smul_nonneg K (by norm_num : (0 : ℝ) ≤ 2)] at h2
      linarith
    have heuler : inner ℝ ξ x = gauge K x := le_antisymm hhigh hlow
    refine ⟨heuler, fun y => ?_⟩
    have hy := key y
    rw [heuler] at hy
    linarith
  · rintro ⟨h1, h2⟩ y
    rw [inner_sub_right, h1]
    have := h2 y
    linarith

/-- The two-sided coordinate bounds `-ψ_K(-e_i) ≤ ξ_i ≤ ψ_K(e_i)` for a subgradient `ξ` of `ψ_K`
at any point. The lower bound uses `ψ_K(-e_i)`, not `ψ_K(e_i)`, and there is no evenness. Holds for
every set `K`. -/
theorem coord_bounds_of_isSubgradient (K : Set (EuclideanSpace ℝ (Fin d)))
    {x ξ : EuclideanSpace ℝ (Fin d)} (h : IsSubgradient (gauge K) x ξ) (i : Fin d) :
    -gauge K (-coordVec i) ≤ ξ i ∧ ξ i ≤ gauge K (coordVec i) := by
  have hb := ((isSubgradient_gauge_iff K).mp h).2
  have hpos := hb (coordVec i)
  have hneg := hb (-coordVec i)
  rw [inner_coordVec] at hpos
  rw [inner_neg_right, inner_coordVec] at hneg
  constructor <;> linarith

/-! ### The body: compact, convex, with the origin in its interior -/

section Body

variable {K : Set (EuclideanSpace ℝ (Fin d))}

/-- A set with the origin in its interior is a neighbourhood of the origin. -/
private lemma mem_nhds_zero_of_mem_interior (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) :=
  mem_interior_iff_mem_nhds.mp h0

/-- A set with the origin in its interior is absorbent. -/
private lemma absorbent_of_mem_interior (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    Absorbent ℝ K :=
  absorbent_nhds_zero (mem_nhds_zero_of_mem_interior h0)

/-- A compact set is von Neumann bounded. -/
private lemma isVonNBounded_of_isCompact (hK : IsCompact K) : Bornology.IsVonNBounded ℝ K :=
  NormedSpace.isVonNBounded_of_isBounded ℝ hK.isBounded

/-- `ψ_K(x) ≤ 1` exactly when `x ∈ K`: the body is the closed unit sublevel set of its
functional. -/
theorem gauge_le_one_iff (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (x : EuclideanSpace ℝ (Fin d)) :
    gauge K x ≤ 1 ↔ x ∈ K := by
  rw [gauge_le_one_iff_mem_closure hc (mem_nhds_zero_of_mem_interior h0), hK.isClosed.closure_eq]

/-- `ψ_K(x) < 1` exactly when `x` is an interior point of `K`. -/
theorem gauge_lt_one_iff (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (x : EuclideanSpace ℝ (Fin d)) :
    gauge K x < 1 ↔ x ∈ interior K :=
  gauge_lt_one_iff_mem_interior hc (mem_nhds_zero_of_mem_interior h0)

/-- `ψ_K` vanishes only at the origin. -/
theorem gauge_eq_zero_iff (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    (x : EuclideanSpace ℝ (Fin d)) : gauge K x = 0 ↔ x = 0 :=
  gauge_eq_zero (absorbent_of_mem_interior h0) (isVonNBounded_of_isCompact hK)

/-- `ψ_K` is strictly positive away from the origin. -/
theorem gauge_pos_of_ne_zero (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ≠ 0) : 0 < gauge K x :=
  (gauge_pos (absorbent_of_mem_interior h0) (isVonNBounded_of_isCompact hK)).mpr hx

/-- `ψ_K` is subadditive. -/
theorem gauge_subadditive (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    (x y : EuclideanSpace ℝ (Fin d)) : gauge K (x + y) ≤ gauge K x + gauge K y :=
  gauge_add_le hc (absorbent_of_mem_interior h0) x y

/-- `ψ_K` is convex on `ℝ^d`. -/
theorem convexOn_gauge (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ConvexOn ℝ univ (gauge K) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  calc gauge K (a • x + b • y) ≤ gauge K (a • x) + gauge K (b • y) := gauge_subadditive hc h0 _ _
    _ = a • gauge K x + b • gauge K y := by
      rw [gauge_smul_nonneg K ha, gauge_smul_nonneg K hb, smul_eq_mul, smul_eq_mul]

/-- Comparison with explicit constants: if `K` contains the ball of radius `r` and lies in the ball
of radius `M` about the origin, then `‖x‖ / M ≤ ψ_K(x) ≤ ‖x‖ / r`. -/
theorem gauge_bounds_of_ball_subset {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hrK : ball (0 : EuclideanSpace ℝ (Fin d)) r ⊆ K) (hKM : K ⊆ closedBall 0 M)
    (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ / M ≤ gauge K x ∧ gauge K x ≤ ‖x‖ / r := by
  have habs : Absorbent ℝ K := (absorbent_ball_zero hr).mono hrK
  refine ⟨le_gauge_of_subset_closedBall habs hM.le hKM, ?_⟩
  rw [le_div_iff₀ hr, mul_comm]
  exact mul_gauge_le_norm hrK

/-- The comparison `c ‖x‖ ≤ ψ_K(x) ≤ C ‖x‖` with positive constants. -/
theorem exists_gauge_comparison (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      c * ‖x‖ ≤ gauge K x ∧ gauge K x ≤ C * ‖x‖ := by
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp (mem_nhds_zero_of_mem_interior h0)
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hM' : K ⊆ closedBall 0 (max M 1) :=
    hM.trans (closedBall_subset_closedBall (le_max_left M 1))
  refine ⟨1 / max M 1, 1 / r, by positivity, by positivity, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := gauge_bounds_of_ball_subset hr (lt_of_lt_of_le one_pos (le_max_right M 1))
    hrK hM' x
  exact ⟨by rwa [one_div, inv_mul_eq_div], by rwa [one_div, inv_mul_eq_div]⟩

/-- The volume `|B_ψ|` of the unit ball of `ψ_K` is the volume `|K|` of the body, the quantity
that replaces `|B_Ψ|` in the radius of the walk. -/
theorem normBallVolume_gauge (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    normBallVolume (gauge K) = (volume K).toReal := by
  have hset : {y : EuclideanSpace ℝ (Fin d) | gauge K y < 1} = interior K :=
    setOf_gauge_lt_one_eq_interior hc (mem_nhds_zero_of_mem_interior h0)
  unfold normBallVolume
  rw [hset]
  congr 1
  refine le_antisymm (measure_mono interior_subset) ?_
  calc volume K ≤ volume (interior K ∪ frontier K) :=
        measure_mono (by rw [← closure_eq_interior_union_frontier, hK.isClosed.closure_eq])
    _ ≤ volume (interior K) + volume (frontier K) := measure_union_le _ _
    _ = volume (interior K) := by rw [hc.addHaar_frontier volume, add_zero]

/-- Every point has a subgradient of `ψ_K` (Hahn–Banach, for the sublinear functional `ψ_K`). -/
theorem exists_isSubgradient (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ ξ : EuclideanSpace ℝ (Fin d), IsSubgradient (gauge K) x ξ := by
  by_cases hx : x = 0
  · subst hx
    refine ⟨0, fun y => ?_⟩
    rw [gauge_zero, sub_zero, inner_zero_left, zero_add]
    exact gauge_nonneg y
  · obtain ⟨g, hg1, hg2⟩ :=
      exists_extension_of_le_sublinear (LinearPMap.mkSpanSingleton x (gauge K x) hx) (gauge K)
      (fun c hc' y => by rw [gauge_smul_nonneg K hc'.le])
      (gauge_subadditive hc h0)
      (fun y => by
        obtain ⟨y, hy⟩ := y
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        have h1 : (LinearPMap.mkSpanSingleton x (gauge K x) hx) ⟨c • x, hy⟩ =
            c * gauge K x := by
          rw [LinearPMap.mkSpanSingleton'_apply]
          simp
        rw [h1]
        show c * gauge K x ≤ gauge K (c • x)
        by_cases hcn : 0 ≤ c
        · rw [gauge_smul_nonneg K hcn]
        · exact (mul_nonpos_of_nonpos_of_nonneg (not_le.mp hcn).le
            (gauge_nonneg x)).trans (gauge_nonneg _))
    have hgx : g x = gauge K x := by
      have := hg1 ⟨x, Submodule.mem_span_singleton_self x⟩
      rw [show (⟨x, Submodule.mem_span_singleton_self x⟩ :
          (LinearPMap.mkSpanSingleton x (gauge K x) hx).domain)
        = ⟨(1 : ℝ) • x, by simp⟩ from by simp] at this
      rw [LinearPMap.mkSpanSingleton'_apply] at this
      simpa using this
    let gc : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap g
    refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm gc, ?_⟩
    rw [isSubgradient_gauge_iff]
    have hin : ∀ z,
        inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm gc) z = g z := by
      intro z
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    exact ⟨by rw [hin, hgx], fun y => by rw [hin]; exact hg2 y⟩

/-- A subgradient selection of `ψ_K` with `ξ 0 = 0`, at the nonzero sites of `ℤ^d`. -/
theorem exists_isSubgradient_selection (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) :
    ∃ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) ∧ ξ 0 = 0 := by
  classical
  refine ⟨fun x => if x = 0 then 0 else (exists_isSubgradient hc h0 (toSpace x)).choose,
    fun x hx => ?_, by simp⟩
  simp only [hx, if_false]
  exact (exists_isSubgradient hc h0 (toSpace x)).choose_spec

/-- Under the asymmetric ellipticity condition `ε ψ_K(±e_i) < 1/d`, the first-departure
probabilities `1/(2d) ∓ (ε/2) ξ_i` at `±e_i` are positive for every subgradient `ξ` of `ψ_K`. -/
theorem driftFirstStep_pos {ε : ℝ} (hε : 0 ≤ ε)
    (hell : ∀ i : Fin d, ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧
      ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {x ξ : EuclideanSpace ℝ (Fin d)} (h : IsSubgradient (gauge K) x ξ) (i : Fin d) :
    0 < driftFirstStep d ε ξ (unit i) ∧ 0 < driftFirstStep d ε ξ (-unit i) := by
  have hd : (d : ℝ) ≠ 0 := by
    have : d ≠ 0 := fun h0 => by subst h0; exact i.elim0
    exact_mod_cast this
  obtain ⟨hlo, hhi⟩ := coord_bounds_of_isSubgradient K h i
  obtain ⟨h1, h2⟩ := hell i
  have e1 : ε * ξ i ≤ ε * gauge K (coordVec i) := mul_le_mul_of_nonneg_left hhi hε
  have e2 : ε * (-gauge K (-coordVec i)) ≤ ε * ξ i := mul_le_mul_of_nonneg_left hlo hε
  have hhalf : 1 / (2 * (d : ℝ)) = 1 / (d : ℝ) / 2 := by field_simp
  rw [CERW.Support.Drift.driftFirstStep_unit, CERW.Support.Drift.driftFirstStep_neg_unit, hhalf]
  constructor <;> nlinarith

end Body

/-! ### A nonsymmetric planar body -/

/-- The disc of radius `2` about the origin in the plane, cut by the half-plane `y₀ ≥ -1`. It is
compact, convex, contains a ball about the origin, and is not symmetric about the origin. -/
def cutDisc : Set (EuclideanSpace ℝ (Fin 2)) :=
  closedBall 0 2 ∩ {y | -1 ≤ y 0}

/-- The basis vector `e_i` has norm one. -/
private lemma norm_coordVec (i : Fin d) : ‖(coordVec i : EuclideanSpace ℝ (Fin d))‖ = 1 := by
  simp [coordVec]

/-- The inner product of the basis vector `e_i` on the left is the `i`-th coordinate. -/
private lemma inner_coordVec_left (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    inner ℝ (coordVec i) y = y i := by
  simp [coordVec, EuclideanSpace.inner_single_left]

/-- A point of norm at most `2` with first coordinate at least `-1` lies in `cutDisc`. -/
private lemma mem_cutDisc {v : EuclideanSpace ℝ (Fin 2)} (h1 : ‖v‖ ≤ 2) (h2 : -1 ≤ v 0) :
    v ∈ cutDisc :=
  ⟨mem_closedBall_zero_iff.mpr h1, h2⟩

/-- `cutDisc` is compact. -/
theorem isCompact_cutDisc : IsCompact cutDisc :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2).inter_right
    (isClosed_le continuous_const (by fun_prop))

/-- `cutDisc` is convex. -/
theorem convex_cutDisc : Convex ℝ cutDisc :=
  (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2).inter
    (convex_halfSpace_ge (f := fun y : EuclideanSpace ℝ (Fin 2) => y 0)
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩ (-1))

/-- `cutDisc` contains the open unit disc. -/
theorem ball_subset_cutDisc : ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ cutDisc := by
  intro y hy
  have hy1 : ‖y‖ < 1 := by simpa using hy
  have h1 := PiLp.norm_apply_le y 0
  rw [Real.norm_eq_abs] at h1
  exact mem_cutDisc (by linarith) (by linarith [neg_abs_le (y 0)])

/-- `cutDisc` lies in the closed disc of radius `2`. -/
theorem cutDisc_subset_closedBall : cutDisc ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2 :=
  inter_subset_left

/-- The origin is an interior point of `cutDisc`. -/
theorem zero_mem_interior_cutDisc : (0 : EuclideanSpace ℝ (Fin 2)) ∈ interior cutDisc :=
  interior_mono ball_subset_cutDisc (isOpen_ball.subset_interior_iff.mpr (subset_refl _)
    (mem_ball_self one_pos))

/-- The functional of `cutDisc` dominates the negative of the first coordinate: a point of
`t • cutDisc` has first coordinate at least `-t`. -/
theorem neg_apply_zero_le_gauge_cutDisc (y : EuclideanSpace ℝ (Fin 2)) :
    -(y 0) ≤ gauge cutDisc y := by
  by_contra h
  obtain ⟨b, hb, hby, hyb⟩ :=
    exists_lt_of_gauge_lt (absorbent_of_mem_interior zero_mem_interior_cutDisc) (not_le.mp h)
  obtain ⟨k, hk, rfl⟩ := mem_smul_set.mp hyb
  have hk0 : -1 ≤ k 0 := hk.2
  have hbk : (b • k) 0 = b * k 0 := rfl
  rw [hbk] at hby
  nlinarith [mul_le_mul_of_nonneg_left hk0 hb.le]

/-- A point `v` of norm one has `ψ(v) ≥ 1/2`. -/
private lemma half_le_gauge_cutDisc {v : EuclideanSpace ℝ (Fin 2)} (hv : ‖v‖ = 1) :
    1 / 2 ≤ gauge cutDisc v := by
  have := (gauge_bounds_of_ball_subset one_pos two_pos ball_subset_cutDisc
    cutDisc_subset_closedBall v).1
  rwa [hv] at this

/-- If `2 v` lies in `cutDisc` then `ψ(v) ≤ 1/2`. -/
private lemma gauge_le_half_cutDisc {v : EuclideanSpace ℝ (Fin 2)}
    (hv : ((2 : ℝ) • v) ∈ cutDisc) : gauge cutDisc v ≤ 1 / 2 := by
  have h := (gauge_le_one_iff isCompact_cutDisc convex_cutDisc
    zero_mem_interior_cutDisc _).mpr hv
  rw [gauge_smul_nonneg _ (by norm_num : (0 : ℝ) ≤ 2)] at h
  linarith

/-- `ψ(e₀) = 1/2`. -/
theorem gauge_cutDisc_coordVec_zero : gauge cutDisc (coordVec 0) = 1 / 2 := by
  refine le_antisymm (gauge_le_half_cutDisc (mem_cutDisc ?_ ?_))
    (half_le_gauge_cutDisc (norm_coordVec 0))
  · rw [norm_smul, norm_coordVec]; norm_num
  · simp [coordVec]; norm_num

/-- `ψ(-e₀) = 1`. -/
theorem gauge_cutDisc_neg_coordVec_zero : gauge cutDisc (-coordVec 0) = 1 := by
  refine le_antisymm ?_ ?_
  · exact (gauge_le_one_iff isCompact_cutDisc convex_cutDisc zero_mem_interior_cutDisc _).mpr
      (mem_cutDisc (by rw [norm_neg, norm_coordVec]; norm_num) (by simp [coordVec]))
  · have := neg_apply_zero_le_gauge_cutDisc (-coordVec 0)
    simpa [coordVec] using this

/-- `ψ(e₁) = 1/2`. -/
theorem gauge_cutDisc_coordVec_one : gauge cutDisc (coordVec 1) = 1 / 2 := by
  refine le_antisymm (gauge_le_half_cutDisc (mem_cutDisc ?_ ?_))
    (half_le_gauge_cutDisc (norm_coordVec 1))
  · rw [norm_smul, norm_coordVec]; norm_num
  · simp [coordVec]

/-- `ψ(-e₁) = 1/2`. -/
theorem gauge_cutDisc_neg_coordVec_one : gauge cutDisc (-coordVec 1) = 1 / 2 := by
  refine le_antisymm (gauge_le_half_cutDisc (mem_cutDisc ?_ ?_))
    (half_le_gauge_cutDisc (by rw [norm_neg, norm_coordVec]))
  · rw [norm_smul, norm_neg, norm_coordVec]; norm_num
  · simp [coordVec]

/-- The functional of `cutDisc` is not even: `ψ(-e₀) = 1 ≠ 1/2 = ψ(e₀)`. -/
theorem gauge_cutDisc_neg_ne : gauge cutDisc (-coordVec 0) ≠ gauge cutDisc (coordVec 0) := by
  rw [gauge_cutDisc_neg_coordVec_zero, gauge_cutDisc_coordVec_zero]
  norm_num

/-- The functional of `cutDisc` is not a norm: absolute homogeneity fails at `t = -1`. -/
theorem not_isNorm_gauge_cutDisc : ¬ IsNorm (gauge cutDisc) := fun h => by
  have := h.smul (-1) (coordVec 0)
  rw [neg_one_smul, abs_neg, abs_one, one_mul] at this
  exact gauge_cutDisc_neg_ne this

/-- `-e₀` is a subgradient of `ψ` at `-e₀`. -/
theorem isSubgradient_cutDisc : IsSubgradient (gauge cutDisc) (-coordVec 0) (-coordVec 0) := by
  rw [isSubgradient_gauge_iff]
  refine ⟨?_, fun y => ?_⟩
  · rw [inner_neg_neg, real_inner_self_eq_norm_sq, norm_coordVec, gauge_cutDisc_neg_coordVec_zero]
    norm_num
  · rw [inner_neg_left, inner_coordVec_left]
    exact neg_apply_zero_le_gauge_cutDisc y

/-- The symmetric coordinate bound `|ξ_i| ≤ ψ(e_i)` fails for `cutDisc`, while the two-sided bound
holds, with equality in its lower half: the subgradient `ξ = -e₀` of `ψ` at `-e₀` has
`ξ₀ = -ψ(-e₀)` and `ψ(e₀) < |ξ₀|`. -/
theorem two_sided_bound_sharp :
    ∃ x ξ : EuclideanSpace ℝ (Fin 2), IsSubgradient (gauge cutDisc) x ξ ∧
      ξ 0 = -gauge cutDisc (-coordVec 0) ∧ gauge cutDisc (coordVec 0) < |ξ 0| := by
  refine ⟨-coordVec 0, -coordVec 0, isSubgradient_cutDisc, ?_, ?_⟩
  · rw [gauge_cutDisc_neg_coordVec_zero]; simp [coordVec]
  · rw [gauge_cutDisc_coordVec_zero]; simp [coordVec]; norm_num

/-- At `ε = 1/4` the asymmetric ellipticity condition `ε ψ(±e_i) < 1/d` holds for `cutDisc`. -/
theorem cutDisc_ellipticity (i : Fin 2) :
    (1 / 4 : ℝ) * gauge cutDisc (coordVec i) < 1 / ((2 : ℕ) : ℝ) ∧
      (1 / 4 : ℝ) * gauge cutDisc (-coordVec i) < 1 / ((2 : ℕ) : ℝ) := by
  fin_cases i
  · simp only [Fin.zero_eta, gauge_cutDisc_coordVec_zero, gauge_cutDisc_neg_coordVec_zero]
    norm_num
  · simp only [Fin.mk_one, gauge_cutDisc_coordVec_one, gauge_cutDisc_neg_coordVec_one]
    norm_num

/-- The walk with drift opposite to subgradients of `ψ` for `cutDisc`, at `ε = 1/4`: a subgradient
selection with `ξ 0 = 0` exists, and at every nonzero site every first-departure probability is
positive. -/
theorem cutDisc_kernel_pos :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 → IsSubgradient (gauge cutDisc) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∀ x : Site 2, x ≠ 0 → ∀ i : Fin 2,
        0 < driftFirstStep 2 (1 / 4) (ξ x) (unit i) ∧
          0 < driftFirstStep 2 (1 / 4) (ξ x) (-unit i) := by
  obtain ⟨ξ, hξ, hξ0⟩ := exists_isSubgradient_selection convex_cutDisc zero_mem_interior_cutDisc
  exact ⟨ξ, hξ, hξ0, fun x hx i => driftFirstStep_pos (by norm_num) cutDisc_ellipticity (hξ x hx) i⟩

/-- The condition `ε ψ(e_i) < 1/d` with only the positive basis vectors does not make the
first-departure probabilities positive for `cutDisc`: at `ε = 3/4` it holds, yet the probability
of stepping to `x - e₀` is negative for the subgradient `ξ = -e₀`. -/
theorem positive_side_ellipticity_insufficient :
    (∀ i : Fin 2, (3 / 4 : ℝ) * gauge cutDisc (coordVec i) < 1 / ((2 : ℕ) : ℝ)) ∧
      ∃ x ξ : EuclideanSpace ℝ (Fin 2), IsSubgradient (gauge cutDisc) x ξ ∧
        driftFirstStep 2 (3 / 4) ξ (-unit 0) < 0 := by
  refine ⟨fun i => ?_, -coordVec 0, -coordVec 0, isSubgradient_cutDisc, ?_⟩
  · fin_cases i
    · simp only [Fin.zero_eta, gauge_cutDisc_coordVec_zero]
      norm_num
    · simp only [Fin.mk_one, gauge_cutDisc_coordVec_one]
      norm_num
  · rw [CERW.Support.Drift.driftFirstStep_neg_unit]
    simp [coordVec]
    norm_num

end CERW.Support.Norm.MinkowskiGauge
