import CERW.Support.Norm.GaugeShapeEvents

/-!
# Every compact convex body with the origin in its interior is a limit shape

Let `K ⊆ ℝ^d`, `d ≥ 2`, be a compact convex set with the origin in its interior and `ψ = gauge K`
its Minkowski functional, which need not be even, nor smooth. The condition `ε ψ(±e_i) < 1/d` for
all `i` (the two-sided ellipticity) is satisfied by the explicit drift `admissibleDrift d K`. For
every such `ε` there are subgradient selections `ξ` of `ψ` with `ξ(0) = 0` and walks with drift
opposite to `ξ` (`IsDriftCERW`), and for every selection and every walk of that law the walk has `K`
as its limit shape: with `r_n = ((d+1) n/(2 d ε |K|))^{1/(d+1)}` and `|K|` the volume of the body,
almost surely, for every `η ∈ (0,1)` and all large `n`, the visited lattice sites lie between the
lattice sites of `((1 - η) r_n) • interior K` and `((1 + η) r_n) • interior K`, the local times
follow the cone `2 d ε (r_n - ψ_K)_+` up to `η r_n`, and every site is visited infinitely often. The
proof applies the almost sure shape theorem `GaugeShapeEvents.gauge_shape` to the actual law and
rewrites its conclusion for the body: `|B_ψ| = |K|` and `{ψ_K < ρ} = ρ • interior K`.
-/

universe u

open MeasureTheory Filter Topology
open scoped Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.ConvexBodyShape

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugeShapeEvents

variable {d : ℕ}

/-- The two-sided ellipticity `ε ψ_K(±e_i) < 1/d` of the drift `ε` for the body `K`. -/
def Elliptic (K : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) : Prop :=
  ∀ i : Fin d, ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ)

/-- The explicit admissible drift `1 / (d (S + 1))`, where `S = Σ_i (ψ_K(e_i) + ψ_K(-e_i))`. -/
noncomputable def admissibleDrift (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  1 / ((d : ℝ) * (∑ i : Fin d, (gauge K (coordVec i) + gauge K (-coordVec i)) + 1))

/-- The admissible drift is positive. -/
theorem admissibleDrift_pos (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) :
    0 < admissibleDrift d K := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hS : 0 ≤ ∑ i : Fin d, (gauge K (coordVec i) + gauge K (-coordVec i)) :=
    Finset.sum_nonneg fun i _ => add_nonneg (gauge_nonneg _) (gauge_nonneg _)
  unfold admissibleDrift
  positivity

/-- **The admissible drift satisfies the two-sided ellipticity, for every body.** Each `ψ_K(±e_i)`
is at most `S`, so `ε ψ_K(±e_i) ≤ S/(d (S + 1)) < 1/d`. No evenness, norm, compactness or convexity
is used. -/
theorem admissibleDrift_elliptic (hd : 1 ≤ d) (K : Set (EuclideanSpace ℝ (Fin d))) :
    Elliptic K (admissibleDrift d K) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set S : ℝ := ∑ i : Fin d, (gauge K (coordVec i) + gauge K (-coordVec i)) with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => add_nonneg (gauge_nonneg _) (gauge_nonneg _)
  have hle : ∀ i : Fin d, gauge K (coordVec i) ≤ S ∧ gauge K (-coordVec i) ≤ S := by
    intro i
    have h1 : gauge K (coordVec i) + gauge K (-coordVec i) ≤ S :=
      Finset.single_le_sum (f := fun i : Fin d => gauge K (coordVec i) + gauge K (-coordVec i))
        (fun j _ => add_nonneg (gauge_nonneg _) (gauge_nonneg _)) (Finset.mem_univ i)
    have hn1 : 0 ≤ gauge K (coordVec i) := gauge_nonneg _
    have hn2 : 0 ≤ gauge K (-coordVec i) := gauge_nonneg _
    exact ⟨by linarith, by linarith⟩
  have hε : admissibleDrift d K * S < 1 / (d : ℝ) := by
    unfold admissibleDrift
    rw [← hSdef, div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) hdpos]
    nlinarith
  have hε0 := admissibleDrift_pos hd K
  intro i
  obtain ⟨h1, h2⟩ := hle i
  exact ⟨lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 hε0.le) hε,
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 hε0.le) hε⟩

variable {K : Set (EuclideanSpace ℝ (Fin d))}

/-- The sublevel sets of the gauge of a body are its dilates: for `ρ > 0`,
`{ψ_K < ρ} = ρ • interior K`. -/
theorem sublevel_eq_smul_interior (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ρ : ℝ} (hρ : 0 < ρ) :
    {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} = ρ • interior K := by
  rw [gauge_sublevel_eq_smul K hρ, setOf_gauge_lt_one_eq_interior hc
    (mem_interior_iff_mem_nhds.mp h0)]

/-- The lattice sites of the dilate `ρ • interior K` are the sites `x` with `ψ_K(x) < ρ`. -/
theorem mem_smul_interior_iff (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ρ : ℝ} (hρ : 0 < ρ) (x : Site d) : toSpace x ∈ ρ • interior K ↔ gauge K (toSpace x) < ρ := by
  rw [← sublevel_eq_smul_interior hc h0 hρ]
  rfl

/-- The scale `r_n` of the statement is positive for `n ≥ 1`. -/
theorem scale_pos (hd : 1 ≤ d) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V) {n : ℕ} (hn : 1 ≤ n) :
    0 < ((d + 1) * n / (2 * d * ε * V)) ^ ((1 : ℝ) / (d + 1)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The sandwich of the range between the sublevel sets of the gauge is the sandwich between the
dilates of the interior of the body. -/
theorem sandwich_body_form (hc : Convex ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {r : ℕ → ℝ} (hr : ∀ n : ℕ, 1 ≤ n → 0 < r n) {Y : ℕ → Site d} {η : ℝ} (hη : 0 < η)
    (hη1 : η < 1)
    (h : ∀ᶠ n : ℕ in atTop,
      {x : Site d | gauge K (toSpace x) < (1 - η) * r n} ⊆ ↑(departureRange Y n) ∧
        (↑(departureRange Y n) : Set (Site d)) ⊆ {x | gauge K (toSpace x) < (1 + η) * r n}) :
    ∀ᶠ n : ℕ in atTop,
      {x : Site d | toSpace x ∈ ((1 - η) * r n) • interior K} ⊆ ↑(departureRange Y n) ∧
        (↑(departureRange Y n) : Set (Site d)) ⊆
          {x | toSpace x ∈ ((1 + η) * r n) • interior K} := by
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hr0 := hr n hn1
  have h1 : 0 < (1 - η) * r n := mul_pos (by linarith) hr0
  have h2 : 0 < (1 + η) * r n := mul_pos (by linarith) hr0
  refine ⟨fun x hx => hn.1 ?_, fun x hx => ?_⟩
  · exact (mem_smul_interior_iff hc h0 h1 x).mp hx
  · exact (mem_smul_interior_iff hc h0 h2 x).mpr (hn.2 hx)

/-- **Every compact convex body with the origin in its interior is a limit shape.** The explicit
drift `admissibleDrift K` is positive and satisfies the two-sided ellipticity; and for every drift
`ε > 0` with this ellipticity there are an actual selection of subgradients of `ψ_K` with `ξ(0) = 0`
and an actual walk with drift opposite to it, and, for every selection and every walk of that law,
almost surely: for every `η ∈ (0,1)` and all large `n`, the visited sites lie between the sites of
the dilates `((1 - η) r_n) • interior K` and `((1 + η) r_n) • interior K`, where
`r_n = ((d+1) n/(2 d ε |K|))^{1/(d+1)}` and `|K|` is the volume of the body; the local times are
within `η r_n` of the cone `2 d ε (r_n - ψ_K)_+`; and every site is visited infinitely often. -/
def IsLimitShape (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  (0 < admissibleDrift d K ∧ Elliptic K (admissibleDrift d K)) ∧
  ∀ ε : ℝ, 0 < ε → Elliptic K ε →
    (∃ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X) ∧
    ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X →
      let r : ℕ → ℝ := fun n =>
        ((d + 1) * n / (2 * d * ε * (volume K).toReal)) ^ ((1 : ℝ) / (d + 1))
      ∀ᵐ ω ∂μ,
        (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
          {x : Site d | toSpace x ∈ ((1 - η) * r n) • interior K} ⊆
              ↑(departureRange (X · ω) n) ∧
            (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
              {x | toSpace x ∈ ((1 + η) * r n) • interior K}) ∧
        (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
          |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - gauge K (toSpace x)) 0| ≤
            η * r n) ∧
        (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)

/-- **The limit shape theorem for an arbitrary compact convex body.** Applies the almost sure
shape result `gauge_shape` to the actual walks of the body, with the body's volume in the scale and
the dilates of its interior in the sandwich. -/
theorem isLimitShape_of_compact_convex (hd : 2 ≤ d) (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) : IsLimitShape.{u} d K := by
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < (volume K).toReal := by
    rw [← normBallVolume_gauge hK hc h0]
    exact normBallVolume_gauge_pos hK hc h0
  refine ⟨⟨admissibleDrift_pos hd1 K, admissibleDrift_elliptic hd1 K⟩, ?_⟩
  intro ε hε hell
  refine ⟨?_, ?_⟩
  · obtain ⟨ξ, hξ, hξ0, hw⟩ := exists_isDriftCERW_gauge hd1 hc h0 hε.le hell
    exact ⟨ξ, hξ, hξ0, hw⟩
  · intro ξ hξ hξ0 Ω _ μ _ X hX
    have h := gauge_shape hd hK hc h0 hξ hξ0 hε hell μ X hX
    dsimp only at h ⊢
    rw [normBallVolume_gauge hK hc h0] at h
    filter_upwards [h] with ω hω
    obtain ⟨h1, h2, h3⟩ := hω
    exact ⟨fun η hη hη1 => sandwich_body_form hc h0 (fun n hn => scale_pos hd1 hε hV hn) hη hη1
      (h1 η hη hη1), h2, h3⟩

section Consumption

open CERW.Support.Norm.GaugePotential (cornerTriangle isCompact_cornerTriangle
  convex_cornerTriangle zero_mem_interior_cornerTriangle)

/-- **The cut disc `{|y| ≤ 2, y₀ ≥ -1}` is a limit shape.** Its gauge `max {|y|/2, -y₀}` is not even
and its boundary has two corners. -/
theorem cutDisc_isLimitShape : IsLimitShape.{u} 2 cutDisc :=
  isLimitShape_of_compact_convex (le_refl 2) isCompact_cutDisc convex_cutDisc
    zero_mem_interior_cutDisc

/-- **The triangle with corners `(-1,-1)`, `(2,-1)`, `(-1,2)` is a limit shape.** Its gauge
`max {-y₀, -y₁, y₀ + y₁}` is not even and is not differentiable at the vertices. -/
theorem cornerTriangle_isLimitShape : IsLimitShape.{u} 2 cornerTriangle :=
  isLimitShape_of_compact_convex (le_refl 2) isCompact_cornerTriangle convex_cornerTriangle
    zero_mem_interior_cornerTriangle

/-- The tetrahedron with vertices `(-1,-1,-1)`, `(3,-1,-1)`, `(-1,3,-1)`, `(-1,-1,3)`: a body in
dimension three with the origin in its interior, four corners and no symmetry about the origin. -/
def tetrahedron : Set (EuclideanSpace ℝ (Fin 3)) :=
  {y | -1 ≤ y 0 ∧ -1 ≤ y 1 ∧ -1 ≤ y 2 ∧ y 0 + y 1 + y 2 ≤ 1}

/-- The tetrahedron is compact. -/
theorem isCompact_tetrahedron : IsCompact tetrahedron := by
  have h0 : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 0 := by fun_prop
  have h1 : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 1 := by fun_prop
  have h2 : Continuous fun y : EuclideanSpace ℝ (Fin 3) => y 2 := by fun_prop
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const h0).inter ((isClosed_le continuous_const h1).inter
      ((isClosed_le continuous_const h2).inter
        (isClosed_le ((h0.add h1).add h2) continuous_const)))
  · refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 3))) (r := 6)).subset
      fun y hy => ?_
    obtain ⟨a0, a1, a2, a3⟩ := hy
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_left (by norm_num)]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    nlinarith [mul_nonneg (by linarith : 0 ≤ y 0 + 1) (by linarith : 0 ≤ 3 - y 0),
      mul_nonneg (by linarith : 0 ≤ y 1 + 1) (by linarith : 0 ≤ 3 - y 1),
      mul_nonneg (by linarith : 0 ≤ y 2 + 1) (by linarith : 0 ≤ 3 - y 2)]

/-- The tetrahedron is convex. -/
theorem convex_tetrahedron : Convex ℝ tetrahedron := by
  have l0 : IsLinearMap ℝ (fun y : EuclideanSpace ℝ (Fin 3) => y 0) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have l1 : IsLinearMap ℝ (fun y : EuclideanSpace ℝ (Fin 3) => y 1) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have l2 : IsLinearMap ℝ (fun y : EuclideanSpace ℝ (Fin 3) => y 2) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have l3 : IsLinearMap ℝ (fun y : EuclideanSpace ℝ (Fin 3) => y 0 + y 1 + y 2) :=
    ⟨fun x y => by simp only [PiLp.add_apply]; ring,
      fun c x => by simp only [PiLp.smul_apply, smul_eq_mul]; ring⟩
  exact (convex_halfSpace_ge l0 (-1)).inter ((convex_halfSpace_ge l1 (-1)).inter
    ((convex_halfSpace_ge l2 (-1)).inter (convex_halfSpace_le l3 1)))

/-- The origin is an interior point of the tetrahedron. -/
theorem zero_mem_interior_tetrahedron : (0 : EuclideanSpace ℝ (Fin 3)) ∈ interior tetrahedron := by
  refine mem_interior.mpr ⟨Metric.ball 0 (1 / 4), fun y hy => ?_, Metric.isOpen_ball,
    Metric.mem_ball_self (by norm_num)⟩
  have hy1 : ‖y‖ < 1 / 4 := by simpa using hy
  have h0 := PiLp.norm_apply_le y 0
  have h1 := PiLp.norm_apply_le y 1
  have h2 := PiLp.norm_apply_le y 2
  rw [Real.norm_eq_abs] at h0 h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [neg_abs_le (y 0), neg_abs_le (y 1), neg_abs_le (y 2),
    le_abs_self (y 0), le_abs_self (y 1), le_abs_self (y 2)]

/-- A positively homogeneous functional that is at most `1` on `K` is at most the gauge of `K`. -/
private lemma le_gauge_of_le_one_on {K : Set (EuclideanSpace ℝ (Fin 3))}
    (h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ interior K) (ℓ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hℓ : ∀ (t : ℝ) (k : EuclideanSpace ℝ (Fin 3)), ℓ (t • k) = t * ℓ k)
    (hK : ∀ k ∈ K, ℓ k ≤ 1) (y : EuclideanSpace ℝ (Fin 3)) : ℓ y ≤ gauge K y := by
  by_contra h
  obtain ⟨b, hb, hby, hyb⟩ := exists_lt_of_gauge_lt
    (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)) (not_le.mp h)
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.mp hyb
  rw [hℓ] at hby
  nlinarith [mul_le_mul_of_nonneg_left (hK k hk) hb.le]

/-- The gauge of the tetrahedron is not even: `ψ(a) ≥ 3/4` and `ψ(-a) ≤ 1/4` for
`a = (1/4, 1/4, 1/4)`. -/
theorem gauge_tetrahedron_not_even :
    3 / 4 ≤ gauge tetrahedron ((1 / 4 : ℝ) • (coordVec 0 + coordVec 1 + coordVec 2)) ∧
      gauge tetrahedron (-((1 / 4 : ℝ) • (coordVec 0 + coordVec 1 + coordVec 2))) ≤ 1 / 4 := by
  set a : EuclideanSpace ℝ (Fin 3) := coordVec 0 + coordVec 1 + coordVec 2 with ha
  have ha0 : a 0 = 1 := by simp [ha, coordVec]
  have ha1 : a 1 = 1 := by simp [ha, coordVec]
  have ha2 : a 2 = 1 := by simp [ha, coordVec]
  constructor
  · have h := le_gauge_of_le_one_on zero_mem_interior_tetrahedron
      (fun y => y 0 + y 1 + y 2) (fun t k => by simp [mul_add]) (fun k hk => hk.2.2.2)
      ((1 / 4 : ℝ) • a)
    simp only [PiLp.smul_apply, smul_eq_mul, ha0, ha1, ha2] at h
    linarith
  · refine gauge_le_of_mem (by norm_num) (Set.mem_smul_set.mpr ⟨-a, ?_, by rw [smul_neg]⟩)
    simp only [tetrahedron, Set.mem_setOf_eq, PiLp.neg_apply, ha0, ha1, ha2]
    norm_num

/-- The gauge of the tetrahedron is not even. -/
theorem exists_gauge_tetrahedron_neg_ne :
    ∃ y : EuclideanSpace ℝ (Fin 3), gauge tetrahedron (-y) ≠ gauge tetrahedron y := by
  obtain ⟨h1, h2⟩ := gauge_tetrahedron_not_even
  refine ⟨(1 / 4 : ℝ) • (coordVec 0 + coordVec 1 + coordVec 2), fun h => ?_⟩
  linarith

/-- **The tetrahedron is a limit shape**, in dimension three. -/
theorem tetrahedron_isLimitShape : IsLimitShape.{u} 3 tetrahedron :=
  isLimitShape_of_compact_convex (by norm_num) isCompact_tetrahedron convex_tetrahedron
    zero_mem_interior_tetrahedron

end Consumption

end CERW.Support.Norm.ConvexBodyShape
