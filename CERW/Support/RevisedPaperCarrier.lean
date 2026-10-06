import CERW.Support.RevisedPaper

/-!
# The carrier of the objects of Sections 4 and 5

The statements of Section 4 (`lem:outer-crossing`) and Section 5 (`lem:contact`) of the revised
paper speak of a norm `γ` on `ℝ^d`, a drift `ε > 0` with `ε γ(e_i) < 1/d`, the point of the closed
convex set `{γ ≤ r_n}` nearest to a given point in Euclidean distance, the radial directions
`Λ_γ x / |x|` with `0 < |x| ≤ n`, and constants that are positive. This module makes each of these
objects a declaration whose type is its carrier, so that no object exists outside the situation in
which the paper defines it.

* `NearestProjection Ψ r` is a map that sends every point `y` to a point of `{Ψ ≤ r}` whose
  Euclidean distance to `y` is the least among the points of `{Ψ ≤ r}`. For a norm, there is exactly
  one such map (`exists_nearestProjection`, `nearestProjection_unique`), a point `z` is the image
  of `y` if and only if it is a nearest point of `{Ψ ≤ r}` to `y`
  (`NearestProjection.apply_eq_iff`), and the map is the inherited `canonicalProjection`
  (`NearestProjection.toFun_eq_canonical`), which has an arbitrary value only outside this
  carrier.
* `SourceSetting d` is a norm `Ψ` with a drift `ε` that satisfies the standing assumptions of the
  paper: `0 < ε` and `ε Ψ(e_i) < 1/d` for every coordinate vector `e_i`. Its radius `r_n` is
  nonnegative, so `SourceSetting.Projection S n`, the nearest-point maps onto `{Ψ ≤ r_n}`, is
  nonempty and has one element (`SourceSetting.projection`).
* `PositiveEventConstants` are the seven constants of the event of Section 5.1, each of which is
  positive.
* `SourceEvent` is the event of Section 5.1 on this carrier: its projection is a
  `SourceSetting.Projection`, its constants are positive and its seven estimates are those of
  `Estimates7`. The event does not depend on the choice of the projection, because there is only one
  (`sourceEvent_eq`).
* `SourceRadialEvent` is the event of `eq:linear-mart` for the radial directions `Λ_Ψ x / |x|` with
  `0 < |x| ≤ n`, the family of the event of Section 5.1. For a norm, a nonnegative constant and
  `n ≥ 1`, it is the event `RadialHalfSpaceEvent` for the family of the sites `|z| ≤ n`, whose zero
  direction is the half-space bound at a test function that vanishes identically
  (`sourceRadialEvent_eq`); `outer_crossing_on_source_events` is the outer crossing lemma on it.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.RevisedPaper

open CERW CERW.Support.Norm CERW.Support.Norm.CoarseCrossing CERW.Support.Norm.ContactEvent
  CERW.Support.Norm.Section5Localization

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The nearest-point projection and its carrier -/

/-- A nearest-point projection onto the closed set `{Ψ ≤ r}`: a map `P` such that for every `y`
the point `P y` lies in `{Ψ ≤ r}` and its Euclidean distance to `y` is at most the distance from
`y` to every point of `{Ψ ≤ r}`. -/
structure NearestProjection (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (r : ℝ) where
  /-- The point of `{Ψ ≤ r}` assigned to `y`. -/
  toFun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  /-- The assigned point lies in `{Ψ ≤ r}`. -/
  mem : ∀ y, Ψ (toFun y) ≤ r
  /-- The assigned point is nearest to `y` among the points of `{Ψ ≤ r}`. -/
  min : ∀ y v, Ψ v ≤ r → ‖y - toFun y‖ ≤ ‖y - v‖

namespace NearestProjection

variable {r : ℝ}

/-- Two nearest-point projections with the same underlying map are equal. -/
theorem ext_toFun {P Q : NearestProjection Ψ r} (h : P.toFun = Q.toFun) : P = Q := by
  cases P
  cases Q
  simp only at h
  subst h
  rfl

/-- A nearest-point projection onto the sublevel set of a norm satisfies the variational inequality
`⟨y - P y, v - P y⟩ ≤ 0` of the Euclidean projection onto a closed convex set. -/
theorem isNearestSelection (hΨ : IsNorm Ψ) (P : NearestProjection Ψ r) :
    IsNearestSelection Ψ r P.toFun :=
  isNearestSelection_of_dist_le hΨ P.mem P.min

end NearestProjection

/-- For a norm, the nearest-point projection onto `{Ψ ≤ r}` is unique. -/
theorem nearestProjection_unique (hΨ : IsNorm Ψ) {r : ℝ} (P Q : NearestProjection Ψ r) :
    P = Q :=
  NearestProjection.ext_toFun
    (nearestSelection_unique (P.isNearestSelection hΨ) (Q.isNearestSelection hΨ))

/-- For a norm and a nonnegative radius, there is a nearest-point projection onto `{Ψ ≤ r}`. -/
theorem exists_nearestProjection (hΨ : IsNorm Ψ) {r : ℝ} (hr : 0 ≤ r) :
    Nonempty (NearestProjection Ψ r) := by
  obtain ⟨P, h1, h2, -⟩ := ProjectionGeometry.exists_nearestSelection hΨ hr
  exact ⟨⟨P, h1, h2⟩⟩

/-- For a norm and a nonnegative radius, there is exactly one nearest-point projection onto
`{Ψ ≤ r}`. -/
theorem existsUnique_nearestProjection (hΨ : IsNorm Ψ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ P : NearestProjection Ψ r, ∀ Q : NearestProjection Ψ r, Q = P := by
  obtain ⟨P⟩ := exists_nearestProjection hΨ hr
  exact ⟨P, fun Q => nearestProjection_unique hΨ Q P⟩

namespace NearestProjection

variable {r : ℝ}

/-- The image of a point under the nearest-point projection of a norm is the point of `{Ψ ≤ r}`
nearest to it: a point `z` is `P y` if and only if `Ψ z ≤ r` and `‖y - z‖ ≤ ‖y - v‖` for every `v`
with `Ψ v ≤ r`. -/
theorem apply_eq_iff (hΨ : IsNorm Ψ) (P : NearestProjection Ψ r) (y z : EuclideanSpace ℝ (Fin d)) :
    P.toFun y = z ↔ Ψ z ≤ r ∧ ∀ v, Ψ v ≤ r → ‖y - z‖ ≤ ‖y - v‖ := by
  classical
  constructor
  · rintro rfl
    exact ⟨P.mem y, P.min y⟩
  · rintro ⟨hz, hzmin⟩
    let Q : NearestProjection Ψ r :=
      { toFun := Function.update P.toFun y z
        mem := fun y' => by
          by_cases h : y' = y
          · subst h
            simpa using hz
          · simpa [Function.update_of_ne h] using P.mem y'
        min := fun y' v hv => by
          by_cases h : y' = y
          · subst h
            simpa using hzmin v hv
          · simpa [Function.update_of_ne h] using P.min y' v hv }
    have hPQ : P = Q := nearestProjection_unique hΨ P Q
    have := congrArg (fun R : NearestProjection Ψ r => R.toFun y) hPQ
    simpa [Q] using this

/-- On its carrier, the nearest-point projection is the inherited map `canonicalProjection`, which
takes an arbitrary value outside the carrier. -/
theorem toFun_eq_canonical (hΨ : IsNorm Ψ) (hr : 0 ≤ r) (P : NearestProjection Ψ r) :
    P.toFun = canonicalProjection Ψ r :=
  nearestSelection_unique (P.isNearestSelection hΨ) (canonicalProjection_isNearestSelection hΨ hr)

end NearestProjection

/-! ## The setting of the paper -/

variable (d) in
/-- The setting of Sections 3 to 5: a norm `Ψ` of `ℝ^d`, and a drift `ε > 0` with
`ε Ψ(e_i) < 1/d` for every coordinate vector `e_i`. -/
structure SourceSetting where
  /-- The norm. -/
  Ψ : EuclideanSpace ℝ (Fin d) → ℝ
  /-- `Ψ` is a norm. -/
  isNorm : IsNorm Ψ
  /-- The drift. -/
  ε : ℝ
  /-- The drift is positive. -/
  ε_pos : 0 < ε
  /-- The ellipticity assumption of the paper. -/
  ellipticity : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)

namespace SourceSetting

variable (S : SourceSetting d)

/-- The radius `r_n` of the paper, `((d + 1) n / (2 d ε |B_Ψ|))^{1/(d+1)}`. -/
noncomputable def radius (n : ℕ) : ℝ := scale d S.Ψ S.ε n

/-- The radius `r_n` is nonnegative. -/
theorem radius_nonneg (n : ℕ) : 0 ≤ S.radius n := scale_nonneg S.ε_pos n

/-- The nearest-point projections onto the closed convex ball `{Ψ ≤ r_n}`. -/
abbrev Projection (n : ℕ) : Type := NearestProjection S.Ψ (S.radius n)

/-- At every time there is exactly one nearest-point projection onto `{Ψ ≤ r_n}`. -/
theorem existsUnique_projection (n : ℕ) :
    ∃ P : S.Projection n, ∀ Q : S.Projection n, Q = P :=
  existsUnique_nearestProjection S.isNorm (S.radius_nonneg n)

/-- The nearest-point projection onto `{Ψ ≤ r_n}`, selected from the existence statement
`existsUnique_projection`. -/
noncomputable def projection (n : ℕ) : S.Projection n :=
  Classical.choose (S.existsUnique_projection n)

/-- Every nearest-point projection onto `{Ψ ≤ r_n}` is `SourceSetting.projection`. -/
theorem eq_projection {n : ℕ} (P : S.Projection n) : P = S.projection n :=
  nearestProjection_unique S.isNorm P _

end SourceSetting

/-! ## The constants and the event of Section 5.1 -/

/-- The seven constants of the event of Section 5.1, each positive: `c_co, C_co` of Proposition 4.1,
`C_loc` of Lemma 3.1, `C_vec` of `eq:vector`, `C_mart` of `eq:localmart`, `C_quad` of
`eq:quadratic-coarse` and `C_lin` of `eq:linear-mart`. -/
structure PositiveEventConstants extends EventConstants where
  /-- The lower constant of Proposition 4.1 is positive. -/
  c_co_pos : 0 < c_co
  /-- The upper constant of Proposition 4.1 is positive. -/
  C_co_pos : 0 < C_co
  /-- The constant of Lemma 3.1 is positive. -/
  C_loc_pos : 0 < C_loc
  /-- The constant of `eq:vector` is positive. -/
  C_vec_pos : 0 < C_vec
  /-- The constant of `eq:localmart` is positive. -/
  C_mart_pos : 0 < C_mart
  /-- The constant of `eq:quadratic-coarse` is positive. -/
  C_quad_pos : 0 < C_quad
  /-- The constant of `eq:linear-mart` is positive. -/
  C_lin_pos : 0 < C_lin

/-- **The event of Section 5.1** in the setting `S`, for a field `ξ`, positive constants `K`, a time
`n` and the nearest-point projection `P` onto `{Ψ ≤ r_n}`: the sample points at which the seven
estimates of `Estimates7` hold at time `n`. -/
def SourceEvent {Ω : Type*} (S : SourceSetting d) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (K : PositiveEventConstants) (n : ℕ) (P : S.Projection n) (X : ℕ → Ω → Site d) : Set Ω :=
  {ω | Estimates7 S.Ψ S.ε ξ K.toEventConstants P.toFun (fun j => X j ω) n}

/-- The event of Section 5.1 does not depend on the nearest-point projection, because there is
only one. -/
theorem sourceEvent_eq {Ω : Type*} (S : SourceSetting d) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (K : PositiveEventConstants) (n : ℕ) (P Q : S.Projection n) (X : ℕ → Ω → Site d) :
    SourceEvent S ξ K n P X = SourceEvent S ξ K n Q X := by
  rw [S.eq_projection P, S.eq_projection Q]

/-- The event of Section 5.1 is the event `E7` of `Section5Localization`, whose projection is the
inherited map `canonicalProjection`, which takes arbitrary values outside the carrier. -/
theorem sourceEvent_eq_E7 {Ω : Type*} (S : SourceSetting d) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (K : PositiveEventConstants) (n : ℕ) (P : S.Projection n) (X : ℕ → Ω → Site d) :
    SourceEvent S ξ K n P X = E7 S.Ψ S.ε ξ K.toEventConstants X n := by
  have h : P.toFun = projectionAt S.Ψ S.ε n :=
    P.toFun_eq_canonical S.isNorm (S.radius_nonneg n)
  ext ω
  simp only [SourceEvent, E7, Set.mem_setOf_eq, h]

/-! ## The radial event of `eq:linear-mart` -/

/-- The event of `eq:linear-mart` for the radial directions `Λ_Ψ x / |x|`, `0 < |x| ≤ n`, at the
levels `k Λ_Ψ`, `0 ≤ k ≤ n`, with the constant `C`. -/
def SourceRadialEvent {Ω : Type*} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ) (X : ℕ → Ω → Site d) (n : ℕ) : Set Ω :=
  {ω | ∀ q ∈ radialDirections d Ψ n, HalfSpaceBound Ψ ε ξ C n q (fun j => X j ω)}

/-- The largest value `Λ_Ψ` of a norm on the unit sphere is nonnegative. -/
theorem normMax_nonneg_of_isNorm (hΨ : IsNorm Ψ) : 0 ≤ normMax Ψ := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨u, -, rfl⟩
  exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 u

/-- Every radial direction `Λ_Ψ x / |x|`, `0 < |x| ≤ n`, is a direction `Λ_Ψ u_z`, `|z| ≤ n`. -/
theorem radialDirections_subset_capDirections (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ) :
    radialDirections d Ψ n ⊆ capDirections Ψ n := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  refine Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, ?_⟩
  simp only [capDirection, smul_smul, div_eq_mul_inv]

/-- Every direction `Λ_Ψ u_z`, `|z| ≤ n`, is zero or a radial direction. -/
theorem capDirections_subset_insert_radialDirections (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (n : ℕ) : capDirections Ψ n ⊆ insert 0 (radialDirections d Ψ n) := by
  intro q hq
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
  by_cases h0 : z = 0
  · subst h0
    have h : capDirection Ψ (0 : Site d) = 0 := by
      have hs : toSpace (0 : Site d) = 0 := by
        ext i
        simp [toSpace]
      simp [capDirection, hs]
    rw [h]
    exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, h0⟩, ?_⟩)
    simp only [capDirection, smul_smul, div_eq_mul_inv]

/-- The half-space bound in the direction zero holds for every nonnegative constant, for a norm and
`n ≥ 1`: the test functions `max (0 - k Λ_Ψ) 0` vanish identically, so their Dynkin martingale is
zero. -/
theorem halfSpaceBound_zero (hΨ : IsNorm Ψ) {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {C : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 1 ≤ n) (x : ℕ → Site d) :
    HalfSpaceBound Ψ ε ξ C n 0 x := by
  intro k hk
  have hΛ := normMax_nonneg_of_isNorm hΨ
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hf : (fun z : Site d => max (inner ℝ (0 : EuclideanSpace ℝ (Fin d)) (toSpace z) -
      (k : ℝ) * normMax Ψ) 0) = fun _ => 0 := by
    funext z
    rw [inner_zero_left, zero_sub]
    exact max_eq_right (by simpa using mul_nonneg (Nat.cast_nonneg k) hΛ)
  rw [hf]
  simp only [dynkinMart, stepMean, sub_self, mul_zero, Finset.sum_const_zero, abs_zero]
  exact mul_nonneg hC (add_nonneg (Real.sqrt_nonneg _) hlog)

/-- For a norm, a nonnegative constant and `n ≥ 1`, the event of `eq:linear-mart` for the radial
directions `Λ_Ψ x / |x|`, `0 < |x| ≤ n`, is the event `RadialHalfSpaceEvent` for all directions
`Λ_Ψ u_z`, `|z| ≤ n`. -/
theorem sourceRadialEvent_eq {Ω : Type*} (hΨ : IsNorm Ψ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) {C : ℝ} (hC : 0 ≤ C) (X : ℕ → Ω → Site d) {n : ℕ}
    (hn : 1 ≤ n) :
    SourceRadialEvent Ψ ε ξ C X n = RadialHalfSpaceEvent Ψ ε ξ C X n := by
  ext ω
  simp only [SourceRadialEvent, RadialHalfSpaceEvent, Set.mem_setOf_eq]
  constructor
  · intro h q hq
    rcases Finset.mem_insert.mp (capDirections_subset_insert_radialDirections Ψ n hq) with
      rfl | hq'
    · exact halfSpaceBound_zero hΨ hC hn _
    · exact h q hq'
  · intro h q hq
    exact h q (radialDirections_subset_capDirections Ψ n hq)

/-! ## The outer crossing lemma on the radial event -/

/-- **`lem:outer-crossing` on the events of `eq:vector` and `eq:linear-mart`, with the radial
directions of the event of Section 5.1.** For every `p > 0` there is a constant `C_ev > 0`, which
does not depend on the field `ξ`, such that for every walk with drift field `ξ` and every `n ≥ 2`
the intersection of `VectorEvent` and `SourceRadialEvent` has a complement of probability at most
`C_ev n^{-p}`; and for every `α > 0` there is a constant `C > 0` such that the deterministic outer
crossing inequality holds for every path that satisfies the vector bound and the half-space bounds
in the direction `q` with the constant `C_ev`: this is the statement of `outer_crossing_on_events`
with the radial event of the source in place of the event of all directions `Λ_Ψ u_z`. -/
theorem outer_crossing_on_source_events (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C_ev : ℝ, 0 < C_ev ∧
      (∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
          μ (VectorEvent ε ξ C_ev X n ∩ SourceRadialEvent Ψ ε ξ C_ev X n)ᶜ ≤
            ENNReal.ofReal (C_ev * (n : ℝ) ^ (-p))) ∧
      ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ n : ℕ, 2 ≤ n → ∀ q : EuclideanSpace ℝ (Fin d), ‖q‖ ≤ normMax Ψ →
        ∀ x : ℕ → Site d, x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) →
          VectorIncrementBound ε ξ C_ev n x → HalfSpaceBound Ψ ε ξ C_ev n q x →
          ∀ j₀ : ℕ, j₀ ≤ n →
          (∀ j ≤ n, inner ℝ q (toSpace (x j)) ≤ inner ℝ q (toSpace (x j₀))) →
          ∀ h : ℝ, 0 < h →
          (∀ j ≤ n, inner ℝ q (toSpace (x j₀)) - h < inner ℝ q (toSpace (x j)) →
            α ≤ inner ℝ q (ξ (x j))) →
          ∀ b : ℝ, 0 ≤ b →
            inner ℝ q (toSpace (x j₀)) ≤
              max (inner ℝ q (toSpace (x j₀)) - h) b + C * (1 + ((((departureRange x n).filter
                (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ))
                * Real.log n := by
  obtain ⟨C_ev, hC, hprob, hdet⟩ := outer_crossing_on_events hd hΨ hε hell hp
  refine ⟨C_ev, hC, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_, hdet⟩
  rw [sourceRadialEvent_eq hΨ ε ξ hC.le X (by omega : 1 ≤ n)]
  exact hprob ξ hξ hξ0 μ X hX n hn

end CERW.Support.RevisedPaper
