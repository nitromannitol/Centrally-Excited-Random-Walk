import CERW.Support.Norm
import CERW.Support.Norm.ContactEvent
import CERW.Support.Contact.ContactSetup
import CERW.Support.Contact.InradiusArith
import CERW.Support.Contact.Volume
import CERW.Support.Contact.BallExcess
import CERW.Support.Contact.NormReplace
import CERW.Support.Contact.Quadratic
import CERW.Support.Contact.EnvelopeShell
import CERW.Generic.Kernel.RadialInner

/-!
# The literal event of Section 5.1 and the closed localization of the contact estimate

The event of Section 5.1 of the revised paper is the intersection of exactly seven estimates: the
bounds of Proposition 4.1, the estimates of Lemma 3.1, the vector bound `eq:vector`, the local
martingale bounds `eq:localmart`, the quadratic bound `eq:quadratic-coarse`, and the halfspace
martingale bounds `eq:linear-mart` for the two deterministic families of directions. The model
path legality (the path starts at the origin and takes unit steps) is not one of them.

* `canonicalProjection` is the nearest-point projection onto `{Ψ ≤ r}`, defined from `Ψ` and `r`
  alone by the variational characterization; `canonicalProjection_spec` and
  `canonicalProjection_eq_of` give existence and uniqueness, and `canonicalProjection_dist_le`
  that it minimizes the distance.
* `Estimates7` is the conjunction of the seven estimates for a path, with the projection of the
  second family fixed from `(Ψ, ε, n)`; `E7` is the set of sample points on which they hold. It is
  the preimage of a set of finite paths under the past path (`E7_eq_preimage`), so it is
  `ℱ_n`-measurable (`measurableSet_E7_filtration`). `section5Event_eq` characterizes the event
  with the typing of `ContactEvent` as the intersection of the legal sample points with `E7`.
* `legalCarrier` replaces the walk outside the legal sample points by a straight nearest-neighbour
  path. For every walk with a drift field the legal sample points have probability one
  (`ae_legal_of_isDriftCERW`), the carrier is a walk with the same drift field with measurable
  positions that coincides with the original almost surely (`isDriftCERW_legalCarrier`,
  `legalCarrier_ae_eq`), and it is legal everywhere (`legalCarrier_typing`).
* `section5_localization` is the closed support theorem. The producers of Proposition 4.1,
  Lemma 3.1, the lattice-kernel martingales, the norm-ball potential and the halfspace
  martingales are the proved ones, so no producer is assumed. For all large `n` the complement of
  `E7` has probability at most `C n^{-p}` and, at every legal sample point of `E7` and every
  contact point, the potential of the cell is at most `C r_n q_n`; and the same holds for every
  sample point of `E7` of the legal carrier.
* `inner_of_estimates7` is the deterministic implication behind `prop:inner` for the Euclidean
  norm: a legal path that satisfies the seven estimates and the contact estimate has the inner
  radius, the volume and the local-time profile estimates, at the exact rates `r_n q_n`, `q_n` and
  `r_n q_n^{1/d}`. `section5_euclid_localization` combines it with the localization: on the same
  event `E7`, with the same constants, the contact estimate and the three estimates hold at every
  legal sample point, and for the legal carrier at every sample point. The private lemmas of that
  part are the deterministic ones of the Euclidean inner-radius argument, with the event of that
  argument replaced by the seven estimates.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.Section5Localization

open CERW CERW.Support.Statements CERW.Support.Norm.ContactEvent

variable {d : ℕ}

/-! ## The canonical nearest-point projection -/

/-- The point of `{Ψ ≤ r}` nearest to `y`, defined by the variational characterization
`Ψ z ≤ r` and `⟨y - z, v - z⟩ ≤ 0` for `Ψ v ≤ r`; it is `0` when no point satisfies it, which
does not happen for a norm and `r ≥ 0`. -/
noncomputable def canonicalProjection (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (r : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  open scoped Classical in
  if h : ∃ z, Ψ z ≤ r ∧ ∀ v, Ψ v ≤ r → inner ℝ (y - z) (v - z) ≤ 0 then h.choose else 0

/-- For a norm and `r ≥ 0` the canonical projection of every point lies in `{Ψ ≤ r}` and
satisfies the variational inequality of the Euclidean projection onto a convex set. -/
theorem canonicalProjection_spec {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {r : ℝ}
    (hr : 0 ≤ r) (y : EuclideanSpace ℝ (Fin d)) :
    Ψ (canonicalProjection Ψ r y) ≤ r ∧
      ∀ v, Ψ v ≤ r →
        inner ℝ (y - canonicalProjection Ψ r y) (v - canonicalProjection Ψ r y) ≤ 0 := by
  have hex : ∃ z, Ψ z ≤ r ∧ ∀ v, Ψ v ≤ r → inner ℝ (y - z) (v - z) ≤ 0 := by
    obtain ⟨z, hz, -, hvar⟩ := CERW.Support.Norm.ProjectionGeometry.exists_nearest hΨ hr y
    exact ⟨z, hz, hvar⟩
  classical
  rw [canonicalProjection, dif_pos hex]
  exact hex.choose_spec

/-- The canonical projection is the only point satisfying the variational characterization. -/
theorem canonicalProjection_eq_of {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {r : ℝ}
    (hr : 0 ≤ r) {y z : EuclideanSpace ℝ (Fin d)} (hz : Ψ z ≤ r)
    (hvar : ∀ v, Ψ v ≤ r → inner ℝ (y - z) (v - z) ≤ 0) : canonicalProjection Ψ r y = z :=
  nearest_unique (canonicalProjection_spec hΨ hr y).1 hz (canonicalProjection_spec hΨ hr y).2 hvar

/-- The canonical projection is a nearest-point selection in the sense of `ContactEvent`. -/
theorem canonicalProjection_isNearestSelection {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {r : ℝ} (hr : 0 ≤ r) : IsNearestSelection Ψ r (canonicalProjection Ψ r) :=
  ⟨fun y => (canonicalProjection_spec hΨ hr y).1, fun y v hv =>
    (canonicalProjection_spec hΨ hr y).2 v hv⟩

/-- The canonical projection minimizes the Euclidean distance over `{Ψ ≤ r}`. -/
theorem canonicalProjection_dist_le {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) {r : ℝ}
    (hr : 0 ≤ r) (y : EuclideanSpace ℝ (Fin d)) {v : EuclideanSpace ℝ (Fin d)} (hv : Ψ v ≤ r) :
    ‖y - canonicalProjection Ψ r y‖ ≤ ‖y - v‖ := by
  set z := canonicalProjection Ψ r y with hz
  have hvar := (canonicalProjection_spec hΨ hr y).2 v hv
  have hsq : ‖y - z‖ ^ 2 ≤ ‖y - v‖ ^ 2 := by
    have h1 : y - v = (y - z) - (v - z) := by abel
    have h2 : ‖y - v‖ ^ 2 = ‖y - z‖ ^ 2 - 2 * inner ℝ (y - z) (v - z) + ‖v - z‖ ^ 2 := by
      rw [h1, norm_sub_sq_real]
    nlinarith [sq_nonneg ‖v - z‖]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

/-! ## The literal event -/

/-- The seven estimates of Section 5.1 for a path `x` at time `n`: Proposition 4.1, Lemma 3.1,
`eq:vector`, `eq:localmart`, `eq:quadratic-coarse`, and `eq:linear-mart` for the radial family
and for the family of directions `Λ_Ψ u_{x - P(x)}` of the projection `P`. -/
def Estimates7 (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (K : EventConstants) (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) (n : ℕ) : Prop :=
  CoarseBounds d Ψ ε K.c_co K.C_co x n ∧ LocalBounds d Ψ ε K.C_loc x n ∧
    VectorEstimate d ε ξ K.C_vec x n ∧ LocalMartEstimate d ε ξ K.C_mart x n ∧
    QuadraticEstimate d ε ξ K.C_quad x n ∧
    LinearEstimate d Ψ ε ξ K.C_lin (radialDirections d Ψ n) x n ∧
    LinearEstimate d Ψ ε ξ K.C_lin (projectionDirections d Ψ ε n P) x n

/-- The projection `Π_n` onto the closed convex set `{Ψ ≤ r_n}`, fixed from `Ψ`, `ε` and `n`. -/
noncomputable def projectionAt (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (n : ℕ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  canonicalProjection Ψ (scale d Ψ ε n)

/-- **The event of Section 5.1**: the sample points at which the path satisfies the seven
estimates, with the projection `Π_n` of the second family of directions. It involves the path only
up to time `n`, and no condition on the legality of the whole path. -/
def E7 {Ω : Type*} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants) (X : ℕ → Ω → Site d)
    (n : ℕ) : Set Ω :=
  {ω | Estimates7 Ψ ε ξ K (projectionAt Ψ ε n) (fun j => X j ω) n}

/-- The event of `ContactEvent`, with the legality of the whole path, is the intersection of the
legal sample points with the seven estimates. -/
theorem section5Event_eq {Ω : Type*} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (X : ℕ → Ω → Site d) (n : ℕ) :
    Section5Event Ψ ε ξ K P X n =
      {ω | PathTyping d (fun j => X j ω)} ∩ {ω | Estimates7 Ψ ε ξ K P (fun j => X j ω) n} :=
  Set.ext fun _ => Iff.rfl

/-- With the projection `Π_n`, the event of `ContactEvent` is the legal sample points of `E7`. -/
theorem section5Event_projectionAt {Ω : Type*} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants) (X : ℕ → Ω → Site d) (n : ℕ) :
    Section5Event Ψ ε ξ K (projectionAt Ψ ε n) X n =
      {ω | PathTyping d (fun j => X j ω)} ∩ E7 Ψ ε ξ K X n :=
  Set.ext fun _ => Iff.rfl

/-! ## `E7` depends only on the path up to time `n` -/

section Prefix

open Finset CERW.Support.Law

private theorem departureRange_congr {x y : ℕ → Site d} {n m : ℕ} (h : ∀ j ≤ n, x j = y j)
    (hm : m ≤ n + 1) : departureRange x m = departureRange y m :=
  Finset.image_congr fun j hj => h j (by have := mem_range.mp hj; omega)

private theorem localTime_congr {x y : ℕ → Site d} {n m : ℕ} (h : ∀ j ≤ n, x j = y j)
    (hm : m ≤ n + 1) : localTime x m = localTime y m := by
  funext z
  unfold localTime
  congr 1
  exact Finset.filter_congr fun j hj => by rw [h j (by have := mem_range.mp hj; omega)]

private theorem maxLocalTime_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    maxLocalTime x n = maxLocalTime y n := by
  unfold maxLocalTime
  rw [departureRange_congr h (Nat.le_succ n), localTime_congr h (Nat.le_succ n)]

private theorem maxRadius_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    maxRadius x n = maxRadius y n := by
  unfold maxRadius
  exact Finset.sup'_congr _ rfl fun j hj => by
    rw [h j (by have := mem_range.mp hj; omega)]

private theorem freshCount_congr {x y : ℕ → Site d} {n s t : ℕ} (h : ∀ j ≤ n, x j = y j)
    (ht : t ≤ n) : freshCount x s t = freshCount y s t := by
  unfold freshCount
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  have hjt : j < t := (mem_Ico.mp hj).2
  rw [h j (by omega), departureRange_congr h (by omega : j ≤ n + 1)]

private theorem intervalMax_congr {x y : ℕ → Site d} {n s t : ℕ} (h : ∀ j ≤ n, x j = y j)
    (ht : t ≤ n) : intervalMax x s t = intervalMax y s t := by
  have himg : (Finset.Ico s t).image x = (Finset.Ico s t).image y :=
    Finset.image_congr fun j hj => h j (by have := (mem_Ico.mp hj).2; omega)
  have hloc : intervalLocalTime x s t = intervalLocalTime y s t := by
    funext z
    unfold intervalLocalTime
    congr 1
    exact Finset.filter_congr fun j hj => by
      rw [h j (by have := (mem_Ico.mp hj).2; omega)]
  unfold intervalMax
  rw [himg, hloc]

private theorem cellSet_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    cellSet x n = cellSet y n := by
  unfold cellSet
  rw [departureRange_congr h (Nat.le_succ n)]

private theorem cellLocalTime_congr {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    cellLocalTime x n = cellLocalTime y n := by
  funext v
  unfold cellLocalTime
  rw [localTime_congr h (Nat.le_succ n)]

private theorem driftCompensated_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {x y : ℕ → Site d} {n t : ℕ} (h : ∀ j ≤ n, x j = y j) (ht : t ≤ n) :
    CERW.Support.Norm.VectorBound.driftCompensated ε ξ x t =
      CERW.Support.Norm.VectorBound.driftCompensated ε ξ y t := by
  unfold CERW.Support.Norm.VectorBound.driftCompensated
  rw [h t ht]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjt : j < t := mem_range.mp hj
  rw [h j (by omega), departureRange_congr h (by omega : j ≤ n + 1)]

private theorem quadraticMartingale_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    quadraticMartingale d ε ξ x n = quadraticMartingale d ε ξ y n := by
  unfold quadraticMartingale
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j < n := mem_range.mp hj
  rw [h j (by omega), h (j + 1) (by omega), departureRange_congr h (by omega : j ≤ n + 1)]

private theorem dynkinMart_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) (f : Site d → ℝ) :
    dynkinMart (driftStepProb d ε ξ) f x n = dynkinMart (driftStepProb d ε ξ) f y n := by
  unfold dynkinMart
  rw [h n le_rfl, h 0 (Nat.zero_le n)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j < n := mem_range.mp hj
  unfold stepMean
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [CERW.Support.Drift.driftStepProb_congr (fun i hi => h i (by omega)) e, h j (by omega)]

/-- The seven estimates at time `n` depend only on the path up to time `n`. -/
theorem estimates7_congr (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) {x y : ℕ → Site d}
    (h : ∀ j ≤ n, x j = y j) :
    Estimates7 Ψ ε ξ K P x n ↔ Estimates7 Ψ ε ξ K P y n := by
  have hdep : departureRange x n = departureRange y n := departureRange_congr h (Nat.le_succ n)
  have hloc : localTime x n = localTime y n := localTime_congr h (Nat.le_succ n)
  have hmax : maxLocalTime x n = maxLocalTime y n := maxLocalTime_congr h
  have hrad : maxRadius x n = maxRadius y n := maxRadius_congr h
  have hcell : cellSet x n = cellSet y n := cellSet_congr h
  have hclt : cellLocalTime x n = cellLocalTime y n := cellLocalTime_congr h
  have hdyn : ∀ f : Site d → ℝ, dynkinMart (driftStepProb d ε ξ) f x n =
      dynkinMart (driftStepProb d ε ξ) f y n := dynkinMart_congr h
  unfold Estimates7
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_
    (and_congr ?_ ?_)))))
  · simp only [CoarseBounds, hdep, hmax, hrad]
  · simp only [LocalBounds, hdep, hmax, hcell, hclt]
    refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
    refine forall_congr' fun s => forall_congr' fun t => forall_congr' fun hst =>
      forall_congr' fun htn => ?_
    rw [intervalMax_congr h htn, freshCount_congr h htn]
  · unfold VectorEstimate
    refine forall_congr' fun s => forall_congr' fun t => forall_congr' fun hst =>
      forall_congr' fun htn => ?_
    rw [driftCompensated_congr h htn, driftCompensated_congr h (by omega : s ≤ n)]
  · simp only [LocalMartEstimate, hdep, hloc, hdyn]
  · simp only [QuadraticEstimate, quadraticMartingale_congr h, hrad]
  · simp only [LinearEstimate, hdep, hloc, hdyn]
  · simp only [LinearEstimate, hdep, hloc, hdyn]

/-- `E7` is the preimage, under the past path up to time `n`, of a set of finite paths. -/
theorem E7_eq_preimage {Ω : Type*} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants) (X : ℕ → Ω → Site d) (n : ℕ) :
    E7 Ψ ε ξ K X n = pastPath X n ⁻¹'
      {p | Estimates7 Ψ ε ξ K (projectionAt Ψ ε n) (extendPath p) n} := by
  ext ω
  simp only [E7, Set.mem_setOf_eq, Set.mem_preimage]
  exact estimates7_congr Ψ ε ξ K _ n fun j hj => (extendPath_pastPath X hj ω).symm

/-- `E7` belongs to the `σ`-algebra `ℱ_n = σ(X_0, …, X_n)` of the walk. -/
theorem measurableSet_E7_filtration {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ j, Measurable (X j)) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants) (n : ℕ) :
    MeasurableSet[pathFiltration hX n] (E7 Ψ ε ξ K X n) := by
  rw [E7_eq_preimage]
  exact ⟨_, (Set.to_countable _).measurableSet, rfl⟩

/-- `E7` is measurable. -/
theorem measurableSet_E7 {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ j, Measurable (X j)) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants) (n : ℕ) :
    MeasurableSet (E7 Ψ ε ξ K X n) :=
  (pathFiltration hX).le n _ (measurableSet_E7_filtration hX Ψ ε ξ K n)

end Prefix

/-! ## The legal carrier of a walk -/

section Legal

open CERW.Support.Law

/-- The straight nearest-neighbour path `j ↦ j e₀`. -/
def straightPath (hd : 1 ≤ d) : ℕ → Site d :=
  fun j => (j : ℤ) • LatticeProb.unit (⟨0, hd⟩ : Fin d)

/-- The straight path starts at the origin and takes unit steps. -/
theorem straightPath_typing (hd : 1 ≤ d) : PathTyping d (straightPath hd) := by
  refine ⟨by simp [straightPath], fun j => ?_⟩
  simp only [straightPath, Nat.cast_add, Nat.cast_one]
  rw [add_smul, one_smul, add_sub_cancel_left]
  exact CERW.mem_unitSteps.mpr ⟨_, Or.inl rfl⟩

/-- The sample points at which the whole path is legal: it starts at the origin and takes unit
steps. -/
def legalSet {Ω : Type*} (X : ℕ → Ω → Site d) : Set Ω :=
  {ω | PathTyping d (fun j => X j ω)}

/-- The set of legal sample points is measurable. -/
theorem measurableSet_legalSet {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ j, Measurable (X j)) : MeasurableSet (legalSet X) := by
  have hset : legalSet X =
      X 0 ⁻¹' {0} ∩ ⋂ j : ℕ, (fun ω => (X (j + 1) ω, X j ω)) ⁻¹'
        {q : Site d × Site d | q.1 - q.2 ∈ unitSteps d} := by
    ext ω
    simp only [legalSet, PathTyping, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_iInter]
  rw [hset]
  refine (hX 0 (measurableSet_singleton _)).inter (MeasurableSet.iInter fun j => ?_)
  exact ((hX (j + 1)).prodMk (hX j)) (Set.to_countable _).measurableSet

open scoped Classical in
/-- The legal carrier of `X`: the path itself at the legal sample points and the straight path
elsewhere. -/
noncomputable def legalCarrier {Ω : Type*} (hd : 1 ≤ d) (X : ℕ → Ω → Site d) :
    ℕ → Ω → Site d :=
  fun j ω => if ω ∈ legalSet X then X j ω else straightPath hd j

/-- At a legal sample point the carrier is the path. -/
theorem legalCarrier_of_mem {Ω : Type*} (hd : 1 ≤ d) {X : ℕ → Ω → Site d} {ω : Ω}
    (hω : ω ∈ legalSet X) (j : ℕ) : legalCarrier hd X j ω = X j ω := by
  classical
  simp [legalCarrier, hω]

/-- The carrier is legal at every sample point. -/
theorem legalCarrier_typing {Ω : Type*} (hd : 1 ≤ d) (X : ℕ → Ω → Site d) (ω : Ω) :
    PathTyping d (fun j => legalCarrier hd X j ω) := by
  classical
  by_cases hω : ω ∈ legalSet X
  · have : (fun j => legalCarrier hd X j ω) = fun j => X j ω := funext (legalCarrier_of_mem hd hω)
    rw [this]
    exact hω
  · have : (fun j => legalCarrier hd X j ω) = straightPath hd := by
      funext j
      simp [legalCarrier, hω]
    rw [this]
    exact straightPath_typing hd

/-- The positions of the carrier are measurable when those of the path are. -/
theorem legalCarrier_measurable {Ω : Type*} [MeasurableSpace Ω] (hd : 1 ≤ d)
    {X : ℕ → Ω → Site d} (hX : ∀ j, Measurable (X j)) (j : ℕ) :
    Measurable (legalCarrier hd X j) := by
  classical
  exact Measurable.ite (measurableSet_legalSet hX) (hX j) measurable_const

/-- Every walk with a drift field is almost surely legal: it starts at the origin and, because the
one-step law vanishes off the unit steps, every step is a unit step. -/
theorem ae_legal_of_isDriftCERW {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) :
    ∀ᵐ ω ∂μ, ω ∈ legalSet X := by
  have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  have hs : ∀ n, ∀ᵐ ω ∂μ, X (n + 1) ω - X n ω ∈ unitSteps d := by
    intro n
    rw [ae_iff]
    set S : Set ((i : Finset.Iic (n + 1)) → Site d) :=
      {y | y ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ - y ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩ ∉
        unitSteps d} with hS
    have hsub : {ω | ¬ X (n + 1) ω - X n ω ∈ unitSteps d} ⊆
        ⋃ y ∈ S, {ω | ∀ j ≤ n + 1, X j ω = extendPath y j} := by
      intro ω hω
      refine Set.mem_biUnion (x := pastPath X (n + 1) ω) hω ?_
      intro j hj
      exact (extendPath_pastPath X hj ω).symm
    refine measure_mono_null hsub ((measure_biUnion_null_iff (Set.to_countable S)).2 fun y hy => ?_)
    rw [hX.step n (extendPath y)]
    have hbad : extendPath y (n + 1) - extendPath y n ∉ unitSteps d := by
      rw [extendPath_of_le y le_rfl, extendPath_of_le y (Nat.le_succ n)]
      exact hy
    rw [CERW.Support.Drift.driftStepProb_eq_zero ε ξ _ n hbad]
    simp
  filter_upwards [h0, ae_all_iff.mpr hs] with ω h0 hs
  exact ⟨h0, hs⟩

/-- The carrier agrees with the path at every time, almost surely. -/
theorem legalCarrier_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {X : ℕ → Ω → Site d} (hd : 1 ≤ d)
    (hX : IsDriftCERW μ ε ξ X) : ∀ᵐ ω ∂μ, ∀ j, legalCarrier hd X j ω = X j ω := by
  filter_upwards [ae_legal_of_isDriftCERW hX] with ω hω j
  exact legalCarrier_of_mem hd hω j

/-- **Transport of the walk law.** The legal carrier of a walk with a drift field is a walk with
the same drift field and parameter, with measurable positions, started at the origin at every
sample point. -/
theorem isDriftCERW_legalCarrier {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {X : ℕ → Ω → Site d} (hd : 1 ≤ d)
    (hX : IsDriftCERW μ ε ξ X) : IsDriftCERW μ ε ξ (legalCarrier hd X) := by
  have hae := legalCarrier_ae_eq hd hX
  refine ⟨legalCarrier_measurable hd hX.measurable, ?_, fun n x => ?_⟩
  · have : {ω | legalCarrier hd X 0 ω ≠ 0} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact (legalCarrier_typing hd X ω).1
    rw [this, measure_empty]
  · have hcyl : ∀ m : ℕ, {ω | ∀ j ≤ m, legalCarrier hd X j ω = x j} =ᵐ[μ]
        {ω | ∀ j ≤ m, X j ω = x j} := by
      intro m
      filter_upwards [hae] with ω hω
      simp only [eq_iff_iff]
      exact forall₂_congr fun j _ => by rw [hω j]
    rw [measure_congr (hcyl (n + 1)), measure_congr (hcyl n)]
    exact hX.step n x

/-- The seven estimates of the carrier coincide with those of the path almost surely. -/
theorem E7_legalCarrier_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {X : ℕ → Ω → Site d} (hd : 1 ≤ d)
    (hX : IsDriftCERW μ ε ξ X) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (K : EventConstants)
    (n : ℕ) : E7 Ψ ε ξ K (legalCarrier hd X) n =ᵐ[μ] E7 Ψ ε ξ K X n := by
  filter_upwards [legalCarrier_ae_eq hd hX] with ω hω
  have : (fun j => legalCarrier hd X j ω) = fun j => X j ω := funext hω
  show Estimates7 Ψ ε ξ K (projectionAt Ψ ε n) (fun j => legalCarrier hd X j ω) n =
    Estimates7 Ψ ε ξ K (projectionAt Ψ ε n) (fun j => X j ω) n
  rw [this]

/-- On the legal sample points the carrier and the path have the same seven estimates. -/
theorem E7_inter_legal {Ω : Type*} (hd : 1 ≤ d) (X : ℕ → Ω → Site d)
    (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (K : EventConstants) (n : ℕ) :
    E7 Ψ ε ξ K (legalCarrier hd X) n ∩ legalSet X = E7 Ψ ε ξ K X n ∩ legalSet X := by
  ext ω
  simp only [Set.mem_inter_iff, and_congr_left_iff]
  intro hω
  have : (fun j => legalCarrier hd X j ω) = fun j => X j ω := funext (legalCarrier_of_mem hd hω)
  simp only [E7, Set.mem_setOf_eq, this]

end Legal

/-! ## The Euclidean inner radius and local-time profile on the seven estimates -/

section InnerPort

open ProbabilityTheory CERW.Support.Main CERW.Support.Law CERW.Support.Contact LatticeProb
open scoped symmDiff Pointwise NNReal

/-- Splitting the potential over a measurable subset of finite volume. -/
private lemma potential_sdiff_eq (hd : 1 ≤ d) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y = potential d ε A y + potential d ε (D \ A) y := by
  have hF : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) D :=
    CERW.Support.Geometry.integrableOn_potentialIntegrand hd hD hDfin y
  have hFA : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) A := hF.mono_set hAD
  have hFE : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) (D \ A) := hF.mono_set Set.sdiff_subset
  have hunion : A ∪ (D \ A) = D := Set.union_sdiff_cancel hAD
  have hsplit : ∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d =
      (∫ v in A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) +
      (∫ v in D \ A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) := by
    conv_lhs => rw [← hunion]
    exact setIntegral_union Set.disjoint_sdiff_right (hD.diff hA) hFA hFE
  unfold potential
  rw [hsplit]
  ring

/-- Every point `v ≠ y` with `|y| ≤ |v| ≤ R` satisfies
`(2R)^{1-d} ≤ u_v · (v - y) |v - y|^{-d}`: the sign inequality `eq:contact-sign`. -/
private lemma inv_pow_le_potentialIntegrand (hd : 2 ≤ d) {v y : EuclideanSpace ℝ (Fin d)}
    {R : ℝ} (hv : v ≠ 0) (hvy : v ≠ y) (hyv : ‖y‖ ≤ ‖v‖) (hvR : ‖v‖ ≤ R) :
    1 / (2 * R) ^ (d - 1) ≤ inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hs : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvy)
  have hR : 0 < R := hs.trans_le hvR
  have hsq := CERW.Generic.Kernel.sq_div_le_inner_unitDir_sub hv hyv
  have htR : ‖v - y‖ ≤ 2 * R := by
    calc ‖v - y‖ ≤ ‖v‖ + ‖y‖ := norm_sub_le v y
      _ ≤ 2 * R := by linarith
  have hk : 2 + k - 1 = k + 1 := by omega
  have h2R : 0 < 2 * R := by positivity
  have hdiv : ‖v - y‖ ^ 2 / (2 * ‖v‖) * (2 * R) ^ (k + 1) ≤
      inner ℝ (unitDir v) (v - y) * (2 * R) ^ (k + 1) :=
    mul_le_mul_of_nonneg_right hsq (by positivity)
  rw [show k + 2 - 1 = k + 1 by omega, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h1 : 2 * ‖v‖ * ‖v - y‖ ^ k ≤ (2 * R) ^ (k + 1) := by
    rw [pow_succ']
    exact mul_le_mul (by linarith) (pow_le_pow_left₀ ht.le htR k) (by positivity) h2R.le
  calc ‖v - y‖ ^ (k + 2) = ‖v - y‖ ^ 2 / (2 * ‖v‖) * (2 * ‖v‖ * ‖v - y‖ ^ k) := by
        field_simp
        ring
    _ ≤ ‖v - y‖ ^ 2 / (2 * ‖v‖) * (2 * R) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ _ := hdiv

/-- The volume of the part of `D` outside the ball `B(0, b)`: if `B(0, b) ⊆ D ⊆ B(0, R)` and
`|y₀| = b`, then `|D \ B(0, b)| ≤ (ω_d/(2ε)) (2R)^{d-1} U_D(y₀)`. -/
private lemma volume_excess_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hpball : ∀ ρ : ℝ, 0 < ρ → ∀ y : EuclideanSpace ℝ (Fin d),
      potential d ε (Metric.ball 0 ρ) y = 2 * d * ε * max (ρ - ‖y‖) 0)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) {R b : ℝ} (hb : 0 < b)
    (hDR : D ⊆ Metric.ball 0 R) (hball : Metric.ball 0 b ⊆ D)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : ‖y₀‖ = b) :
    (volume (D \ Metric.ball 0 b)).toReal ≤
      unitBallVolume d / (2 * ε) * (2 * R) ^ (d - 1) * potential d ε D y₀ := by
  have hd1 : 1 ≤ d := by omega
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hDfin : volume D ≠ ⊤ := (lt_of_le_of_lt (measure_mono hDR) measure_ball_lt_top).ne
  have hEm : MeasurableSet (D \ Metric.ball 0 b) := hD.diff measurableSet_ball
  have hEfin : volume (D \ Metric.ball 0 b) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfin (measure_mono Set.sdiff_subset)
  have hsplit := potential_sdiff_eq hd1 (ε := ε) measurableSet_ball hD hDfin hball y₀
  rw [hpball b hb y₀, hy₀, sub_self, max_self, mul_zero, zero_add] at hsplit
  have hint := CERW.Support.Geometry.integrableOn_potentialIntegrand hd1 hEm hEfin y₀
  have hRpos : 0 < R := by
    obtain ⟨v, hv⟩ : ∃ v, v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b := ⟨0, by simpa using hb⟩
    have := Metric.mem_ball.mp (hDR (hball hv))
    exact lt_of_le_of_lt (dist_nonneg) this
  have hlow : ∫ _v in D \ Metric.ball 0 b, 1 / (2 * R) ^ (d - 1) ≤
      ∫ v in D \ Metric.ball 0 b, inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d := by
    refine setIntegral_mono_ae_restrict (integrableOn_const hEfin) hint ?_
    filter_upwards [ae_restrict_mem hEm,
      ae_restrict_of_ae ((Set.countable_singleton y₀).ae_notMem
        (volume : Measure (EuclideanSpace ℝ (Fin d))))] with v hvE hvne
    have hvb : b ≤ ‖v‖ := by
      have : v ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b := hvE.2
      rwa [Metric.mem_ball, dist_zero_right, not_lt] at this
    have hvR : ‖v‖ ≤ R := by
      have := Metric.mem_ball.mp (hDR hvE.1)
      rw [dist_zero_right] at this
      exact this.le
    exact inv_pow_le_potentialIntegrand hd (norm_pos_iff.mp (hb.trans_le hvb))
      (fun h => hvne (by simpa using h)) (hy₀ ▸ hvb) hvR
  rw [setIntegral_const, Measure.real_def, smul_eq_mul] at hlow
  have hpE : potential d ε (D \ Metric.ball 0 b) y₀ =
      2 * ε / unitBallVolume d *
        ∫ v in D \ Metric.ball 0 b, inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d := rfl
  have hω := unitBallVolume_pos d
  have hpow : 0 < (2 * R) ^ (d - 1) := by positivity
  rw [hsplit, hpE]
  set I := ∫ v in D \ Metric.ball 0 b, inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d with hI
  have hpow' : (2 * R) ^ (d - 1) ≠ 0 := hpow.ne'
  calc (volume (D \ Metric.ball 0 b)).toReal
      = (volume (D \ Metric.ball 0 b)).toReal * (1 / (2 * R) ^ (d - 1)) * (2 * R) ^ (d - 1) := by
        field_simp
    _ ≤ I * (2 * R) ^ (d - 1) := mul_le_mul_of_nonneg_right hlow hpow.le
    _ = unitBallVolume d / (2 * ε) * (2 * R) ^ (d - 1) * (2 * ε / unitBallVolume d * I) := by
        field_simp

/-- The exponent of the rate `Q = (L/N)^e`: `1/2` in the plane and `1` for `d ≥ 3`. -/
private noncomputable def rateExp (d : ℕ) : ℝ := if d = 2 then (1 : ℝ) / 2 else 1

/-- The exponent of the rate is positive. -/
private lemma rateExp_pos (d : ℕ) : 0 < rateExp d := by
  rw [rateExp]
  split_ifs <;> norm_num

/-- The exponent of the rate is at most one. -/
private lemma rateExp_le_one (d : ℕ) : rateExp d ≤ 1 := by
  rw [rateExp]
  split_ifs <;> norm_num

/-- The exponent of the rate is at most `d - 1` for `d ≥ 2`. -/
private lemma rateExp_le_d_sub_one {d : ℕ} (hd : 2 ≤ d) : rateExp d ≤ (d : ℝ) - 1 := by
  have h1 : rateExp d ≤ 1 := rateExp_le_one d
  have h2 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  linarith

/-- The exponent of the rate is at least `1/2`. -/
private lemma half_le_rateExp (d : ℕ) : (1 : ℝ) / 2 ≤ rateExp d := by
  rw [rateExp]
  split_ifs <;> norm_num

/-- The exponent inequality behind `N √(nL) ≤ n Q`. -/
private lemma scaleExp {d : ℕ} (hd : 2 ≤ d) :
    (1 : ℝ) / (d + 1) + 1 / 2 ≤ 1 - ((1 : ℝ) / (d + 1)) * rateExp d := by
  rw [rateExp]
  split_ifs with h2
  · rw [h2]; norm_num
  · have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
    have h4 : (1 : ℝ) / (d + 1) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    rw [mul_one]
    linarith

/-- `log(n + 2) ≥ 1` for `n ≥ 1`. -/
private lemma log_nat_add_two_ge_one {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ Real.log (n + 2) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : (3 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  linarith [Real.exp_one_lt_three]

/-- The exponent `1 - (1 + e)/(d + 1)` is positive. -/
private lemma quadExp_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < 1 - (1 + rateExp d) / (d + 1) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < d + 1 := by linarith
  rw [sub_pos, div_lt_one hd1]
  have h1 : rateExp d ≤ 1 := rateExp_le_one d
  linarith

/-- The basic rate identity `n (L/n^a)^e = n^{1-ae} L^e`. -/
private lemma mul_rate_eq {n L e a : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    n * (L / n ^ a) ^ e = n ^ (1 - a * e) * L ^ e := by
  rw [Real.div_rpow hL (Real.rpow_nonneg hn.le a), ← Real.rpow_mul hn.le]
  have h2 : n * n ^ (-(a * e)) = n ^ (1 - a * e) := by
    nth_rewrite 1 [← Real.rpow_one n]
    rw [← Real.rpow_add hn]
    rw [show (1 : ℝ) + -(a * e) = 1 - a * e by ring]
  calc n * (L ^ e / n ^ (a * e))
      = (n * n ^ (-(a * e))) * L ^ e := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hn.le]
        ring
    _ = n ^ (1 - a * e) * L ^ e := by rw [h2]

/-- The scale times `√(nL)` as a single product of powers. -/
private lemma scale_mul_sqrt_eq {d : ℕ} {n L : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    n ^ ((1 : ℝ) / (d + 1)) * Real.sqrt (n * L) =
      n ^ ((1 : ℝ) / (d + 1) + 1 / 2) * L ^ ((1 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hn.le hL]
  have h1 : n ^ ((1 : ℝ) / (d + 1)) * (n ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) =
      (n ^ ((1 : ℝ) / (d + 1)) * n ^ ((1 : ℝ) / 2)) * L ^ ((1 : ℝ) / 2) := by
    ring
  rw [h1, ← Real.rpow_add hn]

/-- `N^σ ≤ Q` whenever `σ ≤ -e` and `n ≥ 1`, `e ≥ 0`. -/
private lemma rpow_scale_le_rate {d : ℕ} {n : ℕ} {e σ : ℝ} (hn : 1 ≤ n) (he0 : 0 ≤ e)
    (hσ : σ ≤ -e) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ σ ≤
      (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ e := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (n + 2) := log_nat_add_two_ge_one hn
  have hL0 : (0 : ℝ) ≤ Real.log (n + 2) := le_trans zero_le_one hL1
  have hN0 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hnpos _
  rw [← Real.rpow_mul hn0, Real.div_rpow hL0 hN0.le, ← Real.rpow_mul hn0]
  have hLe : (1 : ℝ) ≤ Real.log (n + 2) ^ e := Real.one_le_rpow hL1 he0
  have hden : (0 : ℝ) < (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) :=
    Real.rpow_pos_of_pos hnpos _
  have hfrac : (1 : ℝ) / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) ≤
      Real.log (n + 2) ^ e / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) :=
    div_le_div_of_nonneg_right hLe hden.le
  have hone : (1 : ℝ) / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) =
      (n : ℝ) ^ (-(((1 : ℝ) / (d + 1)) * e)) := by
    rw [Real.rpow_neg hn0, inv_eq_one_div]
  have hmono : (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * σ) ≤
      (n : ℝ) ^ (-(((1 : ℝ) / (d + 1)) * e)) := by
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    have h2 : ((1 : ℝ) / (d + 1)) * σ ≤ ((1 : ℝ) / (d + 1)) * (-e) :=
      mul_le_mul_of_nonneg_left hσ (by positivity)
    linarith
  rw [hone] at hfrac
  linarith

/-- `N √(nL) ≤ n Q` for `n ≥ 1`. -/
private lemma scale_mul_sqrt_le_n_rate {d : ℕ} {n : ℕ} {e : ℝ} (hn : 1 ≤ n)
    (he : (1 : ℝ) / 2 ≤ e)
    (hexp : (1 : ℝ) / (d + 1) + 1 / 2 ≤ 1 - ((1 : ℝ) / (d + 1)) * e) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) * Real.sqrt (n * Real.log (n + 2)) ≤
      (n : ℝ) * (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ e := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (n + 2) := log_nat_add_two_ge_one hn
  have hL0 : (0 : ℝ) ≤ Real.log (n + 2) := le_trans zero_le_one hL1
  rw [scale_mul_sqrt_eq hnpos hL0, mul_rate_eq hnpos hL0]
  refine mul_le_mul ?_ ?_ (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hn0 _)
  · refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    linarith [hexp]
  · exact Real.rpow_le_rpow_of_exponent_le hL1 he

/-- `N L ≤ n Q` for `n ≥ 1` once `L ≤ n^c` with `1/(d+1) + c = 1 - e/(d+1)`. -/
private lemma scale_mul_log_le_n_rate {d : ℕ} {n : ℕ} {e c : ℝ} (hn : 1 ≤ n) (he0 : 0 ≤ e)
    (hc : (1 : ℝ) / (d + 1) + c = 1 - ((1 : ℝ) / (d + 1)) * e)
    (hLc : Real.log (n + 2) ≤ (n : ℝ) ^ c) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) * Real.log (n + 2) ≤
      (n : ℝ) * (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ e := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (n + 2) := log_nat_add_two_ge_one hn
  have hL0 : (0 : ℝ) ≤ Real.log (n + 2) := le_trans zero_le_one hL1
  rw [mul_rate_eq hnpos hL0]
  have hLe : (1 : ℝ) ≤ Real.log (n + 2) ^ e := Real.one_le_rpow hL1 he0
  have hbase : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2) ≤
      (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) := by
    have h1 : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2) ≤
        (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ c :=
      mul_le_mul_of_nonneg_left hLc (Real.rpow_nonneg hn0 _)
    have h2 : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ c =
        (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) := by
      rw [← Real.rpow_add hnpos]
      rw [hc]
    rwa [h2] at h1
  calc (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2)
      ≤ (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) := hbase
    _ ≤ (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) * Real.log (n + 2) ^ e := by
        rw [le_mul_iff_one_le_right (Real.rpow_pos_of_pos hnpos _)]
        exact hLe

/-- `eq:inradius`: there are `C` and `n₀` such that, for `n ≥ n₀`, a path from the origin with
`B(0, b) ⊆ D_n ⊆ B̄(0, K N)`, `|X_n| ≤ K N`, `|A_n| ≤ K N^d`, excess volume at most
`C₁ N^d Q`, and quadratic martingale at most `C₁ (N √(nL) + N L)` has `|b/N - a| ≤ C Q`. -/
private theorem exists_inradius_rate (hd : 2 ≤ d) {ε K C₁ : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ) (b : ℝ),
      n₀ ≤ n →
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := (L / N) ^ rateExp d
      X 0 ω = 0 → 0 ≤ b →
      Metric.ball 0 b ⊆ cellSet (fun j => X j ω) n →
      cellSet (fun j => X j ω) n ⊆ Metric.closedBall 0 (K * N) →
      euclidNorm (X n ω) ≤ K * N →
      ((departureRange (fun j => X j ω) n).card : ℝ) ≤ K * N ^ d →
      (volume (cellSet (fun j => X j ω) n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal
        ≤ C₁ * N ^ d * Q →
      |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|
        ≤ C₁ * (N * Real.sqrt (n * L) + N * L) →
        |b / N - ((d + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))| ≤ C * Q := by
  let C₁' : ℝ := K ^ 2 + (Real.sqrt d / 2 * K) + K * C₁ + 2 * C₁ + 1
  have hC₁'val : C₁' = K ^ 2 + (Real.sqrt d / 2 * K) + K * C₁ + 2 * C₁ + 1 := rfl
  have hC₁' : 0 ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    linarith
  obtain ⟨C, hCpos, hC⟩ := exists_abs_div_sub_le hd hε (C₁ := C₁') hC₁'
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    ((CERW.Support.Main.tendsto_log_rpow_div_rpow 1 (quadExp_pos hd)).eventually_lt_const
      one_pos)
  refine ⟨C, hCpos, max n₁ 1, ?_⟩
  intro Ω X ω n b hmn N L Q hX0 hb hball hDsub hXn hA hEvol hQn
  have hn : 1 ≤ n := le_trans (le_max_right n₁ 1) hmn
  have hn₁' : n₁ ≤ n := le_trans (le_max_left n₁ 1) hmn
  have hNpos : 0 < N := by
    dsimp only [N]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hNnonneg : 0 ≤ N := le_of_lt hNpos
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    exact log_nat_add_two_ge_one hn
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hQeq : Q = (L / N) ^ rateExp d := rfl
  have hQnonneg : 0 ≤ Q := by
    rw [hQeq]
    exact Real.rpow_nonneg (div_nonneg hL0 hNnonneg) _
  have hNpow : N ^ (d + 1) = (n : ℝ) := by
    dsimp only [N]
    have hx : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
      rw [one_div, Nat.cast_add, Nat.cast_one]]
    exact Real.rpow_inv_natCast_pow hx (by omega)
  let S : ℝ := ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x
  let I : ℝ := ∫ v in cellSet (fun j => X j ω) n, ‖v‖
  let IE : ℝ :=
    ∫ v in cellSet (fun j => X j ω) n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b, ‖v‖
  let Qn : ℝ := dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω
  let Xsq : ℝ := euclidNorm (X n ω) ^ 2
  have hX : Xsq = (n : ℝ) - 2 * ε * S + Qn := by
    dsimp only [Xsq, S, Qn]
    exact sq_euclidNorm_eq (by omega : 1 ≤ d) ε X ω hX0 n
  have hX_nonneg : 0 ≤ Xsq := by
    dsimp only [Xsq]
    positivity
  have hK2 : K ^ 2 ≤ C₁' := by
    rw [hC₁'val]
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    have h4 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    linarith
  have hXub : Xsq ≤ C₁' * N ^ 2 := by
    dsimp only [Xsq]
    calc euclidNorm (X n ω) ^ 2 ≤ (K * N) ^ 2 :=
          pow_le_pow_left₀ (euclidNorm_nonneg _) hXn 2
      _ = K ^ 2 * N ^ 2 := by ring
      _ ≤ C₁' * N ^ 2 := mul_le_mul_of_nonneg_right hK2 (sq_nonneg N)
  have hsqrtK : Real.sqrt d / 2 * K ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h4 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    linarith
  have hSI : |S - I| ≤ C₁' * N ^ d := by
    have h := abs_sum_euclidNorm_sub_integral_le (fun j => X j ω) n
    dsimp only [S, I]
    calc |∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x -
          ∫ v in cellSet (fun j => X j ω) n, ‖v‖|
        ≤ Real.sqrt d / 2 * ((departureRange (fun j => X j ω) n).card : ℝ) := h
      _ ≤ Real.sqrt d / 2 * (K * N ^ d) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = (Real.sqrt d / 2 * K) * N ^ d := by ring
      _ ≤ C₁' * N ^ d := mul_le_mul_of_nonneg_right hsqrtK (by positivity)
  have hballadd := integral_norm_eq_ball_add (d := d) (by omega : 1 ≤ d)
      (CERW.Support.Occupation.measurableSet_cellSet (fun j => X j ω) n) hb hball hDsub
  have hI : I = d * unitBallVolume d * b ^ (d + 1) / (d + 1) + IE := by
    dsimp only [I, IE]
    exact hballadd.1
  have hIE0 : 0 ≤ IE := by
    dsimp only [IE]
    exact hballadd.2.1
  have hKC₁ : K * C₁ ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    have h4 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    linarith
  have hIEub : IE ≤ C₁' * n * Q := by
    have h3 := hballadd.2.2
    dsimp only [IE] at h3 ⊢
    have hKN : (0 : ℝ) ≤ K * N := mul_nonneg hK.le hNnonneg
    have hnQ : (0 : ℝ) ≤ (n : ℝ) * Q := mul_nonneg (Nat.cast_nonneg n) hQnonneg
    have hstep : (K * N) * (volume (cellSet (fun j => X j ω) n \
        Metric.ball 0 b)).toReal ≤ (K * N) * (C₁ * N ^ d * Q) :=
      mul_le_mul_of_nonneg_left hEvol hKN
    calc ∫ v in cellSet (fun j => X j ω) n \ Metric.ball 0 b, ‖v‖
        ≤ (K * N) * (volume (cellSet (fun j => X j ω) n \
            Metric.ball 0 b)).toReal := h3
      _ ≤ (K * N) * (C₁ * N ^ d * Q) := hstep
      _ = K * C₁ * (N * N ^ d) * Q := by ring
      _ = K * C₁ * N ^ (d + 1) * Q := by rw [← pow_succ']
      _ = K * C₁ * (n : ℝ) * Q := by rw [hNpow]
      _ = (K * C₁) * ((n : ℝ) * Q) := by ring
      _ ≤ C₁' * ((n : ℝ) * Q) := mul_le_mul_of_nonneg_right hKC₁ hnQ
      _ = C₁' * (n : ℝ) * Q := by ring
  have hexp : (1 : ℝ) / (d + 1) + 1 / 2 ≤ 1 - ((1 : ℝ) / (d + 1)) * rateExp d :=
    scaleExp hd
  have hc : (1 : ℝ) / (d + 1) + (1 - (1 + rateExp d) / (d + 1)) =
      1 - ((1 : ℝ) / (d + 1)) * rateExp d := by
    field_simp
    ring
  have hLc : L ≤ (n : ℝ) ^ (1 - (1 + rateExp d) / (d + 1)) := by
    have hlt := hn₁ n hn₁'
    dsimp only [L] at hlt ⊢
    rw [Real.rpow_one] at hlt
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hcp : (0 : ℝ) < (n : ℝ) ^ (1 - (1 + rateExp d) / (d + 1)) :=
      Real.rpow_pos_of_pos hnpos _
    rw [div_lt_one hcp] at hlt
    exact le_of_lt hlt
  have hQn_ev : N * Real.sqrt (n * L) ≤ (n : ℝ) * Q ∧ N * L ≤ (n : ℝ) * Q := by
    constructor
    · rw [hQeq]
      exact scale_mul_sqrt_le_n_rate hn (half_le_rateExp d) hexp
    · rw [hQeq]
      exact scale_mul_log_le_n_rate hn (rateExp_pos d).le hc hLc
  have h2C₁ : 2 * C₁ ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    linarith
  have hQnub : |Qn| ≤ C₁' * n * Q := by
    dsimp only [Qn]
    have hsum : N * Real.sqrt (n * L) + N * L ≤ 2 * ((n : ℝ) * Q) := by
      linarith [hQn_ev.1, hQn_ev.2]
    have hnQ : (0 : ℝ) ≤ (n : ℝ) * Q := mul_nonneg (Nat.cast_nonneg n) hQnonneg
    calc |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|
        ≤ C₁ * (N * Real.sqrt (n * L) + N * L) := hQn
      _ ≤ C₁ * (2 * ((n : ℝ) * Q)) := mul_le_mul_of_nonneg_left hsum hC₁
      _ = (2 * C₁) * ((n : ℝ) * Q) := by ring
      _ ≤ C₁' * ((n : ℝ) * Q) := mul_le_mul_of_nonneg_right h2C₁ hnQ
      _ = C₁' * (n : ℝ) * Q := by ring
  have hNQ1 : N ^ (1 - (d : ℝ)) ≤ Q := by
    rw [hQeq]
    refine rpow_scale_le_rate hn (rateExp_pos d).le ?_
    linarith [rateExp_le_d_sub_one hd]
  have hNQ2 : N⁻¹ ≤ Q := by
    rw [hQeq]
    have h := rpow_scale_le_rate (d := d) (n := n) (e := rateExp d) (σ := -1) hn
      (rateExp_pos d).le (by linarith [rateExp_le_one d])
    simpa only [Real.rpow_neg_one] using h
  exact hC n b S I IE Qn Xsq Q hn hb hQnonneg hX hX_nonneg hXub hSI hI hIE0 hIEub
    hQnub hNQ1 hNQ2


/-- Eventually `K ≤ N`, `L³ ≤ N`, `N² ≤ n` and `1 ≤ n`, where `N = n^{1/(d+1)}` and
`L = log(n + 2)`. -/
private lemma eventually_scales (hd : 1 ≤ d) (K : ℝ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    K ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ∧
    Real.log (n + 2) ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ∧
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ 2 ≤ n ∧ 1 ≤ n := by
  have hc : (0 : ℝ) < 1 / (d + 1) := by positivity
  have h1 : ∀ᶠ n : ℕ in atTop, K ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
    ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  have h2 : ∀ᶠ n : ℕ in atTop,
      Real.log (n + 2) ^ (3 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) < 1 :=
    (tendsto_log_rpow_div_rpow 3 hc).eventually_lt_const one_pos
  have h3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hK, hL, h1n⟩ := hn₀ n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨hK, ?_, ?_, h1n⟩
  · rw [div_lt_one hNpos] at hL
    have e : Real.log (n + 2) ^ (3 : ℕ) = Real.log (n + 2) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [e]; exact hL.le
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    calc (n : ℝ) ^ ((1 : ℝ) / (d + 1) * ((2 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hn1
          have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          push_cast
          linarith
      _ = n := Real.rpow_one _

/-- The error scale of the global approximation is at most `2 (√C₀ + 1) N Q^{1/d}` once
`1 ≤ L`, `L³ ≤ N` and `M ≤ C₀ N`, where `Q = (L/N)^e` is the rate. -/
private lemma error_le_scale (hd : 2 ≤ d) {M C₀ N L : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀)
    (hL : 1 ≤ L) (hLN : L ^ 3 ≤ N) (hMN : M ≤ C₀ * N) :
    (if d = 2 then Real.sqrt M * L + L else Real.sqrt (M * L) + L) ≤
      2 * (Real.sqrt C₀ + 1) * (N * ((L / N) ^ rateExp d) ^ ((1 : ℝ) / d)) := by
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hN1 : 1 ≤ N := hL3.trans hLN
  have hN : 0 < N := by linarith
  have hLN' : L ≤ N := (le_self_pow₀ hL (by norm_num)).trans hLN
  have ht : 0 < L / N := div_pos (by linarith) hN
  have ht1 : L / N ≤ 1 := (div_le_one hN).2 hLN'
  obtain ⟨h2e, h3e⟩ := CERW.Support.Contact.error_scale_le hM hC₀ hMN hN1 hL
  have hs : 0 ≤ Real.sqrt C₀ + 1 := by positivity
  split_ifs with h2
  · have he : rateExp d = 1 / 2 := by rw [rateExp, if_pos h2]
    rw [he]
    subst h2
    have key : Real.sqrt N * L ≤ N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) := by
      have hq : ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) =
          (L / N) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_mul ht.le]; norm_num
      rw [hq]
      apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
      have h4 : ((L / N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = L / N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
      have hsN : Real.sqrt N ^ (4 : ℕ) = N ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hN.le]
      rw [mul_pow, mul_pow, h4, hsN]
      have e : N ^ 4 * (L / N) = N ^ 3 * L := by field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left hLN (by positivity : 0 ≤ N ^ 2 * L)
      nlinarith
    calc Real.sqrt M * L + L ≤ (Real.sqrt C₀ + 1) * (Real.sqrt N * L) := h2e
      _ ≤ (Real.sqrt C₀ + 1) * (N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by
          gcongr
      _ ≤ 2 * (Real.sqrt C₀ + 1) *
            (N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by
          have : 0 ≤ (Real.sqrt C₀ + 1) *
              (N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by positivity
          linarith
  · have he : rateExp d = 1 := by rw [rateExp, if_neg h2]
    rw [he, Real.rpow_one]
    have hd3 : (3 : ℝ) ≤ d := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    have hexp : (1 : ℝ) / d ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hQ : (L / N) ^ ((1 : ℝ) / 2) ≤ (L / N) ^ ((1 : ℝ) / d) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 hexp
    have hsq : Real.sqrt (N * L) = N * (L / N) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, show N * L = N ^ 2 * (L / N) by field_simp,
        Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le]
    have hLsq : L ≤ Real.sqrt (N * L) := by
      calc L = Real.sqrt (L * L) := (Real.sqrt_mul_self (by linarith)).symm
        _ ≤ Real.sqrt (N * L) := Real.sqrt_le_sqrt (by nlinarith)
    calc Real.sqrt (M * L) + L ≤ (Real.sqrt C₀ + 1) * (Real.sqrt (N * L) + L) := h3e
      _ ≤ (Real.sqrt C₀ + 1) * (2 * Real.sqrt (N * L)) := by gcongr; linarith
      _ = 2 * (Real.sqrt C₀ + 1) * (N * (L / N) ^ ((1 : ℝ) / 2)) := by rw [hsq]; ring
      _ ≤ 2 * (Real.sqrt C₀ + 1) * (N * (L / N) ^ ((1 : ℝ) / d)) := by gcongr

/-- `(N ^ d) ^ (1 / d) = N` for `N ≥ 0` and `d > 0`. -/
private lemma rpow_natCast_inv_self {N : ℝ} (hN : 0 ≤ N) (hd : 0 < d) :
    (N ^ d) ^ ((1 : ℝ) / d) = N := by
  have hdR : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  rw [← Real.rpow_natCast N d, ← Real.rpow_mul hN]
  have hmul : (d : ℝ) * ((1 : ℝ) / (d : ℝ)) = 1 := by field_simp
  rw [hmul, Real.rpow_one]

/-- Raising the excess-volume bound to the power `1 / d`. -/
private lemma volume_rpow_inv_le {m C₁ N Q : ℝ} (hm0 : 0 ≤ m) (hC₁ : 0 ≤ C₁)
    (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hm : m ≤ C₁ * N ^ d * Q) (hd : 0 < d) :
    m ^ ((1 : ℝ) / d) ≤ C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : 0 ≤ (1 : ℝ) / d := le_of_lt (div_pos one_pos hdR)
  calc m ^ ((1 : ℝ) / d) ≤ (C₁ * N ^ d * Q) ^ ((1 : ℝ) / d) :=
        Real.rpow_le_rpow hm0 hm hp
    _ = C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d) := by
        rw [Real.mul_rpow (mul_nonneg hC₁ (pow_nonneg hN d)) hQ,
            Real.mul_rpow hC₁ (pow_nonneg hN d)]
        rw [rpow_natCast_inv_self hN hd]

/-- The local-time profile at every point of `ℝ^d`: under the global approximation, the
inradius, excess-volume and error bounds, `ℓ̃_n(y)` is within `C N Q^{1/d}` of the cone
`2dε (aN - |y|)_+`. -/
private theorem abs_cellLocalTime_sub_cone_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Cg : ℝ}
    (hCg : 0 ≤ Cg)
    (hpball : ∀ ρ : ℝ, 0 < ρ → ∀ y : EuclideanSpace ℝ (Fin d),
      potential d ε (Metric.ball 0 ρ) y = 2 * d * ε * max (ρ - ‖y‖) 0)
    (hpbound : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |potential d ε D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d))
    {a C₁ K : ℝ} (hC₁ : 0 ≤ C₁) (hK : a + 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d) (n : ℕ) (b δ₀ N Q : ℝ), 0 < N → 0 ≤ Q → Q ≤ 1 →
      0 < b → Metric.ball 0 b ⊆ cellSet X n → cellSet X n ⊆ Metric.ball 0 ((K - 1) * N) →
      |b - a * N| ≤ C₁ * N * Q →
      (volume (cellSet X n \ Metric.ball 0 b)).toReal ≤ C₁ * N ^ d * Q →
      δ₀ ≤ C₁ * N * Q ^ ((1 : ℝ) / d) →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ < K * N →
        |cellLocalTime X n y - potential d ε (cellSet X n) y| ≤ δ₀) →
      ∀ y : EuclideanSpace ℝ (Fin d),
        |cellLocalTime X n y - 2 * d * ε * max (a * N - ‖y‖) 0| ≤ C * (N * Q ^ ((1 : ℝ) / d)) := by
  have hdpos : 0 < d := by omega
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hp_le_one : (1 : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hdR]
    simpa using hdR1
  let Cd : ℝ := Cg * ε
  have hCd0 : 0 ≤ Cd := mul_nonneg hCg hε.le
  have hCpos : 0 < C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁ + 1 := by
    have h1 : 0 ≤ Cd * C₁ ^ ((1 : ℝ) / d) := mul_nonneg hCd0 (Real.rpow_nonneg hC₁ _)
    have h2 : 0 ≤ 2 * (d : ℝ) * ε * C₁ := by positivity
    linarith
  refine ⟨C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁ + 1, hCpos, ?_⟩
  intro X n b δ₀ N Q hN hQ0 hQle hb hball hDsub hba hvol hδ hall y
  have hNpos : 0 < N := hN
  have hQp0 : 0 ≤ Q ^ ((1 : ℝ) / d) := Real.rpow_nonneg hQ0 _
  have hQleQp : Q ≤ Q ^ ((1 : ℝ) / d) := Real.self_le_rpow_of_le_one hQ0 hQle hp_le_one
  by_cases hy : ‖y‖ < K * N
  · have hlocal : |cellLocalTime X n y - potential d ε (cellSet X n) y| ≤ δ₀ := hall y hy
    have hDmeas : MeasurableSet (cellSet X n) :=
      CERW.Support.Occupation.measurableSet_cellSet X n
    have hEmeas : MeasurableSet (cellSet X n \ Metric.ball 0 b) :=
      hDmeas.diff measurableSet_ball
    have hDfin : volume (cellSet X n) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono hDsub) measure_ball_lt_top).ne
    have hEbdd : Bornology.IsBounded (cellSet X n \ Metric.ball 0 b) :=
      (Metric.isBounded_ball.subset hDsub).subset Set.sdiff_subset
    have hsplit : potential d ε (cellSet X n) y =
        potential d ε (Metric.ball 0 b) y +
        potential d ε (cellSet X n \ Metric.ball 0 b) y :=
      potential_sdiff_eq hd1 measurableSet_ball hDmeas hDfin hball y
    have hUB : potential d ε (Metric.ball 0 b) y = 2 * (d : ℝ) * ε * max (b - ‖y‖) 0 :=
      hpball b hb y
    have hmle : (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / d) ≤
        C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d) :=
      volume_rpow_inv_le ENNReal.toReal_nonneg hC₁ hN.le hQ0 hvol hdpos
    have hUE : |potential d ε (cellSet X n \ Metric.ball 0 b) y| ≤
        Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) := by
      calc |potential d ε (cellSet X n \ Metric.ball 0 b) y|
          ≤ Cd * (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / d) :=
            hpbound _ hEmeas hEbdd y
        _ ≤ Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) :=
            mul_le_mul_of_nonneg_left hmle hCd0
    have hUBdiff : |potential d ε (Metric.ball 0 b) y -
        2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0| ≤
        2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) := by
      rw [hUB]
      have hcoef : 0 ≤ 2 * (d : ℝ) * ε := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hcoef]
      have hmaxle : |max (b - ‖y‖) 0 - max (a * N - ‖y‖) 0| ≤ C₁ * N * Q := by
        have h1 := abs_max_sub_max_le_abs (b - ‖y‖) (a * N - ‖y‖) 0
        have h2 : (b - ‖y‖) - (a * N - ‖y‖) = b - a * N := by ring
        rw [h2] at h1
        exact h1.trans hba
      calc 2 * (d : ℝ) * ε * |max (b - ‖y‖) 0 - max (a * N - ‖y‖) 0|
          ≤ 2 * (d : ℝ) * ε * (C₁ * N * Q) := mul_le_mul_of_nonneg_left hmaxle hcoef
        _ = 2 * (d : ℝ) * ε * C₁ * N * Q := by ring
        _ ≤ 2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) := by
            have hQstep : C₁ * N * Q ≤ C₁ * N * Q ^ ((1 : ℝ) / d) :=
              mul_le_mul_of_nonneg_left hQleQp (mul_nonneg hC₁ hN.le)
            calc 2 * (d : ℝ) * ε * C₁ * N * Q
                = 2 * (d : ℝ) * ε * (C₁ * N * Q) := by ring
              _ ≤ 2 * (d : ℝ) * ε * (C₁ * N * Q ^ ((1 : ℝ) / d)) :=
                  mul_le_mul_of_nonneg_left hQstep hcoef
              _ = 2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) := by ring
    have htri : |(cellLocalTime X n y - potential d ε (cellSet X n) y) +
          potential d ε (cellSet X n \ Metric.ball 0 b) y +
          (potential d ε (Metric.ball 0 b) y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0)| ≤
        |cellLocalTime X n y - potential d ε (cellSet X n) y| +
          |potential d ε (cellSet X n \ Metric.ball 0 b) y| +
          |potential d ε (Metric.ball 0 b) y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0| := by
      have h1 := abs_add_le (cellLocalTime X n y - potential d ε (cellSet X n) y)
          (potential d ε (cellSet X n \ Metric.ball 0 b) y)
      have h2 := abs_add_le
          ((cellLocalTime X n y - potential d ε (cellSet X n) y) +
            potential d ε (cellSet X n \ Metric.ball 0 b) y)
          (potential d ε (Metric.ball 0 b) y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0)
      linarith
    have hdecomp : cellLocalTime X n y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0 =
        (cellLocalTime X n y - potential d ε (cellSet X n) y) +
          potential d ε (cellSet X n \ Metric.ball 0 b) y +
          (potential d ε (Metric.ball 0 b) y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0) := by
      rw [hsplit]
      ring
    calc |cellLocalTime X n y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0|
        = |(cellLocalTime X n y - potential d ε (cellSet X n) y) +
            potential d ε (cellSet X n \ Metric.ball 0 b) y +
            (potential d ε (Metric.ball 0 b) y -
              2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0)| := by rw [hdecomp]
      _ ≤ |cellLocalTime X n y - potential d ε (cellSet X n) y| +
          |potential d ε (cellSet X n \ Metric.ball 0 b) y| +
          |potential d ε (Metric.ball 0 b) y -
            2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0| := htri
      _ ≤ C₁ * N * Q ^ ((1 : ℝ) / d) +
          Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) +
          2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) :=
          add_le_add (add_le_add (hlocal.trans hδ) hUE) hUBdiff
      _ = (C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁) * (N * Q ^ ((1 : ℝ) / d)) := by
          ring
      _ ≤ (C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁ + 1) *
            (N * Q ^ ((1 : ℝ) / d)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hN.le hQp0)
          linarith
  · have hKN : K * N ≤ ‖y‖ := le_of_not_gt hy
    have hynot : y ∉ cellSet X n := by
      intro hymem
      have hlt := Metric.mem_ball.mp (hDsub hymem)
      rw [dist_zero_right] at hlt
      have hle : (K - 1) * N ≤ K * N := mul_le_mul_of_nonneg_right (by linarith) hN.le
      linarith
    have hloc0 : cellLocalTime X n y = 0 :=
      CERW.Support.Occupation.cellLocalTime_eq_zero_of_not_mem X n hynot
    have hmax0 : max (a * N - ‖y‖) 0 = 0 := by
      apply max_eq_right
      have : a * N ≤ K * N := mul_le_mul_of_nonneg_right (by linarith) hN.le
      linarith
    rw [hloc0, hmax0]
    simp only [mul_zero, sub_zero, abs_zero]
    exact mul_nonneg hCpos.le (mul_nonneg hN.le hQp0)

/-- The rate `q_n = (log n/(aN))^e` and the rate `Q = (log(n + 2)/N)^e` are comparable:
`a^e q_n ≤ Q ≤ 2^e a^e q_n` for `n ≥ 2`. -/
private lemma rate_compare {n : ℕ} (hn : 2 ≤ n) {a N e : ℝ} (ha : 0 < a) (hN : 0 < N)
    (he : 0 ≤ e) :
    a ^ e * (Real.log n / (a * N)) ^ e ≤ (Real.log (n + 2) / N) ^ e ∧
    (Real.log (n + 2) / N) ^ e ≤ 2 ^ e * (a ^ e * (Real.log n / (a * N)) ^ e) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlogL : Real.log n ≤ Real.log (n + 2) := Real.log_le_log hn0 (by linarith)
  have hLlog : Real.log (n + 2) ≤ 2 * Real.log n := by
    have h1 : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n := by
      rw [Real.log_pow]; norm_num
    rw [← h1]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hmul : a ^ e * (Real.log n / (a * N)) ^ e = (Real.log n / N) ^ e := by
    rw [← Real.mul_rpow ha.le (div_nonneg hlog0 (mul_nonneg ha.le hN.le))]
    congr 1
    field_simp
  rw [hmul]
  refine ⟨Real.rpow_le_rpow (div_nonneg hlog0 hN.le) (div_le_div_of_nonneg_right hlogL hN.le) he,
    ?_⟩
  calc (Real.log (n + 2) / N) ^ e ≤ (2 * (Real.log n / N)) ^ e := by
        apply Real.rpow_le_rpow (div_nonneg (hlog0.trans hlogL) hN.le) _ he
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right hLlog hN.le
    _ = 2 ^ e * (Real.log n / N) ^ e :=
        Real.mul_rpow (by norm_num) (div_nonneg hlog0 hN.le)

/-- The gradient of the Euclidean norm at a nonzero point is the direction `v/|v|`. -/
theorem gradient_norm_eq_unitDir {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    gradient (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) v = CERW.unitDir v := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := (hasStrictFDerivAt_norm_sq v).hasFDerivAt.sqrt (by positivity)
  have h2 : (fun w : EuclideanSpace ℝ (Fin d) => Real.sqrt (‖w‖ ^ 2)) =
      fun w => ‖w‖ := by
    funext w
    exact Real.sqrt_sq (norm_nonneg w)
  rw [h2] at h1
  have h4 : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) (CERW.unitDir v) =
      (1 / (2 * √(‖v‖ ^ 2))) • 2 • (innerSL ℝ) v := by
    ext w
    simp only [InnerProductSpace.toDual_apply_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Real.sqrt_sq hpos.le, CERW.unitDir,
      real_inner_smul_left]
    norm_num
    field_simp
  have h3 : HasGradientAt (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) (CERW.unitDir v) v := by
    rw [hasGradientAt_iff_hasFDerivAt, h4]
    exact h1
  exact h3.gradient

/-- For the Euclidean norm, the norm potential `eq:potential-norm` is the potential
`eq:potential-intro`, since the gradient is `v/|v|` off the origin. -/
theorem normPotential_norm_eq (hd : 1 ≤ d) (ε : ℝ) (D : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    CERW.normPotential d ε (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) D y =
      CERW.potential d ε D y := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  unfold CERW.normPotential CERW.potential
  congr 1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [(Set.countable_singleton (0 : EuclideanSpace ℝ (Fin d))).ae_notMem
    (volume : Measure (EuclideanSpace ℝ (Fin d)))] with v hv
  rw [gradient_norm_eq_unitDir hv]

/-- The volume of the Euclidean unit ball, written as the volume of `{|v| < 1}`. -/
theorem normBallVolume_norm : CERW.normBallVolume (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) =
    unitBallVolume d := by
  unfold CERW.normBallVolume CERW.unitBallVolume
  congr 2
  ext v
  simp

/-- The deterministic core of the inner-radius estimates for the Euclidean walk: for large `n`, a
path from the origin with the upper coarse bounds, the global approximation of the local times by
the potential, the quadratic martingale bound and a contact-point bound `U_{D_n}(y₀) ≤ C_c r_n q_n`
at every contact point `y₀` has the inner radius, the volume and the local-time profile
estimates. -/
private theorem inner_core_inputs (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {C₀ C₁ Cc Cg : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hCc : 0 < Cc) (hCg : 0 ≤ Cg)
    (hpball : ∀ ρ : ℝ, 0 < ρ → ∀ y : EuclideanSpace ℝ (Fin d),
      potential d ε (Metric.ball 0 ρ) y = 2 * d * ε * max (ρ - ‖y‖) 0)
    (hpbound : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |potential d ε D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d)) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n →
      let r : ℝ := ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      let q : ℝ := if d = 2 then Real.sqrt (Real.log n / r) else Real.log n / r
      X 0 ω = 0 →
      ((departureRange (fun j => X j ω) n).card : ℝ) ≤
        C₀ * ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d →
      (maxLocalTime (fun j => X j ω) n : ℝ) ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) →
      maxRadius (fun j => X j ω) n ≤ C₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
        |cellLocalTime (fun j => X j ω) n y - potential d ε (cellSet (fun j => X j ω) n) y| ≤
          C₁ * (if d = 2 then
              Real.sqrt (maxLocalTime (fun j => X j ω) n : ℝ) * Real.log (n + 2) +
                Real.log (n + 2)
            else Real.sqrt ((maxLocalTime (fun j => X j ω) n : ℝ) * Real.log (n + 2)) +
              Real.log (n + 2))) →
      |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω| ≤
        C₁ * ((n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.sqrt (n * Real.log (n + 2)) +
          (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2)) →
      (∀ y₀ : EuclideanSpace ℝ (Fin d), ‖y₀‖ = innerRadius (fun j => X j ω) n →
          y₀ ∈ closure (cellSet (fun j => X j ω) n)ᶜ →
          potential d ε (cellSet (fun j => X j ω) n) y₀ ≤ Cc * r * q) →
      |innerRadius (fun j => X j ω) n - r| ≤ C * r * q ∧
      volume ((r⁻¹ • cellSet (fun j => X j ω) n) ∆
          Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ ENNReal.ofReal (C * q) ∧
      ∀ y : EuclideanSpace ℝ (Fin d),
        |cellLocalTime (fun j => X j ω) n y - 2 * d * ε * max (r - ‖y‖) 0|
          ≤ C * r * q ^ ((1 : ℝ) / d) := by
  intro ωd
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hωpos : 0 < ωd := unitBallVolume_pos d
  have hbase : 0 < ((d : ℝ) + 1) / (2 * d * ε * ωd) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hbase _
  have he0 : 0 < rateExp d := rateExp_pos d
  have hae : 0 < a ^ rateExp d := Real.rpow_pos_of_pos ha _
  set CE : ℝ := ωd / (2 * ε) * (2 * (C₀ + 1)) ^ (d - 1) * Cc * a * (a ^ rateExp d)⁻¹ with hCE
  have hCEpos : 0 < CE := by positivity
  set cQ : ℝ := 2 ^ rateExp d * a ^ rateExp d with hcQ
  have hcQpos : 0 < cQ := by positivity
  set C₄ : ℝ := max (1 / a) (CE / a ^ d) with hC₄
  have hC₄nn : 0 ≤ C₄ := le_max_of_le_left (by positivity)
  set C₂ : ℝ := max (max (2 * C₁ * (Real.sqrt C₀ + 1)) CE) (max C₁ CE) with hC₂
  have hC₂nn : 0 ≤ C₂ := le_max_of_le_left (le_max_of_le_left (by positivity))
  obtain ⟨Cs, -, hcs⟩ := exists_contact_setup hd
  obtain ⟨Ci, hCi, ni, hir⟩ := exists_inradius_rate hd hε (K := C₀ + 2) (C₁ := max C₁ CE)
    (by linarith only [hC₀]) (le_max_of_le_left hC₁.le)
  obtain ⟨Cv, hCv, hvol⟩ := exists_volume_symmDiff_add_le (d := d) hd1 (a := 1)
    (C₁ := max C₄ (Ci / a)) one_pos (le_max_of_le_left hC₄nn)
  obtain ⟨Cp, hCp, hprof⟩ := abs_cellLocalTime_sub_cone_le hd hε hCg hpball hpbound (a := a)
    (C₁ := max C₂ Ci) (K := a + C₀ + 3) (le_max_of_le_left hC₂nn) (by linarith only [hC₀])
  obtain ⟨ns, hns⟩ := eventually_scales hd1 (max (a + C₀ + 3) (Real.sqrt d + 1))
  refine ⟨max (max (Ci * cQ / a) (Cv * cQ)) (Cp * cQ ^ ((1 : ℝ) / d) / a),
    lt_max_of_lt_left (lt_max_of_lt_left (by positivity)), max (max ni ns) 2, ?_⟩
  intro Ω X ω n hn r q h0 hcard hM hH hglob hquad hcont
  have hni : ni ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnsn : ns ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hKN, hL3, hN2, h1n⟩ := hns n hnsn
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN_def
  set L : ℝ := Real.log (n + 2) with hL_def
  set Q : ℝ := (L / N) ^ rateExp d with hQ_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hsd : Real.sqrt d + 1 ≤ N := (le_max_right _ _).trans hKN
  have hK'N : a + C₀ + 3 ≤ N := (le_max_left _ _).trans hKN
  have hN1 : 1 ≤ N := by linarith only [hsd, Real.sqrt_nonneg (d : ℝ)]
  have hNpos : 0 < N := by linarith only [hN1]
  have hL1 : 1 ≤ L := by
    rw [hL_def, Real.le_log_iff_exp_le (by positivity)]
    linarith only [Real.exp_one_lt_d9, hn1]
  have hL0 : 0 ≤ L := by linarith only [hL1]
  have hLN : L ≤ N := (le_self_pow₀ hL1 (by norm_num)).trans hL3
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg (div_nonneg hL0 hNpos.le) _
  have hQ1 : Q ≤ 1 :=
    Real.rpow_le_one (div_nonneg hL0 hNpos.le) ((div_le_one hNpos).2 hLN) he0.le
  have hNd : 0 ≤ N ^ d := pow_nonneg hNpos.le d
  have hr : r = a * N := by
    show (((d : ℝ) + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) = a * N
    rw [show ((d : ℝ) + 1) * n / (2 * d * ε * ωd) =
      (((d : ℝ) + 1) / (2 * d * ε * ωd)) * n by ring]
    exact Real.mul_rpow hbase.le (Nat.cast_nonneg n)
  have hrpos : 0 < r := by rw [hr]; positivity
  have hq : q = (Real.log n / (a * N)) ^ rateExp d := by
    show (if d = 2 then Real.sqrt (Real.log n / r) else Real.log n / r) = _
    rw [hr]
    by_cases h2 : d = 2
    · rw [if_pos h2, rateExp, if_pos h2, Real.sqrt_eq_rpow]
    · rw [if_neg h2, rateExp, if_neg h2, Real.rpow_one]
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact Real.rpow_nonneg (div_nonneg hlog0 (by positivity)) _
  obtain ⟨hcmp1, hcmp2⟩ := rate_compare hn2 ha hNpos he0.le
  rw [← hq] at hcmp1 hcmp2
  have hQq : Q ≤ cQ * q := by
    rw [hQ_def, hcQ]
    calc (L / N) ^ rateExp d ≤ 2 ^ rateExp d * (a ^ rateExp d * q) := hcmp2
      _ = 2 ^ rateExp d * a ^ rateExp d * q := by ring
  have hqQ : q ≤ (a ^ rateExp d)⁻¹ * Q := by
    rw [inv_mul_eq_div, le_div_iff₀ hae]
    calc q * a ^ rateExp d = a ^ rateExp d * q := by ring
      _ ≤ Q := hcmp1
  have hM0 : (0 : ℝ) ≤ (maxLocalTime (fun j => X j ω) n : ℝ) := Nat.cast_nonneg _
  have hD : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((C₀ + 1) * N) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 (fun j => X j ω) n).trans
      (Metric.ball_subset_ball (by linarith only [hH, hsd]))
  have hDmeas : MeasurableSet (cellSet (fun j => X j ω) n) :=
    CERW.Support.Occupation.measurableSet_cellSet _ n
  have hDfin : volume (cellSet (fun j => X j ω) n) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hD) measure_ball_lt_top).ne
  have hR1 : 1 ≤ (C₀ + 1) * N := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (C₀ + 1) * N :=
          mul_le_mul (by linarith only [hC₀]) hN1 zero_le_one (by linarith only [hC₀])
  obtain ⟨hb', hball', -⟩ := hcs ε hε.le (fun j => X j ω) n ((C₀ + 1) * N) h1n h0 hR1 hD
  set b : ℝ := innerRadius (fun j => X j ω) n with hb_def
  have hb : 0 < b := hb'
  have hball : Metric.ball 0 b ⊆ cellSet (fun j => X j ω) n := hball'
  -- a contact point in the closure of the complement
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hRpos : 0 < (C₀ + 1) * N := by positivity
  obtain ⟨y₁, hy₁⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin d)))
    (r := (C₀ + 1) * N)).mpr hRpos.le
  have hy₁c : y₁ ∉ cellSet (fun j => X j ω) n := by
    intro hy
    have h := Metric.mem_ball.mp (hD hy)
    rw [dist_zero_right] at h
    have h' : ‖y₁‖ = (C₀ + 1) * N := by simpa using (mem_sphere_iff_norm.mp hy₁)
    linarith only [h, h']
  obtain ⟨y₀, hy₀cl, hy₀norm⟩ := exists_mem_closure_norm_eq_sInf (d := d)
    (E := (cellSet (fun j => X j ω) n)ᶜ) ⟨y₁, hy₁c⟩
  have hy₀b : ‖y₀‖ = b := hy₀norm
  have hH0 := hcont y₀ hy₀b hy₀cl
  -- the excess volume
  have hEvol : (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal ≤ CE * N ^ d * Q := by
    have h1 := volume_excess_le hd hε hpball hDmeas hb hD hball hy₀b
    have hcoef : 0 ≤ ωd / (2 * ε) * (2 * ((C₀ + 1) * N)) ^ (d - 1) := by positivity
    have h2 : potential d ε (cellSet (fun j => X j ω) n) y₀ ≤
        Cc * (a * N) * ((a ^ rateExp d)⁻¹ * Q) := by
      calc potential d ε (cellSet (fun j => X j ω) n) y₀ ≤ Cc * r * q := hH0
        _ = Cc * (a * N) * q := by rw [hr]
        _ ≤ Cc * (a * N) * ((a ^ rateExp d)⁻¹ * Q) :=
            mul_le_mul_of_nonneg_left hqQ (by positivity)
    have hNd1 : N ^ (d - 1) * N = N ^ d := by
      rw [← pow_succ]
      congr 1
      omega
    calc (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal
        ≤ ωd / (2 * ε) * (2 * ((C₀ + 1) * N)) ^ (d - 1) *
            potential d ε (cellSet (fun j => X j ω) n) y₀ := by
          exact h1
      _ ≤ ωd / (2 * ε) * (2 * ((C₀ + 1) * N)) ^ (d - 1) *
            (Cc * (a * N) * ((a ^ rateExp d)⁻¹ * Q)) :=
          mul_le_mul_of_nonneg_left h2 hcoef
      _ = CE * N ^ d * Q := by
          rw [hCE, ← hNd1]
          simp only [mul_pow]
          ring
  -- the inner radius
  have hXn : euclidNorm (X n ω) ≤ (C₀ + 2) * N :=
    (euclidNorm_le_maxRadius (fun j => X j ω) (le_refl n)).trans (by linarith only [hH, hNpos])
  have hquad' : |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω| ≤
      max C₁ CE * (N * Real.sqrt (n * L) + N * L) :=
    hquad.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg (mul_nonneg hNpos.le (Real.sqrt_nonneg _)) (mul_nonneg hNpos.le hL0)))
  have hKN1 : (C₀ + 1) * N ≤ (C₀ + 2) * N :=
    mul_le_mul_of_nonneg_right (by linarith only []) hNpos.le
  have hKd : C₀ * N ^ d ≤ (C₀ + 2) * N ^ d := mul_le_mul_of_nonneg_right (by linarith only []) hNd
  have hDcl : cellSet (fun j => X j ω) n ⊆ Metric.closedBall 0 ((C₀ + 2) * N) :=
    hD.trans ((Metric.ball_subset_ball hKN1).trans Metric.ball_subset_closedBall)
  have hrad : |b / N - a| ≤ Ci * Q :=
    hir X ω n b hni h0 hb.le hball hDcl
      hXn (hcard.trans hKd)
      (hEvol.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hNd) hQ0)) hquad'
  have hb_abs : |b - a * N| ≤ Ci * N * Q := by
    rw [show b - a * N = N * (b / N - a) by field_simp, abs_mul, abs_of_pos hNpos]
    calc N * |b / N - a| ≤ N * (Ci * Q) := mul_le_mul_of_nonneg_left hrad hNpos.le
      _ = Ci * N * Q := by ring
  have hC1 : Ci * cQ / a ≤ max (max (Ci * cQ / a) (Cv * cQ)) (Cp * cQ ^ ((1 : ℝ) / d) / a) :=
    le_max_of_le_left (le_max_left _ _)
  have hC2 : Cv * cQ ≤ max (max (Ci * cQ / a) (Cv * cQ)) (Cp * cQ ^ ((1 : ℝ) / d) / a) :=
    le_max_of_le_left (le_max_right _ _)
  have hC3 : Cp * cQ ^ ((1 : ℝ) / d) / a ≤
      max (max (Ci * cQ / a) (Cv * cQ)) (Cp * cQ ^ ((1 : ℝ) / d) / a) := le_max_right _ _
  refine ⟨?_, ?_, ?_⟩
  · -- (i)
    show |b - r| ≤ _ * r * q
    rw [hr]
    calc |b - a * N| ≤ Ci * N * Q := hb_abs
      _ ≤ Ci * N * (cQ * q) := mul_le_mul_of_nonneg_left hQq (by positivity)
      _ = Ci * cQ / a * (a * N) * q := by field_simp
      _ ≤ _ * (a * N) * q := by gcongr
  · -- (ii)
    have hb_r : |b / r - 1| ≤ max C₄ (Ci / a) * Q := by
      rw [hr, show b / (a * N) - 1 = (b / N - a) / a by field_simp, abs_div, abs_of_pos ha]
      calc |b / N - a| / a ≤ (Ci * Q) / a := div_le_div_of_nonneg_right hrad ha.le
        _ = (Ci / a) * Q := by ring
        _ ≤ max C₄ (Ci / a) * Q := mul_le_mul_of_nonneg_right (le_max_right _ _) hQ0
    have hEr : (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal ≤
        max C₄ (Ci / a) * r ^ d * Q := by
      calc (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal ≤ CE * N ^ d * Q :=
            hEvol
        _ = (CE / a ^ d) * (a * N) ^ d * Q := by
            rw [mul_pow]; field_simp
        _ ≤ max C₄ (Ci / a) * r ^ d * Q := by
            rw [hr]
            have h1 : CE / a ^ d ≤ max C₄ (Ci / a) :=
              (le_max_right _ _).trans (le_max_left _ _)
            gcongr
    have hv := hvol (cellSet (fun j => X j ω) n) b r Q hDmeas hDfin hb.le hrpos hQ0 hQ1 hball
      hEr hb_r
    refine (le_trans le_self_add hv).trans (ENNReal.ofReal_le_ofReal ?_)
    calc Cv * Q ≤ Cv * (cQ * q) := mul_le_mul_of_nonneg_left hQq hCv.le
      _ = Cv * cQ * q := by ring
      _ ≤ _ * q := mul_le_mul_of_nonneg_right hC2 hq0
  · -- (iii)
    intro y
    have hK'1 : (a + C₀ + 3) * N ≤ N * N := mul_le_mul_of_nonneg_right hK'N hNpos.le
    have hNN : N * N ≤ (n : ℝ) := by rw [← sq]; exact hN2
    have hK'n : (a + C₀ + 3) * N ≤ 2 * n := by linarith only [hK'1, hNN, hn1]
    have hKm : (a + C₀ + 3 - 1) * N ≥ (C₀ + 1) * N :=
      mul_le_mul_of_nonneg_right (by linarith only [ha]) hNpos.le
    have hDsub' : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((a + C₀ + 3 - 1) * N) :=
      hD.trans (Metric.ball_subset_ball hKm)
    have hCE2 : CE ≤ max C₂ Ci :=
      le_max_of_le_left ((le_max_right _ _).trans (le_max_left _ _))
    have hEvol' : (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal ≤
        max C₂ Ci * N ^ d * Q :=
      hEvol.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCE2 hNd) hQ0)
    have hbnd : |b - a * N| ≤ max C₂ Ci * N * Q :=
      hb_abs.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hNpos.le) hQ0)
    have herr := error_le_scale hd hM0 hC₀.le hL1 hL3 hM
    have hC₂a : 2 * C₁ * (Real.sqrt C₀ + 1) ≤ max C₂ Ci :=
      le_max_of_le_left ((le_max_left _ _).trans (le_max_left _ _))
    have hδ : C₁ * (if d = 2 then Real.sqrt (maxLocalTime (fun j => X j ω) n : ℝ) * L + L
          else Real.sqrt ((maxLocalTime (fun j => X j ω) n : ℝ) * L) + L) ≤
        max C₂ Ci * N * Q ^ ((1 : ℝ) / d) := by
      calc _ ≤ C₁ * (2 * (Real.sqrt C₀ + 1) * (N * Q ^ ((1 : ℝ) / d))) :=
            mul_le_mul_of_nonneg_left herr hC₁.le
        _ = (2 * C₁ * (Real.sqrt C₀ + 1)) * (N * Q ^ ((1 : ℝ) / d)) := by ring
        _ ≤ max C₂ Ci * (N * Q ^ ((1 : ℝ) / d)) :=
            mul_le_mul_of_nonneg_right hC₂a
              (mul_nonneg hNpos.le (Real.rpow_nonneg hQ0 _))
        _ = max C₂ Ci * N * Q ^ ((1 : ℝ) / d) := by ring
    have hall : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ < (a + C₀ + 3) * N →
        |cellLocalTime (fun j => X j ω) n y - potential d ε (cellSet (fun j => X j ω) n) y| ≤
          C₁ * (if d = 2 then Real.sqrt (maxLocalTime (fun j => X j ω) n : ℝ) * L + L
            else Real.sqrt ((maxLocalTime (fun j => X j ω) n : ℝ) * L) + L) :=
      fun y hy => hglob y (by linarith only [hy, hK'n])
    have hprofile := hprof (fun j => X j ω) n b _ N Q hNpos hQ0 hQ1 hb hball hDsub' hbnd hEvol'
      hδ hall y
    rw [hr]
    calc _ ≤ Cp * (N * Q ^ ((1 : ℝ) / d)) := hprofile
      _ ≤ Cp * (N * (cQ * q) ^ ((1 : ℝ) / d)) := by
          have h1 : Q ^ ((1 : ℝ) / d) ≤ (cQ * q) ^ ((1 : ℝ) / d) :=
            Real.rpow_le_rpow hQ0 hQq (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hNpos.le) hCp.le
      _ = Cp * cQ ^ ((1 : ℝ) / d) / a * (a * N) * q ^ ((1 : ℝ) / d) := by
          rw [Real.mul_rpow hcQpos.le hq0]
          field_simp
      _ ≤ _ * (a * N) * q ^ ((1 : ℝ) / d) := by
          have hq1 : 0 ≤ q ^ ((1 : ℝ) / d) := Real.rpow_nonneg hq0 _
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC3 (by positivity)) hq1


end InnerPort

section InnerAdapter

open Finset CERW.Support.Drift CERW.Support.Law

/-- The Euclidean norm is a norm. -/
theorem isNorm_euclidean : IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) :=
  ⟨norm_add_le, fun t x => by simp only [norm_smul, Real.norm_eq_abs],
    fun _ hx => norm_eq_zero.mp hx⟩

private theorem toSpace_ne_zero' {x : Site d} (hx : x ≠ 0) : toSpace x ≠ 0 := by
  intro h
  apply hx
  funext i
  have := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
  simpa [toSpace_apply] using this

/-- The only subgradient of the Euclidean norm at a nonzero point is its direction `v/|v|`. -/
theorem eq_unitDir_of_isSubgradient {x ξ : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0)
    (h : IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) x ξ) : ξ = unitDir x := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hle : ∀ w, inner ℝ ξ w ≤ ‖w‖ := by
    intro w
    have h1 := h (x + w)
    have h2 : inner ℝ ξ (x + w - x) = inner ℝ ξ w := by rw [add_sub_cancel_left]
    simp only [h2] at h1
    linarith [norm_add_le x w]
  have hξ1 : ‖ξ‖ ≤ 1 := by
    have h1 := hle ξ
    rw [real_inner_self_eq_norm_sq] at h1
    by_contra hcon
    have hcon := not_le.mp hcon
    nlinarith [norm_nonneg ξ]
  have hxξ : inner ℝ ξ x = ‖x‖ := by
    have h1 := h 0
    have h2 := h (x + x)
    simp only [zero_sub, inner_neg_right, norm_zero] at h1
    have h3 : inner ℝ ξ (x + x - x) = inner ℝ ξ x := by
      rw [add_sub_cancel_left]
    simp only [h3] at h2
    linarith [norm_add_le x x]
  have hu1 : inner ℝ ξ (unitDir x) = 1 := by
    rw [unitDir, real_inner_smul_right, hxξ, inv_mul_cancel₀ hxpos.ne']
  have hun : ‖unitDir x‖ = 1 := by
    rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne']
  have hsq : ‖ξ - unitDir x‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, hu1, hun]
    nlinarith [norm_nonneg ξ]
  have h0 : ‖ξ - unitDir x‖ = 0 := by nlinarith [norm_nonneg (ξ - unitDir x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- A field of subgradients of the Euclidean norm vanishing at the origin is `x ↦ u_x`. -/
theorem field_eq_unitDir {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 →
      IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x))
    (hξ0 : ξ 0 = 0) : ξ = fun z => unitDir (toSpace z) := by
  funext z
  by_cases hz : z = 0
  · subst hz
    have h0 : toSpace (0 : Site d) = 0 := by
      ext i
      simp
    rw [hξ0, h0, unitDir_zero]
  · exact eq_unitDir_of_isSubgradient (toSpace_ne_zero' hz) (hξ z hz)

/-- A unit step changes the squared norm by `2 ⟪x, e⟫ + 1`. -/
private theorem euclidNorm_sq_add_unit' (x e : Site d) (he : e ∈ unitSteps d) :
    euclidNorm (x + e) ^ 2 = euclidNorm x ^ 2 + 2 * inner ℝ (toSpace x) (toSpace e) + 1 := by
  have hto : toSpace (x + e) = toSpace x + toSpace e := by
    apply PiLp.ext
    intro i
    simp [toSpace_apply, Pi.add_apply, Int.cast_add]
  have he1 : euclidNorm e = 1 := CERW.Support.Law.euclidNorm_of_mem_unitSteps he
  have hnorm : ‖toSpace e‖ = 1 := by rw [norm_toSpace, he1]
  rw [← norm_toSpace (x + e), ← norm_toSpace x, hto, norm_add_sq_real, hnorm]
  ring

/-- The quadratic martingale of the source is the Dynkin martingale of `|x|²`, along a path whose
steps are unit steps, in a field with `ξ 0 = 0`. -/
private theorem quadraticMartingale_eq_driftDynkin' (hd : 1 ≤ d) {Ω : Type*} (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (hξ0 : ξ 0 = 0) (X : ℕ → Ω → Site d) (ω : Ω)
    (hsteps : ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d) (t : ℕ) :
    quadraticMartingale d ε ξ (fun j => X j ω) t =
      driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X t ω := by
  induction t with
  | zero => simp [quadraticMartingale]
  | succ t ih =>
    have hq : quadraticMartingale d ε ξ (fun j => X j ω) (t + 1) =
        quadraticMartingale d ε ξ (fun j => X j ω) t +
          2 * inner ℝ (toSpace (X t ω))
            (toSpace (X (t + 1) ω) - toSpace (X t ω) +
              ε • (if X t ω ∉ departureRange (fun j => X j ω) t then ξ (X t ω) else 0)) := by
      simp only [quadraticMartingale, sum_range_succ]
    set Iv : EuclideanSpace ℝ (Fin d) :=
      if X t ω ∉ departureRange (fun j => X j ω) t then ξ (X t ω) else 0 with hIv
    -- the mean of each coordinate of the next step
    have hcoord : ∀ k : Fin d, ∑ e ∈ unitSteps d,
        driftStepProb d ε ξ (fun j => X j ω) t e * ((e k : ℤ) : ℝ) = -(ε * Iv.ofLp k) := by
      intro k
      have h1 := driftNextMean_coord hd ε ξ (fun j => X j ω) t k
      have h2 : driftNextMean ε ξ (fun z : Site d => ((z k : ℤ) : ℝ)) (fun j => X j ω) t =
          ((X t ω k : ℤ) : ℝ) + ∑ e ∈ unitSteps d,
            driftStepProb d ε ξ (fun j => X j ω) t e * ((e k : ℤ) : ℝ) := by
        simp only [driftNextMean, Pi.add_apply, Int.cast_add, mul_add, sum_add_distrib]
        rw [← sum_mul, sum_driftStepProb hd ε ξ _ t, one_mul]
      have hterm : (if X t ω ≠ 0 ∧ X t ω ∉ (range t).image (fun j => X j ω) then
          ε * ξ (X t ω) k else 0) = ε * Iv.ofLp k := by
        by_cases h0 : X t ω = 0
        · simp [h0, hξ0, hIv, departureRange]
        · by_cases hdep : X t ω ∈ (range t).image (fun i => X i ω)
          · simp [hIv, departureRange, hdep]
          · simp [hIv, departureRange, hdep, h0]
      rw [h2, hterm] at h1
      linarith
    have hmean : driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2) (fun j => X j ω) t =
        euclidNorm (X t ω) ^ 2 + 1 - 2 * ε * inner ℝ (toSpace (X t ω)) Iv := by
      have hsum : ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
          euclidNorm (X t ω + e) ^ 2 =
          ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
            ((euclidNorm (X t ω) ^ 2 + 1) + 2 * ∑ k : Fin d,
              ((X t ω k : ℤ) : ℝ) * ((e k : ℤ) : ℝ)) := by
        refine sum_congr rfl fun e he => ?_
        rw [euclidNorm_sq_add_unit' _ _ he]
        have : inner ℝ (toSpace (X t ω)) (toSpace e) =
            ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * ((e k : ℤ) : ℝ) := by
          simp only [PiLp.inner_apply, toSpace_apply, RCLike.inner_apply, conj_trivial]
          exact sum_congr rfl fun k _ => mul_comm _ _
        rw [this]
        ring
      have hcomm : ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
          (∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * ((e k : ℤ) : ℝ)) =
          ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * (-(ε * Iv.ofLp k)) := by
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [← hcoord k, mul_sum]
        refine sum_congr rfl fun e _ => ?_
        ring
      calc driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2) (fun j => X j ω) t
          = ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
              euclidNorm (X t ω + e) ^ 2 := rfl
        _ = (euclidNorm (X t ω) ^ 2 + 1) *
              ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e +
            2 * ∑ e ∈ unitSteps d, driftStepProb d ε ξ (fun j => X j ω) t e *
              (∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * ((e k : ℤ) : ℝ)) := by
            rw [hsum, mul_sum, mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun e _ => ?_
            ring
        _ = euclidNorm (X t ω) ^ 2 + 1 - 2 * ε * inner ℝ (toSpace (X t ω)) Iv := by
            have hin : inner ℝ (toSpace (X t ω)) Iv =
                ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * Iv.ofLp k := by
              simp only [PiLp.inner_apply, toSpace_apply, RCLike.inner_apply, conj_trivial]
              exact sum_congr rfl fun k _ => mul_comm _ _
            have hs : ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * (-(ε * Iv.ofLp k)) =
                -(ε * ∑ k : Fin d, ((X t ω k : ℤ) : ℝ) * Iv.ofLp k) := by
              rw [mul_sum, ← sum_neg_distrib]
              exact sum_congr rfl fun k _ => by ring
            rw [sum_driftStepProb hd ε ξ _ t, hcomm, hs, hin]
            ring
    have hD : driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (t + 1) ω =
        driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X t ω +
          (euclidNorm (X (t + 1) ω) ^ 2 -
            driftNextMean ε ξ (fun z : Site d => euclidNorm z ^ 2) (fun j => X j ω) t) := by
      have := driftDynkin_succ_sub ε ξ (fun z : Site d => euclidNorm z ^ 2) X t ω
      linarith
    have he := hsteps t
    have hX' : X (t + 1) ω = X t ω + (X (t + 1) ω - X t ω) := by abel
    have hto : toSpace (X (t + 1) ω) - toSpace (X t ω) = toSpace (X (t + 1) ω - X t ω) := by
      apply PiLp.ext
      intro i
      simp [toSpace_apply, Int.cast_sub]
    have hsq := euclidNorm_sq_add_unit' (X t ω) (X (t + 1) ω - X t ω) he
    rw [← hX'] at hsq
    rw [hq, ih, hD, hmean, hto, hsq, inner_add_right, real_inner_smul_right]
    ring

/-- For a legal path, the Dynkin martingale of `|x|²` of the Euclidean walk is the quadratic
martingale `𝒬` of the source with the field `x ↦ u_x`. -/
theorem dynkin_sq_eq_quadraticMartingale (hd : 1 ≤ d) (ε : ℝ) (x : ℕ → Site d)
    (hx : PathTyping d x) (n : ℕ) :
    dynkin ε (fun z : Site d => euclidNorm z ^ 2) (fun j (_ : PUnit.{1}) => x j) n PUnit.unit =
      quadraticMartingale d ε (fun z => unitDir (toSpace z)) x n := by
  have h1 := dynkinMart_stepProb_eq_dynkin hd ε (fun z : Site d => euclidNorm z ^ 2)
    (fun j (_ : PUnit.{1}) => x j) n PUnit.unit
  have hsp : stepProb d ε = driftStepProb d ε (fun z => unitDir (toSpace z)) := by
    funext y m e
    exact stepProb_eq_driftStepProb ε y m e
  rw [← h1, hsp]
  refine (dynkinMart_driftStepProb_eq_driftDynkin hd ε _ _ (fun j (_ : PUnit.{1}) => x j) n
    PUnit.unit).trans ?_
  have h0 : (unitDir (toSpace (0 : Site d)) : EuclideanSpace ℝ (Fin d)) = 0 := by
    have : toSpace (0 : Site d) = 0 := by
      ext i
      simp
    rw [this, unitDir_zero]
  exact (quadraticMartingale_eq_driftDynkin' hd ε (fun z => unitDir (toSpace z)) h0
    (fun j (_ : PUnit.{1}) => x j) PUnit.unit (fun j => hx.2 j) n).symm

end InnerAdapter

/-- The conclusion of `lem:contact` for a path `x` at time `n`: at every contact point `y₀`
(`Ψ(y₀)` is the infimum of `Ψ` over the complement of the cell set `D_n`, and `y₀` is in the
closure of that complement) the potential `U_{D_n}(y₀)` is at most `C r_n q_n`. -/
def ContactBound (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε C : ℝ) (x : ℕ → Site d)
    (n : ℕ) : Prop :=
  ∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ x n →
    y₀ ∈ closure (cellSet x n)ᶜ →
      normPotential d ε Ψ (cellSet x n) y₀ ≤ C * scale d Ψ ε n * contactRate d Ψ ε n


/-! ## The inner radius and the local-time profile on the seven estimates -/

section InnerLocalization

open scoped symmDiff Pointwise

/-- The conclusions of `prop:inner` for a path `x` at time `n`, for the Euclidean norm: the inner
radius `R_in(n)` is within `C r_n q_n` of `r_n`, the rescaled cell set `r_n⁻¹ D_n` differs from the
unit ball by a set of volume at most `C q_n`, and the cell local time is within `C r_n q_n^{1/d}`
of the cone `2dε (r_n - |y|)_+` at every point of `ℝ^d`. -/
def InnerConclusion (d : ℕ) (ε C : ℝ) (x : ℕ → Site d) (n : ℕ) : Prop :=
  |normInnerRadius (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) x n -
      scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n| ≤
    C * scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
      contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n ∧
  volume (((scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n)⁻¹ • cellSet x n) ∆
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
    ENNReal.ofReal (C * contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n) ∧
  ∀ y : EuclideanSpace ℝ (Fin d),
    |cellLocalTime x n y - 2 * d * ε *
        max (scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n - ‖y‖) 0| ≤
      C * scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n *
        contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n ^ ((1 : ℝ) / d)

/-- **The inner radius, the volume and the local times on the seven estimates.** For the
Euclidean norm in dimension `d ≥ 2` and `ε > 0`: given constants `K` of the event and `C_c > 0`,
there are `C` and `n₀` such that every legal
path at a time `n ≥ n₀` that satisfies the seven estimates of the event (for any projection `P`)
and the contact estimate with constant `C_c` has the three conclusions of `prop:inner`. Only the
coarse, local and quadratic estimates and the contact estimate are consumed. -/
theorem inner_of_estimates7 (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (K : EventConstants) {Cc : ℝ}
    (hCc : 0 < Cc) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ),
        n₀ ≤ n → PathTyping d x →
        Estimates7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K P x n →
        ContactBound d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε Cc x n →
        InnerConclusion d ε C x n := by
  have hd1 : 1 ≤ d := by omega
  have hΨ : IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) := isNorm_euclidean
  have hpball : ∀ ρ : ℝ, 0 < ρ → ∀ y : EuclideanSpace ℝ (Fin d),
      potential d ε (Metric.ball 0 ρ) y = 2 * d * ε * max (ρ - ‖y‖) 0 := by
    intro ρ hρ y
    have h := CERW.Support.Norm.norm_ball_potential hd hΨ ε hρ y
    have hset : {v : EuclideanSpace ℝ (Fin d) | ‖v‖ < ρ} = Metric.ball 0 ρ := by
      ext v
      simp
    rw [hset, normPotential_norm_eq hd1] at h
    exact h
  obtain ⟨Cg, hCg, hg⟩ := CERW.Support.Norm.norm_potential_geometry hd
    (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) hΨ
  have hpbound : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |potential d ε D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d) := by
    intro D hDm hDb y
    obtain ⟨h1, -, -⟩ := hg ε hε D hDm hDb
    have h := h1 y
    rw [normPotential_norm_eq hd1] at h
    exact h
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hbase : 0 < ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hbase _
  set Cco : ℝ := max K.C_co 0 with hCco_def
  set Cl : ℝ := max K.C_loc 0 with hCl_def
  set Cq : ℝ := max K.C_quad 0 with hCq_def
  have hCco : 0 ≤ Cco := le_max_right _ _
  have hCl0 : 0 ≤ Cl := le_max_right _ _
  have hCq : 0 ≤ Cq := le_max_right _ _
  set C₀ : ℝ := Cco * (a ^ d + a) + 1 with hC₀_def
  have hC₀ : 0 < C₀ := by
    have : 0 ≤ Cco * (a ^ d + a) := mul_nonneg hCco (by positivity)
    linarith
  set C₁ : ℝ := Cl + Cq * (C₀ + 1) + 1 with hC₁_def
  have hC₁ : 0 < C₁ := by
    have : 0 ≤ Cq * (C₀ + 1) := mul_nonneg hCq (by linarith)
    linarith
  obtain ⟨Cin, hCin, nin, hcore⟩ := inner_core_inputs.{0} hd hε hC₀ hC₁ hCc hCg.le hpball hpbound
  refine ⟨Cin, hCin, max nin 2, fun ξ hξ hξ0 P x n hn hlegal hE hcont => ?_⟩
  have hnin : nin ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN_def
  have hN1 : 1 ≤ N := Real.one_le_rpow hn1R (by positivity)
  set L : ℝ := Real.log (n + 2) with hL_def
  have hlogL : Real.log n ≤ L := Real.log_le_log hnpos (by linarith)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
  have hL0 : 0 ≤ L := hlog0.trans hlogL
  -- the scale and the rate in the notation of the core
  have hr : scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n =
      ((d + 1) * n / (2 * d * ε * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal))
        ^ ((1 : ℝ) / (d + 1)) := by
    unfold scale
    rw [normBallVolume_norm]
    rfl
  have hscale : scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = a * N := by
    unfold scale
    rw [normBallVolume_norm, ha_def, hN_def,
      show ((d : ℝ) + 1) * n / (2 * d * ε * unitBallVolume d) =
        (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) * n by ring]
    exact Real.mul_rpow hbase.le (Nat.cast_nonneg n)
  have hq : contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n =
      (if d = 2 then Real.sqrt (Real.log n / ((d + 1) * n / (2 * d * ε *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
            ((1 : ℝ) / (d + 1)))
        else Real.log n / ((d + 1) * n / (2 * d * ε *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
            ((1 : ℝ) / (d + 1))) := by
    unfold contactRate
    rw [hr]
  obtain ⟨hcoarse, hlocal, -, -, hquad, -, -⟩ := hE
  obtain ⟨-, hcard, -, hM, -, hH⟩ := hcoarse
  obtain ⟨-, -, hglob⟩ := hlocal
  rw [hscale] at hcard hM hH
  have hNd : 0 ≤ N ^ d := pow_nonneg (by linarith) d
  have haN : 0 ≤ a * N := mul_nonneg ha.le (by linarith)
  have had : 0 ≤ a ^ d := by positivity
  have hcard' : ((departureRange x n).card : ℝ) ≤ C₀ * N ^ d := by
    refine hcard.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left K.C_co 0)
      (pow_nonneg haN d)).trans ?_
    rw [mul_pow, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hNd
    have : Cco * a ^ d ≤ Cco * (a ^ d + a) :=
      mul_le_mul_of_nonneg_left (by linarith) hCco
    linarith
  have hM' : (maxLocalTime x n : ℝ) ≤ C₀ * N := by
    refine hM.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left K.C_co 0) haN).trans ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    have : Cco * a ≤ Cco * (a ^ d + a) :=
      mul_le_mul_of_nonneg_left (by linarith) hCco
    linarith
  have hH' : maxRadius x n ≤ C₀ * N := by
    refine hH.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left K.C_co 0) haN).trans ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    have : Cco * a ≤ Cco * (a ^ d + a) :=
      mul_le_mul_of_nonneg_left (by linarith) hCco
    linarith
  have hM0 : (0 : ℝ) ≤ (maxLocalTime x n : ℝ) := Nat.cast_nonneg _
  have hglob' : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - potential d ε (cellSet x n) y| ≤
        C₁ * (if d = 2 then Real.sqrt (maxLocalTime x n : ℝ) * L + L
          else Real.sqrt ((maxLocalTime x n : ℝ) * L) + L) := by
    intro y hy
    have h := hglob y hy
    rw [normPotential_norm_eq hd1] at h
    refine h.trans ?_
    have hCl : Cl ≤ C₁ := by
      have : 0 ≤ Cq * (C₀ + 1) := mul_nonneg hCq (by linarith)
      linarith
    have hKl : K.C_loc ≤ Cl := le_max_left _ _
    by_cases h2 : d = 2
    · simp only [h2, if_true] at h ⊢
      have hs : 0 ≤ Real.sqrt (maxLocalTime x n : ℝ) := Real.sqrt_nonneg _
      calc K.C_loc * Real.log n + K.C_loc * (Real.sqrt (maxLocalTime x n : ℝ) * Real.log n)
          ≤ Cl * L + Cl * (Real.sqrt (maxLocalTime x n : ℝ) * L) := by
            have e1 : K.C_loc * Real.log n ≤ Cl * L :=
              mul_le_mul hKl hlogL hlog0 hCl0
            have e2 : K.C_loc * (Real.sqrt (maxLocalTime x n : ℝ) * Real.log n) ≤
                Cl * (Real.sqrt (maxLocalTime x n : ℝ) * L) :=
              mul_le_mul hKl (mul_le_mul_of_nonneg_left hlogL hs) (by positivity) hCl0
            linarith
        _ = Cl * (Real.sqrt (maxLocalTime x n : ℝ) * L + L) := by ring
        _ ≤ C₁ * (Real.sqrt (maxLocalTime x n : ℝ) * L + L) :=
            mul_le_mul_of_nonneg_right hCl (by positivity)
    · simp only [h2, if_false] at h ⊢
      calc K.C_loc * Real.log n + K.C_loc * Real.sqrt ((maxLocalTime x n : ℝ) * Real.log n)
          ≤ Cl * L + Cl * Real.sqrt ((maxLocalTime x n : ℝ) * L) := by
            have e1 : K.C_loc * Real.log n ≤ Cl * L :=
              mul_le_mul hKl hlogL hlog0 hCl0
            have e2 : K.C_loc * Real.sqrt ((maxLocalTime x n : ℝ) * Real.log n) ≤
                Cl * Real.sqrt ((maxLocalTime x n : ℝ) * L) :=
              mul_le_mul hKl (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlogL hM0))
                (Real.sqrt_nonneg _) hCl0
            linarith
        _ = Cl * (Real.sqrt ((maxLocalTime x n : ℝ) * L) + L) := by ring
        _ ≤ C₁ * (Real.sqrt ((maxLocalTime x n : ℝ) * L) + L) :=
            mul_le_mul_of_nonneg_right hCl (by positivity)
  have hξE := field_eq_unitDir hξ hξ0
  have hquad' : |CERW.Support.Law.dynkin ε (fun z : Site d => euclidNorm z ^ 2)
      (fun j (_ : PUnit.{1}) => x j) n PUnit.unit| ≤ C₁ * (N * Real.sqrt (n * L) + N * L) := by
    rw [dynkin_sq_eq_quadraticMartingale hd1 ε x hlegal n, ← hξE]
    refine hquad.trans ?_
    have hsq : Real.sqrt ((n : ℝ) * Real.log n) ≤ Real.sqrt ((n : ℝ) * L) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlogL hnpos.le)
    have hH1 : maxRadius x n + 1 ≤ (C₀ + 1) * N := by nlinarith
    have hsqrt0 : 0 ≤ Real.sqrt ((n : ℝ) * L) := Real.sqrt_nonneg _
    have hNL : 0 ≤ N * L := mul_nonneg (by linarith) hL0
    have hKq : K.C_quad ≤ Cq := le_max_left _ _
    have hH0 : 0 ≤ maxRadius x n + 1 := by
      have : 0 ≤ maxRadius x n :=
        (LatticeProb.euclidNorm_nonneg _).trans (euclidNorm_le_maxRadius x (Nat.zero_le n))
      linarith
    have hsq0 : 0 ≤ Real.sqrt ((n : ℝ) * Real.log n) := Real.sqrt_nonneg _
    calc K.C_quad * (maxRadius x n + 1) * Real.sqrt ((n : ℝ) * Real.log n)
        ≤ Cq * (maxRadius x n + 1) * Real.sqrt ((n : ℝ) * Real.log n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKq hH0) hsq0
      _ ≤ Cq * ((C₀ + 1) * N) * Real.sqrt ((n : ℝ) * L) := by
          gcongr
      _ = Cq * (C₀ + 1) * (N * Real.sqrt (n * L)) := by ring
      _ ≤ C₁ * (N * Real.sqrt (n * L)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by linarith) hsqrt0)
          linarith
      _ ≤ C₁ * (N * Real.sqrt (n * L) + N * L) := by
          refine mul_le_mul_of_nonneg_left ?_ hC₁.le
          linarith
  have hcont' : ∀ y₀ : EuclideanSpace ℝ (Fin d),
      ‖y₀‖ = innerRadius (fun j => x j) n → y₀ ∈ closure (cellSet (fun j => x j) n)ᶜ →
        potential d ε (cellSet (fun j => x j) n) y₀ ≤
          Cc * ((d + 1) * n / (2 * d * ε *
              (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
            ((1 : ℝ) / (d + 1)) *
            (if d = 2 then Real.sqrt (Real.log n / ((d + 1) * n / (2 * d * ε *
                (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
                  ((1 : ℝ) / (d + 1)))
              else Real.log n / ((d + 1) * n / (2 * d * ε *
                (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^
                  ((1 : ℝ) / (d + 1))) := by
    intro y₀ h1 h2
    have h := hcont y₀ h1 h2
    rw [normPotential_norm_eq hd1, hq, hr] at h
    exact h
  have hmain := hcore (fun j (_ : PUnit.{1}) => x j) PUnit.unit n hnin hlegal.1 hcard' hM' hH'
    hglob' hquad' hcont'
  unfold InnerConclusion
  rw [hq, hr]
  exact hmain

end InnerLocalization

/-! ## The closed localization -/

/-- The localization for the walk itself: the complement of `E7` has probability at most
`C n^{-p}`, and at every legal sample point of `E7` the contact estimate holds. The producers of
Proposition 4.1, Lemma 3.1, the lattice-kernel martingales, the norm-ball potential and the
halfspace martingales are the proved ones. -/
private theorem localization_core {d : ℕ} (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ (K : EventConstants) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        μ (E7 Ψ ε ξ K X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
        ∀ ω ∈ E7 Ψ ε ξ K X n, ω ∈ legalSet X →
          ContactBound d Ψ ε C (fun j => X j ω) n := by
  obtain ⟨K, C, hC, n₀, hn₀, hmain⟩ := contact_on_section5Event.{u}
    (CERW.Support.Norm.norm_coarse_bounds_of
      (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds)
      CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing)
    (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds)
    (fun {_} hd {_} hΨ {_} hε hell {_} hp =>
      CERW.Support.Norm.exists_linear_martingale_bound hd hΨ hε hell hp)
    @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential
    hd hΨ hε hell hp
  refine ⟨K, C, hC, n₀, hn₀, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_⟩
  obtain ⟨hprob, hcontact⟩ := hmain ξ hξ hξ0 μ X hX n hn (projectionAt Ψ ε n)
  refine ⟨le_trans (measure_mono ?_) hprob, fun ω hE hL y₀ h1 h2 => ?_⟩
  · intro ω hω h5
    rw [section5Event_projectionAt] at h5
    exact hω h5.2
  · have h5 : ω ∈ Section5Event Ψ ε ξ K (projectionAt Ψ ε n) X n := by
      rw [section5Event_projectionAt]
      exact ⟨hL, hE⟩
    exact hcontact ω h5 y₀ h1 h2

/-- **The closed localization of the contact estimate on the literal event of Section 5.1.**
Let `Ψ` be a norm in dimension `d ≥ 2`, `ε > 0` with `ε Ψ(e_i) < 1/d`, and `p > 0`. There are
constants `K` of the event, `C` and `n₀`, depending only on `d`, `Ψ`, `ε`, `p`, such that for every
field `ξ` of subgradients with `ξ 0 = 0`, every probability space carrying a walk `X` with drift
field `ξ`, and every `n ≥ n₀`:

* the complement of the literal event `E7` has probability at most `C n^{-p}`;
* at every legal sample point of `E7` the contact estimate holds, and the legal sample points have
  probability one;
* the legal carrier of `X` is a walk with the same drift field, equal to `X` almost surely, legal
  at every sample point; the complement of its `E7` has probability at most `C n^{-p}`, and at
  every sample point of its `E7` the contact estimate holds.

No producer of Proposition 4.1, Lemma 3.1, `eq:vector`, `eq:localmart`, `eq:quadratic-coarse`,
`eq:linear-mart`, the potential of a norm ball or the geometry of the potential is assumed. -/
theorem section5_localization {d : ℕ} (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ (K : EventConstants) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        (μ (E7 Ψ ε ξ K X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ E7 Ψ ε ξ K X n, ω ∈ legalSet X → ContactBound d Ψ ε C (fun j => X j ω) n) ∧
        μ (legalSet X)ᶜ = 0 ∧
        IsDriftCERW μ ε ξ (legalCarrier (by omega : 1 ≤ d) X) ∧
        (∀ᵐ ω ∂μ, ∀ j, legalCarrier (by omega : 1 ≤ d) X j ω = X j ω) ∧
        (∀ ω, PathTyping d (fun j => legalCarrier (by omega : 1 ≤ d) X j ω)) ∧
        μ (E7 Ψ ε ξ K (legalCarrier (by omega : 1 ≤ d) X) n)ᶜ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
        ∀ ω ∈ E7 Ψ ε ξ K (legalCarrier (by omega : 1 ≤ d) X) n,
          ContactBound d Ψ ε C (fun j => legalCarrier (by omega : 1 ≤ d) X j ω) n := by
  obtain ⟨K, C, hC, n₀, hn₀, hmain⟩ := localization_core.{u} hd hΨ hε hell hp
  have hd1 : 1 ≤ d := by omega
  refine ⟨K, C, hC, n₀, hn₀, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_⟩
  have hXc := isDriftCERW_legalCarrier hd1 hX
  refine ⟨hmain ξ hξ hξ0 μ X hX n hn, ?_, hXc, legalCarrier_ae_eq hd1 hX,
    legalCarrier_typing hd1 X, (hmain ξ hξ hξ0 μ _ hXc n hn).1, fun ω hω => ?_⟩
  · exact mem_ae_iff.mp (ae_legal_of_isDriftCERW hX)
  · exact (hmain ξ hξ hξ0 μ _ hXc n hn).2 ω hω (legalCarrier_typing hd1 X ω)

/-! ## The inner radius and the local times on the literal event -/

/-- For the Euclidean norm, the contact estimate and the conclusions of `prop:inner` on the legal
sample points of `E7`, with the producers of Proposition 4.1, Lemma 3.1, the lattice-kernel
martingales, the norm-ball potential and the halfspace martingales all proved. -/
private theorem euclid_core {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ (K : EventConstants) (C Cin : ℝ), 0 < C ∧ 0 < Cin ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n)ᶜ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
        ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n, ω ∈ legalSet X →
          ContactBound d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε C (fun j => X j ω) n ∧
          InnerConclusion d ε Cin (fun j => X j ω) n := by
  have hΨ : IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) := isNorm_euclidean
  have hell : ∀ i : Fin d, ε * (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (coordVec i) <
      1 / (d : ℝ) := by
    intro i
    simpa [coordVec] using hεd
  obtain ⟨K, C, hC, n₀, hn₀, hmain⟩ := localization_core.{u} hd hΨ hε hell hp
  obtain ⟨Cin, hCin, nin, hinner⟩ := inner_of_estimates7 hd hε K (Cc := C) hC
  refine ⟨K, C, Cin, hC, hCin, max n₀ nin, le_trans hn₀ (le_max_left _ _),
    fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_⟩
  have hn₀n : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hninn : nin ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hprob, hcontact⟩ := hmain ξ hξ hξ0 μ X hX n hn₀n
  exact ⟨hprob, fun ω hE hL =>
    ⟨hcontact ω hE hL, hinner ξ hξ hξ0 _ (fun j => X j ω) n hninn hL hE (hcontact ω hE hL)⟩⟩

/-- **The localized inner radius and local-time profile for the Euclidean norm.** Let `d ≥ 2` and
`0 < ε < 1/d`, and `p > 0`. There are constants `K` of the event, `C`, `C'` and `n₀`, depending
only on `d`, `ε`, `p`, such that for every field `ξ` of subgradients of the Euclidean norm with
`ξ 0 = 0`, every probability space carrying a walk `X` with drift field `ξ` and every `n ≥ n₀`:

* the complement of the literal event `E7` has probability at most `C n^{-p}`;
* at every legal sample point of `E7` (they have probability one), the contact estimate holds
  with constant `C` and the conclusions of `prop:inner` hold with constant `C'`: the inner radius
  is within `C' r_n q_n` of `r_n`, the volume of the symmetric difference of `r_n⁻¹ D_n` and the
  unit ball is at most `C' q_n`, and the cell local time is within `C' r_n q_n^{1/d}` of
  `2dε (r_n - |y|)_+` at every point `y`;
* the legal carrier of `X` is a walk with the same drift field, equal to `X` almost surely and
  legal at every sample point, and the same two statements hold for the sample points of its `E7`
  with no legality premise. -/
theorem section5_euclid_localization {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ (K : EventConstants) (C Cin : ℝ), 0 < C ∧ 0 < Cin ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        (μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n)ᶜ ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n, ω ∈ legalSet X →
            ContactBound d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε C (fun j => X j ω) n ∧
            InnerConclusion d ε Cin (fun j => X j ω) n) ∧
        μ (legalSet X)ᶜ = 0 ∧
        IsDriftCERW μ ε ξ (legalCarrier (by omega : 1 ≤ d) X) ∧
        (∀ᵐ ω ∂μ, ∀ j, legalCarrier (by omega : 1 ≤ d) X j ω = X j ω) ∧
        (∀ ω, PathTyping d (fun j => legalCarrier (by omega : 1 ≤ d) X j ω)) ∧
        μ (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K
            (legalCarrier (by omega : 1 ≤ d) X) n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
        ∀ ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K
            (legalCarrier (by omega : 1 ≤ d) X) n,
          ContactBound d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε C
            (fun j => legalCarrier (by omega : 1 ≤ d) X j ω) n ∧
          InnerConclusion d ε Cin (fun j => legalCarrier (by omega : 1 ≤ d) X j ω) n := by
  obtain ⟨K, C, Cin, hC, hCin, n₀, hn₀, hmain⟩ := euclid_core.{u} hd hε hεd hp
  have hd1 : 1 ≤ d := by omega
  refine ⟨K, C, Cin, hC, hCin, n₀, hn₀, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_⟩
  have hXc := isDriftCERW_legalCarrier hd1 hX
  refine ⟨hmain ξ hξ hξ0 μ X hX n hn, ?_, hXc, legalCarrier_ae_eq hd1 hX,
    legalCarrier_typing hd1 X, (hmain ξ hξ hξ0 μ _ hXc n hn).1, fun ω hω => ?_⟩
  · exact mem_ae_iff.mp (ae_legal_of_isDriftCERW hX)
  · exact (hmain ξ hξ hξ0 μ _ hXc n hn).2 ω hω (legalCarrier_typing hd1 X ω)

end CERW.Support.Norm.Section5Localization
