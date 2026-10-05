import CERW.Support.Norm.GaugeCoarseVolume
import CERW.Support.Norm.GaugeProjectionEvents
import CERW.Support.Norm.Section5Localization

/-!
# The finite-prefix events of the half-space martingale estimates for the gauge of a convex body

The compensated-path bound `eq:vector` and the half-space martingale bounds `eq:linear-mart`
(Sections 4.2 and 5.1 of the paper) are estimates on the walk up to time `n`: they involve the
positions `X_0, …, X_n` and nothing after time `n`. The path events `CapEvent` and
`ProjectionEvent` of `GaugeCoarseVolume` and `GaugeProjectionEvents` also require that the whole
infinite path starts at the origin and takes unit steps; they serve the deterministic implications
but are not events of the `σ`-algebra `ℱ_n = σ(X_0, …, X_n)`. This module separates the estimates
from the legality of the path.

* `CompensatedBound` and `HalfSpaceBounds` are the two estimates, as properties of a path at time
  `n`. `ProjectionEstimates` (the compensated-path bound and the half-space bounds in the directions
  `projectionDirections K P n`, all sites of Euclidean norm at most `n`),
  `SourceProjectionEstimates` (the same for the sites with `ψ(x) > r`, the pairs `(q, a)` of the
  source) and `CapEstimates` (the radial directions `capDirections ψ n`) are their conjunctions.
  They depend on the path only up to time `n` (`PrefixDetermined`).
* `FiniteProjectionEvent`, `FiniteSourceProjectionEvent` and `FiniteCapEvent` are the sets of sample
  points on which the estimates hold. Each is the preimage of a set of finite paths under the past
  path `(X_0, …, X_n)` (`setOf_eq_preimage_pastPath`), the countable union of the cylinders of those
  finite paths (`setOf_eq_iUnion_cylinders`), hence belongs to `ℱ_n`
  (`measurableSet_setOf_filtration`) and is measurable. No measurability is assumed: the positions
  of an `IsDriftCERW` walk are measurable.
* The path event of the auxiliary modules is the intersection of the legal sample points with the
  finite event (`projectionEvent_set_eq`, `capEvent_set_eq`). Every walk with a drift field is
  almost surely legal, so the two events agree almost surely under `IsDriftCERW`
  (`projectionEvent_ae_eq`, `capEvent_ae_eq`) and their complements have the same probability
  (`measure_finiteProjectionEvent_compl`, `measure_finiteCapEvent_compl`). The failure bounds of the
  auxiliary events therefore hold for the finite events with the same constants, for every `n ≥ 2`
  (`exists_finiteProjectionEvent_failure_bound`, `exists_finiteCapEvent_failure_bound`).
* `nearestMapAt hd hΨ hr` is the nearest-point map onto `{ψ ≤ r}` selected from the existence
  proof `exists_isNearestMap` for a compact convex body `hΨ` with the origin in its interior and a
  radius `hr : 0 ≤ r`: the carrier is the set of proofs of these hypotheses, with no value outside
  it. `nearestMapAt_spec` is its characterization and `nearestMapAt_eq_of` its uniqueness.
  `projectionAtScale hd hΨ hε n` is the map `Π_n` onto `{ψ ≤ r_n}` at the deterministic radius
  `r_n`, for every `n`. `gauge_finite_projection_event` combines the events `E_n ∈ ℱ_n` at `Π_n`
  with the failure bound for every `n ≥ 2`.
* The deterministic consumers are `ProjectionEstimates.compensated`,
  `SourceProjectionEstimates.compensated` and `SourceProjectionEstimates.martingale`, which give
  the hypotheses of the rates theorem `GaugeContactShape.Rates.ShapeRatesOfEvents` from a legal path
  in the finite event, and `roughOuter_of_capEstimates` for the radial event.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeFiniteEvents

open CERW CERW.Support.Law CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugeCoarseVolume CERW.Support.Norm.GaugeProjectionEvents
open CERW.Support.Norm.ContactEvent (PathTyping)
open CERW.Support.Norm.Section5Localization (legalSet ae_legal_of_isDriftCERW)

variable {d : ℕ}

/-! ## The estimates depend only on the path up to time `n` -/

section Prefix

open Finset

private theorem departureRange_congr {x y : ℕ → Site d} {n m : ℕ} (h : ∀ j ≤ n, x j = y j)
    (hm : m ≤ n + 1) : departureRange x m = departureRange y m :=
  Finset.image_congr fun j hj => h j (by have := mem_range.mp hj; omega)

private theorem localTime_congr {x y : ℕ → Site d} {n m : ℕ} (h : ∀ j ≤ n, x j = y j)
    (hm : m ≤ n + 1) : localTime x m = localTime y m := by
  funext z
  unfold localTime
  congr 1
  exact Finset.filter_congr fun j hj => by rw [h j (by have := mem_range.mp hj; omega)]

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

/-- **The compensated-path bound** `eq:vector` at time `n` with constant `C`:
`|Z_t - Z_s| ≤ C √((t - s) log n)` for `0 ≤ s < t ≤ n`. -/
def CompensatedBound (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ) (n : ℕ)
    (x : ℕ → Site d) : Prop :=
  ∀ s t : ℕ, s < t → t ≤ n →
    ‖VectorBound.driftCompensated ε ξ x t - VectorBound.driftCompensated ε ξ x s‖ ≤
      C * Real.sqrt (((t : ℝ) - s) * Real.log n)

/-- **The half-space martingale bounds** `eq:linear-mart` at time `n` with constant `C`, for every
direction `q` of the finite set `Q` and every level `kΛ_ψ`, `k ≤ n`:
`|M^{q,kΛ}_n| ≤ C (√(log n Σ_{x: q·x > kΛ - Λ} ℓ_n(x)) + log n)`. -/
def HalfSpaceBounds (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ) (Q : Finset (EuclideanSpace ℝ (Fin d)))
    (n : ℕ) (x : ℕ → Site d) : Prop :=
  ∀ q ∈ Q, ∀ k : ℕ, k ≤ n →
    |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) x n| ≤
      C * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
          (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
        (localTime x n z : ℝ)) + Real.log n)

/-- The compensated-path bound at time `n` depends only on the path up to time `n`. -/
theorem compensatedBound_congr {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C : ℝ} {n : ℕ}
    {x y : ℕ → Site d} (h : ∀ j ≤ n, x j = y j) :
    CompensatedBound ε ξ C n x ↔ CompensatedBound ε ξ C n y := by
  unfold CompensatedBound
  refine forall_congr' fun s => forall_congr' fun t => forall_congr' fun hst =>
    forall_congr' fun htn => ?_
  rw [driftCompensated_congr h htn, driftCompensated_congr h (by omega : s ≤ n)]

/-- The half-space bounds at time `n` depend only on the path up to time `n`. -/
theorem halfSpaceBounds_congr (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C : ℝ} (Q : Finset (EuclideanSpace ℝ (Fin d)))
    {n : ℕ} {x y : ℕ → Site d} (h : ∀ j ≤ n, x j = y j) :
    HalfSpaceBounds Ψ ε ξ C Q n x ↔ HalfSpaceBounds Ψ ε ξ C Q n y := by
  unfold HalfSpaceBounds
  have hdep : departureRange x n = departureRange y n := departureRange_congr h (Nat.le_succ n)
  have hloc : localTime x n = localTime y n := localTime_congr h (Nat.le_succ n)
  simp only [hdep, hloc, dynkinMart_congr h]

end Prefix

/-! ## Events that depend only on the path up to time `n` -/

section Cylinder

variable {Ω : Type*}

/-- A property of paths that depends on the path only up to time `n`. -/
def PrefixDetermined (n : ℕ) (S : (ℕ → Site d) → Prop) : Prop :=
  ∀ x y : ℕ → Site d, (∀ j ≤ n, x j = y j) → (S x ↔ S y)

/-- **Cylinder characterization.** The set of sample points whose path has a property that depends
only on the path up to time `n` is the preimage, under the past path `(X_0, …, X_n)`, of the set of
finite paths with that property. -/
theorem setOf_eq_preimage_pastPath {n : ℕ} {S : (ℕ → Site d) → Prop} (hS : PrefixDetermined n S)
    (X : ℕ → Ω → Site d) :
    {ω | S (fun j => X j ω)} = pastPath X n ⁻¹' {p | S (extendPath p)} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  exact hS _ _ fun j hj => (extendPath_pastPath X hj ω).symm

/-- The same set is the countable union, over the finite paths with the property, of the
cylinders `{X_j = p_j, j ≤ n}`. -/
theorem setOf_eq_iUnion_cylinders {n : ℕ} {S : (ℕ → Site d) → Prop} (hS : PrefixDetermined n S)
    (X : ℕ → Ω → Site d) :
    {ω | S (fun j => X j ω)} =
      ⋃ p ∈ {p : (i : Finset.Iic n) → Site d | S (extendPath p)},
        {ω | ∀ j ≤ n, X j ω = extendPath p j} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro h
    exact ⟨pastPath X n ω, (hS _ _ fun j hj => (extendPath_pastPath X hj ω).symm).mp h,
      fun j hj => (extendPath_pastPath X hj ω).symm⟩
  · rintro ⟨p, hp, hω⟩
    exact (hS _ _ hω).mpr hp

/-- **Measurability in the filtration.** A set of sample points defined by a property of the path
up to time `n` belongs to `ℱ_n = σ(X_0, …, X_n)`. -/
theorem measurableSet_setOf_filtration [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ j, Measurable (X j)) {n : ℕ} {S : (ℕ → Site d) → Prop} (hS : PrefixDetermined n S) :
    MeasurableSet[pathFiltration hX n] {ω | S (fun j => X j ω)} := by
  rw [setOf_eq_preimage_pastPath hS]
  exact ⟨_, (Set.to_countable _).measurableSet, rfl⟩

/-- Such a set is measurable. -/
theorem measurableSet_setOf [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ j, Measurable (X j)) {n : ℕ} {S : (ℕ → Site d) → Prop} (hS : PrefixDetermined n S) :
    MeasurableSet {ω | S (fun j => X j ω)} :=
  (pathFiltration hX).le n _ (measurableSet_setOf_filtration hX hS)

/-- **Almost-sure transport of the legality.** For every walk with a drift field, the sample points
at which the whole path is legal and has the property `S` agree almost surely with those at which
it has the property `S`: the path starts at the origin and takes unit steps almost surely. -/
theorem setOf_pathTyping_ae_eq [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X)
    (S : (ℕ → Site d) → Prop) :
    {ω | PathTyping d (fun j => X j ω) ∧ S (fun j => X j ω)} =ᵐ[μ] {ω | S (fun j => X j ω)} := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [ae_legal_of_isDriftCERW hX] with ω hω
  exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩

end Cylinder

/-! ## The finite-prefix projection event -/

section Projection

variable {K : Set (EuclideanSpace ℝ (Fin d))}

/-- **The estimates of the projection event** at time `n` for the nearest-point map `P`: the
compensated-path bound and the half-space martingale bounds in the directions
`projectionDirections K P n`, with the constant `C₁`. No condition on the legality of the path. -/
def ProjectionEstimates (K : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C₁ : ℝ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) (x : ℕ → Site d) : Prop :=
  CompensatedBound ε ξ C₁ n x ∧
    HalfSpaceBounds (gauge K) ε ξ C₁ (projectionDirections K P n) n x

/-- The projection estimates at time `n` depend only on the path up to time `n`. -/
theorem projectionEstimates_prefixDetermined (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (C₁ : ℝ) (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    PrefixDetermined n (ProjectionEstimates K ε ξ C₁ P n) := fun _ _ h =>
  and_congr (compensatedBound_congr h) (halfSpaceBounds_congr _ _ h)

/-- **The finite-prefix projection event**: the sample points on which the projection estimates
hold at time `n`. -/
def FiniteProjectionEvent {Ω : Type*} (K : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C₁ : ℝ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (X : ℕ → Ω → Site d) (n : ℕ) :
    Set Ω :=
  {ω | ProjectionEstimates K ε ξ C₁ P n (fun j => X j ω)}

/-- The finite paths `(x_0, …, x_n)` that satisfy the projection estimates. -/
def projectionPaths (K : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C₁ : ℝ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    Set ((i : Finset.Iic n) → Site d) :=
  {p | ProjectionEstimates K ε ξ C₁ P n (extendPath p)}

variable {Ω : Type*} {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C₁ : ℝ}
  {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {X : ℕ → Ω → Site d} {n : ℕ}

/-- The finite projection event is the preimage of the set of admissible finite paths under the
past path. -/
theorem finiteProjectionEvent_eq_preimage :
    FiniteProjectionEvent K ε ξ C₁ P X n = pastPath X n ⁻¹' projectionPaths K ε ξ C₁ P n :=
  setOf_eq_preimage_pastPath (projectionEstimates_prefixDetermined ε ξ C₁ P n) X

/-- The finite projection event is the countable union of the cylinders of the admissible finite
paths. -/
theorem finiteProjectionEvent_eq_iUnion_cylinders :
    FiniteProjectionEvent K ε ξ C₁ P X n =
      ⋃ p ∈ projectionPaths K ε ξ C₁ P n, {ω | ∀ j ≤ n, X j ω = extendPath p j} :=
  setOf_eq_iUnion_cylinders (projectionEstimates_prefixDetermined ε ξ C₁ P n) X

/-- Membership in the finite projection event depends only on the positions up to time `n`. -/
theorem mem_finiteProjectionEvent_congr {ω ω' : Ω} (h : ∀ j ≤ n, X j ω = X j ω') :
    ω ∈ FiniteProjectionEvent K ε ξ C₁ P X n ↔ ω' ∈ FiniteProjectionEvent K ε ξ C₁ P X n :=
  projectionEstimates_prefixDetermined ε ξ C₁ P n _ _ h

/-- **The finite projection event belongs to `ℱ_n = σ(X_0, …, X_n)`.** -/
theorem measurableSet_finiteProjectionEvent_filtration [MeasurableSpace Ω]
    (hX : ∀ j, Measurable (X j)) :
    MeasurableSet[pathFiltration hX n] (FiniteProjectionEvent K ε ξ C₁ P X n) :=
  measurableSet_setOf_filtration hX (projectionEstimates_prefixDetermined ε ξ C₁ P n)

/-- The finite projection event is measurable. -/
theorem measurableSet_finiteProjectionEvent [MeasurableSpace Ω] (hX : ∀ j, Measurable (X j)) :
    MeasurableSet (FiniteProjectionEvent K ε ξ C₁ P X n) :=
  measurableSet_setOf hX (projectionEstimates_prefixDetermined ε ξ C₁ P n)

/-- The path event `ProjectionEvent` is legality together with the projection estimates. -/
theorem projectionEvent_iff {x : ℕ → Site d} :
    ProjectionEvent K ε ξ C₁ P n x ↔
      PathTyping d x ∧ ProjectionEstimates K ε ξ C₁ P n x := by
  unfold ProjectionEvent PathTyping ProjectionEstimates CompensatedBound HalfSpaceBounds
  exact and_assoc.symm

/-- The sample points of the auxiliary path event are the legal sample points of the finite
event. -/
theorem projectionEvent_set_eq :
    {ω | ProjectionEvent K ε ξ C₁ P n (fun j => X j ω)} =
      legalSet X ∩ FiniteProjectionEvent K ε ξ C₁ P X n :=
  Set.ext fun ω => projectionEvent_iff (x := fun j => X j ω)

/-- **Almost-sure transport.** Under `IsDriftCERW` the auxiliary path event and the finite event
agree almost surely. -/
theorem projectionEvent_ae_eq [MeasurableSpace Ω] {μ : Measure Ω}
    (hX : IsDriftCERW μ ε ξ X) :
    {ω | ProjectionEvent K ε ξ C₁ P n (fun j => X j ω)} =ᵐ[μ]
      FiniteProjectionEvent K ε ξ C₁ P X n := by
  have h := setOf_pathTyping_ae_eq hX (ProjectionEstimates K ε ξ C₁ P n)
  refine Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq ?_) h
  ext ω
  exact projectionEvent_iff (x := fun j => X j ω)

/-- **Exact probability transport.** Under `IsDriftCERW` the complement of the finite event has
the same probability as the failure set of the auxiliary path event. -/
theorem measure_finiteProjectionEvent_compl [MeasurableSpace Ω] {μ : Measure Ω}
    (hX : IsDriftCERW μ ε ξ X) :
    μ (FiniteProjectionEvent K ε ξ C₁ P X n)ᶜ =
      μ {ω | ¬ ProjectionEvent K ε ξ C₁ P n (fun j => X j ω)} :=
  (measure_congr (projectionEvent_ae_eq hX).compl).symm

/-- The compensated-path hypothesis of the rates theorem, from the finite event. -/
theorem ProjectionEstimates.compensated {x : ℕ → Site d}
    (h : ProjectionEstimates K ε ξ C₁ P n x) :
    ∀ s t : ℕ, s < t → t ≤ n →
      ‖(toSpace (x t) + ε • ∑ j ∈ Finset.range t,
          if x j ∉ departureRange x j then ξ (x j) else 0) -
        (toSpace (x s) + ε • ∑ j ∈ Finset.range s,
          if x j ∉ departureRange x j then ξ (x j) else 0)‖ ≤
        C₁ * Real.sqrt ((t - s : ℝ) * Real.log n) :=
  h.1

/-- The linear martingale hypothesis of the rates theorem, from the finite event and the legality
of the path: at each visited site `x_j`, `j ≤ n`, the direction `Λ_ψ (x_j - P x_j)/|x_j - P x_j|`
is in the family. -/
theorem ProjectionEstimates.martingale {x : ℕ → Site d} (hl : PathTyping d x)
    (h : ProjectionEstimates K ε ξ C₁ P n x) {j : ℕ} (hj : j ≤ n) {k : ℕ} (hk : k ≤ n) :
    |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ (GaugeContactShape.Projection.projDir K P (toSpace (x j)))
          (toSpace z) - k * normMax (gauge K)) 0) x n| ≤
      C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
          (fun z => k * normMax (gauge K) - normMax (gauge K) <
            inner ℝ (GaugeContactShape.Projection.projDir K P (toSpace (x j))) (toSpace z)),
        (localTime x n z : ℝ)) + Real.log n) :=
  (projectionEvent_iff.mpr ⟨hl, h⟩).martingale hj hk

/-- **The failure probability of the finite projection event.** For every `p > 0` there are
constants `C₁` and `C`, those of `exists_projectionEvent_failure_bound`, chosen before `ξ`, the
probability space, the walk, `n` and `P`, such that for every `n ≥ 2` (no larger threshold) and
every map `P` fixed before the walk, the finite event is in `ℱ_n` and its complement has
probability at most `C n^{-p}`. -/
theorem exists_finiteProjectionEvent_failure_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C₁ C : ℝ, 0 < C₁ ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X), ∀ n : ℕ, 2 ≤ n →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        MeasurableSet[pathFiltration hX.measurable n] (FiniteProjectionEvent K ε ξ C₁ P X n) ∧
        μ (FiniteProjectionEvent K ε ξ C₁ P X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C₁, C, hC₁, hC, hev⟩ := exists_projectionEvent_failure_bound.{u} (K := K) hd hε hell hp
  refine ⟨C₁, C, hC₁, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn P
  refine ⟨measurableSet_finiteProjectionEvent_filtration hX.measurable, ?_⟩
  rw [measure_finiteProjectionEvent_compl hX]
  exact hev ξ hξ hξ0 μ X hX n hn P

end Projection

/-! ## The directions of the source -/

section Source

variable {K : Set (EuclideanSpace ℝ (Fin d))}

open scoped Classical in
/-- The directions `Λ_ψ u_{x - P x}` of the source, for the sites `x ∈ ℤ^d` with `|x| ≤ n` and
`ψ(x) > r`. -/
noncomputable def sourceProjectionDirections (K : Set (EuclideanSpace ℝ (Fin d)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r : ℝ) (n : ℕ) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  ((LatticeProb.ballFinset d (n : ℝ)).filter fun z => r < gauge K (toSpace z)).image
    fun z => GaugeContactShape.Projection.projDir K P (toSpace z)

/-- The directions of the source are among the directions of the auxiliary event. -/
theorem sourceProjectionDirections_subset
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r : ℝ) (n : ℕ) :
    sourceProjectionDirections K P r n ⊆ projectionDirections K P n := by
  classical
  unfold sourceProjectionDirections projectionDirections
  exact Finset.image_subset_image (Finset.filter_subset _ _)

/-- The family of the source has at most `(2n + 1)^d` vectors. -/
theorem card_sourceProjectionDirections_le
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r : ℝ) (n : ℕ) :
    ((sourceProjectionDirections K P r n).card : ℝ) ≤ (2 * (n : ℝ) + 1) ^ d :=
  (Nat.cast_le.mpr (Finset.card_le_card (sourceProjectionDirections_subset P r n))).trans
    (card_projectionDirections_le P n)

/-- The direction at a site of Euclidean norm at most `n` with `ψ > r` is in the family of the
source. -/
theorem projDir_mem_sourceProjectionDirections
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {r : ℝ} {n : ℕ} {z : Site d}
    (hz : euclidNorm z ≤ n) (hr : r < gauge K (toSpace z)) :
    GaugeContactShape.Projection.projDir K P (toSpace z) ∈ sourceProjectionDirections K P r n := by
  classical
  unfold sourceProjectionDirections
  exact Finset.mem_image_of_mem _
    (Finset.mem_filter.mpr ⟨LatticeProb.mem_ballFinset_iff.mpr hz, hr⟩)

/-- Every direction of the source has length exactly `Λ_ψ`, when `P` maps into `{ψ ≤ r}`. -/
theorem norm_eq_of_mem_sourceProjectionDirections (hΛ : 0 ≤ normMax (gauge K))
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hP : ∀ z, gauge K (P z) ≤ r) {n : ℕ} {q : EuclideanSpace ℝ (Fin d)}
    (hq : q ∈ sourceProjectionDirections K P r n) : ‖q‖ = normMax (gauge K) := by
  classical
  unfold sourceProjectionDirections at hq
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
  exact norm_projDir_of_lt hΛ hP (Finset.mem_filter.mp hz).2

/-- The half-space bounds for a larger family imply those for a subfamily. -/
theorem HalfSpaceBounds.mono {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C : ℝ} {Q Q' : Finset (EuclideanSpace ℝ (Fin d))}
    {n : ℕ} {x : ℕ → Site d} (hQ : Q ⊆ Q') (h : HalfSpaceBounds Ψ ε ξ C Q' n x) :
    HalfSpaceBounds Ψ ε ξ C Q n x :=
  fun q hq => h q (hQ hq)

/-- **The estimates of the source** at time `n`: the compensated-path bound and the half-space
martingale bounds `eq:linear-mart` for the pairs `(q, a)` with `q = Λ_ψ u_{x - P x}`, `|x| ≤ n`,
`ψ(x) > r` and `a = kΛ_ψ`, `0 ≤ k ≤ n`. -/
def SourceProjectionEstimates (K : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C₁ : ℝ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r : ℝ) (n : ℕ)
    (x : ℕ → Site d) : Prop :=
  CompensatedBound ε ξ C₁ n x ∧
    HalfSpaceBounds (gauge K) ε ξ C₁ (sourceProjectionDirections K P r n) n x

/-- The estimates of the source at time `n` depend only on the path up to time `n`. -/
theorem sourceProjectionEstimates_prefixDetermined (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C₁ : ℝ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r : ℝ) (n : ℕ) :
    PrefixDetermined n (SourceProjectionEstimates K ε ξ C₁ P r n) := fun _ _ h =>
  and_congr (compensatedBound_congr h) (halfSpaceBounds_congr _ _ h)

/-- The estimates of the auxiliary event imply those of the source. -/
theorem ProjectionEstimates.toSource {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C₁ : ℝ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {n : ℕ} {x : ℕ → Site d} {r : ℝ}
    (h : ProjectionEstimates K ε ξ C₁ P n x) : SourceProjectionEstimates K ε ξ C₁ P r n x :=
  ⟨h.1, h.2.mono (sourceProjectionDirections_subset P r n)⟩

/-- **The finite-prefix event of the source** for the directions of the projection `P`: the sample
points on which the estimates of the source hold at time `n`. -/
def FiniteSourceProjectionEvent {Ω : Type*} (K : Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C₁ : ℝ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r : ℝ) (X : ℕ → Ω → Site d)
    (n : ℕ) : Set Ω :=
  {ω | SourceProjectionEstimates K ε ξ C₁ P r n (fun j => X j ω)}

variable {Ω : Type*} {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C₁ : ℝ}
  {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {r : ℝ} {X : ℕ → Ω → Site d}
  {n : ℕ}

/-- The finite event of the source is the preimage of a set of finite paths under the past path. -/
theorem finiteSourceProjectionEvent_eq_preimage :
    FiniteSourceProjectionEvent K ε ξ C₁ P r X n =
      pastPath X n ⁻¹' {p | SourceProjectionEstimates K ε ξ C₁ P r n (extendPath p)} :=
  setOf_eq_preimage_pastPath (sourceProjectionEstimates_prefixDetermined ε ξ C₁ P r n) X

/-- The finite event of the source is the countable union of the cylinders of its finite paths. -/
theorem finiteSourceProjectionEvent_eq_iUnion_cylinders :
    FiniteSourceProjectionEvent K ε ξ C₁ P r X n =
      ⋃ p ∈ {p : (i : Finset.Iic n) → Site d |
        SourceProjectionEstimates K ε ξ C₁ P r n (extendPath p)},
        {ω | ∀ j ≤ n, X j ω = extendPath p j} :=
  setOf_eq_iUnion_cylinders (sourceProjectionEstimates_prefixDetermined ε ξ C₁ P r n) X

/-- **The finite event of the source belongs to `ℱ_n = σ(X_0, …, X_n)`.** -/
theorem measurableSet_finiteSourceProjectionEvent_filtration [MeasurableSpace Ω]
    (hX : ∀ j, Measurable (X j)) :
    MeasurableSet[pathFiltration hX n] (FiniteSourceProjectionEvent K ε ξ C₁ P r X n) :=
  measurableSet_setOf_filtration hX (sourceProjectionEstimates_prefixDetermined ε ξ C₁ P r n)

/-- The finite event of the auxiliary family is contained in the finite event of the source. -/
theorem finiteProjectionEvent_subset_source :
    FiniteProjectionEvent K ε ξ C₁ P X n ⊆ FiniteSourceProjectionEvent K ε ξ C₁ P r X n :=
  fun _ h => ProjectionEstimates.toSource h

/-- The compensated-path hypothesis of the rates theorem, from the estimates of the source. -/
theorem SourceProjectionEstimates.compensated {x : ℕ → Site d}
    (h : SourceProjectionEstimates K ε ξ C₁ P r n x) :
    ∀ s t : ℕ, s < t → t ≤ n →
      ‖(toSpace (x t) + ε • ∑ j ∈ Finset.range t,
          if x j ∉ departureRange x j then ξ (x j) else 0) -
        (toSpace (x s) + ε • ∑ j ∈ Finset.range s,
          if x j ∉ departureRange x j then ξ (x j) else 0)‖ ≤
        C₁ * Real.sqrt ((t - s : ℝ) * Real.log n) :=
  h.1

/-- **The linear martingale hypothesis of the rates theorem, from the estimates of the source.**
For a legal path, at each visited site `x_j`, `j ≤ n`, with `ψ(x_j) > r`, the direction
`Λ_ψ (x_j - P x_j)/|x_j - P x_j|` is one of the pairs of the source. -/
theorem SourceProjectionEstimates.martingale {x : ℕ → Site d} (hl : PathTyping d x)
    (h : SourceProjectionEstimates K ε ξ C₁ P r n x) {j : ℕ} (hj : j ≤ n)
    (hrj : r < gauge K (toSpace (x j))) {k : ℕ} (hk : k ≤ n) :
    |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ (GaugeContactShape.Projection.projDir K P (toSpace (x j)))
          (toSpace z) - k * normMax (gauge K)) 0) x n| ≤
      C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
          (fun z => k * normMax (gauge K) - normMax (gauge K) <
            inner ℝ (GaugeContactShape.Projection.projDir K P (toSpace (x j))) (toSpace z)),
        (localTime x n z : ℝ)) + Real.log n) := by
  have hxj : euclidNorm (x j) ≤ n :=
    (CERW.Support.Occupation.euclidNorm_le_of_steps x hl.1 hl.2 j).trans (by exact_mod_cast hj)
  exact h.2 _ (projDir_mem_sourceProjectionDirections hxj hrj) k hk

end Source

/-! ## The nearest-point map at the deterministic radius -/

section Nearest

variable {K : Set (EuclideanSpace ℝ (Fin d))}

/-- `P` is a nearest-point map onto the closed convex set `{ψ ≤ r}`: it maps into the set and
satisfies the variational inequality `(z - P z) · (y - P z) ≤ 0` for every `y` of the set. -/
def IsNearestMap (K : Set (EuclideanSpace ℝ (Fin d))) (r : ℝ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ z, gauge K (P z) ≤ r) ∧ ∀ z y, gauge K y ≤ r → inner ℝ (z - P z) (y - P z) ≤ 0

/-- A nearest-point map is unique (`nearestPoint_unique`). -/
theorem IsNearestMap.unique {r : ℝ} {P P' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (h : IsNearestMap K r P) (h' : IsNearestMap K r P') : P = P' :=
  nearestPoint_unique h.1 h.2 h'.1 h'.2

/-- **Existence of the nearest-point map.** For a compact convex body with the origin in its
interior and a radius `r ≥ 0` there is a nearest-point map onto `{ψ ≤ r}`: for `r > 0` it is the
nearest point of a closed convex set (`Projection.exists_nearestPoint`), and for `r = 0` the set is
`{0}` and the map is the constant `0`. -/
theorem exists_isNearestMap (hd : 1 ≤ d) (hΨ : GaugeContactShape.Adm K) {r : ℝ} (hr : 0 ≤ r) :
    ∃ P, IsNearestMap K r P := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨fun _ => 0, fun _ => by simp [hΨ.map_zero], fun z y hy => ?_⟩
    obtain ⟨hc, hcle⟩ := hΨ.normMin_pos_mul_le hd
    have hy0 : y = 0 := by
      have h1 : normMin (gauge K) * ‖y‖ ≤ 0 := (hcle y).trans hy
      have h2 : ‖y‖ ≤ 0 := by
        by_contra hcon
        exact absurd h1 (not_le.mpr (mul_pos hc (not_le.mp hcon)))
      exact norm_le_zero_iff.mp h2
    simp [hy0]
  · exact GaugeContactShape.Projection.exists_nearestPoint hΨ hpos

/-- **The selected nearest-point map.** For a compact convex body `K` with the origin in its
interior and a radius `r ≥ 0`, the nearest-point map onto `{ψ ≤ r}` selected from the existence
proof `exists_isNearestMap`. It is defined only on this carrier (the arguments `hd`, `hΨ`, `hr` are
the proofs of the hypotheses of existence), with no value outside it; `nearestMapAt_spec` is its
complete characterization and `nearestMapAt_eq_of` its uniqueness. -/
noncomputable def nearestMapAt (hd : 1 ≤ d) (hΨ : GaugeContactShape.Adm K) {r : ℝ} (hr : 0 ≤ r) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  (exists_isNearestMap hd hΨ hr).choose

/-- The selected map is a nearest-point map onto `{ψ ≤ r}`. -/
theorem nearestMapAt_spec (hd : 1 ≤ d) (hΨ : GaugeContactShape.Adm K) {r : ℝ} (hr : 0 ≤ r) :
    IsNearestMap K r (nearestMapAt hd hΨ hr) :=
  (exists_isNearestMap hd hΨ hr).choose_spec

/-- It is the only nearest-point map: it equals every nearest-point map onto `{ψ ≤ r}`. -/
theorem nearestMapAt_eq_of (hd : 1 ≤ d) (hΨ : GaugeContactShape.Adm K) {r : ℝ} (hr : 0 ≤ r)
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hP : IsNearestMap K r P) :
    nearestMapAt hd hΨ hr = P :=
  (nearestMapAt_spec hd hΨ hr).unique hP

/-- The deterministic radius `r_n = ((d+1) n/(2 d ε |B_ψ|))^{1/(d+1)}` is nonnegative on the
carrier: for a compact convex body with the origin in its interior and `ε > 0`. -/
theorem coarseScale_nonneg_of_adm (hΨ : GaugeContactShape.Adm K) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 ≤ coarseScale (gauge K) ε n :=
  coarseScale_nonneg hε (normBallVolume_gauge_pos hΨ.compact hΨ.convex hΨ.zero_mem) n

/-- **The projection `Π_n`** onto `{ψ ≤ r_n}` at the deterministic radius `r_n`, for a compact
convex body with the origin in its interior and `ε > 0`: the selected nearest-point map at the
nonnegative radius `r_n`. -/
noncomputable def projectionAtScale (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  nearestMapAt (by omega) hΨ (coarseScale_nonneg_of_adm hΨ hε n)

/-- For every `n`, `Π_n` is the nearest-point map onto `{ψ ≤ r_n}`, the only one, and
`n = 2 ε d |B_ψ| r_n^{d+1}/(d+1)`. -/
theorem projectionAtScale_spec (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) :
    IsNearestMap K (coarseScale (gauge K) ε n) (projectionAtScale hd hΨ hε n) ∧
      (∀ P, IsNearestMap K (coarseScale (gauge K) ε n) P → P = projectionAtScale hd hΨ hε n) ∧
      (n : ℝ) = 2 * ε * d * normBallVolume (gauge K) * coarseScale (gauge K) ε n ^ (d + 1) /
        (d + 1) := by
  have hV : 0 < normBallVolume (gauge K) :=
    normBallVolume_gauge_pos hΨ.compact hΨ.convex hΨ.zero_mem
  refine ⟨nearestMapAt_spec _ hΨ _, fun P hP => (nearestMapAt_eq_of _ hΨ _ hP).symm, ?_⟩
  have h := nat_eq_coarseScale_pow (Ψ := gauge K) (by omega : 1 ≤ d) hε hV n
  rw [h]
  ring

variable {Ω : Type*} {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C₁ : ℝ}
  {X : ℕ → Ω → Site d} {n : ℕ} {r : ℝ}

/-- The finite projection event does not depend on the choice of the nearest-point map. -/
theorem finiteProjectionEvent_eq_of_isNearestMap
    {P P' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (h : IsNearestMap K r P)
    (h' : IsNearestMap K r P') :
    FiniteProjectionEvent K ε ξ C₁ P X n = FiniteProjectionEvent K ε ξ C₁ P' X n := by
  rw [h.unique h']

/-- **The event `E_n ∈ ℱ_n` of the source for the family of the auxiliary event**: the estimates in
the directions of the projection `Π_n` onto `{ψ ≤ r_n}` at the deterministic radius `r_n`, for every
site of Euclidean norm at most `n`. -/
def FiniteProjectionEventAtScale (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) (hε : 0 < ε)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C₁ : ℝ) (X : ℕ → Ω → Site d) (n : ℕ) : Set Ω :=
  FiniteProjectionEvent K ε ξ C₁ (projectionAtScale hd hΨ hε n) X n

/-- **The event `E_n ∈ ℱ_n` of the source** for the directions `Λ_ψ u_{x - Π_n x}` of the sites
`|x| ≤ n` with `ψ(x) > r_n`, at the deterministic radius `r_n`. -/
def FiniteSourceProjectionEventAtScale (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K)
    (hε : 0 < ε) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C₁ : ℝ) (X : ℕ → Ω → Site d)
    (n : ℕ) : Set Ω :=
  FiniteSourceProjectionEvent K ε ξ C₁ (projectionAtScale hd hΨ hε n) (coarseScale (gauge K) ε n)
    X n

/-- **The finite events of the source.** For the gauge of a compact convex body with the origin in
its interior, `ε` with `ε ψ(±e_i) < 1/d` and `p > 0`, there are constants `C₁`, `C`, chosen before
`ξ`, the probability space, the walk and `n`, such that for every subgradient selection and every
walk: the events `E_n`, `n ≥ 0`, belong to `ℱ_n`; and for every `n ≥ 2` the map `Π_n` is the
nearest-point map onto `{ψ ≤ r_n}` (and the only one), `n = 2 ε d |B_ψ| r_n^{d+1}/(d+1)`, the event
for all sites agrees almost surely with the auxiliary path event `ProjectionEvent` at `Π_n` and is
contained in the event of the source, and both have complement of probability at most `C n^{-p}`. -/
theorem gauge_finite_projection_event (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {ε : ℝ}
    (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C₁ C : ℝ, 0 < C₁ ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X),
        (∀ n : ℕ, MeasurableSet[pathFiltration hX.measurable n]
            (FiniteProjectionEventAtScale hd hΨ hε ξ C₁ X n) ∧
          MeasurableSet[pathFiltration hX.measurable n]
            (FiniteSourceProjectionEventAtScale hd hΨ hε ξ C₁ X n)) ∧
        ∀ n : ℕ, 2 ≤ n →
          IsNearestMap K (coarseScale (gauge K) ε n) (projectionAtScale hd hΨ hε n) ∧
          (n : ℝ) = 2 * ε * d * normBallVolume (gauge K) * coarseScale (gauge K) ε n ^ (d + 1) /
            (d + 1) ∧
          {ω | ProjectionEvent K ε ξ C₁ (projectionAtScale hd hΨ hε n) n (fun j => X j ω)} =ᵐ[μ]
            FiniteProjectionEventAtScale hd hΨ hε ξ C₁ X n ∧
          FiniteProjectionEventAtScale hd hΨ hε ξ C₁ X n ⊆
            FiniteSourceProjectionEventAtScale hd hΨ hε ξ C₁ X n ∧
          μ (FiniteProjectionEventAtScale hd hΨ hε ξ C₁ X n)ᶜ ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          μ (FiniteSourceProjectionEventAtScale hd hΨ hε ξ C₁ X n)ᶜ ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C₁, C, hC₁, hC, hev⟩ := exists_finiteProjectionEvent_failure_bound.{u} (K := K) hd hε
    hell hp
  refine ⟨C₁, C, hC₁, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX
  refine ⟨fun n => ⟨measurableSet_finiteProjectionEvent_filtration hX.measurable,
    measurableSet_finiteSourceProjectionEvent_filtration hX.measurable⟩, ?_⟩
  intro n hn
  obtain ⟨hP, -, hrel⟩ := projectionAtScale_spec hd hΨ hε n
  have h := (hev ξ hξ hξ0 μ X hX n hn (projectionAtScale hd hΨ hε n)).2
  exact ⟨hP, hrel, projectionEvent_ae_eq hX, finiteProjectionEvent_subset_source, h,
    (measure_mono (Set.compl_subset_compl.mpr finiteProjectionEvent_subset_source)).trans h⟩

end Nearest

/-! ## The finite-prefix radial event -/

section Cap

variable {Ω : Type*} {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {n : ℕ}
  {X : ℕ → Ω → Site d} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **The estimates of the radial event** at time `n`: the compensated-path bound with constant
`C_V` and the half-space martingale bounds with constant `C_M` in the radial directions
`capDirections Ψ n`. No condition on the legality of the path. -/
def CapEstimates (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C_V C_M : ℝ) (n : ℕ) (x : ℕ → Site d) : Prop :=
  CompensatedBound ε ξ C_V n x ∧ HalfSpaceBounds Ψ ε ξ C_M (capDirections Ψ n) n x

/-- The radial estimates at time `n` depend only on the path up to time `n`. -/
theorem capEstimates_prefixDetermined (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C_V C_M : ℝ) (n : ℕ) :
    PrefixDetermined n (CapEstimates Ψ ε ξ C_V C_M n) := fun _ _ h =>
  and_congr (compensatedBound_congr h) (halfSpaceBounds_congr _ _ h)

/-- **The finite-prefix radial event**: the sample points on which the radial estimates hold at
time `n`. -/
def FiniteCapEvent (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C_V C_M : ℝ) (X : ℕ → Ω → Site d) (n : ℕ) :
    Set Ω :=
  {ω | CapEstimates Ψ ε ξ C_V C_M n (fun j => X j ω)}

/-- The finite radial event is the preimage of a set of finite paths under the past path. -/
theorem finiteCapEvent_eq_preimage {C_V C_M : ℝ} :
    FiniteCapEvent Ψ ε ξ C_V C_M X n =
      pastPath X n ⁻¹' {p | CapEstimates Ψ ε ξ C_V C_M n (extendPath p)} :=
  setOf_eq_preimage_pastPath (capEstimates_prefixDetermined Ψ ε ξ C_V C_M n) X

/-- The finite radial event is the countable union of the cylinders of its finite paths. -/
theorem finiteCapEvent_eq_iUnion_cylinders {C_V C_M : ℝ} :
    FiniteCapEvent Ψ ε ξ C_V C_M X n =
      ⋃ p ∈ {p : (i : Finset.Iic n) → Site d | CapEstimates Ψ ε ξ C_V C_M n (extendPath p)},
        {ω | ∀ j ≤ n, X j ω = extendPath p j} :=
  setOf_eq_iUnion_cylinders (capEstimates_prefixDetermined Ψ ε ξ C_V C_M n) X

/-- **The finite radial event belongs to `ℱ_n = σ(X_0, …, X_n)`.** -/
theorem measurableSet_finiteCapEvent_filtration [MeasurableSpace Ω] {C_V C_M : ℝ}
    (hX : ∀ j, Measurable (X j)) :
    MeasurableSet[pathFiltration hX n] (FiniteCapEvent Ψ ε ξ C_V C_M X n) :=
  measurableSet_setOf_filtration hX (capEstimates_prefixDetermined Ψ ε ξ C_V C_M n)

/-- The finite radial event is measurable. -/
theorem measurableSet_finiteCapEvent [MeasurableSpace Ω] {C_V C_M : ℝ}
    (hX : ∀ j, Measurable (X j)) : MeasurableSet (FiniteCapEvent Ψ ε ξ C_V C_M X n) :=
  measurableSet_setOf hX (capEstimates_prefixDetermined Ψ ε ξ C_V C_M n)

/-- The path event `CapEvent` is legality together with the radial estimates. -/
theorem capEvent_iff {C_V C_M : ℝ} {x : ℕ → Site d} :
    CapEvent Ψ ε ξ C_V C_M n x ↔ PathTyping d x ∧ CapEstimates Ψ ε ξ C_V C_M n x := by
  unfold CapEvent PathTyping CapEstimates CompensatedBound HalfSpaceBounds
  exact and_assoc.symm

/-- The sample points of the auxiliary path event are the legal sample points of the finite
radial event. -/
theorem capEvent_set_eq {C_V C_M : ℝ} :
    {ω | CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω)} =
      legalSet X ∩ FiniteCapEvent Ψ ε ξ C_V C_M X n :=
  Set.ext fun ω => capEvent_iff (x := fun j => X j ω)

/-- **Almost-sure transport.** Under `IsDriftCERW` the auxiliary path event and the finite radial
event agree almost surely. -/
theorem capEvent_ae_eq [MeasurableSpace Ω] {μ : Measure Ω} {C_V C_M : ℝ}
    (hX : IsDriftCERW μ ε ξ X) :
    {ω | CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω)} =ᵐ[μ]
      FiniteCapEvent Ψ ε ξ C_V C_M X n := by
  have h := setOf_pathTyping_ae_eq hX (CapEstimates Ψ ε ξ C_V C_M n)
  refine Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq ?_) h
  ext ω
  exact capEvent_iff (x := fun j => X j ω)

/-- **Exact probability transport** for the radial event. -/
theorem measure_finiteCapEvent_compl [MeasurableSpace Ω] {μ : Measure Ω} {C_V C_M : ℝ}
    (hX : IsDriftCERW μ ε ξ X) :
    μ (FiniteCapEvent Ψ ε ξ C_V C_M X n)ᶜ =
      μ {ω | ¬ CapEvent Ψ ε ξ C_V C_M n (fun j => X j ω)} :=
  (measure_congr (capEvent_ae_eq hX).compl).symm

end Cap

section CapBounds

variable {K : Set (EuclideanSpace ℝ (Fin d))}

/-- **The failure probability of the finite radial event**, with the constants of
`exists_capEvent_failure_bound`, for every `n ≥ 2`. -/
theorem exists_finiteCapEvent_failure_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C_V C_M C : ℝ, 0 < C_V ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X), ∀ n : ℕ, 2 ≤ n →
        MeasurableSet[pathFiltration hX.measurable n] (FiniteCapEvent (gauge K) ε ξ C_V C_M X n) ∧
        μ (FiniteCapEvent (gauge K) ε ξ C_V C_M X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C_V, C_M, C, hC_V, hC, hev⟩ := exists_capEvent_failure_bound.{u} (K := K) hd hε hell hp
  refine ⟨C_V, C_M, C, hC_V, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  refine ⟨measurableSet_finiteCapEvent_filtration hX.measurable, ?_⟩
  rw [measure_finiteCapEvent_compl hX]
  exact hev ξ hξ hξ0 μ X hX n hn

/-- **The rough outer bound on the finite radial event.** For a legal path (a property that holds
almost surely) in the finite radial event, the Euclidean-max cap bound holds at every real level. -/
theorem roughOuter_of_capEstimates (hd : 2 ≤ d) (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {C_V C_M : ℝ} (hC_V : 0 < C_V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ n : ℕ, 2 ≤ n → ∀ x : ℕ → Site d, PathTyping d x →
        CapEstimates (gauge K) ε ξ C_V C_M n x → RoughOuter (gauge K) C n x := by
  obtain ⟨C, hC, hrough⟩ := exists_rough_outer_of_capEvent hd hK h0 hε hell (C_M := C_M) hC_V
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hξ0 n hn x hl h
  exact hrough ξ hξ hξ0 n hn x (capEvent_iff.mpr ⟨hl, h⟩)

end CapBounds

end CERW.Support.Norm.GaugeFiniteEvents
