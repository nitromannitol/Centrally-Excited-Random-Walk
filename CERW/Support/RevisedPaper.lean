import CERW.Support.Norm.CoarseCapEvents
import CERW.Support.Norm.Section5Localization

/-!
# The event forms of the crossing and contact lemmas

The revised statements of `lem:crossing`, `lem:outer-crossing` and `lem:contact` are assertions on
named events of the walk: the event of `eq:vector`, the events of `eq:vector` and `eq:linear-mart`,
and the event of Section 5.1. A bound on the probability of the set where one of the conclusions
fails does not give a bound on a previously named event; this module states and proves the
assertions on the events themselves, with the constants of the events. Throughout, `Ψ` is a norm of
`ℝ^d`, `d ≥ 2`, `ε > 0` satisfies `ε Ψ(e_i) < 1/d` for every coordinate vector `e_i`, `ξ(x)` is a
subgradient of `Ψ` at every site `x ≠ 0` and `ξ(0) = 0`; a walk is a process with the law
`IsDriftCERW μ ε ξ X`.

* `VectorEvent` is the set of sample points at which the compensated position `Z` satisfies
  `|Z_t - Z_s| ≤ C √((t - s) log n)` for all `0 ≤ s < t ≤ n` (`eq:vector`), and
  `crossing_on_vector_event` is `lem:crossing` on it, together with the bound of its
  complement by `C n^{-p}`.
* `RadialHalfSpaceEvent` is the set of sample points at which the half-space martingale bounds
  of `eq:linear-mart` hold for the directions `Λ_Ψ u_x`, `|x| ≤ n`, at the levels `k Λ_Ψ`,
  `0 ≤ k ≤ n`; `outer_crossing_on_events` is `lem:outer-crossing` for a path satisfying the vector
  bound and the half-space bounds in a direction `q`, with the constants of the two events and the
  failure probability of their intersection.
* `sourceEvent` is the event of Section 5.1 for an explicitly characterized selection `P` of
  nearest points of `{Ψ ≤ r_n}`; `contact_on_source_event` is `lem:contact` on it for all large
  `n` and at every contact point, for walks whose sample paths start at the origin and take unit
  steps, and `contact_on_source_event_almost_surely` is the same for an arbitrary walk, almost
  surely on the event. A selection of nearest points is a map that sends every point to a point of
  `{Ψ ≤ r_n}` nearest to it in Euclidean distance (`isNearestSelection_of_dist_le`,
  `dist_le_of_isNearestSelection`); it exists (`exists_nearestSelection_at_scale`), it is unique
  (`nearestSelection_unique`), and the event does not depend on it
  (`sourceEvent_eq_of_nearestSelection`).

The producers are the vector bound, the half-space martingale bounds, the crossing lemmas and the
localization of the contact estimate in the modules imported here; no producer is a hypothesis.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.RevisedPaper

open CERW CERW.Support.Norm CERW.Support.Norm.CoarseCrossing CERW.Support.Norm.ContactEvent
  CERW.Support.Norm.Section5Localization

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The events of `eq:vector` and `eq:linear-mart` -/

/-- The vector bound `eq:vector` for a path `x` at time `n` with constant `C`: the compensated
position `Z_t = x_t + ε Σ_{j<t} I_j ξ(x_j)`, with `I_j` the indicator of a first departure,
satisfies `|Z_t - Z_s| ≤ C √((t - s) log n)` for all `0 ≤ s < t ≤ n`. -/
def VectorIncrementBound (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ) (n : ℕ)
    (x : ℕ → Site d) : Prop :=
  ∀ s t : ℕ, s < t → t ≤ n →
    ‖VectorBound.driftCompensated ε ξ x t - VectorBound.driftCompensated ε ξ x s‖ ≤
      C * Real.sqrt (((t : ℝ) - s) * Real.log n)

/-- The half-space martingale bounds `eq:linear-mart` for a path `x` at time `n`, a direction `q`
and the constant `C`: for every level `a = k Λ_Ψ` with `0 ≤ k ≤ n`, the Dynkin martingale of
`z ↦ (q · z - a)_+` satisfies `|𝓜^{q,a}_n| ≤ C (√(log n Σ_{z : q · z > a - Λ_Ψ} ℓ_n(z)) + log n)`,
where `ℓ_n` is the local time. -/
def HalfSpaceBound (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ) (n : ℕ) (q : EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) : Prop :=
  ∀ k : ℕ, k ≤ n →
    |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) x n| ≤
      C * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
          (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
        (localTime x n z : ℝ)) + Real.log n)

/-- The event of `eq:vector`: the sample points at which the path of the walk satisfies the vector
bound with constant `C` at time `n`. -/
def VectorEvent {Ω : Type*} (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ)
    (X : ℕ → Ω → Site d) (n : ℕ) : Set Ω :=
  {ω | VectorIncrementBound ε ξ C n (fun j => X j ω)}

/-- The event of `eq:linear-mart` for the radial family of directions: the sample points at which
the half-space bounds with constant `C` hold at time `n` for every direction `Λ_Ψ u_x` with
`|x| ≤ n`. -/
def RadialHalfSpaceEvent {Ω : Type*} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ) (X : ℕ → Ω → Site d) (n : ℕ) : Set Ω :=
  {ω | ∀ q ∈ capDirections Ψ n, HalfSpaceBound Ψ ε ξ C n q (fun j => X j ω)}

/-- The vector bound with a smaller constant implies the vector bound with a larger one. -/
theorem VectorIncrementBound.mono {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C C' : ℝ}
    {n : ℕ} {x : ℕ → Site d} (h : VectorIncrementBound ε ξ C n x) (hC : C ≤ C') :
    VectorIncrementBound ε ξ C' n x :=
  fun s t hst htn =>
    (h s t hst htn).trans (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))

/-- The half-space bounds with a smaller constant imply those with a larger one, for `n ≥ 1`. -/
theorem HalfSpaceBound.mono {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)} {C C' : ℝ}
    {n : ℕ} (hn : 1 ≤ n) {q : EuclideanSpace ℝ (Fin d)} {x : ℕ → Site d}
    (h : HalfSpaceBound Ψ ε ξ C n q x) (hC : C ≤ C') : HalfSpaceBound Ψ ε ξ C' n q x := by
  intro k hk
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  refine (h k hk).trans (mul_le_mul_of_nonneg_right hC ?_)
  exact add_nonneg (Real.sqrt_nonneg _) hlog

/-! ## `lem:crossing` on the event of `eq:vector` -/

/-- **`lem:crossing` on the event of `eq:vector`.** For every `p > 0` there is a constant `C > 0`,
which does not depend on the field `ξ`, with the following two properties for every walk with
drift field `ξ` and every `n ≥ 2`. The event `VectorEvent` has a complement of probability at most
`C n^{-p}`; and at every sample point of the event, for every unit vector `u` and all integers
`0 ≤ s < t ≤ n` such that `u · ξ(X_j) ≥ 0` at every first departure time `j` with `s ≤ j < t`,
`u · (X_t - X_s) ≤ C √((t - s) log n)`, with the constant of the event. -/
theorem crossing_on_vector_event (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ (VectorEvent ε ξ C X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
        ∀ ω ∈ VectorEvent ε ξ C X n, ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
          ∀ s t : ℕ, s < t → t ≤ n →
          (∀ j : ℕ, s ≤ j → j < t → X j ω ∉ departureRange (fun i => X i ω) j →
            0 ≤ inner ℝ u (ξ (X j ω))) →
          inner ℝ u (toSpace (X t ω) - toSpace (X s ω)) ≤
            C * Real.sqrt (((t : ℝ) - s) * Real.log n) := by
  obtain ⟨C, hC, hvec⟩ := VectorBound.exists_driftCompensated_bound.{u} (by omega : 1 ≤ d)
    hε.le hp
  refine ⟨C, hC, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ⟨?_, ?_⟩⟩
  · have hξ' := ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
    refine le_trans (measure_mono fun ω hω => ?_) (hvec hξ' hξ0 hX n hn)
    simp only [VectorEvent, VectorIncrementBound, Set.mem_compl_iff, Set.mem_setOf_eq,
      not_forall, not_le] at hω ⊢
    obtain ⟨s, t, hst, htn, hlt⟩ := hω
    exact ⟨s, t, hst, htn, hlt⟩
  · intro ω hω u hu s t hst htn hdrift
    exact drift_crossing hε.le ξ (fun j => X j ω) n C hω u hu s t hst htn hdrift

/-! ## `lem:outer-crossing` on the events of `eq:vector` and `eq:linear-mart` -/

/-- **`lem:outer-crossing` with the constants of the events.** For every `p > 0` there is a constant
`C_ev > 0`, which does not depend on the field `ξ`, such that for every walk with drift field `ξ`
and every `n ≥ 2` the intersection of `VectorEvent` and `RadialHalfSpaceEvent` has a complement of
probability at most `C_ev n^{-p}`; and for every `α > 0` there is a constant `C > 0` with the
following property. Let `q` have length at most `Λ_Ψ`, and let `x` be a nearest-neighbour path from
the origin that satisfies the vector bound and the half-space bounds in the direction `q` with the
constant `C_ev`, at time `n ≥ 2`. Let `x_{j₀}` satisfy `q · x_j ≤ T := q · x_{j₀}` for
`0 ≤ j ≤ n`, and let `h > 0` be such that `q · ξ(x_j) ≥ α` for every `0 ≤ j ≤ n` with
`q · x_j > T - h`. Then every `b ≥ 0` satisfies `T ≤ max {T - h, b} + C L_b log n`, where `L_b` is
one plus the largest local time at a site `z` with `q · z ≥ b`. -/
theorem outer_crossing_on_events (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C_ev : ℝ, 0 < C_ev ∧
      (∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
          μ (VectorEvent ε ξ C_ev X n ∩ RadialHalfSpaceEvent Ψ ε ξ C_ev X n)ᶜ ≤
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
  obtain ⟨C_V, C_M, C_P, hC_V, hC_P, hev⟩ :=
    CoarseCapEvents.exists_capEvent_failure_bound.{u} hd hΨ hε hell hp
  set C_ev : ℝ := max (max C_V C_M) C_P with hC_ev
  have hCV : C_V ≤ C_ev := (le_max_left _ _).trans (le_max_left _ _)
  have hCM : C_M ≤ C_ev := (le_max_right _ _).trans (le_max_left _ _)
  have hCP : C_P ≤ C_ev := le_max_right _ _
  have hpos : 0 < C_ev := lt_of_lt_of_le hC_V hCV
  refine ⟨C_ev, hpos, ?_, fun α hα => ?_⟩
  · intro ξ hξ hξ0 Ω _ μ _ X hX n hn
    have hn1 : 1 ≤ n := by omega
    have hnp : 0 ≤ (n : ℝ) ^ (-p) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    refine le_trans (measure_mono ?_)
      ((hev ξ hξ hξ0 μ X hX n hn).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCP hnp)))
    intro ω hω
    simp only [Set.mem_setOf_eq]
    intro hcap
    apply hω
    obtain ⟨-, -, hvec, hmart⟩ := hcap
    exact ⟨VectorIncrementBound.mono hvec hCV,
      fun q hq => HalfSpaceBound.mono hn1 (hmart q hq) hCM⟩
  · exact outer_crossing_holds hd Ψ hΨ ε hε hell α hα C_ev hpos

/-! ## `lem:contact` on the event of Section 5.1 -/

/-- The event of Section 5.1 for a selection `P` of nearest points of `{Ψ ≤ r_n}` and the event
constants `K`: the sample points at which the seven estimates hold at time `n`, namely
Proposition 4.1, Lemma 3.1, `eq:vector`, `eq:localmart`, `eq:quadratic-coarse`, and
`eq:linear-mart` for the directions `Λ_Ψ u_x` with `|x| ≤ n` and for the directions
`Λ_Ψ u_{x - P x}` with `|x| ≤ n` and `Ψ(x) > r_n`. The event involves the path only up to time
`n`. -/
def sourceEvent {Ω : Type*} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (X : ℕ → Ω → Site d)
    (n : ℕ) : Set Ω :=
  {ω | Estimates7 Ψ ε ξ K P (fun j => X j ω) n}

/-- A selection of nearest points minimizes the Euclidean distance: for every `y` and every `v` with
`Ψ v ≤ r`, `‖y - P y‖ ≤ ‖y - v‖`. -/
theorem dist_le_of_isNearestSelection {r : ℝ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP : IsNearestSelection Ψ r P) (y : EuclideanSpace ℝ (Fin d))
    {v : EuclideanSpace ℝ (Fin d)} (hv : Ψ v ≤ r) : ‖y - P y‖ ≤ ‖y - v‖ := by
  have hvar := hP.2 y v hv
  have hsq : ‖y - P y‖ ^ 2 ≤ ‖y - v‖ ^ 2 := by
    have h1 : y - v = (y - P y) - (v - P y) := by abel
    have h2 : ‖y - v‖ ^ 2 =
        ‖y - P y‖ ^ 2 - 2 * inner ℝ (y - P y) (v - P y) + ‖v - P y‖ ^ 2 := by
      rw [h1, norm_sub_sq_real]
    nlinarith [sq_nonneg ‖v - P y‖]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

/-- A map `P` into `{Ψ ≤ r}` that sends every point to a point of `{Ψ ≤ r}` nearest to it in
Euclidean distance satisfies the variational inequality `⟨y - P y, v - P y⟩ ≤ 0` for all `v` with
`Ψ v ≤ r`, because `{Ψ ≤ r}` is convex: the characterization `IsNearestSelection` of a selection of
nearest points is equivalent to minimizing the Euclidean distance. -/
theorem isNearestSelection_of_dist_le (hΨ : IsNorm Ψ) {r : ℝ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hmem : ∀ y, Ψ (P y) ≤ r)
    (hmin : ∀ y v, Ψ v ≤ r → ‖y - P y‖ ≤ ‖y - v‖) : IsNearestSelection Ψ r P := by
  refine ⟨hmem, fun y v hv => ?_⟩
  by_contra hpos
  push Not at hpos
  set z := P y with hz
  set a : ℝ := inner ℝ (y - z) (v - z) with ha
  set b : ℝ := ‖v - z‖ ^ 2 with hb
  have hbpos : 0 < b := by
    refine pow_pos (norm_pos_iff.mpr fun h0 => ?_) 2
    rw [h0, inner_zero_right] at ha
    linarith
  set t : ℝ := min 1 (a / b) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos hpos hbpos)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htab : t * b ≤ a := by
    have : t ≤ a / b := min_le_right _ _
    rwa [le_div_iff₀ hbpos] at this
  have hw : Ψ (z + t • (v - z)) ≤ r := by
    have hdecomp : z + t • (v - z) = (1 - t) • z + t • v := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [hdecomp]
    refine (hΨ.add_le _ _).trans ?_
    rw [hΨ.smul, hΨ.smul, abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_pos ht0]
    nlinarith [hmem y, hv]
  have hle := hmin y _ hw
  have hsq : ‖y - z‖ ^ 2 ≤ ‖y - (z + t • (v - z))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hexp : ‖y - (z + t • (v - z))‖ ^ 2 = ‖y - z‖ ^ 2 - 2 * t * a + t ^ 2 * b := by
    have h1 : y - (z + t • (v - z)) = (y - z) - t • (v - z) := by abel
    rw [h1, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  nlinarith [mul_pos ht0 hpos]

/-- The selection of nearest points is unique: two selections of nearest points of `{Ψ ≤ r}` are
equal. -/
theorem nearestSelection_unique {r : ℝ}
    {P P' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP : IsNearestSelection Ψ r P) (hP' : IsNearestSelection Ψ r P') : P = P' :=
  funext fun y => nearest_unique (hP.1 y) (hP'.1 y) (hP.2 y) (hP'.2 y)

/-- The radius `r_n` of `eq:radius-norm` is nonnegative. -/
theorem scale_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℕ) : 0 ≤ scale d Ψ ε n := by
  unfold scale
  refine Real.rpow_nonneg (div_nonneg (by positivity) ?_) _
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hε.le)
    ENNReal.toReal_nonneg

/-- For a norm and a positive drift there is a selection of nearest points of `{Ψ ≤ r_n}`: a map
`P` with `Ψ (P y) ≤ r_n` and `⟨y - P y, v - P y⟩ ≤ 0` for all `y` and all `v` with `Ψ v ≤ r_n`. -/
theorem exists_nearestSelection_at_scale (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∃ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      IsNearestSelection Ψ (scale d Ψ ε n) P :=
  ⟨canonicalProjection Ψ (scale d Ψ ε n),
    canonicalProjection_isNearestSelection hΨ (scale_nonneg hε n)⟩

/-- The event of Section 5.1 does not depend on the selection of nearest points, because the nearest
point of a convex set is unique. -/
theorem sourceEvent_eq_of_nearestSelection {Ω : Type*} {ε : ℝ}
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {K : EventConstants} {X : ℕ → Ω → Site d} {n : ℕ}
    {P P' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hP : IsNearestSelection Ψ (scale d Ψ ε n) P) (hP' : IsNearestSelection Ψ (scale d Ψ ε n) P') :
    sourceEvent Ψ ε ξ K P X n = sourceEvent Ψ ε ξ K P' X n := by
  have hdir := projectionDirections_eq_of_nearest Ψ ε n hP hP'
  ext ω
  simp only [sourceEvent, Set.mem_setOf_eq, Estimates7, hdir]

/-- **`lem:contact` on the event of Section 5.1.** For every `p > 0` there are event constants `K`,
a constant `C > 0` and an integer `n₀ ≥ 2`, which do not depend on the field `ξ`, the probability
space, the walk or `n`, such that the following holds for every walk with drift field `ξ` whose
sample paths start at the origin and take unit steps, every `n ≥ n₀` and every selection `P` of
nearest points of `{Ψ ≤ r_n}`. The complement of the event of Section 5.1 has probability at most
`C n^{-p}`; and at every sample point of the event and every point `y₀` of the closure of the
complement of the cell set `D_n` with `Ψ(y₀) = inf_{y ∉ D_n} Ψ(y)`, the potential satisfies
`U_{D_n}(y₀) ≤ C r_n q_n`, with `q_n = √(log n / r_n)` for `d = 2` and `q_n = log n / r_n` for
`d ≥ 3`. -/
theorem contact_on_source_event (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ (K : EventConstants) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X →
        (∀ ω, PathTyping d (fun j => X j ω)) → ∀ n : ℕ, n₀ ≤ n →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          IsNearestSelection Ψ (scale d Ψ ε n) P →
          μ (sourceEvent Ψ ε ξ K P X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ sourceEvent Ψ ε ξ K P X n, ∀ y₀ : EuclideanSpace ℝ (Fin d),
            Ψ y₀ = normInnerRadius Ψ (fun j => X j ω) n →
            y₀ ∈ closure (cellSet (fun j => X j ω) n)ᶜ →
              normPotential d ε Ψ (cellSet (fun j => X j ω) n) y₀ ≤
                C * scale d Ψ ε n * contactRate d Ψ ε n := by
  obtain ⟨K, C, hC, n₀, hn₀, hmain⟩ := section5_localization hd hΨ hε hell hp
  refine ⟨K, C, hC, n₀, hn₀, fun ξ hξ hξ0 Ω _ μ _ X hX hlegal n hn P hP => ?_⟩
  have hPeq : sourceEvent Ψ ε ξ K P X n = E7 Ψ ε ξ K X n :=
    sourceEvent_eq_of_nearestSelection hP
      (canonicalProjection_isNearestSelection hΨ (scale_nonneg hε n))
  obtain ⟨⟨hprob, hcontact⟩, -⟩ := hmain ξ hξ hξ0 μ X hX n hn
  rw [hPeq]
  exact ⟨hprob, fun ω hω => hcontact ω hω (hlegal ω)⟩

/-- **`lem:contact` on the event of Section 5.1 for an arbitrary walk.** The statement of
`contact_on_source_event` without the typing of the sample paths: the complement of the event has
probability at most `C n^{-p}`, and almost every sample point of the event satisfies the contact
bound at every contact point. -/
theorem contact_on_source_event_almost_surely (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ (K : EventConstants) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          IsNearestSelection Ψ (scale d Ψ ε n) P →
          μ (sourceEvent Ψ ε ξ K P X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ᵐ ω ∂μ, ω ∈ sourceEvent Ψ ε ξ K P X n → ∀ y₀ : EuclideanSpace ℝ (Fin d),
            Ψ y₀ = normInnerRadius Ψ (fun j => X j ω) n →
            y₀ ∈ closure (cellSet (fun j => X j ω) n)ᶜ →
              normPotential d ε Ψ (cellSet (fun j => X j ω) n) y₀ ≤
                C * scale d Ψ ε n * contactRate d Ψ ε n := by
  obtain ⟨K, C, hC, n₀, hn₀, hmain⟩ := section5_localization hd hΨ hε hell hp
  refine ⟨K, C, hC, n₀, hn₀, fun ξ hξ hξ0 Ω _ μ _ X hX n hn P hP => ?_⟩
  have hPeq : sourceEvent Ψ ε ξ K P X n = E7 Ψ ε ξ K X n :=
    sourceEvent_eq_of_nearestSelection hP
      (canonicalProjection_isNearestSelection hΨ (scale_nonneg hε n))
  obtain ⟨⟨hprob, hcontact⟩, -⟩ := hmain ξ hξ hξ0 μ X hX n hn
  rw [hPeq]
  refine ⟨hprob, ?_⟩
  filter_upwards [ae_legal_of_isDriftCERW hX] with ω hlegal hω
  exact hcontact ω hω hlegal

end CERW.Support.RevisedPaper
