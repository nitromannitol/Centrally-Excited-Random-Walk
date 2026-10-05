import CERW.Support.Lower.SeparatedBracketsEvent
import CERW.Support.Norm.GaugeSection5Event
import CERW.Support.Norm.GaugeFiniteEvents

/-!
# The separated bracket bounds on the event of Section 5.1 at the nearest-point projection

`lem:separated-brackets` asserts, for the Euclidean norm and `0 < ε < 1/d`, that for all large `n`
the normalized brackets of the martingales `S^i` satisfy `c₀ ≤ ⟨S^i⟩_n ≤ C₀` and
`|⟨S^i, S^j⟩_n| ≤ C r_n^{-1/4}` on the event `Ω_n` of Section 5.1 with `p = 10`. The event `Ω_n` is
the set of sample points on which the seven estimates hold at time `n`, the second family of
half-space directions being those of the nearest-point projection `Π_n` onto the closed ball
`{|y| ≤ r_n}`.

This module proves the lemma for the event with the projection characterized by its variational
inequality (`GaugeFiniteEvents.projectionAtScale`), and with the contact estimate, the inner radius
estimate, the outer radius and the profile of the local times all produced from the seven
estimates:

* `adm_closedBall_one`, `gauge_closedBall_one`, `coarseScale_norm`, `projectionAtScale_spec_norm`:
  the closed unit ball is a compact convex body with the origin in its interior, its Minkowski
  functional is the Euclidean norm, the radius of the gauge event is the radius `r_n` of the paper,
  and the selected projection `Π_n` is the nearest-point map onto `{|y| ≤ r_n}`, characterized by
  membership and the variational inequality, and the only such map.
* `projectionAt_norm_eq`: on this carrier the projection `projectionAt` of `Section5Localization`,
  which has a fallback value outside it, is the selected nearest-point map.
* `brackets_of_estimates7_closed`: the deterministic implication with no premise on the contact
  estimate. For constants `E` of the seven estimates with `C_co, C_loc, C_mart ≥ 0`, a path from
  the origin with unit steps that satisfies the seven estimates at time `n` has the bracket bounds
  for all `n` beyond a threshold. The contact estimate is produced from the coarse bounds, the local
  estimate and the local martingale estimate of the event
  (`ContactEvent.contact_bound_of_event_inputs`).
* `separated_brackets_on_source_event`: the lemma for the walk with `IsCERW μ ε X`. The constants of
  the event, `c₀`, `C₀`, `C`, `C_p` and the threshold `n₀` are chosen before the probability space,
  the walk and `n`. For every `n ≥ n₀`: the event `Ω_n` depends on the path up to time `n` only
  (it is in `ℱ_n`) and is the event `E7` of `Section5Localization`; its complement has probability
  at most `C_p n^{-10}`; the sample points with an illegal path have probability zero; at every
  legal sample point of `Ω_n` the bracket bounds hold, in particular at every sample point of the
  typed event `ContactEvent.Section5Event`, which is the intersection of the legal sample points
  and `Ω_n` and agrees with `Ω_n` almost surely. The legality of the whole path is a condition on
  the future of the path and is not part of `Ω_n`.
  The same bounds hold at every sample point of the event of the legal carrier of `X`, a walk with
  the same law that is legal at every sample point and agrees with `X` almost surely; that walk is
  an auxiliary law-preserving realization, not the walk selected by the paper.

No bracket bound, contact estimate, profile or radius estimate and no map `Π_n` is assumed.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower.SeparatedBracketsCarrier

open CERW CERW.Support.Law CERW.Support.Lower.SeparatedBracketsEvent
  CERW.Support.Norm.ContactEvent CERW.Support.Norm.Section5Localization
  CERW.Support.Norm.GaugeSection5Event CERW.Support.Norm.GaugeFiniteEvents
  CERW.Support.Norm.GaugeCoarseVolume

variable {d : ℕ}

/-! ## The Euclidean norm as the gauge of the closed unit ball -/

/-- The closed unit ball is a compact convex set with the origin in its interior. -/
theorem adm_closedBall_one (d : ℕ) :
    CERW.Support.Norm.GaugeContactShape.Adm
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) where
  compact := isCompact_closedBall _ _
  convex := convex_closedBall _ _
  zero_mem := mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ one_pos)

/-- The Minkowski functional of the closed unit ball is the Euclidean norm. -/
theorem gauge_closedBall_one (d : ℕ) :
    gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) = fun v => ‖v‖ := by
  funext v
  rw [gauge_closedBall zero_le_one, div_one]

/-- The radius `r_n` of the gauge event at the Euclidean norm is the radius of the paper,
`r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}`, with `ω_d` the volume of the unit ball. -/
theorem coarseScale_norm (d : ℕ) (ε : ℝ) (n : ℕ) :
    coarseScale (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n =
      (((d : ℝ) + 1) * n / (2 * d * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^ ((1 : ℝ) / (d + 1)) := by
  unfold coarseScale
  rw [normBallVolume_norm]
  rfl

/-- A nearest-point map onto the gauge ball of the closed unit ball is a nearest-point map onto
the Euclidean ball `{|y| ≤ r}`: membership and the variational inequality. -/
theorem isNearestMap_closedBall_one_iff {r : ℝ}
    {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} :
    IsNearestMap (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) r P ↔
      (∀ z, ‖P z‖ ≤ r) ∧ ∀ z y, ‖y‖ ≤ r → inner ℝ (z - P z) (y - P z) ≤ 0 := by
  simp only [IsNearestMap, gauge_closedBall_one]

/-- **The projection `Π_n` of the source at the Euclidean norm.** For `d ≥ 2`, `ε > 0` and every
`n`, the projection `projectionAtScale` onto the closed ball of radius `r_n` maps into the ball,
satisfies the variational inequality `(z - Π_n z) · (y - Π_n z) ≤ 0` for every `y` of the ball, and
is the only map with these two properties. -/
theorem projectionAtScale_spec_norm (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    let r : ℝ := (((d : ℝ) + 1) * n / (2 * d * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^ ((1 : ℝ) / (d + 1))
    let P := projectionAtScale hd (adm_closedBall_one d) hε n
    ((∀ z, ‖P z‖ ≤ r) ∧ ∀ z y, ‖y‖ ≤ r → inner ℝ (z - P z) (y - P z) ≤ 0) ∧
      ∀ P' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), (∀ z, ‖P' z‖ ≤ r) →
        (∀ z y, ‖y‖ ≤ r → inner ℝ (z - P' z) (y - P' z) ≤ 0) → P' = P := by
  intro r P
  obtain ⟨h1, h2, -⟩ := projectionAtScale_spec hd (adm_closedBall_one d) hε n
  have hr : coarseScale (gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) ε n = r := by
    rw [gauge_closedBall_one, coarseScale_norm]
  rw [hr] at h1 h2
  refine ⟨isNearestMap_closedBall_one_iff.mp h1, fun P' hP'1 hP'2 => h2 P' ?_⟩
  exact isNearestMap_closedBall_one_iff.mpr ⟨hP'1, hP'2⟩

/-! ## The bracket bounds on the seven estimates, with the contact estimate produced -/

/-- **The bracket bounds on the seven estimates.** Let `d ≥ 2` and `0 < ε < 1/d`, and let `E` be
constants of the seven estimates of Section 5.1 with `C_co, C_loc, C_mart ≥ 0`. There are
`0 < c₀ ≤ C₀`, `C > 0` and `n₀`, depending only on `d`, `ε` and `E`, such that for every field `ξ`
of subgradients of the Euclidean norm with `ξ 0 = 0`, every map `P`, every path `Y` from the origin
with unit steps and every `n ≥ n₀`: if `Y` satisfies the seven estimates at time `n` then the
normalized brackets of `lem:separated-brackets` satisfy `c₀ ≤ ⟨S^i⟩_n ≤ C₀` and
`|⟨S^i, S^j⟩_n| ≤ C r_n^{-1/4}` for `i ≠ j`. The contact estimate is not a premise: it follows from
the coarse bounds, the local estimate and the local martingale estimate of the seven estimates
(`contact_bound_of_event_inputs`). -/
theorem brackets_of_estimates7_closed (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (E : EventConstants) (hCco : 0 ≤ E.C_co) (hCloc : 0 ≤ E.C_loc)
    (hCm : 0 ≤ E.C_mart) :
    ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ,
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (Y : ℕ → Site d) (n : ℕ),
        n₀ ≤ n → PathTyping d Y →
        Estimates7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E P Y n →
        BracketBounds hd ε c₀ C₀ C Y n := by
  obtain ⟨Cc, hCc, nc, hcontact⟩ := contact_bound_of_event_inputs
    @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential hd
    (isNorm_euclidean (d := d)) hε E.c_co E.C_co E.C_loc E.C_mart hCco hCloc hCm
  obtain ⟨c₀, C₀, C, hc₀, hcC, hC, nb, hbr⟩ := brackets_of_estimates7 hd hε hεd E hCc
  refine ⟨c₀, C₀, C, hc₀, hcC, hC, max nc nb, ?_⟩
  intro ξ hξ hξ0 P Y n hn hty hE
  have hnc : nc ≤ n := le_trans (le_max_left _ _) hn
  have hnb : nb ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hco, hloc, hvec, hlm, hquad, hrad, hproj⟩ := hE
  have hct := hcontact ξ hξ hξ0 Y n hnc hty hco hloc hlm
  exact hbr ξ hξ hξ0 P Y n hnb hty ⟨hco, hloc, hvec, hlm, hquad, hrad, hproj⟩ hct

/-! ## The event at the nearest-point projection, for the Euclidean norm -/

/-- **The source-locus equality for the Euclidean norm.** The projection `projectionAt` of
`Section5Localization`, which has the value `0` at the points where no point satisfies the
variational characterization, is the selected nearest-point map `projectionAtScale` onto
`{|y| ≤ r_n}` for every `n`: at the radius `r_n` every point has a solution of the characterization
(the value of the selected map), and the nearest point is unique. -/
theorem projectionAt_norm_eq (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    projectionAt (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n =
      projectionAtScale hd (adm_closedBall_one d) hε n := by
  have h := projectionAt_gauge_eq hd (adm_closedBall_one d) hε n
  rwa [gauge_closedBall_one] at h

/-- A sample point of the event at the selected projection has the seven estimates for the
Euclidean norm (the gauge of the closed unit ball is the norm). -/
theorem estimates7_of_mem_eventAtScale (hd : 2 ≤ d) {Ω : Type*} {ε : ℝ} (hε : 0 < ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} {E : EventConstants} {X : ℕ → Ω → Site d} {n : ℕ}
    {ω : Ω} (h : ω ∈ EventAtScale hd (adm_closedBall_one d) hε ξ E X n) :
    Estimates7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E
      (projectionAtScale hd (adm_closedBall_one d) hε n) (fun j => X j ω) n := by
  have h' : Estimates7 (gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) ε ξ E
      (projectionAtScale hd (adm_closedBall_one d) hε n) (fun j => X j ω) n := h
  rwa [gauge_closedBall_one] at h'

/-- The event at the selected projection is the literal event `E7` for the Euclidean norm. -/
theorem eventAtScale_eq_E7_norm (hd : 2 ≤ d) {Ω : Type*} {ε : ℝ} (hε : 0 < ε)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (E : EventConstants) (X : ℕ → Ω → Site d) (n : ℕ) :
    EventAtScale hd (adm_closedBall_one d) hε ξ E X n =
      E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E X n := by
  have h := eventAtScale_eq_E7 hd (adm_closedBall_one d) hε E X n (ξ := ξ)
  rwa [gauge_closedBall_one] at h

/-- The typed event of `ContactEvent` at the selected projection is the set of legal sample points
of the event, for the Euclidean norm. This is an equality of sets, by definition. -/
theorem section5Event_eq_legal_inter_norm (hd : 2 ≤ d) {Ω : Type*} {ε : ℝ} (hε : 0 < ε)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (E : EventConstants) (X : ℕ → Ω → Site d) (n : ℕ) :
    Section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E
        (projectionAtScale hd (adm_closedBall_one d) hε n) X n =
      legalSet X ∩ EventAtScale hd (adm_closedBall_one d) hε ξ E X n := by
  have h := section5Event_eq_legal_inter hd (adm_closedBall_one d) hε E X n (ξ := ξ)
  rwa [gauge_closedBall_one] at h

/-- The typed event and the event agree almost surely: the walk is almost surely legal. The
legality of the whole path depends on the future of the path, so the two sets are not equal as
sets. -/
theorem section5Event_ae_eq_norm (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ε : ℝ} (hε : 0 < ε) {ξ : Site d → EuclideanSpace ℝ (Fin d)} (E : EventConstants)
    {X : ℕ → Ω → Site d} (hX : IsDriftCERW μ ε ξ X) (n : ℕ) :
    Section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E
        (projectionAtScale hd (adm_closedBall_one d) hε n) X n =ᵐ[μ]
      EventAtScale hd (adm_closedBall_one d) hε ξ E X n := by
  have h := section5Event_ae_eq hd (adm_closedBall_one d) hε E hX n
  rwa [gauge_closedBall_one] at h

/-! ## The lemma on the event of Section 5.1 -/

/-- **`lem:separated-brackets` on the event `Ω_n` of Section 5.1 with `p = 10`, at the nearest-point
projection, for the centrally excited random walk.** Let `d ≥ 2` and `0 < ε < 1/d`. There are
constants `E` of the seven estimates (all positive), `0 < c₀ ≤ C₀`, `C > 0`, `C_p > 0` and a
threshold `n₀ ≥ 2`, chosen before the probability space, the walk and `n`, such that for every
probability space carrying a walk `X` with `IsCERW μ ε X` and every `n ≥ n₀`, with `r_n` the radius
of the paper, `ξ` the field `x ↦ x/|x|` of subgradients of the Euclidean norm, `Π_n` the selected
projection and `Ω_n` the event of the seven estimates at `Π_n`:

* `Π_n` maps into `{|y| ≤ r_n}`, satisfies `(z - Π_n z)·(y - Π_n z) ≤ 0` for every `y` with
  `|y| ≤ r_n`, and is the only map with these two properties;
* `Ω_n` belongs to `ℱ_n = σ(X_0, …, X_n)` (it depends on the path up to time `n` only) and is the
  event `E7` of `Section5Localization`; its complement has probability at most `C_p n^{-10}`;
* the sample points whose whole path is not a nearest-neighbour path from the origin have
  probability zero;
* the typed event `Section5Event` is `legalSet X ∩ Ω_n`, it agrees with `Ω_n` almost surely and its
  complement has probability at most `C_p n^{-10}`;
* at every legal sample point of `Ω_n`, in particular at every sample point of the typed event, the
  bounds `c₀ ≤ ⟨S^i⟩_n ≤ C₀` and `|⟨S^i, S^j⟩_n| ≤ C r_n^{-1/4}` for `i ≠ j`, `1 ≤ i, j ≤ m`, hold;
  they hold almost surely on `Ω_n`, and the set where they fail has probability at most
  `C_p n^{-10}`;
* the same holds at every sample point of the event of the legal carrier of `X`, a walk with the
  same law that is legal at every sample point and agrees with `X` almost surely.

The inclusion is that of the lemma: the bracket bounds hold on the event, not only outside a set of
small probability. -/
theorem separated_brackets_on_source_event (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) :
    ∃ (E : EventConstants) (c₀ C₀ C Cp : ℝ) (n₀ : ℕ),
      (0 < E.c_co ∧ 0 < E.C_co ∧ 0 < E.C_loc ∧ 0 < E.C_vec ∧ 0 < E.C_mart ∧ 0 < E.C_quad ∧
        0 < E.C_lin) ∧ 2 ≤ n₀ ∧ 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ 0 < Cp ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d) (hX : IsCERW μ ε X), ∀ n : ℕ, n₀ ≤ n →
        let r : ℝ := (((d : ℝ) + 1) * n / (2 * d * ε *
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^ ((1 : ℝ) / (d + 1))
        let ξ : Site d → EuclideanSpace ℝ (Fin d) := fun z => unitDir (toSpace z)
        let P := projectionAtScale hd (adm_closedBall_one d) hε n
        let Ωn : Set Ω := EventAtScale hd (adm_closedBall_one d) hε ξ E X n
        (((∀ z, ‖P z‖ ≤ r) ∧ ∀ z y, ‖y‖ ≤ r → inner ℝ (z - P z) (y - P z) ≤ 0) ∧
          ∀ P' : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), (∀ z, ‖P' z‖ ≤ r) →
            (∀ z y, ‖y‖ ≤ r → inner ℝ (z - P' z) (y - P' z) ≤ 0) → P' = P) ∧
        (MeasurableSet[pathFiltration hX.measurable n] Ωn ∧
          Ωn = E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E X n) ∧
        μ Ωnᶜ ≤ ENNReal.ofReal (Cp * (n : ℝ) ^ (-(10 : ℝ))) ∧
        μ (legalSet X)ᶜ = 0 ∧
        (Section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E P X n =
            legalSet X ∩ Ωn ∧
          Section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E P X n =ᵐ[μ] Ωn ∧
          μ (Section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E P X n)ᶜ ≤
            ENNReal.ofReal (Cp * (n : ℝ) ^ (-(10 : ℝ)))) ∧
        ((∀ ω ∈ Ωn, ω ∈ legalSet X → BracketBounds hd ε c₀ C₀ C (fun j => X j ω) n) ∧
          (∀ ω ∈ Section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E P X n,
            BracketBounds hd ε c₀ C₀ C (fun j => X j ω) n) ∧
          (∀ᵐ ω ∂μ, ω ∈ Ωn → BracketBounds hd ε c₀ C₀ C (fun j => X j ω) n) ∧
          μ {ω | ¬ BracketBounds hd ε c₀ C₀ C (fun j => X j ω) n} ≤
            ENNReal.ofReal (Cp * (n : ℝ) ^ (-(10 : ℝ)))) ∧
        (μ (EventAtScale hd (adm_closedBall_one d) hε ξ E
              (legalCarrier (by omega : 1 ≤ d) X) n)ᶜ ≤
            ENNReal.ofReal (Cp * (n : ℝ) ^ (-(10 : ℝ))) ∧
          ∀ ω ∈ EventAtScale hd (adm_closedBall_one d) hε ξ E
              (legalCarrier (by omega : 1 ≤ d) X) n,
            BracketBounds hd ε c₀ C₀ C (fun j => legalCarrier (by omega : 1 ≤ d) X j ω) n) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, hsub, hξ0, -⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := d) hεd
  have hsubK : ∀ x : Site d, x ≠ 0 →
      IsSubgradient (gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) (toSpace x)
        (unitDir (toSpace x)) := by
    intro x hx
    rw [gauge_closedBall_one]
    exact hsub x hx
  have hell : ∀ i : Fin d,
      ε * gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (coordVec i) < 1 / (d : ℝ) ∧
      ε * gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) (-coordVec i) <
        1 / (d : ℝ) := by
    intro i
    rw [gauge_closedBall_one]
    constructor <;> simpa [coordVec] using hεd
  obtain ⟨E, Cp, hEpos, hCp, hmain⟩ :=
    gauge_section5_event.{u} hd (adm_closedBall_one d) hε hell (p := 10) (by norm_num)
  obtain ⟨c₀, C₀, C, hc₀, hcC, hC, nb, hbr⟩ := brackets_of_estimates7_closed hd hε hεd E
    hEpos.2.1.le hEpos.2.2.1.le hEpos.2.2.2.2.1.le
  refine ⟨E, c₀, C₀, C, Cp, max 2 nb, hEpos, le_max_left _ _, hc₀, hcC, hC, hCp, ?_⟩
  intro Ω _ μ _ X hX n hn r ξ P Ωn
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnb : nb ≤ n := le_trans (le_max_right _ _) hn
  have hXd : IsDriftCERW μ ε ξ X := (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).1 hX
  obtain ⟨hevt, hprobn⟩ := hmain ξ hsubK hξ0 μ X hXd
  obtain ⟨-, hprob⟩ := hprobn n hn2
  have hbrk : ∀ ω ∈ Ωn, ω ∈ legalSet X → BracketBounds hd ε c₀ C₀ C (fun j => X j ω) n :=
    fun ω hω hL => hbr ξ hsub hξ0 P (fun j => X j ω) n hnb hL
      (estimates7_of_mem_eventAtScale hd hε hω)
  have hlegal : μ (legalSet X)ᶜ = 0 := mem_ae_iff.mp (ae_legal_of_isDriftCERW hXd)
  have hty : Section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E P X n =
      legalSet X ∩ Ωn := section5Event_eq_legal_inter_norm hd hε ξ E X n
  have haeq : Section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ E P X n =ᵐ[μ] Ωn :=
    section5Event_ae_eq_norm hd hε E hXd n
  refine ⟨projectionAtScale_spec_norm hd hε n, ⟨(hevt n).1, eventAtScale_eq_E7_norm hd hε ξ E X n⟩,
    hprob, hlegal, ⟨hty, haeq, ?_⟩, ⟨hbrk, ?_, ?_, ?_⟩, ?_⟩
  · rw [measure_congr haeq.compl]
    exact hprob
  · intro ω hω
    rw [hty] at hω
    exact hbrk ω hω.2 hω.1
  · filter_upwards [ae_legal_of_isDriftCERW hXd] with ω hL hω
    exact hbrk ω hω hL
  · calc μ {ω | ¬ BracketBounds hd ε c₀ C₀ C (fun j => X j ω) n}
        ≤ μ (Ωnᶜ ∪ (legalSet X)ᶜ) := by
          refine measure_mono fun ω hω => ?_
          by_contra hcon
          simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
          exact hω (hbrk ω hcon.1 hcon.2)
      _ ≤ μ Ωnᶜ + μ (legalSet X)ᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Cp * (n : ℝ) ^ (-(10 : ℝ))) := by
          rw [hlegal, add_zero]
          exact hprob
  · have hXc : IsDriftCERW μ ε ξ (legalCarrier hd1 X) := isDriftCERW_legalCarrier hd1 hXd
    obtain ⟨-, hprobc⟩ := (hmain ξ hsubK hξ0 μ (legalCarrier hd1 X) hXc).2 n hn2
    refine ⟨hprobc, fun ω hω => ?_⟩
    exact hbr ξ hsub hξ0 P (fun j => legalCarrier hd1 X j ω) n hnb (legalCarrier_typing hd1 X ω)
      (estimates7_of_mem_eventAtScale hd hε hω)

end CERW.Support.Lower.SeparatedBracketsCarrier
