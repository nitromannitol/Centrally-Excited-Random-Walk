import CERW.Support.Norm.GaugeFiniteEvents
import CERW.Support.Norm.GaugeCoarseClosed
import CERW.Support.Norm.GaugePointwise
import CERW.Support.Norm.Section5Localization

/-!
# The event of Section 5.1 for the gauge of a convex body

The event of Section 5.1 of the paper is the set of sample points on which seven estimates hold at
time `n`: the bounds of Proposition 4.1, the estimates of Lemma 3.1, the vector bound `eq:vector`,
the local martingale bounds `eq:localmart` at the lattice targets `|y| ≤ 3n`, the quadratic bound
`eq:quadratic-coarse`, and the half-space martingale bounds `eq:linear-mart` for the radial
directions `Λ_ψ u_x`, `0 < |x| ≤ n`, and for the directions `Λ_ψ u_{x - Π_n x}`, `|x| ≤ n`,
`ψ(x) > r_n`, of the nearest-point projection `Π_n` onto `{ψ ≤ r_n}` at the deterministic radius
`r_n`. This module proves, for the literal Minkowski functional `ψ = gauge K` of a compact convex
set `K` with the origin in its interior (not necessarily symmetric):

* `exists_estimates7_failure_bound`: constants of the event `Estimates7` and `C`, chosen before the
  field of subgradients, the probability space, the walk, `n` and the projection, such that for
  every `n ≥ 2` and every map `P` fixed before the walk, the set of sample points at which the
  seven estimates hold is in `ℱ_n = σ(X_0, …, X_n)` and its complement has probability at most
  `C n^{-p}`. The producers are the proved ones: `GaugeCoarseClosed.gauge_coarse_bounds`,
  `GaugeLocalTime.gauge_local_time_potential`, the vector bound, the local martingale bound for the
  lattice kernel, the quadratic bound, and the half-space bounds for finite families
  (`exists_gauge_linear_martingale_bound`).
* `EventAtScale`: the event at the selected nearest-point map `Π_n = projectionAtScale`, a
  map characterized and unique on the carrier of compact convex bodies with the origin in the
  interior (`GaugeFiniteEvents`); `gauge_section5_event` combines the failure bound with its
  measurability.
* `eventAtScale_eq_E7`: at these objects the event equals `Section5Localization.E7`, whose
  projection is defined by the variational characterization with a fallback outside the carrier;
  on the carrier it is the selected map (`projectionAt_gauge_eq`).
* `section5Event_eq_legal_inter`, `section5Event_ae_eq`: the typed event of `ContactEvent` is the
  legal sample points of the event, and agrees with it almost surely.
* `projectionDirections_eq_sourceProjectionDirections` and `Estimates7.toSource`: the directions of
  the seven estimates are the directions of the source of `GaugeFiniteEvents`, and a path in the
  event has the estimates `SourceProjectionEstimates`, which give the hypotheses of the rates
  theorem `GaugeContactShape.Rates.ShapeRatesOfEvents`.
* `exists_pointwise_of_localMart` and `shape_rates_of_estimates7`: on a legal path of the event,
  the fine pointwise local time bound follows from the local martingale bound
  (`GaugePointwise`), and the three rates of the limit shape hold in the regime of the rates
  theorem.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeSection5Event

open CERW CERW.Support.Law CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugeCoarseVolume
open CERW.Support.Norm.ContactEvent (EventConstants CoarseBounds LocalBounds VectorEstimate
  LocalMartEstimate QuadraticEstimate LinearEstimate radialDirections PathTyping)
open CERW.Support.Norm.Section5Localization (Estimates7 E7 projectionAt estimates7_congr)
open CERW.Support.Norm.GaugeFiniteEvents (PrefixDetermined IsNearestMap projectionAtScale
  nearestMapAt)

variable {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-! ## The seven estimates depend only on the path up to time `n` -/

/-- The seven estimates at time `n` depend only on the path up to time `n`
(`Section5Localization.estimates7_congr`). -/
theorem estimates7_prefixDetermined (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (E : EventConstants)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    PrefixDetermined n (fun x => Estimates7 Ψ ε ξ E P x n) := fun _ _ h =>
  estimates7_congr Ψ ε ξ E P n h

/-! ## The producers, assembled -/

/-- A set covered by six events of small probability has small probability. -/
private lemma measure_le_of_subset_union_six {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ E₃ E₄ E₅ E₆ : Set Ω} {a₁ a₂ a₃ a₄ a₅ a₆ C : ℝ}
    (hS : S ⊆ E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂)
    (h₃ : μ E₃ ≤ ENNReal.ofReal a₃) (h₄ : μ E₄ ≤ ENNReal.ofReal a₄)
    (h₅ : μ E₅ ≤ ENNReal.ofReal a₅) (h₆ : μ E₆ ≤ ENNReal.ofReal a₆)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄) (ha₅ : 0 ≤ a₅) (ha₆ : 0 ≤ a₆)
    (hC : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ≤ C) : μ S ≤ ENNReal.ofReal C := by
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆) := measure_mono hS
    _ ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅) + μ E₆ := measure_union_le _ _
    _ ≤ (μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄) + μ E₅) + μ E₆ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ((μ (E₁ ∪ E₂ ∪ E₃) + μ E₄) + μ E₅) + μ E₆ :=
        add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ (((μ (E₁ ∪ E₂) + μ E₃) + μ E₄) + μ E₅) + μ E₆ :=
        add_le_add (add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ ((((μ E₁ + μ E₂) + μ E₃) + μ E₄) + μ E₅) + μ E₆ :=
        add_le_add (add_le_add (add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl)
          le_rfl) le_rfl
    _ ≤ ((((ENNReal.ofReal a₁ + ENNReal.ofReal a₂) + ENNReal.ofReal a₃) + ENNReal.ofReal a₄) +
          ENNReal.ofReal a₅) + ENNReal.ofReal a₆ := by gcongr
    _ = ENNReal.ofReal (a₁ + a₂ + a₃ + a₄ + a₅ + a₆) := by
        rw [ENNReal.ofReal_add (by positivity) ha₆, ENNReal.ofReal_add (by positivity) ha₅,
          ENNReal.ofReal_add (by positivity) ha₄, ENNReal.ofReal_add (add_nonneg ha₁ ha₂) ha₃,
          ENNReal.ofReal_add ha₁ ha₂]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-- The count of the directions in the union bound: at most `2 (2n+1)^d` directions and `n + 1`
levels cost at most `4 · 3^d n^{-p}` when each pair has probability `n^{-(p+d+1)}`. -/
private lemma union_count_arith {C p : ℝ} (hC : 0 ≤ C) (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : c ≤ 2 * (2 * (n : ℝ) + 1) ^ d) :
    C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1)) ≤ (C * 4 * 3 ^ d) * (n : ℝ) ^ (-p) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hrp : 0 ≤ (n : ℝ) ^ (-(p + d + 1)) := Real.rpow_nonneg hnpos.le _
  have h1 : (2 * (n : ℝ) + 1) ^ d ≤ (3 * n) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have h2 : c * ((n : ℝ) + 1) ≤ 2 * (3 ^ d * (n : ℝ) ^ d) * (2 * n) := by
    calc c * ((n : ℝ) + 1) ≤ (2 * (3 * (n : ℝ)) ^ d) * (2 * n) :=
          mul_le_mul (hc.trans (mul_le_mul_of_nonneg_left h1 (by norm_num)))
            (by linarith) (by positivity) (by positivity)
      _ = 2 * (3 ^ d * (n : ℝ) ^ d) * (2 * n) := by rw [mul_pow]
  have h3 : (n : ℝ) ^ (-(p + d + 1)) = (n : ℝ) ^ (-p) * ((n : ℝ) ^ (d + 1))⁻¹ := by
    rw [show -(p + d + 1) = -p + -((d + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hnpos, Real.rpow_neg hnpos.le ((d + 1 : ℕ) : ℝ), Real.rpow_natCast]
  have h4 : (n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹ = 1 := by
    rw [← pow_succ]
    exact mul_inv_cancel₀ (pow_ne_zero _ hnpos.ne')
  calc C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1))
      ≤ C * (2 * (3 ^ d * (n : ℝ) ^ d) * (2 * n)) * (n : ℝ) ^ (-(p + d + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC) hrp
    _ = (C * 4 * 3 ^ d) * (n : ℝ) ^ (-p) * ((n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹) := by
        rw [h3]
        ring
    _ = (C * 4 * 3 ^ d) * (n : ℝ) ^ (-p) := by rw [h4, mul_one]

/-- `log (n + 2) ≤ 2 log n` for `n ≥ 2`. -/
private lemma log_add_two_le' {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n :=
  CERW.Support.Norm.ContactAssembly.log_add_two_le hn

/-- **The failure probability of the seven estimates of Section 5.1 for the gauge.** Let `K` be a
compact convex set with the origin in its interior, `d ≥ 2`, `ε > 0` with
`ε max {ψ(e_i), ψ(-e_i)} < 1/d`, and `p > 0`. There are constants `E` of the seven estimates and
`C`, chosen before every subgradient selection `ξ`, every probability space carrying a walk
`IsDriftCERW μ ε ξ X`, every `n` and every map `P` fixed before the walk, such that for every
`n ≥ 2` (no larger threshold) the set of sample points on which `Estimates7 (gauge K) ε ξ E P` holds
at time `n` is in `ℱ_n = σ(X_0, …, X_n)` and has complement of probability at most `C n^{-p}`.
The constants of the event are positive. There is no hypothesis on the legality of the path (it
holds almost surely) and none on `P`. -/
theorem exists_estimates7_failure_bound (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {ε : ℝ}
    (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ (E : EventConstants) (C : ℝ), (0 < E.c_co ∧ 0 < E.C_co ∧ 0 < E.C_loc ∧ 0 < E.C_vec ∧
        0 < E.C_mart ∧ 0 < E.C_quad ∧ 0 < E.C_lin) ∧ 0 < C ∧
      ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X), ∀ n : ℕ, 2 ≤ n →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        MeasurableSet[pathFiltration hX.measurable n]
          {ω | Estimates7 (gauge K) ε ξ E P (fun j => X j ω) n} ∧
        μ {ω | ¬ Estimates7 (gauge K) ε ξ E P (fun j => X j ω) n} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  have hΛ : 0 ≤ normMax (gauge K) := normMax_gauge_nonneg K
  obtain ⟨c_co, C_co, hcc, hCc, hco⟩ :=
    GaugeCoarseClosed.gauge_coarse_bounds.{u} hd hΨ.compact hΨ.convex hΨ.zero_mem ε hε hell p hp
  obtain ⟨C_loc, hCl, hloc⟩ :=
    GaugeLocalTime.gauge_local_time_potential.{u} hd hΨ.compact hΨ.convex hΨ.zero_mem ε hε
      hell p hp
  obtain ⟨C_V, hCV, hvec⟩ :=
    CERW.Support.Norm.VectorBound.exists_driftCompensated_bound.{u} hd1 hε.le hp
  obtain ⟨h, hKF⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hgrad⟩ := hKF.gradBound
  obtain ⟨C_lm, hClm, hlm⟩ :=
    CERW.Support.Norm.ContactDynkin.exists_drift_local_mart hd hε.le hgrad hp
  obtain ⟨C_LM, hCLM, hLM⟩ :=
    exists_gauge_linear_martingale_bound hd hε hell (p := p + d + 1) (by positivity)
  obtain ⟨C_Q, hCQ, hQ⟩ := CERW.Support.Norm.ContactEvent.exists_quadratic_producer.{u} hd hε hp
  refine ⟨⟨c_co, C_co, C_loc, C_V, 2 * C_lm, C_Q, C_LM⟩,
    C_co + C_loc + C_V + C_lm + C_Q + C_LM * 4 * 3 ^ d,
    ⟨hcc, hCc, hCl, hCV, by positivity, hCQ, hCLM⟩, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn2 P
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnR.le _
  have hξ' := drift_coord_bound_gauge hε.le hell hξ hξ0
  refine ⟨GaugeFiniteEvents.measurableSet_setOf_filtration hX.measurable
    (estimates7_prefixDetermined (gauge K) ε ξ _ P n), ?_⟩
  have hE_co : μ {ω | ¬ CoarseBounds d (gauge K) ε c_co C_co (fun j => X j ω) n} ≤
      ENNReal.ofReal (C_co * (n : ℝ) ^ (-p)) := hco ξ hξ hξ0 μ X hX n hn2
  have hE_loc : μ {ω | ¬ LocalBounds d (gauge K) ε C_loc (fun j => X j ω) n} ≤
      ENNReal.ofReal (C_loc * (n : ℝ) ^ (-p)) := hloc ξ hξ hξ0 μ X hX n hn2
  have hE_vec := hvec hξ' hξ0 hX n hn2
  have hE_lm := hlm hξ' hX n hn2
  have hE_quad : μ {ω | ¬ QuadraticEstimate d ε ξ C_Q (fun j => X j ω) n} ≤
      ENNReal.ofReal (C_Q * (n : ℝ) ^ (-p)) := hQ hξ' hξ0 hX n hn2
  have hQnorm : ∀ q ∈ radialDirections d (gauge K) n ∪
      CERW.Support.Norm.ContactEvent.projectionDirections d (gauge K) ε n P,
      ‖q‖ ≤ normMax (gauge K) := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact CERW.Support.Norm.ContactEvent.norm_le_normMax_of_mem_radialDirections hΛ hq
    · exact CERW.Support.Norm.ContactEvent.norm_le_normMax_of_mem_projectionDirections hΛ hq
  have hcard : (((radialDirections d (gauge K) n ∪
      CERW.Support.Norm.ContactEvent.projectionDirections d (gauge K) ε n P).card : ℕ) : ℝ) ≤
      2 * (2 * (n : ℝ) + 1) ^ d := by
    obtain ⟨h1, h2⟩ := CERW.Support.Norm.ContactEvent.card_directions_le (gauge K) ε n P
    have := Finset.card_union_le (radialDirections d (gauge K) n)
      (CERW.Support.Norm.ContactEvent.projectionDirections d (gauge K) ε n P)
    have h3 : (((radialDirections d (gauge K) n ∪
        CERW.Support.Norm.ContactEvent.projectionDirections d (gauge K) ε n P).card : ℕ) : ℝ) ≤
        ((radialDirections d (gauge K) n).card : ℝ) +
          ((CERW.Support.Norm.ContactEvent.projectionDirections d (gauge K) ε n P).card : ℝ) := by
      exact_mod_cast this
    linarith
  have hE_lin := (hLM hξ hξ0 hX n hn2 (radialDirections d (gauge K) n ∪
      CERW.Support.Norm.ContactEvent.projectionDirections d (gauge K) ε n P) hQnorm).trans
    (ENNReal.ofReal_le_ofReal (union_count_arith (p := p) hCLM.le d (by omega) hcard))
  refine measure_le_of_subset_union_six
    (E₁ := {ω | ¬ CoarseBounds d (gauge K) ε c_co C_co (fun j => X j ω) n})
    (E₂ := {ω | ¬ LocalBounds d (gauge K) ε C_loc (fun j => X j ω) n})
    (E₃ := {ω | ∃ s t : ℕ, s < t ∧ t ≤ n ∧ C_V * Real.sqrt (((t : ℝ) - s) * Real.log n) <
      ‖CERW.Support.Norm.VectorBound.driftCompensated ε ξ (fun j => X j ω) t -
        CERW.Support.Norm.VectorBound.driftCompensated ε ξ (fun j => X j ω) s‖})
    (E₄ := {ω | ∃ y : Site d, euclidNorm y ≤ 3 * n ∧
      C_lm * (Real.sqrt ((∑ j ∈ Finset.range n,
          (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log (n + 2)) +
        Real.log (n + 2)) <
      |CERW.Support.Drift.driftDynkin ε ξ (fun z => latticeKernel d (z - y)) X n ω|})
    (E₅ := {ω | ¬ QuadraticEstimate d ε ξ C_Q (fun j => X j ω) n})
    (E₆ := {ω | ∃ q ∈ radialDirections d (gauge K) n ∪
        CERW.Support.Norm.ContactEvent.projectionDirections d (gauge K) ε n P, ∃ k : ℕ,
      k ≤ n ∧ C_LM * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * normMax (gauge K) - normMax (gauge K) <
              inner ℝ q (toSpace z)),
          (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
        |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax (gauge K)) 0)
          (fun j => X j ω) n|})
    ?_ hE_co hE_loc hE_vec hE_lm hE_quad hE_lin (mul_nonneg hCc.le hnp) (mul_nonneg hCl.le hnp)
    (mul_nonneg hCV.le hnp) (mul_nonneg hClm.le hnp) (mul_nonneg hCQ.le hnp)
    (mul_nonneg (by positivity) hnp) (le_of_eq (by ring))
  intro ω hω
  by_contra hnot
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq] at hnot
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hnot
  apply hω
  unfold Estimates7
  refine ⟨not_not.mp h1, not_not.mp h2, ?_, ?_, not_not.mp h5, ?_, ?_⟩
  · intro s t hst htn
    exact not_lt.mp fun hlt => h3 ⟨s, t, hst, htn, hlt⟩
  · intro y hy
    have h4y := not_lt.mp fun hlt => h4 ⟨y, hy, hlt⟩
    rw [CERW.Support.Drift.dynkinMart_driftStepProb_eq_driftDynkin hd1 ε ξ _ X n ω]
    have hW : (∑ j ∈ Finset.range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) =
        ∑ x ∈ departureRange (fun j => X j ω) n,
          (localTime (fun j => X j ω) n x : ℝ) *
            (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)) :=
      CERW.Support.LocalTime.sum_range_eq_sum_localTime (fun j => X j ω) n
        (fun x => (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ)))
    have hS0 : 0 ≤ ∑ j ∈ Finset.range n, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) :=
      Finset.sum_nonneg fun j _ =>
        Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (X j ω - y)]) _
    have hL0 := CERW.Support.Norm.ContactAssembly.log_pos_of_two_le hn2
    have hL := log_add_two_le' hn2
    have hsq : Real.sqrt ((∑ j ∈ Finset.range n,
        (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) ≤
        2 * Real.sqrt ((∑ j ∈ Finset.range n,
          (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) := by
      have h4' : (∑ j ∈ Finset.range n,
          (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2) ≤
          2 ^ 2 * ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) := by
        have := mul_le_mul_of_nonneg_left hL hS0
        nlinarith [mul_nonneg hS0 hL0.le]
      calc _ ≤ Real.sqrt (2 ^ 2 * ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n)) :=
            Real.sqrt_le_sqrt h4'
        _ = 2 * Real.sqrt _ := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    show _ ≤ 2 * C_lm * (Real.sqrt ((∑ x ∈ departureRange (fun j => X j ω) n,
        (localTime (fun j => X j ω) n x : ℝ) *
          (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) + Real.log n)
    rw [← hW]
    calc _ ≤ C_lm * (Real.sqrt ((∑ j ∈ Finset.range n,
          (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
            Real.log ((n : ℝ) + 2)) := h4y
      _ ≤ C_lm * (2 * Real.sqrt ((∑ j ∈ Finset.range n,
          (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) +
            2 * Real.log n) :=
          mul_le_mul_of_nonneg_left (add_le_add hsq hL) hClm.le
      _ = 2 * C_lm * (Real.sqrt ((∑ j ∈ Finset.range n,
          (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) +
            Real.log n) := by ring
  · intro q hq k hk
    exact not_lt.mp fun hlt => h6 ⟨q, Finset.mem_union_left _ hq, k, hk, hlt⟩
  · intro q hq k hk
    exact not_lt.mp fun hlt => h6 ⟨q, Finset.mem_union_right _ hq, k, hk, hlt⟩

/-! ## The event at the selected nearest-point projection -/

section Carrier

variable {Ω : Type*} {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}

/-- **The event of Section 5.1 for the gauge.** The set of sample points at which the seven
estimates hold at time `n`, with the projection `Π_n` onto `{ψ ≤ r_n}` selected at the
deterministic radius `r_n` (`projectionAtScale`), for a compact convex body `K` with the origin in
its interior. It involves the path only up to time `n` and no condition on its legality. -/
def EventAtScale (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) (hε : 0 < ε)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (E : EventConstants) (X : ℕ → Ω → Site d)
    (n : ℕ) : Set Ω :=
  {ω | Estimates7 (gauge K) ε ξ E (projectionAtScale hd hΨ hε n) (fun j => X j ω) n}

/-- The event is the preimage of a set of finite paths under the past path `(X_0, …, X_n)`. -/
theorem eventAtScale_eq_preimage (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K)
    (hε : 0 < ε) (E : EventConstants) (X : ℕ → Ω → Site d) (n : ℕ) :
    EventAtScale hd hΨ hε ξ E X n = pastPath X n ⁻¹'
      {p | Estimates7 (gauge K) ε ξ E (projectionAtScale hd hΨ hε n) (extendPath p) n} :=
  GaugeFiniteEvents.setOf_eq_preimage_pastPath
    (estimates7_prefixDetermined (gauge K) ε ξ E (projectionAtScale hd hΨ hε n) n) X

/-- The event is the countable union of the cylinders `{X_j = p_j, j ≤ n}` of the finite paths
`p` that satisfy the seven estimates. -/
theorem eventAtScale_eq_iUnion_cylinders (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K)
    (hε : 0 < ε) (E : EventConstants) (X : ℕ → Ω → Site d) (n : ℕ) :
    EventAtScale hd hΨ hε ξ E X n =
      ⋃ p ∈ {p : (i : Finset.Iic n) → Site d |
          Estimates7 (gauge K) ε ξ E (projectionAtScale hd hΨ hε n) (extendPath p) n},
        {ω | ∀ j ≤ n, X j ω = extendPath p j} :=
  GaugeFiniteEvents.setOf_eq_iUnion_cylinders
    (estimates7_prefixDetermined (gauge K) ε ξ E (projectionAtScale hd hΨ hε n) n) X

/-- **The event belongs to `ℱ_n = σ(X_0, …, X_n)`.** -/
theorem measurableSet_eventAtScale_filtration [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) (hε : 0 < ε) (E : EventConstants)
    (hX : ∀ j, Measurable (X j)) (n : ℕ) :
    MeasurableSet[pathFiltration hX n] (EventAtScale hd hΨ hε ξ E X n) :=
  GaugeFiniteEvents.measurableSet_setOf_filtration hX
    (estimates7_prefixDetermined (gauge K) ε ξ E (projectionAtScale hd hΨ hε n) n)

/-- The event is measurable. -/
theorem measurableSet_eventAtScale [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) (hε : 0 < ε) (E : EventConstants)
    (hX : ∀ j, Measurable (X j)) (n : ℕ) :
    MeasurableSet (EventAtScale hd hΨ hε ξ E X n) :=
  GaugeFiniteEvents.measurableSet_setOf hX
    (estimates7_prefixDetermined (gauge K) ε ξ E (projectionAtScale hd hΨ hε n) n)

/-! ## The selected projection is the projection of `Section5Localization` on the carrier -/

/-- On the carrier, the projection `canonicalProjection (gauge K) r` of `Section5Localization`,
defined by the variational characterization with the value `0` where no point satisfies it, is the
selected nearest-point map: for every point the characterization has a solution, namely the value
of the selected map, and nearest points are unique. -/
theorem canonicalProjection_gauge_eq (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {r : ℝ}
    (hr : 0 ≤ r) :
    CERW.Support.Norm.Section5Localization.canonicalProjection (gauge K) r =
      nearestMapAt (by omega) hΨ hr := by
  funext y
  have hspec := GaugeFiniteEvents.nearestMapAt_spec (by omega : 1 ≤ d) hΨ hr
  have hex : ∃ z, gauge K z ≤ r ∧ ∀ v, gauge K v ≤ r → inner ℝ (y - z) (v - z) ≤ 0 :=
    ⟨nearestMapAt (by omega) hΨ hr y, hspec.1 y, hspec.2 y⟩
  classical
  rw [CERW.Support.Norm.Section5Localization.canonicalProjection, dif_pos hex]
  exact CERW.Support.Norm.ContactEvent.nearest_unique (Ψ := gauge K) hex.choose_spec.1
    (hspec.1 y) hex.choose_spec.2 (hspec.2 y)

/-- The projection `Π_n` of `Section5Localization.E7` at the gauge is the selected projection at the
deterministic radius. -/
theorem projectionAt_gauge_eq (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) (hε : 0 < ε)
    (n : ℕ) : projectionAt (gauge K) ε n = projectionAtScale hd hΨ hε n :=
  canonicalProjection_gauge_eq hd hΨ (GaugeFiniteEvents.coarseScale_nonneg_of_adm hΨ hε n)

/-- **The event equals `Section5Localization.E7`** at the gauge of a compact convex body: the
event with the selected, characterized projection is the literal event `E7`, whose projection is
the fallback-defined `projectionAt`. -/
theorem eventAtScale_eq_E7 (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) (hε : 0 < ε)
    (E : EventConstants) (X : ℕ → Ω → Site d) (n : ℕ) :
    EventAtScale hd hΨ hε ξ E X n = E7 (gauge K) ε ξ E X n := by
  unfold EventAtScale E7
  rw [projectionAt_gauge_eq hd hΨ hε n]

/-- **The event of Section 5.1 for the gauge, with its failure bound.** For the gauge of a compact
convex body with the origin in its interior, `ε` with `ε ψ(±e_i) < 1/d` and `p > 0`, there are
positive constants `E` of the event and `C`, chosen before the field of subgradients, the
probability space, the walk and `n`, such that for every walk: the events `E_n`, `n ≥ 0`, belong to
`ℱ_n` and equal `E7`; and for every `n ≥ 2` the map `Π_n` is the nearest-point map onto
`{ψ ≤ r_n}` and the complement of `E_n` has probability at most `C n^{-p}`. -/
theorem gauge_section5_event (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ (E : EventConstants) (C : ℝ), (0 < E.c_co ∧ 0 < E.C_co ∧ 0 < E.C_loc ∧ 0 < E.C_vec ∧
        0 < E.C_mart ∧ 0 < E.C_quad ∧ 0 < E.C_lin) ∧ 0 < C ∧
      ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d) (hX : IsDriftCERW μ ε ξ X),
        (∀ n : ℕ, MeasurableSet[pathFiltration hX.measurable n]
            (EventAtScale hd hΨ hε ξ E X n) ∧
          EventAtScale hd hΨ hε ξ E X n = E7 (gauge K) ε ξ E X n) ∧
        ∀ n : ℕ, 2 ≤ n →
          IsNearestMap K (coarseScale (gauge K) ε n) (projectionAtScale hd hΨ hε n) ∧
          μ (EventAtScale hd hΨ hε ξ E X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨E, C, hE, hC, hev⟩ := exists_estimates7_failure_bound.{u} hd hΨ hε hell hp
  refine ⟨E, C, hE, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX
  refine ⟨fun n => ⟨measurableSet_eventAtScale_filtration hd hΨ hε E hX.measurable n,
    eventAtScale_eq_E7 hd hΨ hε E X n⟩, ?_⟩
  intro n hn
  exact ⟨(GaugeFiniteEvents.projectionAtScale_spec hd hΨ hε n).1,
    (hev ξ hξ hξ0 μ X hX n hn (projectionAtScale hd hΨ hε n)).2⟩

/-- The event of `ContactEvent` with the typing of the model, at the selected projection, is the
legal sample points of the event. -/
theorem section5Event_eq_legal_inter (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) (hε : 0 < ε)
    (E : EventConstants) (X : ℕ → Ω → Site d) (n : ℕ) :
    CERW.Support.Norm.ContactEvent.Section5Event (gauge K) ε ξ E (projectionAtScale hd hΨ hε n)
        X n =
      CERW.Support.Norm.Section5Localization.legalSet X ∩ EventAtScale hd hΨ hε ξ E X n :=
  Set.ext fun _ => Iff.rfl

/-- **Almost-sure transport to the typed event.** Under `IsDriftCERW` the typed event and the
event agree almost surely, since the walk is almost surely legal
(`Section5Localization.ae_legal_of_isDriftCERW`); their complements have the same probability. -/
theorem section5Event_ae_eq [MeasurableSpace Ω] {μ : Measure Ω} (hd : 2 ≤ d)
    (hΨ : GaugeContactShape.Adm K) (hε : 0 < ε) (E : EventConstants) {X : ℕ → Ω → Site d}
    (hX : IsDriftCERW μ ε ξ X) (n : ℕ) :
    CERW.Support.Norm.ContactEvent.Section5Event (gauge K) ε ξ E (projectionAtScale hd hΨ hε n)
        X n =ᵐ[μ] EventAtScale hd hΨ hε ξ E X n := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [CERW.Support.Norm.Section5Localization.ae_legal_of_isDriftCERW hX] with ω hω
  exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩

/-- The complement of the typed event has the same probability as that of the event. -/
theorem measure_section5Event_compl [MeasurableSpace Ω] {μ : Measure Ω} (hd : 2 ≤ d)
    (hΨ : GaugeContactShape.Adm K) (hε : 0 < ε) (E : EventConstants) {X : ℕ → Ω → Site d}
    (hX : IsDriftCERW μ ε ξ X) (n : ℕ) :
    μ (CERW.Support.Norm.ContactEvent.Section5Event (gauge K) ε ξ E
        (projectionAtScale hd hΨ hε n) X n)ᶜ = μ (EventAtScale hd hΨ hε ξ E X n)ᶜ :=
  measure_congr (section5Event_ae_eq hd hΨ hε E hX n).compl

end Carrier

/-! ## The directions of the seven estimates are those of the source -/

open scoped Classical in
/-- The family `projectionDirections` of the seven estimates (`Λ_ψ u_{x - Π_n x}` for the sites
`|x| ≤ n` with `ψ(x) > r_n`) is the family `sourceProjectionDirections` of the finite events. -/
theorem projectionDirections_eq_sourceProjectionDirections (ε : ℝ) (n : ℕ)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    CERW.Support.Norm.ContactEvent.projectionDirections d (gauge K) ε n P =
      GaugeFiniteEvents.sourceProjectionDirections K P (coarseScale (gauge K) ε n) n := by
  have hf : ∀ a : Site d, (normMax (gauge K) / ‖toSpace a - P (toSpace a)‖) •
      (toSpace a - P (toSpace a)) =
      GaugeContactShape.Projection.projDir K P (toSpace a) := fun a => by
    rw [GaugeContactShape.Projection.projDir, div_eq_mul_inv, mul_smul]
  ext q
  simp only [CERW.Support.Norm.ContactEvent.projectionDirections,
    GaugeFiniteEvents.sourceProjectionDirections, Finset.mem_image, Finset.mem_filter, hf,
    CERW.Support.Norm.ContactEvent.scale, coarseScale]

/-- **A path of the event has the estimates of the source.** The compensated-path bound and the
half-space bounds in the directions of the source, with the constant `max {C_vec, C_lin}`, are
implied by the seven estimates; they give the hypotheses of the rates theorem
`GaugeContactShape.Rates.ShapeRatesOfEvents`. -/
theorem Estimates7.toSource {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {E : EventConstants} {P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {n : ℕ}
    {x : ℕ → Site d} (h : Estimates7 (gauge K) ε ξ E P x n) :
    GaugeFiniteEvents.SourceProjectionEstimates K ε ξ (max E.C_vec E.C_lin) P
      (coarseScale (gauge K) ε n) n x := by
  obtain ⟨-, -, hvec, -, -, -, hlin⟩ := h
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  refine ⟨fun s t hst htn => (hvec s t hst htn).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)), ?_⟩
  intro q hq k hk
  rw [← projectionDirections_eq_sourceProjectionDirections] at hq
  exact (hlin q hq k hk).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (add_nonneg (Real.sqrt_nonneg _) hlog))

/-! ## The fine pointwise bound and the rates on the event -/

/-- **The fine pointwise bound on a legal path with the local martingale bound.** Let `K` be a
compact convex set with the origin in its interior, `ε > 0` and `C_m ≥ 0`. There is `C_F ≥ 0` such
that for every subgradient selection `ξ` and every path from the origin with unit steps that
satisfies the local martingale bounds `LocalMartEstimate` with constant `C_m` at time `n ≥ 1`, the
local time at every lattice site `|y| ≤ 3n` is within
`C_F (√(Σ_{j<n} (1 + |x_j - y|)^{2-2d} log (n + 2)) + log (n + 2))` of the potential of the cell
set. The deterministic decomposition is
`GaugePointwise.gauge_abs_localTime_sub_normPotential_add_driftDynkin_le`. -/
theorem exists_pointwise_of_localMart (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {ε : ℝ}
    (hε : 0 < ε) {C_m : ℝ} (hC_m : 0 ≤ C_m) :
    ∃ C_F : ℝ, 0 ≤ C_F ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (x : ℕ → Site d) (n : ℕ), x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) → 1 ≤ n →
        LocalMartEstimate d ε ξ C_m x n →
        ∀ y : Site d, euclidNorm y ≤ 3 * n →
          |(localTime x n y : ℝ) - normPotential d ε (gauge K) (cellSet x n) (toSpace y)| ≤
            C_F * (Real.sqrt ((∑ j ∈ Finset.range n,
              (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
              Real.log ((n : ℝ) + 2)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨h, hKF⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨C_pt, hCpt, hpt⟩ :=
    GaugePointwise.gauge_abs_localTime_sub_normPotential_add_driftDynkin_le hd hΨ.compact
      hΨ.convex hΨ.zero_mem hKF
  refine ⟨C_pt * (1 + ε) + C_m, add_nonneg (mul_nonneg hCpt (by linarith)) hC_m, ?_⟩
  intro ξ hξ hξ0 x n hx0 hstep hn hmart y hy
  have hpath : ∀ j, euclidNorm (x j) ≤ j :=
    CERW.Support.Occupation.euclidNorm_le_of_steps x hx0 hstep
  have h1 := hpt ε hε.le ξ hξ hξ0 (Ω := Unit) (fun j _ => x j) () hx0 hpath n hn y hy
  have hD : CERW.Support.Drift.driftDynkin ε ξ (fun z => latticeKernel d (z - y))
      (fun j _ => x j) n () =
      dynkinMart (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y)) x n :=
    (CERW.Support.Drift.dynkinMart_driftStepProb_eq_driftDynkin hd1 ε ξ _
      (fun j _ => x j) n ()).symm
  rw [hD] at h1
  have hM := hmart y hy
  have hW : (∑ j ∈ Finset.range n, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) =
      ∑ z ∈ departureRange x n, (localTime x n z : ℝ) *
        (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)) :=
    CERW.Support.LocalTime.sum_range_eq_sum_localTime x n
      (fun z => (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ)))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : Real.log n ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log hnpos (by linarith)
  have hS0 : 0 ≤ ∑ j ∈ Finset.range n, (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ)) :=
    Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (by linarith [LatticeProb.euclidNorm_nonneg (x j - y)]) _
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hsq : Real.sqrt ((∑ z ∈ departureRange x n, (localTime x n z : ℝ) *
      (1 + euclidNorm (z - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n) ≤
      Real.sqrt ((∑ j ∈ Finset.range n,
        (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) := by
    rw [← hW]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hS0)
  have hM' : |dynkinMart (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y)) x n| ≤
      C_m * (Real.sqrt ((∑ j ∈ Finset.range n,
        (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
        Real.log ((n : ℝ) + 2)) :=
    hM.trans (mul_le_mul_of_nonneg_left (add_le_add hsq hlog) hC_m)
  have hlogp : 0 ≤ Real.log ((n : ℝ) + 2) := hlog0.trans hlog
  have hsqrt0 : 0 ≤ Real.sqrt ((∑ j ∈ Finset.range n,
      (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) :=
    Real.sqrt_nonneg _
  have hdiff : (localTime x n y : ℝ) - normPotential d ε (gauge K) (cellSet x n) (toSpace y) =
      ((localTime x n y : ℝ) - normPotential d ε (gauge K) (cellSet x n) (toSpace y) +
        dynkinMart (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y)) x n) -
      dynkinMart (driftStepProb d ε ξ) (fun z => latticeKernel d (z - y)) x n := by ring
  rw [hdiff]
  refine (abs_sub _ _).trans ?_
  have hcoef : 0 ≤ C_pt * (1 + ε) := mul_nonneg hCpt (by linarith)
  calc _ ≤ C_pt * (1 + ε) * Real.log ((n : ℝ) + 2) +
        C_m * (Real.sqrt ((∑ j ∈ Finset.range n,
          (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
          Real.log ((n : ℝ) + 2)) := add_le_add h1 hM'
    _ ≤ (C_pt * (1 + ε) + C_m) * (Real.sqrt ((∑ j ∈ Finset.range n,
          (1 + euclidNorm (x j - y)) ^ (2 - 2 * (d : ℝ))) * Real.log ((n : ℝ) + 2)) +
          Real.log ((n : ℝ) + 2)) := by
        nlinarith [mul_nonneg hcoef hsqrt0]

/-- **The rates of the limit shape on the event of Section 5.1.** For the gauge of a compact convex
body with the origin in its interior, `ε` with `ε ψ(±e_i) < 1/d` and constants `E` of the event with
`C_co, C_loc, C_vec, C_lin > 0` and `C_mart ≥ 0`, there are `C`, `r₀` and `M` such that for every
subgradient selection and every legal path `x` of the event `Estimates7` at time `n`, with the
selected projection `Π_n` onto `{ψ ≤ r_n}`, in the regime `r₀ ≤ r_n`, `1 ≤ log n` and
`M (log n)^{d+5} ≤ r_n`: the inner radius is `r_n + O(r_n q_n^{1/2})`, the outer radius is
`r_n + O(r_n q_n^{1/(d+1)} log n)` and the local times are within `O(r_n q_n^{1/(d+1)})` of
`2 d ε (r_n - ψ)_+`. The hypotheses of the rates theorem `ShapeRatesOfEvents` are supplied by the
seven estimates: the coarse bounds, Lemma 3.1, the vector bound, the fine pointwise bound
(`exists_pointwise_of_localMart`) and the half-space bounds in the directions of `Π_n`. -/
theorem shape_rates_of_estimates7 (hd : 2 ≤ d) (hΨ : GaugeContactShape.Adm K) {ε : ℝ}
    (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {E : EventConstants} (hC_co : 0 < E.C_co) (hC_loc : 0 < E.C_loc) (hC_vec : 0 < E.C_vec)
    (hC_mart : 0 ≤ E.C_mart) :
    ∃ C r₀ M : ℝ, 0 < C ∧ 0 < M ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (x : ℕ → Site d) (n : ℕ), PathTyping d x → r₀ ≤ coarseScale (gauge K) ε n →
        1 ≤ Real.log n → M * Real.log n ^ (d + 5) ≤ coarseScale (gauge K) ε n →
        Estimates7 (gauge K) ε ξ E (projectionAtScale hd hΨ hε n) x n →
        ∀ r : ℝ, r = coarseScale (gauge K) ε n →
          |normInnerRadius (gauge K) x n - r| ≤
              C * (r * GaugeContactShape.Rates.rateQ d r (Real.log n) ^ ((1 : ℝ) / 2)) ∧
            normMaxRadius (gauge K) x n - r ≤
              C * (r * GaugeContactShape.Rates.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)) *
                Real.log n) ∧
            ∀ y : EuclideanSpace ℝ (Fin d),
              |cellLocalTime x n y - 2 * d * ε * max (r - gauge K y) 0| ≤
                C * (r * GaugeContactShape.Rates.rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
  obtain ⟨C_F, hCF0, hpt⟩ := exists_pointwise_of_localMart hd hΨ hε hC_mart
  obtain ⟨C, r₀, M, hC, hM, hmain⟩ := GaugeContactShape.Rates.gauge_shape_rates_of_events hd hΨ hε
    hell hC_co hCF0 hC_loc (C₁ := max E.C_vec E.C_lin) (lt_max_of_lt_left hC_vec)
  refine ⟨C, r₀, M, hC, hM, ?_⟩
  intro ξ hξ hξ0 x n hty hr₀ hℓ hMr hE r hr
  subst hr
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have h0 : n = 0 := by omega
    subst h0
    rw [Nat.cast_zero, Real.log_zero] at hℓ
    norm_num at hℓ
  have hsrc := Estimates7.toSource hE
  obtain ⟨hco, hloc, -, hlm, -, -, -⟩ := hE
  obtain ⟨hP, -, hrel⟩ := GaugeFiniteEvents.projectionAtScale_spec hd hΨ hε n
  exact hmain ξ hξ hξ0 x n _ hty.1 hty.2 hr₀ hℓ hMr hrel hco.2.2.2.2.2 hco.2.2.2.1
    (hpt ξ hξ hξ0 x n hty.1 hty.2 hn1 hlm) hloc.2.2 (projectionAtScale hd hΨ hε n) hP.1 hP.2
    hsrc.compensated (fun j hj hrj k hk => hsrc.martingale hty hj hrj hk)

end CERW.Support.Norm.GaugeSection5Event
