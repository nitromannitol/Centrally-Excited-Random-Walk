import CERW.Support.RevisedPaperCarrier

/-!
# The contact estimate on the event of Section 5.1 with positive constants

`Section5Event` is the event of Section 5.1 with the typing of the model, and
`ContactEvent.contact_on_section5Event` bounds its complement and the contact estimate on it, with
constants of the event chosen from the proved producers of its constituents before the field, the
probability space, the walk and `n`. That theorem exports only the positivity of the common constant
`C`. Proposition 4.1 and the other constituents of the source have positive constants, which the
proof of the theorem obtains from the producers.

* `section5Event_positive` is `ContactEvent.contact_on_section5Event` with the producers applied,
  proved by the same argument, in which the positivity of the seven constants of the event, each
  given by its producer, is part of the conclusion: `K : PositiveEventConstants`.
* `contact_on_source_carrier` is `lem:contact` on `SourceEvent`: the constants are positive, the
  projection is the nearest-point projection of the carrier `SourceSetting.Projection`, and, for
  every walk law, the contact estimate holds at almost every sample point of the event. The legality
  of the sample paths, namely `X 0 ω = 0` and unit steps, holds almost surely for the walk
  (`ae_legal_of_isDriftCERW`) and is not assumed.
* `contact_on_source_carrier_typed` is the statement for a walk all of whose sample paths are legal,
  with this typing as an explicit hypothesis, at every sample point of the event.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site euclidNorm)

namespace CERW.Support.RevisedPaper

open CERW CERW.Support.Statements CERW.Support.Norm.ContactShared CERW.Support.Norm.ContactAssembly
  CERW.Support.Norm.ContactEvent CERW.Support.Norm.Section5Localization

variable {d : ℕ}

/-! ## Two arithmetic and measure lemmas of the union bound -/

/-- The arithmetic of the union bound: at most `2 (2n + 1)^d` directions and `n + 1` thresholds cost
at most `4 · 3^d n^{-p}` when each pair has probability `n^{-(p + d + 1)}`. -/
private theorem union_count_arith {C p : ℝ} (hC : 0 ≤ C) (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
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
/-- A set covered by six events of small probability and a null event has small probability. -/
private theorem measure_le_of_subset_union_six {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ E₃ E₄ E₅ E₆ N : Set Ω} {a₁ a₂ a₃ a₄ a₅ a₆ C : ℝ}
    (hS : S ⊆ E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆ ∪ N)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂)
    (h₃ : μ E₃ ≤ ENNReal.ofReal a₃) (h₄ : μ E₄ ≤ ENNReal.ofReal a₄)
    (h₅ : μ E₅ ≤ ENNReal.ofReal a₅) (h₆ : μ E₆ ≤ ENNReal.ofReal a₆) (hN : μ N = 0)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄) (ha₅ : 0 ≤ a₅) (ha₆ : 0 ≤ a₆)
    (hC : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ ≤ C) : μ S ≤ ENNReal.ofReal C := by
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆ ∪ N) := measure_mono hS
    _ ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆) + μ N := measure_union_le _ _
    _ = μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆) := by rw [hN, add_zero]
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


/-! ## The event of Section 5.1 with positive constants -/

/-- The composition of the producers, with the positivity of the constants of the event in the
conclusion. -/
private theorem section5Event_positive_of_producers (hcoarse : norm_coarse_bounds.{u})
    (hlocal : norm_local_time_potential.{u}) (hlin : LinearProducer.{u})
    (hgeom : norm_potential_geometry) (hball : norm_ball_potential) (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ (K : PositiveEventConstants) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          μ (Section5Event Ψ ε ξ K.toEventConstants P X n)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ Section5Event Ψ ε ξ K.toEventConstants P X n, ∀ y₀ : EuclideanSpace ℝ (Fin d),
            Ψ y₀ = normInnerRadius Ψ (fun j => X j ω) n →
            y₀ ∈ closure (cellSet (fun j => X j ω) n)ᶜ →
            normPotential d ε Ψ (cellSet (fun j => X j ω) n) y₀ ≤
              C * scale d Ψ ε n * contactRate d Ψ ε n := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc0, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 (normMin_le_normMax hd1 hΨ)
  obtain ⟨c_co, C_co, hcc, hCc, hco⟩ := hcoarse hd Ψ hΨ ε hε hell p hp
  obtain ⟨C_loc, hCl, hloc⟩ := hlocal hd Ψ hΨ ε hε hell p hp
  obtain ⟨C_V, hCV, hvec⟩ :=
    CERW.Support.Norm.VectorBound.exists_driftCompensated_bound hd1 hε.le hp
  obtain ⟨h, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts_latticeKernel hd
  obtain ⟨Cg, hgrad⟩ := hK.gradBound
  obtain ⟨C_lm, hClm, hlm⟩ :=
    CERW.Support.Norm.ContactDynkin.exists_drift_local_mart hd hε.le hgrad hp
  obtain ⟨C_LM, hCLM, hLM⟩ := hlin hd hΨ hε hell (p := p + d + 1) (by positivity)
  obtain ⟨C_Q, hCQ, hQ⟩ := exists_quadratic_producer.{u} hd hε hp
  obtain ⟨C₀, hC₀, n₁, hdet⟩ := contact_bound_of_event_inputs hgeom hball hd hΨ hε c_co C_co
    C_loc (2 * C_lm) hCc.le hCl.le (by positivity)
  refine ⟨⟨⟨c_co, C_co, C_loc, C_V, 2 * C_lm, C_Q, C_LM⟩, hcc, hCc, hCl, hCV,
      by positivity, hCQ, hCLM⟩,
    max (C_co + C_loc + C_V + C_lm + C_Q + C_LM * 4 * 3 ^ d) C₀,
    lt_max_of_lt_left (by positivity), max n₁ 2, le_max_right _ _, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn P
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnR.le _
  have hξ' := drift_coord_le hΨ hε hell hξ hξ0
  have hN : μ {ω | ¬ PathTyping d (fun j => X j ω)} = 0 := by
    have hpath : ∀ᵐ ω ∂μ, PathTyping d (fun j => X j ω) := by
      have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
        rw [ae_iff]
        exact hX.start
      filter_upwards [h0, ae_all_iff.mpr
        (CERW.Support.Drift.ae_sub_mem_unitSteps_drift hd1 hε.le hξ' hX)] with ω h0 hs
      exact ⟨h0, hs⟩
    exact ae_iff.mp hpath
  have hE_co : μ {ω | ¬ CoarseBounds d Ψ ε c_co C_co (fun j => X j ω) n} ≤
      ENNReal.ofReal (C_co * (n : ℝ) ^ (-p)) := hco ξ hξ hξ0 μ X hX n hn2
  have hE_loc : μ {ω | ¬ LocalBounds d Ψ ε C_loc (fun j => X j ω) n} ≤
      ENNReal.ofReal (C_loc * (n : ℝ) ^ (-p)) := hloc ξ hξ hξ0 μ X hX n hn2
  have hE_vec := hvec hξ' hξ0 hX n hn2
  have hE_lm := hlm hξ' hX n hn2
  have hE_quad : μ {ω | ¬ QuadraticEstimate d ε ξ C_Q (fun j => X j ω) n} ≤
      ENNReal.ofReal (C_Q * (n : ℝ) ^ (-p)) := hQ hξ' hξ0 hX n hn2
  have hQnorm : ∀ q ∈ radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P,
      ‖q‖ ≤ normMax Ψ := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact norm_le_normMax_of_mem_radialDirections hΛ.le hq
    · exact norm_le_normMax_of_mem_projectionDirections hΛ.le hq
  have hcard : (((radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P).card : ℕ) : ℝ) ≤
      2 * (2 * (n : ℝ) + 1) ^ d := by
    obtain ⟨h1, h2⟩ := card_directions_le Ψ ε n P
    have := Finset.card_union_le (radialDirections d Ψ n) (projectionDirections d Ψ ε n P)
    have h3 : (((radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P).card : ℕ) : ℝ) ≤
        ((radialDirections d Ψ n).card : ℝ) + ((projectionDirections d Ψ ε n P).card : ℝ) := by
      exact_mod_cast this
    linarith
  have hE_lin := (hLM hξ hξ0 hX n hn2 (radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P)
    hQnorm).trans (ENNReal.ofReal_le_ofReal
      (union_count_arith (p := p) hCLM.le d (by omega) hcard))
  refine ⟨?_, ?_⟩
  · refine measure_le_of_subset_union_six (E₁ := {ω | ¬ CoarseBounds d Ψ ε c_co C_co
      (fun j => X j ω) n}) (E₂ := {ω | ¬ LocalBounds d Ψ ε C_loc (fun j => X j ω) n})
      (E₃ := {ω | ∃ s t : ℕ, s < t ∧ t ≤ n ∧ C_V * Real.sqrt (((t : ℝ) - s) * Real.log n) <
        ‖CERW.Support.Norm.VectorBound.driftCompensated ε ξ (fun j => X j ω) t -
          CERW.Support.Norm.VectorBound.driftCompensated ε ξ (fun j => X j ω) s‖})
      (E₄ := {ω | ∃ y : Site d, euclidNorm y ≤ 3 * n ∧
        C_lm * (Real.sqrt ((∑ j ∈ Finset.range n,
            (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * Real.log (n + 2)) +
          Real.log (n + 2)) <
        |CERW.Support.Drift.driftDynkin ε ξ (fun z => latticeKernel d (z - y)) X n ω|})
      (E₅ := {ω | ¬ QuadraticEstimate d ε ξ C_Q (fun j => X j ω) n})
      (E₆ := {ω | ∃ q ∈ radialDirections d Ψ n ∪ projectionDirections d Ψ ε n P, ∃ k : ℕ,
        k ≤ n ∧ C_LM * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
              (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
            (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
          |dynkinMart (driftStepProb d ε ξ)
            (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) (fun j => X j ω) n|})
      (N := {ω | ¬ PathTyping d (fun j => X j ω)}) ?_ hE_co hE_loc hE_vec hE_lm hE_quad
      hE_lin hN (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) ?_
    · intro ω hω
      by_contra hnot
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq] at hnot
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hnot
      apply hω
      simp only [Section5Event, Set.mem_setOf_eq]
      refine ⟨not_not.mp h7, not_not.mp h1, not_not.mp h2, ?_, ?_, not_not.mp h5, ?_, ?_⟩
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
        have hL0 := log_pos_of_two_le hn2
        have hL := log_add_two_le hn2
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
    · calc C_co * (n : ℝ) ^ (-p) + C_loc * (n : ℝ) ^ (-p) + C_V * (n : ℝ) ^ (-p) +
          C_lm * (n : ℝ) ^ (-p) + C_Q * (n : ℝ) ^ (-p) + C_LM * 4 * 3 ^ d * (n : ℝ) ^ (-p)
          = (C_co + C_loc + C_V + C_lm + C_Q + C_LM * 4 * 3 ^ d) * (n : ℝ) ^ (-p) := by ring
        _ ≤ max (C_co + C_loc + C_V + C_lm + C_Q + C_LM * 4 * 3 ^ d) C₀ * (n : ℝ) ^ (-p) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hnp
  · intro ω hω y₀ hy₀ hcl
    obtain ⟨hty, hcoω, hlocω, -, hlmω, -, -, -⟩ := hω
    have hU := hdet ξ hξ hξ0 (fun j => X j ω) n hn1 hty hcoω hlocω hlmω y₀ hy₀ hcl
    have hV : 0 < normBallVolume Ψ := normBallVolume_pos' hd1 hΨ
    have hr : 0 < scale d Ψ ε n := by
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      exact Real.rpow_pos_of_pos (by positivity) _
    have hq : 0 ≤ contactRate d Ψ ε n := by
      unfold contactRate
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact div_nonneg (log_pos_of_two_le hn2).le hr.le
    exact hU.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le) hq)


/-- **The contact estimate on the event of Section 5.1, with positive constants.** Let `Ψ` be a norm
in dimension `d ≥ 2`, `ε > 0` with `ε Ψ(e_i) < 1/d`, and `p > 0`. There are positive constants `K`
of the event, a constant `C > 0` and an integer `n₀ ≥ 2`, depending only on `d`, `Ψ`, `ε` and `p`,
such that for every field `ξ` of subgradients with `ξ 0 = 0`, every probability space carrying the
walk with drift field `ξ`, every `n ≥ n₀` and every map `P` fixed before the walk, the complement of
`Section5Event` has probability at most `C n^{-p}`, and on `Section5Event` every contact point
satisfies the contact estimate. No producer is a hypothesis: Proposition 4.1, Lemma 3.1, the vector
bound, the local martingale bound of the lattice kernel, the quadratic bound and the half-space
bounds are the proved ones. -/
theorem section5Event_positive (hd : 2 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ (K : PositiveEventConstants) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          μ (Section5Event Ψ ε ξ K.toEventConstants P X n)ᶜ ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ Section5Event Ψ ε ξ K.toEventConstants P X n, ∀ y₀ : EuclideanSpace ℝ (Fin d),
            Ψ y₀ = normInnerRadius Ψ (fun j => X j ω) n →
            y₀ ∈ closure (cellSet (fun j => X j ω) n)ᶜ →
            normPotential d ε Ψ (cellSet (fun j => X j ω) n) y₀ ≤
              C * scale d Ψ ε n * contactRate d Ψ ε n :=
  section5Event_positive_of_producers.{u}
    (CERW.Support.Norm.norm_coarse_bounds_of
      (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds)
      CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing)
    (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds)
    (fun {_} hd {_} hΨ {_} hε hell {_} hp =>
      CERW.Support.Norm.exists_linear_martingale_bound hd hΨ hε hell hp)
    @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential
    hd hΨ hε hell hp

/-! ## `lem:contact` on the carrier -/

/-- **`lem:contact` on the event of Section 5.1, on its carrier.** Let `S` be a norm `Ψ` and a drift
`ε` with `ε Ψ(e_i) < 1/d`, in dimension `d ≥ 2`, and `p > 0`. There are positive constants `K` of
the event, a constant `C > 0` and an integer `n₀ ≥ 2`, which do not depend on the field `ξ`, the
probability space, the walk, `n` or the projection, such that the following holds for every walk
with drift field `ξ` (a field of subgradients of `Ψ` with `ξ 0 = 0`), every `n ≥ n₀` and the
nearest-point projection `P` onto `{Ψ ≤ r_n}`. The complement of `SourceEvent` has probability at
most `C n^{-p}`; and almost every sample point of the event has the contact estimate
`U_{D_n}(y₀) ≤ C r_n q_n` at every point `y₀` of the closure of the complement of the cell set `D_n`
with `Ψ(y₀) = inf_{y ∉ D_n} Ψ(y)`. -/
theorem contact_on_source_carrier (hd : 2 ≤ d) (S : SourceSetting d) {p : ℝ} (hp : 0 < p) :
    ∃ (K : PositiveEventConstants) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient S.Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ S.ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        ∀ P : S.Projection n,
          μ (SourceEvent S ξ K n P X)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ᵐ ω ∂μ, ω ∈ SourceEvent S ξ K n P X → ∀ y₀ : EuclideanSpace ℝ (Fin d),
            S.Ψ y₀ = normInnerRadius S.Ψ (fun j => X j ω) n →
            y₀ ∈ closure (cellSet (fun j => X j ω) n)ᶜ →
              normPotential d S.ε S.Ψ (cellSet (fun j => X j ω) n) y₀ ≤
                C * S.radius n * contactRate d S.Ψ S.ε n := by
  obtain ⟨K, C, hC, n₀, hn₀, hmain⟩ :=
    section5Event_positive hd S.isNorm S.ε_pos S.ellipticity hp
  refine ⟨K, C, hC, n₀, hn₀, fun ξ hξ hξ0 Ω _ μ _ X hX n hn P => ?_⟩
  obtain ⟨hprob, hcontact⟩ := hmain ξ hξ hξ0 μ X hX n hn P.toFun
  refine ⟨le_trans (measure_mono ?_) hprob, ?_⟩
  · intro ω hω h5
    exact hω h5.2
  · filter_upwards [ae_legal_of_isDriftCERW hX] with ω hlegal hω y₀ h1 h2
    have h5 : ω ∈ Section5Event S.Ψ S.ε ξ K.toEventConstants P.toFun X n := by
      rw [section5Event_eq]
      exact ⟨hlegal, hω⟩
    exact hcontact ω h5 y₀ h1 h2

/-- **`lem:contact` on the event of Section 5.1, on its carrier, for a walk with legal sample
paths.** The statement of `contact_on_source_carrier` for a walk all of whose sample paths start at
the origin and take unit steps, at every sample point of the event. -/
theorem contact_on_source_carrier_typed (hd : 2 ≤ d) (S : SourceSetting d) {p : ℝ} (hp : 0 < p) :
    ∃ (K : PositiveEventConstants) (C : ℝ), 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient S.Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ S.ε ξ X →
        (∀ ω, PathTyping d (fun j => X j ω)) → ∀ n : ℕ, n₀ ≤ n →
        ∀ P : S.Projection n,
          μ (SourceEvent S ξ K n P X)ᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ ω ∈ SourceEvent S ξ K n P X, ∀ y₀ : EuclideanSpace ℝ (Fin d),
            S.Ψ y₀ = normInnerRadius S.Ψ (fun j => X j ω) n →
            y₀ ∈ closure (cellSet (fun j => X j ω) n)ᶜ →
              normPotential d S.ε S.Ψ (cellSet (fun j => X j ω) n) y₀ ≤
                C * S.radius n * contactRate d S.Ψ S.ε n := by
  obtain ⟨K, C, hC, n₀, hn₀, hmain⟩ :=
    section5Event_positive hd S.isNorm S.ε_pos S.ellipticity hp
  refine ⟨K, C, hC, n₀, hn₀, fun ξ hξ hξ0 Ω _ μ _ X hX hlegal n hn P => ?_⟩
  obtain ⟨hprob, hcontact⟩ := hmain ξ hξ hξ0 μ X hX n hn P.toFun
  refine ⟨le_trans (measure_mono ?_) hprob, fun ω hω y₀ h1 h2 => ?_⟩
  · intro ω hω h5
    exact hω h5.2
  · have h5 : ω ∈ Section5Event S.Ψ S.ε ξ K.toEventConstants P.toFun X n := by
      rw [section5Event_eq]
      exact ⟨hlegal ω, hω⟩
    exact hcontact ω h5 y₀ h1 h2

end CERW.Support.RevisedPaper
