module

public import CERW.LimitShapes.Frozen.CommonEvent
public import CERW.LimitShapes.Frozen.ContactPotential

@[expose] public section

/-!
# Contact potential on the common event

The common event at `sec:norm-event` has polynomial exceptional probability,
and `lem:contact` holds on it with constants depending only on the source parameters.
-/

universe u

open MeasureTheory Topology
open LatticeProb (Site)

/-- The contact rate is nonnegative at positive scale for every positive time. -/
theorem CERW.LimitShapes.ContactEvent.contactRate_nonneg {d : ℕ}
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {ε : ℝ} {n : ℕ}
    (hr : 0 < CERW.Support.Norm.ContactEvent.scale d Ψ ε n) (hn : 1 ≤ n) :
    0 ≤ CERW.Support.Norm.ContactEvent.contactRate d Ψ ε n := by
  unfold CERW.Support.Norm.ContactEvent.contactRate
  split
  · exact Real.sqrt_nonneg _
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) hr.le

/-- The contact conclusion together with the actual common-event probability bound,
with every event and contact constant chosen before the subgradient field and law. -/
theorem CERW.LimitShapes.ContactEvent.contact_potential_on_common_event {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) (p : ℝ) (hp : 0 < p) :
    ∃ K : CERW.LimitShapes.EventConstants,
      0 < K.cCo ∧ 0 < K.CCo ∧ 0 < K.CLoc ∧ 0 < K.CQuad ∧
      0 < K.CSquare ∧ 0 < K.CMart ∧ 0 < K.CCross ∧
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
          (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
          μ (CERW.LimitShapes.section5Event Ψ ε ξ K X n)ᶜ ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
          ∀ᵐ ω ∂μ, ω ∈ CERW.LimitShapes.section5Event Ψ ε ξ K X n →
            ∀ y₀ : EuclideanSpace ℝ (Fin d),
              Ψ y₀ = CERW.normInnerRadius Ψ (X · ω) n →
              y₀ ∈ closure (CERW.cellSet (X · ω) n)ᶜ →
              CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y₀ ≤
                C * CERW.Support.Norm.ContactEvent.scale d Ψ ε n *
                  CERW.Support.Norm.ContactEvent.contactRate d Ψ ε n
:= by
  obtain ⟨K, hc, hCo, hLoc, hQ, hS, hM, hCross, Cp, hCp, np, hnp, hprob⟩ :=
    CERW.LimitShapes.exists_common_event hd hΨ hε hell p hp
  obtain ⟨Ct, hCt, nt, hnt, hcontact⟩ :=
    CERW.LimitShapes.contact_potential hd Ψ hΨ ε hε hell K hCo.le hLoc.le hM.le
  refine ⟨K, hc, hCo, hLoc, hQ, hS, hM, hCross, Cp + Ct, by positivity,
    max np nt, hnp.trans (le_max_left _ _), ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hn2 : 2 ≤ n := hnp.trans ((le_max_left _ _).trans hn)
  have hr := CERW.LimitShapes.scale_pos (by omega : 1 ≤ d) hΨ hε (by omega : 0 < n)
  have hrate := CERW.LimitShapes.ContactEvent.contactRate_nonneg hr (by omega : 1 ≤ n)
  refine ⟨(hprob ξ hξ hξ0 μ X hX n ((le_max_left _ _).trans hn)).trans ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · have hcoord := CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
    have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := ae_iff.mpr hX.start
    filter_upwards [h0, ae_all_iff.mpr
      (CERW.Support.Drift.ae_sub_mem_unitSteps_drift (by omega : 1 ≤ d)
        hε.le hcoord hX)] with ω h0 hs
    intro hE y₀ hy houtside
    have hbound := hcontact ξ hξ hξ0 (X · ω) n ((le_max_right _ _).trans hn)
      ⟨h0, hs⟩ hE y₀ hy houtside
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Ct ≤ Cp + Ct) hr.le) hrate)
