module

public import CERW.LimitShapes.EuclideanEvent
public import CERW.Support.Outer.Radius.PathBounds

@[expose] public section

/-!
# Outer-radius probability from the common event

The deterministic estimate of Proposition `prop:stronger-outer` transfers through the
common event of `sec:norm-event`. Enlarging the constant covers the finite initial times.
-/

universe u

open CERW LatticeProb MeasureTheory

namespace CERW.LimitShapes.Curvature

open CERW.Support.Norm.EuclideanCoarse
open CERW.Support.Norm.Section5Localization

/-- The deterministic outer-radius bound on the common event implies the probability
bound of Proposition `prop:stronger-outer`, uniformly over walk realizations. -/
theorem outer_radius_of_event_bound
    (houter : ∀ {d : ℕ} (_hd : 2 ≤ d) {ε : ℝ}, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ K : CERW.LimitShapes.EventConstants,
        0 < K.cCo → 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CQuad → 0 ≤ K.CMart → 0 < K.CCross →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
        CERW.maxRadius X n ≤ CERW.Support.Outer.Radius.radius d ε n + C *
          (if d = 2 then Real.sqrt (CERW.Support.Outer.Radius.radius d ε n) *
            Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1))) :
    CERW.Support.Statements.outer_radius.{u} := by
  intro d hd
  dsimp only
  intro ε hε hεd p hp
  obtain ⟨K, hc, hCo, hLoc, hQuad, _, hMart, hCross, Cp, hCp, np, _, hprob⟩ :=
    EuclideanEvent.exists_euclidean_event.{u} hd hε hεd p hp
  obtain ⟨Co, hCoPos, no, _, hbound⟩ :=
    houter hd hε hεd K hc hCo.le hLoc.le hQuad.le hMart.le hCross
  let N := max np no
  let C := Co + Cp + (N : ℝ) ^ p
  have hNpow : 0 ≤ (N : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg N) p
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  by_cases hNn : N ≤ n
  · have hlog : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hrate : 0 ≤ (if d = 2 then
        Real.sqrt (CERW.Support.Outer.Radius.radius d ε n) * Real.log n ^ ((5 : ℝ) / 2)
        else Real.log n ^ ((d : ℝ) + 1)) := by
      split_ifs
      · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hlog _)
      · exact Real.rpow_nonneg hlog _
    have hCoC : Co ≤ C := by dsimp [C]; linarith
    have hCpC : Cp ≤ C := by dsimp [C]; linarith
    have hXd := (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX
    have hsub : ∀ x : Site d, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
          (toSpace x) (unitDir (toSpace x)) := by
      intro x hx
      exact isSubgradient_unitDir fun h => hx (eq_zero_of_toSpace_eq_zero h)
    have hbad : μ {ω | ¬ maxRadius (X · ω) n ≤
        CERW.Support.Outer.Radius.radius d ε n + C *
          (if d = 2 then Real.sqrt (CERW.Support.Outer.Radius.radius d ε n) *
            Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1))} ≤
        μ (section5Event (fun v => ‖v‖) ε (fun x => unitDir (toSpace x)) K X n)ᶜ := by
      apply measure_mono_ae
      filter_upwards [ae_legal_of_isDriftCERW hXd] with ω hlegal
      intro hfail hgood
      apply hfail
      exact (hbound _ hsub unitDir_toSpace_zero (X · ω) n
        ((le_max_right np no).trans hNn) hlegal hgood).trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right hCoC hrate))
    have hfinal := hbad.trans ((hprob μ X hX n
      ((le_max_left np no).trans hNn)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCpC hnp)))
    simpa only [CERW.Support.Outer.Radius.radius, unitBallVolume] using hfinal
  · apply prob_le_one.trans
    rw [ENNReal.one_le_ofReal]
    have hpow : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hnpos p
    have hle : (n : ℝ) ^ p ≤ (N : ℝ) ^ p :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast (by omega : n ≤ N)) hp.le
    rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, le_div_iff₀ hpow, one_mul]
    dsimp [C]
    linarith

end CERW.LimitShapes.Curvature
