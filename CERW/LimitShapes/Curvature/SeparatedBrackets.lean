import CERW.LimitShapes.Curvature.ProfileEvent
import CERW.LimitShapes.Curvature.PositiveEvent
import CERW.LimitShapes.Curvature.OuterEvent
import CERW.Support.Lower.SeparatedBrackets

/-!
# Separated brackets from curvature

Lemma `lem:separated-brackets` follows from the curvature profile on the common event
and the existing Gamma sum and kernel estimates.
-/

open MeasureTheory Filter Topology
open LatticeProb (Site)

open private brackets_core sqrt_mul_le_sqrt_mul_rpow from CERW.Support.Lower.SeparatedBrackets

/-- The estimate follows from the deterministic inputs on the common event. -/
theorem CERW.LimitShapes.Curvature.separated_brackets_from_curvature {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let e₁ : Site d := LatticeProb.unit ⟨0, by omega⟩
    let g : Site d → ℝ := CERW.latticeKernel d
    let σ : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (r n * Real.log (r n)) else Real.sqrt (r n)
    let k : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let m : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let y : ℕ → ℕ → Site d := fun n i => ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • e₁
    let f : ℕ → ℕ → Site d → ℝ := fun n i z =>
      if d = 2 then g (z - (y n i + (k n : ℤ) • e₁)) - g (z - y n i) else g (z - y n i)
    ∀ K : CERW.LimitShapes.EventConstants,
      0 < K.cCo → 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CQuad → 0 ≤ K.CMart → 0 < K.CCross →
    ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ,
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 →
          CERW.IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) →
        ξ 0 = 0 → ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
        ∀ i j : ℕ, 1 ≤ i → i ≤ m n → 1 ≤ j → j ≤ m n →
            let B : ℝ := CERW.dynkinBracket (CERW.stepProb d ε) (f n i) (f n j) X n /
              σ n ^ 2
            (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C * r n ^ (-(1 : ℝ) / 4))
:= by
  intro ωd ε hε hεd r e₁ g σ k m y f K hc hCo hLoc hQuad hMart hCross
  obtain ⟨P, hP, np, hnp, hprofile⟩ :=
    CERW.LimitShapes.Curvature.profile_on_event_of_bounds
      CERW.LimitShapes.Curvature.exists_positive_on_event
      CERW.LimitShapes.Curvature.exists_outer_width_on_event
      hd hε hεd K hc hCo hLoc hQuad hMart hCross
  obtain ⟨c₀, C₀, C, hc₀, hcC, hC, nb, hbr⟩ := brackets_core hd hε hεd hP.le
  refine ⟨c₀, C₀, C, hc₀, hcC, hC, max np nb, ?_⟩
  intro ξ hξ hξ0 X n hn hty hE
  apply hbr n ((le_max_right _ _).trans hn) X
  intro x
  have hp := hprofile ξ hξ hξ0 X n ((le_max_left _ _).trans hn) hty hE
    (CERW.toSpace x)
  rw [CERW.cellLocalTime_of_mem_cell X n (CERW.toSpace_mem_cell x),
    CERW.norm_toSpace] at hp
  refine hp.trans ?_
  have hlog : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast (show 0 < n by omega))]
    have he := Real.exp_one_lt_d9
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
    linarith
  have hr : 0 ≤ CERW.Support.Outer.Radius.radius d ε n := by
    rw [← CERW.LimitShapes.Curvature.euclidean_scale_eq_radius d ε n]
    exact (CERW.LimitShapes.scale_pos (by omega : 1 ≤ d)
      CERW.Support.Norm.EuclideanCoarse.isNorm_euclidean hε (by omega)).le
  apply mul_le_mul_of_nonneg_left _ hP.le
  split_ifs
  · exact le_rfl
  · exact sqrt_mul_le_sqrt_mul_rpow hr hlog
