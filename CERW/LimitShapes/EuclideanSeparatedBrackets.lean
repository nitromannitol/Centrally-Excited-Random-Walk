module

public import CERW.LimitShapes.Frozen.SeparatedBrackets
public import CERW.LimitShapes.EuclideanEvent

@[expose] public section

/-!
# Separated brackets on the common event

The event defining Ωₙ at `lem:separated-brackets` is the event of `sec:norm-event`
at exponent ten. Its constants are selected before the Euclidean walk and its law.
-/

universe u

open MeasureTheory Filter Topology
open LatticeProb (Site)

/-- Separated bracket bounds on the actual common event with its polynomial
probability estimate at exponent ten and source-uniform constants. -/
theorem CERW.LimitShapes.EuclideanSeparatedBrackets.separated_brackets_on_euclidean_event
    {d : ℕ} (hd : 2 ≤ d) :
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
    ∃ K : CERW.LimitShapes.EventConstants,
      0 < K.cCo ∧ 0 < K.CCo ∧ 0 < K.CLoc ∧ 0 < K.CQuad ∧
      0 < K.CSquare ∧ 0 < K.CMart ∧ 0 < K.CCross ∧
    ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ (CERW.LimitShapes.section5Event (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
            ε (fun x => CERW.unitDir (CERW.toSpace x)) K X n)ᶜ ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (-(10 : ℝ))) ∧
        ∀ᵐ ω ∂μ, ω ∈ CERW.LimitShapes.section5Event
            (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε
            (fun x => CERW.unitDir (CERW.toSpace x)) K X n →
          ∀ i j : ℕ, 1 ≤ i → i ≤ m n → 1 ≤ j → j ≤ m n →
            let B : ℝ := CERW.dynkinBracket (CERW.stepProb d ε) (f n i) (f n j)
              (X · ω) n / σ n ^ 2
            (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C * r n ^ (-(1 : ℝ) / 4))
:= by
  intro ωd ε hε hεd r e₁ g σ k m y f
  obtain ⟨K, hc, hCo, hLoc, hQuad, hSquare, hMart, hCross, Cp, hCp, np, hnp, hprob⟩ :=
    CERW.LimitShapes.EuclideanEvent.exists_euclidean_event.{u} hd hε hεd 10 (by norm_num)
  obtain ⟨c₀, C₀, Cb, hc₀, hC₀, hCb, nb, hbr⟩ :=
    CERW.LimitShapes.separated_brackets hd ε hε hεd K hc hCo.le hLoc.le hQuad.le
      hMart.le hCross
  have hξ : ∀ x : Site d, x ≠ 0 →
      CERW.IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
        (CERW.toSpace x) (CERW.unitDir (CERW.toSpace x)) := by
    intro x hx
    exact CERW.Support.Norm.EuclideanCoarse.isSubgradient_unitDir fun h =>
      hx (CERW.Support.Norm.EuclideanCoarse.eq_zero_of_toSpace_eq_zero h)
  have hξ0 := CERW.Support.Norm.EuclideanCoarse.unitDir_toSpace_zero (d := d)
  have hell : ∀ i : Fin d, ε * ‖CERW.coordVec i‖ < 1 / (d : ℝ) := by
    intro i
    simpa only [CERW.coordVec, PiLp.norm_single, norm_one, mul_one] using hεd
  have hcoord := CERW.Support.Norm.ContactAssembly.drift_coord_le
    CERW.Support.Norm.EuclideanCoarse.isNorm_euclidean hε hell hξ hξ0
  refine ⟨K, hc, hCo, hLoc, hQuad, hSquare, hMart, hCross,
    c₀, C₀, Cp + Cb, hc₀, hC₀, by positivity,
    max np (max nb 2), hnp.trans (le_max_left _ _), ?_⟩
  intro Ω _ μ _ X hX n hn
  have hnp' : np ≤ n := (le_max_left _ _).trans hn
  have hnb : nb ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  refine ⟨(hprob μ X hX n hnp').trans ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (by linarith : Cp ≤ Cp + Cb)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · have hXd := (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).mp hX
    have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := ae_iff.mpr hX.start
    filter_upwards [h0, ae_all_iff.mpr
      (CERW.Support.Drift.ae_sub_mem_unitSteps_drift (by omega : 1 ≤ d)
        hε.le hcoord hXd)] with ω hstart hsteps
    intro hE i j hi him hj hjm
    have hbound := hbr (fun x => CERW.unitDir (CERW.toSpace x)) hξ hξ0 (X · ω) n hnb
      ⟨hstart, hsteps⟩ hE i j hi him hj hjm
    refine ⟨hbound.1, fun hij => (hbound.2 hij).trans ?_⟩
    apply mul_le_mul_of_nonneg_right (by linarith : Cb ≤ Cp + Cb)
    exact Real.rpow_nonneg (Real.rpow_nonneg (by positivity) _) _
