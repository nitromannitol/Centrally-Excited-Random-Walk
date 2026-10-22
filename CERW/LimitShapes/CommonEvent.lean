import CERW.LimitShapes.Frozen.DistanceCrossing
import CERW.LimitShapes.Frozen.NormCoarseBounds
import CERW.LimitShapes.Frozen.NormLocalTime
import CERW.LimitShapes.KernelEvents
import CERW.LimitShapes.EventConsequences

/-!
# Probability of the common martingale event

All six estimates at `sec:norm-event` hold together outside a polynomially
small exceptional event. On the coarse event the first-exit stopping does
not change the quadratic process, whose existing bound gives the required scale.
-/

universe u

open MeasureTheory Filter LatticeProb
open CERW CERW.LimitShapes
open CERW.Support.Norm.ContactEvent (scale CoarseBounds QuadraticEstimate quadraticMartingale)
open private tendsto_scale from CERW.Support.Norm.ShapeRates
open private measure_le_of_subset_union_six from CERW.Support.Norm.ContactEvent

/-- The exact sixfold common event has polynomial exceptional probability with
all constants chosen before the field and realization. -/
theorem CERW.LimitShapes.CommonEvent.exists_common_event {d : ℕ} (hd : 2 ≤ d)
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
            ENNReal.ofReal (C * (n : ℝ) ^ (-p))
:= by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cCo, CCo, hcCo, hCCo, hco⟩ :=
    CERW.LimitShapes.norm_coarse_bounds hd Ψ hΨ ε hε hell p hp
  obtain ⟨CLoc, hCLoc, hloc⟩ :=
    CERW.LimitShapes.norm_local_time_potential hd Ψ hΨ ε hε hell p hp
  obtain ⟨CMart, hCMart, hmart⟩ := KernelEvents.exists_localMartingaleBound.{u} hd p hp
  obtain ⟨CSquare, hCSquare, hsquare⟩ :=
    KernelEvents.exists_squareMartingaleBound.{u} hd hΨ hε p hp
  obtain ⟨CQuad, hCQuad, hquad⟩ :=
    CERW.Support.Norm.ContactEvent.exists_quadratic_producer.{u} hd hε hp
  obtain ⟨CCross, hCCross, hcross⟩ :=
    CERW.LimitShapes.distance_crossing_bound hd hΨ hε hell p hp
  have hV := CERW.Support.Norm.ContactAssembly.normBallVolume_pos' hd1 hΨ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hrt : Tendsto (fun n => scale d Ψ ε n) atTop atTop :=
    tendsto_scale d (show 0 < 2 * d * ε * normBallVolume Ψ by positivity)
  obtain ⟨ns, hns⟩ := eventually_atTop.mp (hrt.eventually (eventually_ge_atTop (1 : ℝ)))
  let K : CERW.LimitShapes.EventConstants :=
    ⟨cCo, CCo, CLoc, CQuad * (CCo + 1), CSquare, CMart, CCross⟩
  let C := CCo + CLoc + CQuad + CSquare + CMart + CCross
  refine ⟨K, hcCo, hCCo, hCLoc, by dsimp [K]; positivity,
    hCSquare, hCMart, hCCross, C, by dsimp [C]; positivity,
    max ns 2, le_max_right _ _, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hr : 1 ≤ scale d Ψ ε n := hns n ((le_max_left _ _).trans hn)
  have hcoord := CERW.Support.Norm.ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
  let ECo : Set Ω := {ω | ¬ CoarseBounds d Ψ ε cCo CCo (X · ω) n}
  let ELoc : Set Ω := {ω | ¬ LocalApproximation Ψ ε CLoc (X · ω) n}
  let EQuad : Set Ω := {ω | ¬ QuadraticEstimate d ε ξ CQuad (X · ω) n}
  let ESquare : Set Ω := {ω | ¬ SquareMartingaleBound Ψ ε ξ CSquare (X · ω) n}
  let EMart : Set Ω := {ω | ¬ LocalMartingaleBound ε ξ CMart (X · ω) n}
  let ECross : Set Ω := {ω | ¬ DistanceCrossingBound Ψ CCross (X · ω) n}
  have hCo : μ ECo ≤ ENNReal.ofReal (CCo * (n : ℝ) ^ (-p)) :=
    hco ξ hξ hξ0 μ X hX n hn2
  have hLoc : μ ELoc ≤ ENNReal.ofReal (CLoc * (n : ℝ) ^ (-p)) :=
    hloc ξ hξ hξ0 μ X hX n hn2
  have hQuad : μ EQuad ≤ ENNReal.ofReal (CQuad * (n : ℝ) ^ (-p)) :=
    hquad hcoord hξ0 hX n hn2
  have hSquare : μ ESquare ≤ ENNReal.ofReal (CSquare * (n : ℝ) ^ (-p)) :=
    hsquare ξ hcoord μ X hX n hn2
  have hMart : μ EMart ≤ ENNReal.ofReal (CMart * (n : ℝ) ^ (-p)) :=
    hmart ε ξ hε.le hcoord μ X hX n hn2
  have hCross : μ ECross ≤ ENNReal.ofReal (CCross * (n : ℝ) ^ (-p)) :=
    hcross ξ hξ hξ0 μ X hX n hn2
  have hsub : (section5Event Ψ ε ξ K X n)ᶜ ⊆
      ECo ∪ ELoc ∪ EQuad ∪ ESquare ∪ EMart ∪ ECross ∪ ∅ := by
    classical
    intro ω hbad
    by_contra hnot
    simp only [Set.mem_union, ECo, ELoc, EQuad, ESquare, EMart, ECross,
      Set.mem_setOf_eq, not_or, not_not,
      Set.mem_empty_iff_false, not_false_eq_true, and_true] at hnot
    obtain ⟨⟨⟨⟨⟨hco, hloc⟩, hquad⟩, hsquare⟩, hmart⟩, hcross⟩ := hnot
    apply hbad
    refine ⟨hco, hloc, ?_, hsquare, hmart, hcross⟩
    obtain ⟨_, _, _, _, _, hR⟩ := hco
    have hstop : stoppedQuadratic ε ξ ((CCo + 1) * scale d Ψ ε n) (X · ω) n =
        quadraticMartingale d ε ξ (X · ω) n := by
      apply stoppedQuadratic_eq
      intro j hj
      have h := euclidNorm_le_maxRadius (X · ω) (Nat.le_of_lt hj)
      nlinarith
    change |stoppedQuadratic ε ξ ((CCo + 1) * scale d Ψ ε n) (X · ω) n| ≤
      CQuad * (CCo + 1) * scale d Ψ ε n * Real.sqrt (n * Real.log n)
    rw [hstop]
    change |quadraticMartingale d ε ξ (X · ω) n| ≤
      CQuad * (maxRadius (X · ω) n + 1) * Real.sqrt (n * Real.log n) at hquad
    calc |quadraticMartingale d ε ξ (X · ω) n|
        ≤ CQuad * (maxRadius (X · ω) n + 1) * Real.sqrt (n * Real.log n) := hquad
      _ ≤ CQuad * ((CCo + 1) * scale d Ψ ε n) * Real.sqrt (n * Real.log n) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by nlinarith) hCQuad.le) (Real.sqrt_nonneg _)
      _ = CQuad * (CCo + 1) * scale d Ψ ε n * Real.sqrt (n * Real.log n) := by ring
  exact measure_le_of_subset_union_six hsub hCo hLoc hQuad hSquare hMart hCross
    (by simp only [measure_empty]) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (le_of_eq (by dsimp [C]; ring))
