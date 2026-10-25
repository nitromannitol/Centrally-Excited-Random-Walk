module

public import CERW.LimitShapes.DynkinBounds
public import CERW.Support.Norm.ShapeRates

@[expose] public section

/-!
# Ramp martingales before a fixed horizon

The actual bracket of a ramp is bounded by the occupation mass above its
lower level. Freedman's inequality therefore controls its value at each
prefix using the terminal horizon's logarithm and exceptional probability.
-/

universe u

open MeasureTheory ProbabilityTheory LatticeProb

namespace CERW.LimitShapes.Crossing.RampBound

open CERW CERW.Support.Drift
open private abs_ramp_sub_le sum_ramp_sq_le sum_filter_localTime
  from CERW.Support.Norm.ShapeRates

/-- The actual ramp bracket is bounded by its upper half-space occupation mass. -/
theorem dynkinBracket_ramp_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    {q : EuclideanSpace ℝ (Fin d)} {Λ : ℝ} (hq : ‖q‖ ≤ Λ)
    (a : ℝ) (X : ℕ → Site d) (n : ℕ) :
    dynkinBracket (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - a) 0)
        (fun z => max (inner ℝ q (toSpace z) - a) 0) X n ≤
      Λ ^ 2 * ∑ z ∈ (departureRange X n).filter
        (fun z => a - Λ < inner ℝ q (toSpace z)), (localTime X n z : ℝ) := by
  rw [sum_filter_localTime X n, Finset.mul_sum]
  unfold dynkinBracket
  refine Finset.sum_le_sum fun j _ => ?_
  have hsq := sum_ramp_sq_le hq a (X j)
    (fun e => driftStepProb_nonneg hε hξ X j e) (sum_driftStepProb hd ε ξ X j)
  simp only [← pow_two]
  nlinarith [sq_nonneg (stepMean (driftStepProb d ε ξ)
    (fun z => max (inner ℝ q (toSpace z) - a) 0) X j)]

/-- A ramp with direction bounded by `Λ` satisfies the occupation-mass Freedman bound
at any fixed earlier time, with logarithm and failure probability at the horizon. -/
theorem exists_ramp_freedman_bound {Λ : ℝ} (hΛ : 0 ≤ Λ) (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {d : ℕ}, 1 ≤ d →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)),
        0 ≤ ε → (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) →
      ∀ (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X →
      ∀ N : ℕ, 2 ≤ N → ∀ n : ℕ, n ≤ N →
      ∀ q : EuclideanSpace ℝ (Fin d), ‖q‖ ≤ Λ → ∀ a : ℝ,
        μ {ω | ¬ |dynkinMart (driftStepProb d ε ξ)
            (fun z => max (inner ℝ q (toSpace z) - a) 0) (X · ω) n| ≤
          C * (Real.sqrt (Real.log N * ∑ z ∈ (departureRange (X · ω) n).filter
            (fun z => a - Λ < inner ℝ q (toSpace z)), (localTime (X · ω) n z : ℝ)) +
            Real.log N)} ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-p)) := by
  obtain ⟨A, hA, hF⟩ := DynkinBounds.exists_dynkin_freedman_bound.{u} p hp
  refine ⟨A * (Λ + 1), by positivity, ?_⟩
  intro d hd Ω _ μ _ ε ξ hε hξ X hX N hN n hn q hq a
  let f : Site d → ℝ := fun z => max (inner ℝ q (toSpace z) - a) 0
  have hstep : ∀ x e : Site d, e ∈ unitSteps d → |f (x + e) - f x| ≤ Λ + 1 := by
    intro x e he
    exact ((abs_ramp_sub_le q a x he).trans hq).trans (by linarith)
  have htail := hF N hN n hn hd μ ε ξ hε hξ X hX f (Λ + 1) (by positivity) hstep
  refine (measure_mono ?_).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro ω hbad hgood
    apply hbad
    let S := ∑ z ∈ (departureRange (X · ω) n).filter
      (fun z => a - Λ < inner ℝ q (toSpace z)), (localTime (X · ω) n z : ℝ)
    have hL := Real.log_natCast_nonneg N
    have hbr := dynkinBracket_ramp_le hd hε hξ hq a (X · ω) n
    have hsqrt : Real.sqrt (dynkinBracket (driftStepProb d ε ξ) f f (X · ω) n *
        Real.log N) ≤ Λ * Real.sqrt (Real.log N * S) := by
      calc _ ≤ Real.sqrt (Λ ^ 2 * (Real.log N * S)) :=
          Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_right hbr hL])
        _ = Λ * Real.sqrt (Real.log N * S) := by
          rw [Real.sqrt_mul (sq_nonneg Λ), Real.sqrt_sq hΛ]
    have hs := Real.sqrt_nonneg (Real.log N * S)
    calc |dynkinMart (driftStepProb d ε ξ) f (X · ω) n|
        ≤ A * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ) f f (X · ω) n *
          Real.log N) + (Λ + 1) * Real.log N) := hgood
      _ ≤ A * ((Λ + 1) * Real.sqrt (Real.log N * S) + (Λ + 1) * Real.log N) :=
        mul_le_mul_of_nonneg_left (by linarith) hA.le
      _ = A * (Λ + 1) * (Real.sqrt (Real.log N * S) + Real.log N) := by ring
  · exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)

end CERW.LimitShapes.Crossing.RampBound
