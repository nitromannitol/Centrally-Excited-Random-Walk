import CERW.Support.Drift.Dynkin
import CERW.Support.Occupation.FreshSum
import CERW.Support.LocalTime.Bracket

/-!
# Site-grouped exponential drift

Conditional deterministic occupation bound for the grouped stopping argument in
`eq:distance-crossing`. First departures pay for all departures from far sites.
-/

namespace CERW.LimitShapes.Crossing.ExponentialOccupation

open CERW LatticeProb Finset

/-- A site-dependent positive cost is paid once at its first departure. -/
theorem sum_far_drift_nonpos {d : ℕ} (X : ℕ → Site d) (T L : ℕ)
    (far : Site d → Prop) [DecidablePred far] (b c : Site d → ℝ)
    (hb : ∀ x, far x → 0 ≤ b x) (hc : ∀ x, far x → (L + 1 : ℝ) * b x ≤ c x)
    (hcount : ∀ x, far x → localTime X T x ≤ L + 1) :
    (∑ j ∈ range T, ((if far (X j) then b (X j) else 0) -
      (if X j ∉ departureRange X j then
        (if far (X j) then c (X j) else 0) else 0))) ≤ 0 := by
  classical
  rw [sum_sub_distrib,
    CERW.Support.LocalTime.sum_range_eq_sum_localTime X T
      (fun x => if far x then b x else 0)]
  have hf : (∑ j ∈ range T, if X j ∉ departureRange X j then
      (if far (X j) then c (X j) else 0) else 0) =
      ∑ x ∈ departureRange X T, if far x then c x else 0 := by
    exact CERW.Support.Occupation.sum_fresh_eq_sum_departureRange X T
      (fun x => if far x then c x else 0)
  rw [hf]
  rw [← sum_sub_distrib]
  apply sum_nonpos
  intro x _
  by_cases hx : far x
  · simp only [if_pos hx]
    have hn : (localTime X T x : ℝ) ≤ (L + 1 : ℝ) := by
      exact_mod_cast hcount x hx
    exact sub_nonpos.mpr ((mul_le_mul_of_nonneg_right hn (hb x hx)).trans (hc x hx))
  · simp only [if_neg hx, mul_zero, sub_self, le_refl]

/-- The exponential compensator is bounded by `exp 1` per elapsed time, conditional
on the far-site drift and occupation hypotheses of `eq:distance-crossing`. -/
theorem sum_exponential_drift_le {d : ℕ} (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε)
    (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ x i, ε * |ξ x i| ≤ 1 / (d : ℝ))
    (X : ℕ → Site d) (T : ℕ) (δ : Site d → ℝ) (_hδ : ∀ x, 0 ≤ δ x)
    (θ R κ : ℝ) (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) (hR : 1 ≤ R)
    (hθR : θ * R ≤ 1 / 2) (_hκ : 0 < κ) (L : ℕ)
    (hL : (L + 1 : ℝ) * (θ + 1 / (2 * R)) ≤ κ)
    (hlip : ∀ x e, e ∈ unitSteps d → δ (x + e) ≤ δ x + 1)
    (hcount : ∀ x, R ≤ δ x → localTime X T x ≤ L + 1)
    (hfar : ∀ j < T, R ≤ δ (X j) →
      (∑ e ∈ unitSteps d, driftStepProb d ε ξ X j e *
        (Real.exp (θ * δ (X j + e)) - Real.exp (θ * δ (X j)))) ≤
      θ * Real.exp (θ * δ (X j)) * (θ + 1 / (2 * δ (X j)) -
        if X j ∉ departureRange X j then κ else 0)) :
    (∑ j ∈ range T, ∑ e ∈ unitSteps d, driftStepProb d ε ξ X j e *
      (Real.exp (θ * δ (X j + e)) - Real.exp (θ * δ (X j)))) ≤
        Real.exp 1 * T := by
  classical
  let b := fun x => θ * Real.exp (θ * δ x) * (θ + 1 / (2 * δ x))
  let c := fun x => θ * Real.exp (θ * δ x) * κ
  have hb (x) (hx : R ≤ δ x) : 0 ≤ b x := by
    have hxpos : 0 < δ x := lt_of_lt_of_le (by linarith : 0 < R) hx
    dsimp [b]
    positivity
  have hc (x) (hx : R ≤ δ x) : (L + 1 : ℝ) * b x ≤ c x := by
    have hinv : 1 / (2 * δ x) ≤ 1 / (2 * R) := by
      apply one_div_le_one_div_of_le (by linarith)
      linarith
    have hcoef : (L + 1 : ℝ) * (θ + 1 / (2 * δ x)) ≤ κ :=
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl θ) hinv)
        (show (0 : ℝ) ≤ (L + 1 : ℝ) by positivity)).trans hL
    have hp : 0 ≤ θ * Real.exp (θ * δ x) := by positivity
    dsimp [b, c]
    nlinarith [mul_le_mul_of_nonneg_left hcoef hp]
  have hgroup := sum_far_drift_nonpos X T L (fun x => R ≤ δ x) b c hb hc hcount
  have hstep (j) (hj : j ∈ range T) :
      (∑ e ∈ unitSteps d, driftStepProb d ε ξ X j e *
        (Real.exp (θ * δ (X j + e)) - Real.exp (θ * δ (X j)))) ≤
      Real.exp 1 + ((if R ≤ δ (X j) then b (X j) else 0) -
        if X j ∉ departureRange X j then
          (if R ≤ δ (X j) then c (X j) else 0) else 0) := by
    by_cases hx : R ≤ δ (X j)
    · have hf := hfar j (mem_range.mp hj) hx
      have he := (Real.exp_pos (1 : ℝ)).le
      by_cases hnew : X j ∉ departureRange X j <;>
        simp only [if_pos hx, if_pos hnew, if_neg hnew] at * <;>
        dsimp [b, c] at * <;> nlinarith
    · simp only [if_neg hx, ite_self, sub_zero, add_zero]
      have hnear (e) (he : e ∈ unitSteps d) :
          Real.exp (θ * δ (X j + e)) - Real.exp (θ * δ (X j)) ≤ Real.exp 1 := by
        have hdist := hlip (X j) e he
        have harg : θ * δ (X j + e) ≤ 1 := by
          have := mul_le_mul_of_nonneg_left hdist hθ.le
          have := mul_le_mul_of_nonneg_left (le_of_not_ge hx) hθ.le
          nlinarith
        have hexp := Real.exp_le_exp.mpr harg
        linarith [Real.exp_pos (θ * δ (X j))]
      calc
        _ ≤ ∑ e ∈ unitSteps d, driftStepProb d ε ξ X j e * Real.exp 1 := by
          apply sum_le_sum
          intro e he
          exact mul_le_mul_of_nonneg_left (hnear e he)
            (CERW.Support.Drift.driftStepProb_nonneg hε hξ X j e)
        _ = Real.exp 1 := by
          rw [← sum_mul, CERW.Support.Drift.sum_driftStepProb hd, one_mul]
  have hs := sum_le_sum hstep
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at hs
  nlinarith

end CERW.LimitShapes.Crossing.ExponentialOccupation
