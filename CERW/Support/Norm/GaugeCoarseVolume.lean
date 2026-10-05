import CERW.Support.Statements
import CERW.Support.Drift
import CERW.Support.Norm.Freedman
import CERW.Support.Norm.VectorBound
import CERW.Support.Norm.GaugeModel
import CERW.Support.Norm.GaugePotential
import CERW.Support.Occupation.FreshSum
import CERW.Support.Occupation.SiteArith
import CERW.Support.Occupation.Facts
import CERW.Support.Occupation.Cells
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Occupation.CellIntegral
import CERW.Support.Crossing.LastEntrance
import CERW.Support.Law.Moments
import CERW.Support.LocalTime.Bracket

/-!
# The coarse bounds for the Minkowski functional of a compact convex body

Let `K` be a compact convex set with the origin in its interior and `ψ = gauge K` its Minkowski
functional. It is neither assumed even nor a norm. For the walk whose drift is minus a selection
of subgradients of `ψ`, this module proves the parts of the coarse bounds (Proposition 4.1) that
do not use the local time potential lemma:

* the linear martingale family, with a polynomial failure probability, over a finite family of
  directions bounded by `Λ_ψ` (`exists_gauge_linear_martingale_bound`);
* the cap event over the finite family of directions `capDirections ψ n` and all thresholds, its
  polynomial failure probability, and the radial Euclidean-max bound `RoughOuter` that it implies
  (`exists_capEvent_failure_bound`, `exists_rough_outer_of_capEvent`);
* the geometry of the inner radius from the ball, layer and potential statements of the gauge
  (`gauge_inner_geometry`);
* the real arithmetic and the six bounds on every path with the cap event, the rough outer bound
  and the local time event (`gauge_coarse_deterministic`).

The assembly `gauge_coarse_bounds_of_local_time` takes the local time potential lemma of the
gauge as the hypothesis `GaugeLocalTimePotential`; that lemma is not proved in this module.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.GaugeCoarseVolume.OuterCore

open CERW CERW.Support.Statements

section Ramp

variable {d : ℕ}

/-- The embedding of lattice sites is additive. -/
private lemma toSpace_add (x y : Site d) : toSpace (x + y) = toSpace x + toSpace y := by
  ext i
  simp [toSpace]

/-- A unit step changes a projection `q · z` by at most `‖q‖`. -/
private lemma abs_inner_toSpace_le (q : EuclideanSpace ℝ (Fin d)) {e : Site d}
    (he : e ∈ unitSteps d) : |inner ℝ q (toSpace e)| ≤ ‖q‖ := by
  calc |inner ℝ q (toSpace e)| ≤ ‖q‖ * ‖toSpace e‖ := abs_real_inner_le_norm _ _
    _ = ‖q‖ := by
      rw [norm_toSpace, CERW.Support.Law.euclidNorm_of_mem_unitSteps he, mul_one]

/-- A nearest-neighbour path started at the origin satisfies `‖x_j‖ ≤ j`. -/
private lemma norm_toSpace_le_index (x : ℕ → Site d) (hx0 : x 0 = 0)
    (hstep : ∀ j, x (j + 1) - x j ∈ unitSteps d) (j : ℕ) : ‖toSpace (x j)‖ ≤ j := by
  induction j with
  | zero => simp [hx0, CERW.Support.Occupation.toSpace_zero]
  | succ j ih =>
    have h1 : toSpace (x (j + 1)) = toSpace (x j) + toSpace (x (j + 1) - x j) := by
      rw [← toSpace_add]
      congr 1
      abel
    rw [h1]
    calc ‖toSpace (x j) + toSpace (x (j + 1) - x j)‖
        ≤ ‖toSpace (x j)‖ + ‖toSpace (x (j + 1) - x j)‖ := norm_add_le _ _
      _ ≤ ((j + 1 : ℕ) : ℝ) := by
          rw [norm_toSpace (x (j + 1) - x j),
            CERW.Support.Law.euclidNorm_of_mem_unitSteps (hstep j)]
          push_cast
          linarith

/-- The ramp `z ↦ (q · z - a)₊`. -/
private noncomputable def ramp (q : EuclideanSpace ℝ (Fin d)) (a : ℝ) (z : Site d) : ℝ :=
  max (inner ℝ q (toSpace z) - a) 0

/-- One unit step changes the ramp by at most `‖q‖`. -/
private lemma abs_ramp_step_le (q : EuclideanSpace ℝ (Fin d)) (a : ℝ) (z : Site d) {e : Site d}
    (he : e ∈ unitSteps d) : |ramp q a (z + e) - ramp q a z| ≤ ‖q‖ := by
  unfold ramp
  calc |max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0|
      ≤ |(inner ℝ q (toSpace (z + e)) - a) - (inner ℝ q (toSpace z) - a)| :=
        abs_max_sub_max_le_abs _ _ _
    _ = |inner ℝ q (toSpace e)| := by
        rw [toSpace_add, inner_add_right]
        congr 1
        ring
    _ ≤ ‖q‖ := abs_inner_toSpace_le q he

/-- At `z` with `q · z ≥ a + Λ` the ramp is linear across every unit step. -/
private lemma ramp_step_of_top {q : EuclideanSpace ℝ (Fin d)} {a Λ : ℝ} (hq : ‖q‖ ≤ Λ)
    {z e : Site d} (he : e ∈ unitSteps d) (hz : a + Λ ≤ inner ℝ q (toSpace z)) :
    ramp q a (z + e) - ramp q a z = inner ℝ q (toSpace e) := by
  have h2 := abs_le.mp ((abs_inner_toSpace_le q he).trans hq)
  unfold ramp
  rw [toSpace_add, inner_add_right, max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

/-- At `z` with `q · z ≤ a - Λ` the ramp vanishes after every unit step. -/
private lemma ramp_step_of_bottom {q : EuclideanSpace ℝ (Fin d)} {a Λ : ℝ} (hq : ‖q‖ ≤ Λ)
    {z e : Site d} (he : e ∈ unitSteps d) (hz : inner ℝ q (toSpace z) ≤ a - Λ) :
    ramp q a (z + e) - ramp q a z = 0 := by
  have h2 := abs_le.mp ((abs_inner_toSpace_le q he).trans hq)
  unfold ramp
  rw [toSpace_add, inner_add_right, max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- Above the level `a + Λ`, the mean increment of the ramp is minus `ε q · ξ` at a first
departure from a nonzero site and zero otherwise. -/
private lemma stepMean_ramp_of_top {q : EuclideanSpace ℝ (Fin d)} {a Λ : ℝ} (hq : ‖q‖ ≤ Λ)
    (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (j : ℕ)
    (hz : a + Λ ≤ inner ℝ q (toSpace (x j))) :
    stepMean (driftStepProb d ε ξ) (ramp q a) x j =
      -(if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then
        ε * inner ℝ q (ξ (x j)) else 0) := by
  unfold stepMean
  have hterm : ∀ e ∈ unitSteps d,
      driftStepProb d ε ξ x j e * (ramp q a (x j + e) - ramp q a (x j)) =
        inner ℝ q (driftStepProb d ε ξ x j e • toSpace e) := by
    intro e he
    rw [ramp_step_of_top hq he hz, real_inner_smul_right]
  rw [Finset.sum_congr rfl hterm, ← inner_sum]
  by_cases h : x j ≠ 0 ∧ x j ∉ (Finset.range j).image x
  · have hsum : ∑ e ∈ unitSteps d, driftStepProb d ε ξ x j e • toSpace e =
        -(ε • ξ (x j)) := by
      simp only [driftStepProb, if_pos h]
      exact CERW.Support.Drift.sum_driftFirstStep_smul ε (ξ (x j))
    rw [hsum, if_pos h, inner_neg_right, real_inner_smul_right]
  · have hsum : ∑ e ∈ unitSteps d, driftStepProb d ε ξ x j e • toSpace e = 0 := by
      simp only [driftStepProb, if_neg h]
      exact CERW.Support.Law.sum_srwStep_smul
    rw [hsum, if_neg h, inner_zero_right, neg_zero]

/-- Below the level `a - Λ`, the mean increment of the ramp is zero. -/
private lemma stepMean_ramp_of_bottom {q : EuclideanSpace ℝ (Fin d)} {a Λ : ℝ} (hq : ‖q‖ ≤ Λ)
    (p : (ℕ → Site d) → ℕ → Site d → ℝ) (x : ℕ → Site d) (j : ℕ)
    (hz : inner ℝ q (toSpace (x j)) ≤ a - Λ) : stepMean p (ramp q a) x j = 0 := by
  unfold stepMean
  refine Finset.sum_eq_zero fun e he => ?_
  rw [ramp_step_of_bottom hq he hz, mul_zero]

/-- The mean increment of the ramp is at most `‖q‖` in absolute value, for nonnegative step
probabilities that sum to one. -/
private lemma abs_stepMean_ramp_le (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (p : (ℕ → Site d) → ℕ → Site d → ℝ) (x : ℕ → Site d) (j : ℕ) (hp : ∀ e, 0 ≤ p x j e)
    (hp1 : ∑ e ∈ unitSteps d, p x j e = 1) : |stepMean p (ramp q a) x j| ≤ ‖q‖ := by
  unfold stepMean
  calc |∑ e ∈ unitSteps d, p x j e * (ramp q a (x j + e) - ramp q a (x j))|
      ≤ ∑ e ∈ unitSteps d, |p x j e * (ramp q a (x j + e) - ramp q a (x j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ unitSteps d, p x j e * ‖q‖ := by
        refine Finset.sum_le_sum fun e he => ?_
        rw [abs_mul, abs_of_nonneg (hp e)]
        exact mul_le_mul_of_nonneg_left (abs_ramp_step_le q a (x j) he) (hp e)
    _ = ‖q‖ := by rw [← Finset.sum_mul, hp1, one_mul]

/-- The number of sites `z` of the departure range with `q · z > a`. -/
private noncomputable def aboveCount (q : EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ)
    (a : ℝ) : ℕ :=
  ((departureRange x n).filter (fun z => a < inner ℝ q (toSpace z))).card

/-- Raising the level can only remove sites. -/
private lemma aboveCount_anti (q : EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ)
    {a a' : ℝ} (h : a ≤ a') : aboveCount q x n a' ≤ aboveCount q x n a := by
  unfold aboveCount
  refine Finset.card_le_card fun z hz => ?_
  simp only [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, lt_of_le_of_lt h hz.2⟩

/-- The comparison of neighboring levels (`eq:norm-linear` before the absorption): at a level
`a` past which every site has local time at most `S` and drift at least `α` in the direction `q`,
the Dynkin martingale of the ramp controls the number of sites above `a + Λ`. -/
private lemma level_inequality {ε α C₁ Λ lg : ℝ} (hd : 1 ≤ d) (hε : 0 < ε) (hα : 0 < α)
    (hΛ : 0 < Λ) (hlg : 0 ≤ lg) (hC₁ : 0 ≤ C₁)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ Λ) (x : ℕ → Site d) (hx0 : x 0 = 0) (n : ℕ)
    {a : ℝ} (ha : 0 ≤ a) {S : ℕ}
    (hS : ∀ z ∈ departureRange x n, a - Λ < inner ℝ q (toSpace z) → localTime x n z ≤ S)
    (hα' : ∀ j < n, a + Λ ≤ inner ℝ q (toSpace (x j)) → α ≤ inner ℝ q (ξ (x j)))
    (hM : |dynkinMart (driftStepProb d ε ξ) (ramp q a) x n| ≤
      C₁ * (Real.sqrt (lg * ∑ z ∈ (departureRange x n).filter
        (fun z => a - Λ < inner ℝ q (toSpace z)), (localTime x n z : ℝ)) + lg)) :
    ε * α * (aboveCount q x n (a + Λ) : ℝ) ≤
      Λ * S * ((aboveCount q x n (a - Λ) : ℝ) - aboveCount q x n (a + Λ)) +
        C₁ * (Real.sqrt (lg * (S * aboveCount q x n (a - Λ))) + lg) := by
  have hεα : 0 < ε * α := mul_pos hε hα
  -- the Dynkin identity for the ramp
  have hmart : -∑ j ∈ Finset.range n, stepMean (driftStepProb d ε ξ) (ramp q a) x j ≤
      |dynkinMart (driftStepProb d ε ξ) (ramp q a) x n| := by
    have h0 : ramp q a (x 0) = 0 := by
      unfold ramp
      rw [hx0, CERW.Support.Occupation.toSpace_zero, inner_zero_right]
      exact max_eq_right (by linarith)
    have h1 : 0 ≤ ramp q a (x n) := le_max_right _ _
    have hdef : dynkinMart (driftStepProb d ε ξ) (ramp q a) x n =
        ramp q a (x n) - ramp q a (x 0) -
          ∑ j ∈ Finset.range n, stepMean (driftStepProb d ε ξ) (ramp q a) x j := rfl
    rw [hdef, h0]
    have := le_abs_self (ramp q a (x n) - 0 -
      ∑ j ∈ Finset.range n, stepMean (driftStepProb d ε ξ) (ramp q a) x j)
    linarith
  -- the pointwise lower bound for minus the mean increments
  have hpt : ∀ j ∈ Finset.range n,
      ε * α * (if x j ∉ (Finset.range j).image x then
          (if a + Λ ≤ inner ℝ q (toSpace (x j)) then (1 : ℝ) else 0) else 0) -
        Λ * (if a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ
          then (1 : ℝ) else 0) ≤
        -stepMean (driftStepProb d ε ξ) (ramp q a) x j := by
    intro j hj
    by_cases htop : a + Λ ≤ inner ℝ q (toSpace (x j))
    · have hx_ne : x j ≠ 0 := by
        intro h
        rw [h, CERW.Support.Occupation.toSpace_zero, inner_zero_right] at htop
        linarith
      have hmid : ¬ (a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ) :=
        fun h => absurd h.2 (not_lt.mpr htop)
      rw [stepMean_ramp_of_top hq ε ξ x j htop, if_neg hmid, if_pos htop]
      by_cases hf : x j ∉ (Finset.range j).image x
      · rw [if_pos hf, if_pos ⟨hx_ne, hf⟩]
        have := mul_le_mul_of_nonneg_left (hα' j (Finset.mem_range.mp hj) htop) hε.le
        linarith
      · rw [if_neg hf, if_neg (fun h => hf h.2)]
        simp
    · by_cases hbot : inner ℝ q (toSpace (x j)) ≤ a - Λ
      · have hmid : ¬ (a - Λ < inner ℝ q (toSpace (x j)) ∧
            inner ℝ q (toSpace (x j)) < a + Λ) :=
          fun h => absurd h.1 (not_lt.mpr hbot)
        rw [stepMean_ramp_of_bottom hq _ x j hbot, if_neg hmid, if_neg htop]
        simp
      · have hmid : a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ :=
          ⟨not_le.mp hbot, not_le.mp htop⟩
        rw [if_pos hmid, if_neg htop, ite_self, mul_zero]
        have hp0 : ∀ e, 0 ≤ driftStepProb d ε ξ x j e :=
          CERW.Support.Drift.driftStepProb_nonneg hε.le hξ x j
        have habs := abs_stepMean_ramp_le q a (driftStepProb d ε ξ) x j hp0
          (CERW.Support.Drift.sum_driftStepProb hd ε ξ x j)
        have := le_abs_self (stepMean (driftStepProb d ε ξ) (ramp q a) x j)
        simp only [Finset.mem_range] at hj
        linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_neg_distrib] at hsum
  -- the count of first departures above the level
  have hF : (aboveCount q x n (a + Λ) : ℝ) ≤ ∑ j ∈ Finset.range n,
      (if x j ∉ (Finset.range j).image x then
          (if a + Λ ≤ inner ℝ q (toSpace (x j)) then (1 : ℝ) else 0) else 0) := by
    rw [CERW.Support.Occupation.sum_fresh_eq_sum_departureRange x n
      (fun z => if a + Λ ≤ inner ℝ q (toSpace z) then (1 : ℝ) else 0), Finset.sum_boole]
    unfold aboveCount
    refine Nat.cast_le.mpr (Finset.card_le_card fun z hz => ?_)
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.le⟩
  -- the count of times spent strictly between the levels
  have hcard : ((departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z) ∧
        inner ℝ q (toSpace z) < a + Λ)).card + aboveCount q x n (a + Λ) ≤
      aboveCount q x n (a - Λ) := by
    unfold aboveCount
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card fun z hz => ?_
      simp only [Finset.mem_union, Finset.mem_filter] at hz ⊢
      rcases hz with ⟨h1, h2, _⟩ | ⟨h1, h2⟩
      · exact ⟨h1, h2⟩
      · exact ⟨h1, by linarith⟩
    · rw [Finset.disjoint_filter]
      intro z _ h1 h2
      exact absurd h2 (not_lt.mpr h1.2.le)
  have hG : ((∑ j ∈ Finset.range n,
      (if a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ
        then (1 : ℝ) else 0)) : ℝ) ≤ S * ((departureRange x n).filter
          (fun z => a - Λ < inner ℝ q (toSpace z) ∧ inner ℝ q (toSpace z) < a + Λ)).card := by
    rw [Finset.sum_boole]
    have hle := Finset.card_le_mul_card_image_of_maps_to
      (s := (Finset.range n).filter (fun j => a - Λ < inner ℝ q (toSpace (x j)) ∧
        inner ℝ q (toSpace (x j)) < a + Λ)) (f := x)
      (t := (departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z) ∧
        inner ℝ q (toSpace z) < a + Λ))
      (fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp only [Finset.mem_filter, departureRange, Finset.mem_image, Finset.mem_range]
        exact ⟨⟨j, hj.1, rfl⟩, hj.2⟩) S (fun z hz => by
        simp only [Finset.mem_filter] at hz
        refine le_trans (Finset.card_le_card fun j hj => ?_) (hS z hz.1 hz.2.1)
        simp only [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1.1, hj.2⟩)
    exact_mod_cast hle
  -- the martingale term
  have hsumS : ∑ z ∈ (departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z)),
      (localTime x n z : ℝ) ≤ S * aboveCount q x n (a - Λ) := by
    calc ∑ z ∈ (departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z)),
          (localTime x n z : ℝ)
        ≤ ∑ _z ∈ (departureRange x n).filter (fun z => a - Λ < inner ℝ q (toSpace z)),
            (S : ℝ) := by
          refine Finset.sum_le_sum fun z hz => ?_
          simp only [Finset.mem_filter] at hz
          exact_mod_cast hS z hz.1 hz.2
      _ = S * aboveCount q x n (a - Λ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          rfl
  have hM' : C₁ * (Real.sqrt (lg * ∑ z ∈ (departureRange x n).filter
        (fun z => a - Λ < inner ℝ q (toSpace z)), (localTime x n z : ℝ)) + lg) ≤
      C₁ * (Real.sqrt (lg * (S * aboveCount q x n (a - Λ))) + lg) := by
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsumS hlg)
    linarith
  have hcard' : ((((departureRange x n).filter
        (fun z => a - Λ < inner ℝ q (toSpace z) ∧ inner ℝ q (toSpace z) < a + Λ)).card : ℕ) : ℝ)
      ≤ (aboveCount q x n (a - Λ) : ℝ) - aboveCount q x n (a + Λ) := by
    have : (((departureRange x n).filter
        (fun z => a - Λ < inner ℝ q (toSpace z) ∧ inner ℝ q (toSpace z) < a + Λ)).card : ℝ) +
        aboveCount q x n (a + Λ) ≤ aboveCount q x n (a - Λ) := by exact_mod_cast hcard
    linarith
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have h1 : Λ * ((∑ j ∈ Finset.range n,
      (if a - Λ < inner ℝ q (toSpace (x j)) ∧ inner ℝ q (toSpace (x j)) < a + Λ
        then (1 : ℝ) else 0))) ≤ Λ * S * ((aboveCount q x n (a - Λ) : ℝ) -
          aboveCount q x n (a + Λ)) := by
    calc Λ * (∑ j ∈ Finset.range n, (if a - Λ < inner ℝ q (toSpace (x j)) ∧
            inner ℝ q (toSpace (x j)) < a + Λ then (1 : ℝ) else 0))
        ≤ Λ * (S * ((departureRange x n).filter
          (fun z => a - Λ < inner ℝ q (toSpace z) ∧ inner ℝ q (toSpace z) < a + Λ)).card) :=
          mul_le_mul_of_nonneg_left hG hΛ.le
      _ ≤ Λ * (S * ((aboveCount q x n (a - Λ) : ℝ) - aboveCount q x n (a + Λ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard' hS0) hΛ.le
      _ = Λ * S * ((aboveCount q x n (a - Λ) : ℝ) - aboveCount q x n (a + Λ)) := by ring
  have h2 := mul_le_mul_of_nonneg_left hF hεα.le
  linarith [hmart, hM, hM']

/-- The compensated path `Z_t = X_t + ε Σ_{j<t} I_j ξ(X_j)`, where `I_j` marks a first
departure. -/
private noncomputable def compensatedPath (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  toSpace (x t) + ε • ∑ j ∈ Finset.range t, if x j ∉ departureRange x j then ξ (x j) else 0

/-- If every first departure in `[s, t)` has nonnegative drift in the direction `u`, then the
increment of `u · X` over `[s, t)` obeys the bound on the increments of the compensated path. -/
private lemma inner_sub_le_of_drift {ε : ℝ} (hε : 0 ≤ ε) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) {n : ℕ} {C Λ lg : ℝ} {u : EuclideanSpace ℝ (Fin d)} (hu : ‖u‖ ≤ Λ)
    (hZ : ∀ s t : ℕ, s < t → t ≤ n →
      ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ ≤ C * Real.sqrt ((t - s : ℝ) * lg))
    {s t : ℕ} (hst : s < t) (htn : t ≤ n)
    (hxi : ∀ j : ℕ, s ≤ j → j < t → x j ∉ departureRange x j → 0 ≤ inner ℝ u (ξ (x j))) :
    inner ℝ u (toSpace (x t) - toSpace (x s)) ≤ Λ * (C * Real.sqrt ((t - s : ℝ) * lg)) := by
  set f : ℕ → EuclideanSpace ℝ (Fin d) := fun j =>
    if x j ∉ departureRange x j then ξ (x j) else 0 with hf
  have hsum : ∑ j ∈ Finset.range t, f j =
      ∑ j ∈ Finset.range s, f j + ∑ j ∈ Finset.Ico s t, f j :=
    (Finset.sum_range_add_sum_Ico f hst.le).symm
  have hZeq : compensatedPath ε ξ x t - compensatedPath ε ξ x s =
      (toSpace (x t) - toSpace (x s)) + ε • ∑ j ∈ Finset.Ico s t, f j := by
    simp only [compensatedPath, ← hf, hsum, smul_add]
    abel
  have hT : 0 ≤ inner ℝ u (∑ j ∈ Finset.Ico s t, f j) := by
    rw [inner_sum]
    refine Finset.sum_nonneg fun j hj => ?_
    by_cases hdep : x j ∉ departureRange x j
    · simp only [hf, if_pos hdep]
      exact hxi j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2 hdep
    · simp only [hf, if_neg hdep, inner_zero_right, le_refl]
  have hinner : inner ℝ u (compensatedPath ε ξ x t - compensatedPath ε ξ x s) =
      inner ℝ u (toSpace (x t) - toSpace (x s)) +
        ε * inner ℝ u (∑ j ∈ Finset.Ico s t, f j) := by
    rw [hZeq, inner_add_right, real_inner_smul_right]
  have hεT : 0 ≤ ε * inner ℝ u (∑ j ∈ Finset.Ico s t, f j) := mul_nonneg hε hT
  have hΛ : 0 ≤ Λ := (norm_nonneg u).trans hu
  calc inner ℝ u (toSpace (x t) - toSpace (x s))
      ≤ inner ℝ u (compensatedPath ε ξ x t - compensatedPath ε ξ x s) := by linarith
    _ ≤ ‖u‖ * ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ := real_inner_le_norm _ _
    _ ≤ Λ * ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ :=
        mul_le_mul_of_nonneg_right hu (norm_nonneg _)
    _ ≤ Λ * (C * Real.sqrt ((t - s : ℝ) * lg)) :=
        mul_le_mul_of_nonneg_left (hZ s t hst htn) hΛ

/-- A path that finishes above the level `ā + Λ` and spends few steps above `ā`, at sites of
small local time, gains little above `ā`: its last entrance into `{q · z > ā}` is followed by a
crossing whose duration is at most the number of sites times the largest local time. -/
private lemma top_bound {ε : ℝ} (hε : 0 ≤ ε) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    {q : EuclideanSpace ℝ (Fin d)} {Λ : ℝ} (hΛ : 0 < Λ) (hq : ‖q‖ ≤ Λ) (x : ℕ → Site d)
    (hx0 : x 0 = 0) (hstep : ∀ j, x (j + 1) - x j ∈ unitSteps d) {n : ℕ} {C₁ lg : ℝ}
    (hC₁ : 0 ≤ C₁) (hlg : 0 ≤ lg)
    (hZ : ∀ s t : ℕ, s < t → t ≤ n →
      ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ ≤ C₁ * Real.sqrt ((t - s : ℝ) * lg))
    {σ : ℕ} (hσn : σ ≤ n) {ā : ℝ} (hā : 0 ≤ ā) (hT : ā + Λ < inner ℝ q (toSpace (x σ)))
    (hxi : ∀ j < σ, ā < inner ℝ q (toSpace (x j)) → x j ∉ departureRange x j →
      0 ≤ inner ℝ q (ξ (x j)))
    {S : ℕ} (hS : ∀ z ∈ departureRange x n, ā < inner ℝ q (toSpace z) → localTime x n z ≤ S) :
    inner ℝ q (toSpace (x σ)) ≤
      ā + Λ + Λ * (C₁ * Real.sqrt (S * aboveCount q x n ā * lg)) := by
  have hσ0 : 0 < σ := by
    rcases Nat.eq_zero_or_pos σ with h | h
    · rw [h, hx0, CERW.Support.Occupation.toSpace_zero, inner_zero_right] at hT
      linarith
    · exact h
  have hstepq : ∀ j, inner ℝ q (toSpace (x (j + 1))) ≤ inner ℝ q (toSpace (x j)) + Λ := by
    intro j
    have h1 : toSpace (x (j + 1)) = toSpace (x j) + toSpace (x (j + 1) - x j) := by
      rw [← toSpace_add]
      congr 1
      abel
    rw [h1, inner_add_right]
    have := abs_inner_toSpace_le q (hstep j)
    have := (abs_le.mp (this.trans hq)).2
    linarith
  obtain ⟨s, hs0, hsσ, hfs, hfj⟩ := CERW.Support.Crossing.exists_last_entrance
    (f := fun j => inner ℝ q (toSpace (x j)) / Λ) (b := ā / Λ) (τ := σ)
    (by
      rw [hx0, CERW.Support.Occupation.toSpace_zero, inner_zero_right, zero_div]
      exact div_nonneg hā hΛ.le)
    (fun j => by
      rw [div_le_iff₀ hΛ, add_mul, one_mul, div_mul_cancel₀ _ hΛ.ne']
      exact hstepq j) hσ0
  have hxs : inner ℝ q (toSpace (x s)) ≤ ā + Λ := by
    have := hfs
    rw [div_le_iff₀ hΛ, add_mul, one_mul, div_mul_cancel₀ _ hΛ.ne'] at this
    exact this
  have hxj : ∀ j, s ≤ j → j < σ → ā < inner ℝ q (toSpace (x j)) := fun j h1 h2 =>
    (div_lt_div_iff_of_pos_right hΛ).mp (hfj j h1 h2)
  have hsσ' : s < σ := by
    rcases hsσ.lt_or_eq with h | h
    · exact h
    · rw [h] at hxs
      linarith
  have hdrift := inner_sub_le_of_drift hε ξ x hq hZ hsσ' hσn
    (fun j h1 h2 h3 => hxi j h2 (hxj j h1 h2) h3)
  -- the duration of the crossing
  have hdur : σ - s ≤ S * aboveCount q x n ā := by
    have hle := Finset.card_le_mul_card_image_of_maps_to (s := Finset.Ico s σ) (f := x)
      (t := (departureRange x n).filter (fun z => ā < inner ℝ q (toSpace z)))
      (fun j hj => by
        rw [Finset.mem_Ico] at hj
        simp only [Finset.mem_filter, departureRange, Finset.mem_image, Finset.mem_range]
        exact ⟨⟨j, by omega, rfl⟩, hxj j hj.1 hj.2⟩) S (fun z hz => by
        simp only [Finset.mem_filter] at hz
        refine le_trans (Finset.card_le_card fun j hj => ?_) (hS z hz.1 hz.2)
        simp only [Finset.mem_filter, Finset.mem_Ico] at hj
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hj.2⟩)
    rw [Nat.card_Ico] at hle
    exact hle
  have hdur' : ((σ : ℝ) - s) * lg ≤ S * aboveCount q x n ā * lg := by
    have : ((σ : ℝ) - s) ≤ S * aboveCount q x n ā := by
      have h := (Nat.cast_le (α := ℝ)).mpr hdur
      rwa [Nat.cast_sub hsσ'.le, Nat.cast_mul] at h
    exact mul_le_mul_of_nonneg_right this hlg
  have hsqrt : Real.sqrt (((σ : ℝ) - s) * lg) ≤ Real.sqrt (S * aboveCount q x n ā * lg) :=
    Real.sqrt_le_sqrt hdur'
  have hsplit : inner ℝ q (toSpace (x σ)) =
      inner ℝ q (toSpace (x s)) + inner ℝ q (toSpace (x σ) - toSpace (x s)) := by
    rw [inner_sub_right]
    ring
  have hfin : Λ * (C₁ * Real.sqrt (((σ : ℝ) - s) * lg)) ≤
      Λ * (C₁ * Real.sqrt (S * aboveCount q x n ā * lg)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt hC₁) hΛ.le
  linarith

/-- `log n ≥ 1/2` for `n ≥ 2`. -/
private lemma half_le_log {n : ℕ} (hn : 2 ≤ n) : 1 / 2 ≤ Real.log n := by
  have h1 : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have h2 := Real.log_two_gt_d9
  linarith

/-- A sequence contracted at each step by the factor `1 - 1/(2 (A L + 1))` up to an additive
error `O(L log n)` is of order `L log n` after `O(L log n)` steps, when it starts below `n`. -/
private lemma exists_small_level {A B L : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hL : 1 ≤ L) {n : ℕ}
    (hn : 2 ≤ n) (u : ℕ → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hun : u 0 ≤ n)
    (hrec : ∀ i, u (i + 1) ≤ A * L * (u i - u (i + 1)) +
      B * Real.sqrt (L * u i * Real.log n) + B * Real.log n) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ (2 * A + 4) * L * Real.log n ∧
      u k ≤ (B ^ 2 + 2 * B + 2) * L * Real.log n := by
  set lg : ℝ := Real.log n with hlg
  have hlg2 : 1 / 2 ≤ lg := half_le_log hn
  have hlg0 : 0 < lg := by linarith
  set c : ℝ := A * L + 1 with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ A * L := mul_nonneg hA.le (by linarith)
    linarith
  have hc0 : 0 < c := by linarith
  set E : ℝ := (B ^ 2 / 2 + B) * L * lg with hE
  have hE0 : 0 ≤ E := by positivity
  set ρ : ℝ := 1 - 1 / (2 * c) with hρ
  have hρ0 : 0 ≤ ρ := by
    have : 1 / (2 * c) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  -- one step of the contraction
  have hstep : ∀ i, u (i + 1) ≤ ρ * u i + E / c := by
    intro i
    have h1 := hrec i
    have hsq : B * Real.sqrt (L * u i * lg) ≤ (u i + B ^ 2 * L * lg) / 2 := by
      have hLl : 0 ≤ L * lg := by positivity
      have hsplit : Real.sqrt (L * u i * lg) = Real.sqrt (L * lg) * Real.sqrt (u i) := by
        rw [← Real.sqrt_mul hLl]
        congr 1
        ring
      have ht : (B * Real.sqrt (L * lg)) ^ 2 = B ^ 2 * L * lg := by
        rw [mul_pow, Real.sq_sqrt hLl]
        ring
      have hs : Real.sqrt (u i) ^ 2 = u i := Real.sq_sqrt (hu0 i)
      have hprod : B * Real.sqrt (L * u i * lg) =
          (B * Real.sqrt (L * lg)) * Real.sqrt (u i) := by
        rw [hsplit]
        ring
      rw [hprod]
      linarith [sq_nonneg (B * Real.sqrt (L * lg) - Real.sqrt (u i))]
    have hLlg : lg ≤ L * lg := by
      have := mul_le_mul_of_nonneg_right hL hlg0.le
      linarith
    have hBl : B * lg ≤ B * L * lg := by
      have := mul_le_mul_of_nonneg_left hLlg hB
      linarith
    have hmain : c * u (i + 1) ≤ (c - 1 / 2) * u i + E := by
      rw [hc, hE]
      linarith
    rw [← sub_nonneg] at hmain ⊢
    have : ρ * u i + E / c - u (i + 1) = ((c - 1 / 2) * u i + E - c * u (i + 1)) / c := by
      rw [hρ]
      field_simp
    rw [this]
    exact div_nonneg hmain hc0.le
  -- iteration
  have hiter : ∀ k : ℕ, u k ≤ ρ ^ k * u 0 + 2 * E := by
    intro k
    induction k with
    | zero => simp only [pow_zero, one_mul]; linarith
    | succ k ih =>
        have h1 := hstep k
        have h2 : ρ * u k ≤ ρ * (ρ ^ k * u 0 + 2 * E) := mul_le_mul_of_nonneg_left ih hρ0
        have hkey : ρ * (2 * E) + E / c = 2 * E := by
          rw [hρ]
          field_simp
          ring
        rw [pow_succ]
        linarith [hkey, h1, h2]
  -- the choice of the number of steps
  set k : ℕ := ⌈2 * c * lg⌉₊ with hk
  have hk1 : 1 ≤ k := by
    rw [hk]
    exact Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Nat.ceil_eq_zero, not_le]
      positivity)
  have hkge : 2 * c * lg ≤ k := Nat.le_ceil _
  have hρk : ρ ^ k * u 0 ≤ 1 := by
    have hexp : ρ ≤ Real.exp (-(1 / (2 * c))) := by
      have := Real.add_one_le_exp (-(1 / (2 * c)))
      rw [hρ]
      linarith
    have hpow : ρ ^ k ≤ Real.exp (-(1 / (2 * c))) ^ k := pow_le_pow_left₀ hρ0 hexp k
    have hexp2 : Real.exp (-(1 / (2 * c))) ^ k = Real.exp (-(1 / (2 * c)) * k) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    have hlow : lg ≤ 1 / (2 * c) * k := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      linarith
    have hexp3 : Real.exp (-(1 / (2 * c)) * k) ≤ Real.exp (-lg) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hexp4 : Real.exp (-lg) = (n : ℝ)⁻¹ := by
      rw [hlg, Real.exp_neg, Real.exp_log (by exact_mod_cast (by omega : 0 < n))]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    calc ρ ^ k * u 0 ≤ (n : ℝ)⁻¹ * n := by
          apply mul_le_mul _ hun (hu0 0) (by positivity)
          calc ρ ^ k ≤ _ := hpow
            _ = _ := hexp2
            _ ≤ _ := hexp3
            _ = _ := hexp4
      _ = 1 := inv_mul_cancel₀ hnpos.ne'
  refine ⟨k, hk1, ?_, ?_⟩
  · have hk2 : (k : ℝ) < 2 * c * lg + 1 := Nat.ceil_lt_add_one (by positivity)
    have hLlg : lg ≤ L * lg := by
      have := mul_le_mul_of_nonneg_right hL hlg0.le
      linarith
    rw [hc] at hk2
    linarith
  · have := hiter k
    have h2 : 2 * E = (B ^ 2 + 2 * B) * L * lg := by rw [hE]; ring
    have hLlg : lg ≤ L * lg := by
      have := mul_le_mul_of_nonneg_right hL hlg0.le
      linarith
    linarith

/-- The recurrence for the level counts: divide the level inequality by `ε α`, using
`S ≤ L` and `u' ≤ u`. -/
private lemma recurrence_step {ε α C₁ Λ S L lg ui un A B : ℝ} (hεα : 0 < ε * α)
    (hΛ : 0 < Λ) (hlg : 0 ≤ lg) (hC₁ : 0 ≤ C₁) (hSL : S ≤ L) (hui : 0 ≤ ui)
    (hdiff : un ≤ ui) (hA : A = Λ / (ε * α)) (hB : B = C₁ / (ε * α))
    (hlev : ε * α * un ≤ Λ * S * (ui - un) +
      C₁ * (Real.sqrt (lg * (S * ui)) + lg)) :
    un ≤ A * L * (ui - un) + B * Real.sqrt (L * ui * lg) + B * lg := by
  have hd0 : 0 ≤ ui - un := sub_nonneg.mpr hdiff
  have h1 : Λ * S * (ui - un) ≤ Λ * L * (ui - un) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSL hΛ.le) hd0
  have h2 : Real.sqrt (lg * (S * ui)) ≤ Real.sqrt (L * ui * lg) := by
    refine Real.sqrt_le_sqrt ?_
    rw [mul_comm lg]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSL hui) hlg
  have h3 := mul_le_mul_of_nonneg_left (add_le_add_right h2 lg) hC₁
  have hlev' : ε * α * un ≤ Λ * L * (ui - un) + C₁ * (Real.sqrt (L * ui * lg) + lg) := by
    linarith
  have hAe : A * (ε * α) = Λ := by rw [hA]; exact div_mul_cancel₀ _ hεα.ne'
  have hBe : B * (ε * α) = C₁ := by rw [hB]; exact div_mul_cancel₀ _ hεα.ne'
  have key : (A * L * (ui - un) + B * Real.sqrt (L * ui * lg) + B * lg) * (ε * α) =
      Λ * L * (ui - un) + C₁ * (Real.sqrt (L * ui * lg) + lg) := by
    calc (A * L * (ui - un) + B * Real.sqrt (L * ui * lg) + B * lg) * (ε * α)
        = (A * (ε * α)) * L * (ui - un) + (B * (ε * α)) * (Real.sqrt (L * ui * lg) + lg) := by
          ring
      _ = _ := by rw [hAe, hBe]
  refine le_of_mul_le_mul_right ?_ hεα
  rw [key]
  linarith

/-- The arithmetic of the last step: the level `ā` and the crossing bound combine into the
estimate `T ≤ max {T - h, b} + C L log n`. -/
private lemma final_arithmetic {T h b m a₀ Λ K₁ K₂ C₁ L lg k Y : ℝ} (hΛ : 0 < Λ)
    (hC₁ : 0 ≤ C₁) (hL : 1 ≤ L) (hlg : 1 / 2 ≤ lg)
    (hm : m ≤ max (T - h) b + Λ) (ha₀ : a₀ < m + Λ) (hkK : k ≤ K₁ * L * lg)
    (hYb : Y ≤ (K₂ + 1) * (L * lg))
    (hT : T ≤ a₀ - Λ + 2 * k * Λ + Λ + Λ * (C₁ * Y)) :
    T ≤ max (T - h) b + (4 * Λ + 2 * K₁ * Λ + Λ * C₁ * (K₂ + 1)) * L * lg := by
  have hLl : 1 / 2 ≤ L * lg := by
    have := mul_le_mul_of_nonneg_right hL (by linarith : 0 ≤ lg)
    linarith
  have h1 : 2 * k * Λ ≤ 2 * K₁ * Λ * (L * lg) := by
    have := mul_le_mul_of_nonneg_left hkK (by positivity : (0 : ℝ) ≤ 2 * Λ)
    linarith
  have h2 : 2 * Λ ≤ 4 * Λ * (L * lg) := by
    have := mul_le_mul_of_nonneg_left hLl hΛ.le
    linarith
  have h3 : Λ * (C₁ * Y) ≤ Λ * C₁ * (K₂ + 1) * (L * lg) := by
    have := mul_le_mul_of_nonneg_left hYb (mul_nonneg hΛ.le hC₁)
    linarith
  have hexp : (4 * Λ + 2 * K₁ * Λ + Λ * C₁ * (K₂ + 1)) * L * lg =
      4 * Λ * (L * lg) + 2 * K₁ * Λ * (L * lg) + Λ * C₁ * (K₂ + 1) * (L * lg) := by ring
  rw [hexp]
  linarith

/-- The square root in the crossing duration bound is at most `(K₂ + 1) L log n`. -/
private lemma sqrt_crossing_bound {S L lg u K₂ : ℝ} (hS : S ≤ L) (hS0 : 0 ≤ S) (hu : 0 ≤ u)
    (hlg : 0 ≤ lg) (hK₂ : 0 ≤ K₂) (huK : u ≤ K₂ * (L * lg)) :
    Real.sqrt (S * u * lg) ≤ (K₂ + 1) * (L * lg) := by
  have hL : 0 ≤ L := hS0.trans hS
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 : S * u * lg ≤ L * (K₂ * (L * lg)) * lg :=
    mul_le_mul_of_nonneg_right (mul_le_mul hS huK hu hL) hlg
  have h2 : K₂ ≤ (K₂ + 1) ^ 2 := by nlinarith [sq_nonneg (K₂ + 1 / 2)]
  calc S * u * lg ≤ L * (K₂ * (L * lg)) * lg := h1
    _ = K₂ * (L * lg) ^ 2 := by ring
    _ ≤ (K₂ + 1) ^ 2 * (L * lg) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = ((K₂ + 1) * (L * lg)) ^ 2 := by ring

/-- The outer crossing estimate for a path and a direction `q`, in terms of a bound `Λ ≥ ‖q‖`
and the explicit inequalities of the hypotheses. -/
private lemma outer_crossing_core {d : ℕ} (hd : 1 ≤ d) {ε α C₁ Λ : ℝ} (hε : 0 < ε) (hα : 0 < α)
    (hC₁ : 0 < C₁) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) → ∀ n : ℕ, 2 ≤ n →
      ∀ q : EuclideanSpace ℝ (Fin d), ‖q‖ ≤ Λ →
      ∀ x : ℕ → Site d, x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) →
      (∀ s t : ℕ, s < t → t ≤ n → ‖compensatedPath ε ξ x t - compensatedPath ε ξ x s‖ ≤
        C₁ * Real.sqrt ((t - s : ℝ) * Real.log n)) →
      (∀ k : ℕ, k ≤ n →
        |dynkinMart (driftStepProb d ε ξ) (ramp q (k * Λ)) x n| ≤
          C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
            (fun z => k * Λ - Λ < inner ℝ q (toSpace z)), (localTime x n z : ℝ)) +
              Real.log n)) →
      ∀ j₀ : ℕ, j₀ ≤ n → ∀ h : ℝ, 0 < h →
      (∀ j ≤ n, inner ℝ q (toSpace (x j₀)) - h < inner ℝ q (toSpace (x j)) →
        α ≤ inner ℝ q (ξ (x j))) →
      ∀ b : ℝ, 0 ≤ b →
        inner ℝ q (toSpace (x j₀)) ≤ max (inner ℝ q (toSpace (x j₀)) - h) b +
          C * (1 + ((((departureRange x n).filter
            (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) *
              Real.log n := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Λ / (ε * α) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = C₁ / (ε * α) := ⟨_, rfl⟩
  have hεα : 0 < ε * α := mul_pos hε hα
  have hA : 0 < A := by rw [hAdef]; positivity
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = 2 * A + 4 := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂def⟩ : ∃ K₂ : ℝ, K₂ = B ^ 2 + 2 * B + 2 := ⟨_, rfl⟩
  have hK₁ : 0 < K₁ := by rw [hK₁def]; linarith
  have hK₂ : 0 < K₂ := by rw [hK₂def]; positivity
  refine ⟨4 * Λ + 2 * K₁ * Λ + Λ * C₁ * (K₂ + 1), by positivity, ?_⟩
  intro ξ hξ n hn q hq x hx0 hstep hZ hmart j₀ hj₀ h hh hα' b hb
  have hlg2 : 1 / 2 ≤ Real.log n := half_le_log hn
  have hlg0 : 0 ≤ Real.log n := by linarith
  -- the largest local time above `b`
  have hSloc : ∀ z ∈ departureRange x n, b ≤ inner ℝ q (toSpace z) → localTime x n z ≤
      ((departureRange x n).filter (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) :=
    fun z hz hbz => Finset.le_sup (f := localTime x n) (Finset.mem_filter.mpr ⟨hz, hbz⟩)
  generalize ((departureRange x n).filter
    (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) = S at hSloc ⊢
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 1 + S := ⟨_, rfl⟩
  rw [← hLdef]
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hSL : (S : ℝ) ≤ L := by rw [hLdef]; linarith
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = inner ℝ q (toSpace (x j₀)) := ⟨_, rfl⟩
  rw [← hTdef] at hα' ⊢
  have hproj : ∀ j : ℕ, inner ℝ q (toSpace (x j)) ≤ Λ * j := fun j =>
    calc inner ℝ q (toSpace (x j)) ≤ ‖q‖ * ‖toSpace (x j)‖ := real_inner_le_norm _ _
      _ ≤ Λ * j := mul_le_mul hq (norm_toSpace_le_index x hx0 hstep j) (norm_nonneg _) hΛ.le
  -- the first level above `max {T - h, b + Λ}` on the grid `Λ ℕ`
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = max (T - h) (b + Λ) := ⟨_, rfl⟩
  have hTm : T - h ≤ m := hmdef ▸ le_max_left _ _
  have hbm : b + Λ ≤ m := hmdef ▸ le_max_right _ _
  have hmax : m ≤ max (T - h) b + Λ := by
    rw [hmdef]
    exact max_le (by linarith [le_max_left (T - h) b]) (by linarith [le_max_right (T - h) b])
  obtain ⟨k₀, hk₀def⟩ : ∃ k₀ : ℕ, k₀ = ⌈m / Λ⌉₊ := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = k₀ * Λ := ⟨_, rfl⟩
  have hma₀ : m ≤ a₀ := by
    have := Nat.le_ceil (m / Λ)
    rw [← hk₀def, div_le_iff₀ hΛ] at this
    rwa [ha₀]
  have ha₀m : a₀ < m + Λ := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ m / Λ from div_nonneg (by linarith) hΛ.le)
    rw [← hk₀def] at h1
    have h2 := mul_lt_mul_of_pos_right h1 hΛ
    rw [add_mul, div_mul_cancel₀ _ hΛ.ne', one_mul] at h2
    rwa [ha₀]
  have ha₀nn : 0 ≤ a₀ := by linarith
  -- the number of sites above the levels `a₀ - Λ + 2 i Λ`
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ i : ℕ,
      u i = (aboveCount q x n (a₀ - Λ + 2 * i * Λ) : ℝ) := ⟨fun i => _, fun i => rfl⟩
  have hu0 : ∀ i, 0 ≤ u i := fun i => by rw [hu]; exact Nat.cast_nonneg _
  have hun : u 0 ≤ n := by
    rw [hu]
    have h1 : aboveCount q x n (a₀ - Λ + 2 * ((0 : ℕ) : ℝ) * Λ) ≤ n :=
      (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp))
    exact_mod_cast h1
  have hu_anti : ∀ i, u (i + 1) ≤ u i := fun i => by
    rw [hu, hu]
    refine Nat.cast_le.mpr (aboveCount_anti q x n ?_)
    push_cast
    linarith
  have hrec : ∀ i : ℕ, u (i + 1) ≤
      A * L * (u i - u (i + 1)) + B * Real.sqrt (L * u i * Real.log n) + B * Real.log n := by
    intro i
    have hlo : a₀ ≤ ((k₀ + 2 * i : ℕ) : ℝ) * Λ := by
      push_cast
      rw [ha₀]
      have : 0 ≤ 2 * (i : ℝ) * Λ := by positivity
      linarith
    have hul : a₀ - Λ + 2 * (i : ℝ) * Λ = ((k₀ + 2 * i : ℕ) : ℝ) * Λ - Λ := by
      push_cast
      rw [ha₀]
      ring
    have huh : a₀ - Λ + 2 * ((i + 1 : ℕ) : ℝ) * Λ = ((k₀ + 2 * i : ℕ) : ℝ) * Λ + Λ := by
      push_cast
      rw [ha₀]
      ring
    by_cases hk : k₀ + 2 * i ≤ n
    · have hlev := level_inequality hd hε hα hΛ hlg0 hC₁.le hξ hq x hx0 n
        (a := ((k₀ + 2 * i : ℕ) : ℝ) * Λ) (by positivity) (S := S)
        (fun z hz hzq => hSloc z hz (by linarith))
        (fun j hj hjq => hα' j hj.le (by linarith)) (hmart _ hk)
      rw [← hul, ← huh, ← hu, ← hu] at hlev
      exact recurrence_step hεα hΛ hlg0 hC₁.le hSL (hu0 i) (hu_anti i) hAdef hBdef hlev
    · have hzero : u i = 0 := by
        rw [hu, hul]
        have : aboveCount q x n (((k₀ + 2 * i : ℕ) : ℝ) * Λ - Λ) = 0 := by
          refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun z hz => ?_)
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
          rw [Finset.mem_range] at hj
          rw [not_lt]
          refine (hproj j).trans ?_
          have h1 : (n : ℝ) ≤ ((k₀ + 2 * i : ℕ) : ℝ) - 1 := by
            have : n + 1 ≤ k₀ + 2 * i := by omega
            have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((k₀ + 2 * i : ℕ) : ℝ) := Nat.cast_le.mpr this
            linarith [(Nat.cast_add_one n : ((n + 1 : ℕ) : ℝ) = n + 1)]
          have h2 : (j : ℝ) ≤ n := by exact_mod_cast hj.le
          have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) hΛ.le
          linarith
        rw [this]
        simp
      have hzero' : u (i + 1) = 0 := le_antisymm (hzero ▸ hu_anti i) (hu0 _)
      rw [hzero, hzero']
      simp only [sub_self, mul_zero, zero_mul, Real.sqrt_zero, zero_add]
      exact mul_nonneg hB hlg0
  -- the level at which few sites remain
  obtain ⟨k, hk1, hkK, hukK⟩ := exists_small_level hA hB hL1 hn u hu0 hun hrec
  rw [← hK₁def] at hkK
  rw [← hK₂def] at hukK
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hbar : a₀ + Λ ≤ a₀ - Λ + 2 * (k : ℝ) * Λ := by
    have := mul_nonneg (sub_nonneg.mpr hk1') hΛ.le
    linarith
  have hL0 : 0 ≤ L := by linarith
  by_cases hcase : T ≤ a₀ - Λ + 2 * (k : ℝ) * Λ + Λ
  · refine final_arithmetic (Y := 0) hΛ hC₁.le hL1 hlg2 hmax ha₀m hkK ?_ ?_
    · exact mul_nonneg (by linarith) (mul_nonneg hL0 hlg0)
    · rw [mul_zero, mul_zero, add_zero]
      exact hcase
  · have htop := top_bound hε.le ξ hΛ hq x hx0 hstep hC₁.le hlg0 hZ hj₀
      (ā := a₀ - Λ + 2 * (k : ℝ) * Λ) (by linarith)
      (by rw [← hTdef]; exact not_le.mp hcase)
      (fun j hj hjq _ => by
        have := hα' j (by omega) (by linarith)
        linarith)
      (S := S) (fun z hz hzq => hSloc z hz (by linarith))
    rw [← hTdef] at htop
    have hukS : (aboveCount q x n (a₀ - Λ + 2 * (k : ℝ) * Λ) : ℝ) ≤ K₂ * (L * Real.log n) := by
      rw [← hu k]
      linarith
    exact final_arithmetic hΛ hC₁.le hL1 hlg2 hmax ha₀m hkK
      (sqrt_crossing_bound hSL hS0 (Nat.cast_nonneg _) hlg0 hK₂.le hukS) htop

end Ramp

end CERW.Support.Norm.GaugeCoarseVolume.OuterCore

namespace CERW.Support.Norm.GaugeCoarseVolume.LinearCore

open CERW CERW.Support.Drift CERW.Support.Law

variable {d : ℕ}

/-- The embedding of lattice sites into `ℝ^d` is additive. -/
private lemma toSpace_add (x y : Site d) : toSpace (x + y) = toSpace x + toSpace y := by
  ext i
  simp [toSpace]

/-- A unit step changes a projection `⟨q, ·⟩` of the embedded position by at most `‖q‖`. -/
private lemma abs_inner_toSpace_le (q : EuclideanSpace ℝ (Fin d)) {e : Site d}
    (he : e ∈ unitSteps d) : |inner ℝ q (toSpace e)| ≤ ‖q‖ := by
  have h := abs_real_inner_le_norm q (toSpace e)
  rw [norm_toSpace, euclidNorm_of_mem_unitSteps he, mul_one] at h
  exact h

/-- The ramp `max (⟨q, ·⟩ - a) 0` moves by at most `‖q‖` in one unit step. -/
private lemma abs_ramp_sub_le (q : EuclideanSpace ℝ (Fin d)) (a : ℝ) (z : Site d) {e : Site d}
    (he : e ∈ unitSteps d) :
    |max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0| ≤ ‖q‖ := by
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have h : inner ℝ q (toSpace (z + e)) - a - (inner ℝ q (toSpace z) - a) =
      inner ℝ q (toSpace e) := by
    rw [toSpace_add, inner_add_right]
    ring
  rw [h]
  exact abs_inner_toSpace_le q he

/-- The squared one-step oscillation of the ramp is at most `Λ²` when the current value of
`⟨q, ·⟩` exceeds `a - Λ`, and vanishes otherwise. -/
private lemma ramp_sq_sub_le {q : EuclideanSpace ℝ (Fin d)} {Λ : ℝ} (hq : ‖q‖ ≤ Λ) (a : ℝ)
    (z : Site d) {e : Site d} (he : e ∈ unitSteps d) :
    (max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0) ^ 2 ≤
      Λ ^ 2 * (if a - Λ < inner ℝ q (toSpace z) then 1 else 0) := by
  split_ifs with h
  · rw [mul_one, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_ramp_sub_le q a z he).trans hq) 2
  · rw [mul_zero]
    have hle : inner ℝ q (toSpace z) ≤ a - Λ := not_lt.mp h
    have he' := (abs_le.mp (abs_inner_toSpace_le q he)).2
    have hq0 := norm_nonneg q
    have h1 : max (inner ℝ q (toSpace (z + e)) - a) 0 = 0 := by
      rw [toSpace_add, inner_add_right]
      exact max_eq_right (by linarith)
    have h2 : max (inner ℝ q (toSpace z) - a) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2]
    norm_num

/-- The one-step mean square oscillation of the ramp under a probability vector on the unit
steps is at most `Λ² 1{a - Λ < ⟨q, z⟩}`. -/
private lemma sum_ramp_sq_le {q : EuclideanSpace ℝ (Fin d)} {Λ : ℝ} (hq : ‖q‖ ≤ Λ) (a : ℝ)
    (z : Site d) {w : Site d → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∑ e ∈ unitSteps d, w e = 1) :
    ∑ e ∈ unitSteps d, w e *
        (max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0) ^ 2 ≤
      Λ ^ 2 * (if a - Λ < inner ℝ q (toSpace z) then 1 else 0) := by
  calc ∑ e ∈ unitSteps d, w e *
        (max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0) ^ 2
      ≤ ∑ e ∈ unitSteps d,
          w e * (Λ ^ 2 * (if a - Λ < inner ℝ q (toSpace z) then 1 else 0)) :=
        Finset.sum_le_sum fun e he =>
          mul_le_mul_of_nonneg_left (ramp_sq_sub_le hq a z he) (hw0 e)
    _ = Λ ^ 2 * (if a - Λ < inner ℝ q (toSpace z) then 1 else 0) := by
        rw [← Finset.sum_mul, hw1, one_mul]

/-- The predictable bracket of the rescaling `c M` of a martingale is at most
`c² K ∑_{t<n} g_t` whenever the conditional variances of the increments of `M` are at most
`K g_t`. -/
private lemma predBracket_smul_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c K : ℝ) (g : ℕ → Ω → ℝ)
    (hvar : ∀ t, μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t] ≤ᵐ[μ] fun ω => K * g t ω) :
    ∀ᵐ ω ∂μ, ∀ n, predBracket μ ℱ (fun t ω => c * M t ω) (fun t ω => c * M t ω) n ω ≤
      c ^ 2 * (K * ∑ t ∈ Finset.range n, g t ω) := by
  have hscale : ∀ t,
      μ[fun ω => (c * M (t + 1) ω - c * M t ω) * (c * M (t + 1) ω - c * M t ω) | ℱ t]
        =ᵐ[μ] fun ω => c ^ 2 * μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t] ω := by
    intro t
    have hfun : (fun ω => (c * M (t + 1) ω - c * M t ω) * (c * M (t + 1) ω - c * M t ω)) =
        (c ^ 2) • fun ω => (M (t + 1) ω - M t ω) ^ 2 := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    exact condExp_smul (c ^ 2) _ (ℱ t)
  filter_upwards [ae_all_iff.mpr hvar, ae_all_iff.mpr hscale] with ω h1 h2 n
  unfold predBracket
  rw [Finset.sum_apply]
  calc ∑ t ∈ Finset.range n,
        μ[fun ω => (c * M (t + 1) ω - c * M t ω) * (c * M (t + 1) ω - c * M t ω) | ℱ t] ω
      ≤ ∑ t ∈ Finset.range n, c ^ 2 * (K * g t ω) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [h2 t]
        exact mul_le_mul_of_nonneg_left (h1 t) (sq_nonneg c)
    _ = c ^ 2 * (K * ∑ t ∈ Finset.range n, g t ω) := by
        rw [Finset.mul_sum, Finset.mul_sum]

/-- The local times summed over the sites of the departure range that satisfy `P` count the
times `t < n` at which the path satisfies `P`. -/
private lemma sum_filter_localTime (Y : ℕ → Site d) (n : ℕ) (P : Site d → Prop)
    [DecidablePred P] :
    ∑ z ∈ (departureRange Y n).filter P, (localTime Y n z : ℝ) =
      ∑ t ∈ Finset.range n, if P (Y t) then (1 : ℝ) else 0 := by
  have h := CERW.Support.LocalTime.sum_range_eq_sum_localTime Y n
    (fun z => if P z then (1 : ℝ) else 0)
  refine Eq.trans ?_ h.symm
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : P z <;> simp [hz]

/-- Rescaling: if `|c M_n - c M_0| ≤ C_F (√(b L) + L)` with `c (2 B) = 1`, `M_0 = 0` and
`b ≤ S`, then `|M_n| ≤ 2 B C_F (√(L S) + L)`. -/
private lemma abs_le_of_rescaled {c B C_F L b S M₀ Mₙ : ℝ} (hB : 0 ≤ B) (hc : c * (2 * B) = 1)
    (hC_F : 0 ≤ C_F) (hL : 0 ≤ L) (hbS : b ≤ S) (hM₀ : M₀ = 0)
    (h : |c * Mₙ - c * M₀| ≤ C_F * (Real.sqrt (b * L) + L)) :
    |Mₙ| ≤ 2 * B * C_F * (Real.sqrt (L * S) + L) := by
  have hMn : Mₙ = 2 * B * (c * Mₙ) := by
    calc Mₙ = (c * (2 * B)) * Mₙ := by rw [hc, one_mul]
      _ = 2 * B * (c * Mₙ) := by ring
  rw [hM₀, mul_zero, sub_zero] at h
  have habs : |Mₙ| = 2 * B * |c * Mₙ| := by
    have h2B : (0 : ℝ) ≤ 2 * B := by linarith
    calc |Mₙ| = |2 * B * (c * Mₙ)| := congrArg (fun x => |x|) hMn
      _ = 2 * B * |c * Mₙ| := by rw [abs_mul, abs_of_nonneg h2B]
  have hsqrt : Real.sqrt (b * L) ≤ Real.sqrt (L * S) :=
    Real.sqrt_le_sqrt (by rw [mul_comm L S]; exact mul_le_mul_of_nonneg_right hbS hL)
  calc |Mₙ| = 2 * B * |c * Mₙ| := habs
    _ ≤ 2 * B * (C_F * (Real.sqrt (b * L) + L)) :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ ≤ 2 * B * (C_F * (Real.sqrt (L * S) + L)) := by
        gcongr
    _ = 2 * B * C_F * (Real.sqrt (L * S) + L) := by ring

/-- For one pair `(q, k)`, the Dynkin martingale of the ramp `max (⟨q, ·⟩ - kΛ) 0` of the drift
walk exceeds `2 (Λ + 1) C_F (√(log n · S) + log n)` with probability at most `C_F n^{-p}`, where
`S` is the total local time of the sites with `⟨q, z⟩ > kΛ - Λ`, given Freedman's bound for the
natural filtration of the walk. -/
private lemma measure_linear_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {X : ℕ → Ω → Site d} (hd : 1 ≤ d) (hε : 0 ≤ ε) (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) {Λ : ℝ} (hΛ : 0 ≤ Λ) {q : EuclideanSpace ℝ (Fin d)}
    (hq : ‖q‖ ≤ Λ) (k : ℕ) {n : ℕ} {C_F p : ℝ} (hC_F : 0 ≤ C_F)
    (hF : ∀ Z : ℕ → Ω → ℝ, Martingale Z (pathFiltration hX.measurable) μ →
      (∀ᵐ ω ∂μ, ∀ t, |Z (t + 1) ω - Z t ω| ≤ 1) →
      μ {ω | ¬ |Z n ω - Z 0 ω| ≤ C_F * (Real.sqrt (predBracket μ (pathFiltration hX.measurable)
          Z Z n ω * Real.log n) + Real.log n)} ≤ ENNReal.ofReal (C_F * (n : ℝ) ^ (-p))) :
    μ {ω | 2 * (Λ + 1) * C_F * (Real.sqrt (Real.log n *
          ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
          (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
        |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * Λ) 0) (fun j => X j ω) n|} ≤
      ENNReal.ofReal (C_F * (n : ℝ) ^ (-p)) := by
  classical
  set ℱ := pathFiltration hX.measurable with hℱ
  set f : Site d → ℝ := fun z => max (inner ℝ q (toSpace z) - k * Λ) 0 with hf
  set c : ℝ := (2 * (Λ + 1))⁻¹ with hc
  have hB : 0 < 2 * (Λ + 1) := by linarith
  have hc0 : 0 ≤ c := inv_nonneg.mpr hB.le
  have hc1 : c * (2 * (Λ + 1)) = 1 := inv_mul_cancel₀ hB.ne'
  have hc2 : c * (2 * Λ) ≤ 1 := by
    calc c * (2 * Λ) ≤ c * (2 * (Λ + 1)) := mul_le_mul_of_nonneg_left (by linarith) hc0
      _ = 1 := hc1
  have hcΛ : c * Λ ≤ 1 := by
    have h2 : c * (2 * Λ) = 2 * (c * Λ) := by ring
    linarith
  have hM := martingale_driftDynkin hd hε hξ hX f
  have hZ : Martingale (fun t ω => c * driftDynkin ε ξ f X t ω) ℱ μ := hM.smul c
  have hinc : ∀ᵐ ω ∂μ, ∀ t,
      |driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω| ≤ 2 * Λ := by
    filter_upwards [ae_abs_driftDynkin_succ_sub_le hd hε hξ hX f] with ω hω t
    exact hω t Λ fun e he => (abs_ramp_sub_le q (k * Λ) (X t ω) he).trans hq
  have hincZ : ∀ᵐ ω ∂μ, ∀ t,
      |c * driftDynkin ε ξ f X (t + 1) ω - c * driftDynkin ε ξ f X t ω| ≤ 1 := by
    filter_upwards [hinc] with ω hω t
    rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left (hω t) hc0).trans hc2
  have hvar : ∀ t, μ[fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) ^ 2 |
        ℱ t] ≤ᵐ[μ]
      fun ω => Λ ^ 2 * (if (k : ℝ) * Λ - Λ < inner ℝ q (toSpace (X t ω)) then 1 else 0) := by
    intro t
    refine (condExp_sq_driftDynkin_succ_sub_le hd hε hξ hX f t).trans
      (Filter.Eventually.of_forall fun ω => ?_)
    exact sum_ramp_sq_le hq (k * Λ) (X t ω) (fun e => driftStepProb_nonneg hε hξ _ t e)
      (sum_driftStepProb hd ε ξ _ t)
  have hbr := predBracket_smul_le ℱ (driftDynkin ε ξ f X) c (Λ ^ 2)
    (fun t ω => if (k : ℝ) * Λ - Λ < inner ℝ q (toSpace (X t ω)) then 1 else 0) hvar
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  refine le_trans (measure_mono_ae ?_) (hF _ hZ hincZ)
  filter_upwards [hbr] with ω hω hmem
  intro hle
  have hcount : ∑ z ∈ (departureRange (fun j => X j ω) n).filter
        (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
        (localTime (fun j => X j ω) n z : ℝ) =
      ∑ t ∈ Finset.range n,
        (if (k : ℝ) * Λ - Λ < inner ℝ q (toSpace (X t ω)) then (1 : ℝ) else 0) :=
    sum_filter_localTime (fun j => X j ω) n _
  have hS0 : 0 ≤ ∑ z ∈ (departureRange (fun j => X j ω) n).filter
        (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
        (localTime (fun j => X j ω) n z : ℝ) :=
    Finset.sum_nonneg fun z _ => Nat.cast_nonneg _
  have hcΛ2 : c ^ 2 * Λ ^ 2 ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg hc0 hΛ) hcΛ
  have hbS : predBracket μ ℱ (fun t ω => c * driftDynkin ε ξ f X t ω)
        (fun t ω => c * driftDynkin ε ξ f X t ω) n ω ≤
      ∑ z ∈ (departureRange (fun j => X j ω) n).filter
        (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
        (localTime (fun j => X j ω) n z : ℝ) := by
    calc predBracket μ ℱ (fun t ω => c * driftDynkin ε ξ f X t ω)
          (fun t ω => c * driftDynkin ε ξ f X t ω) n ω
        ≤ c ^ 2 * (Λ ^ 2 * ∑ t ∈ Finset.range n,
            (if (k : ℝ) * Λ - Λ < inner ℝ q (toSpace (X t ω)) then (1 : ℝ) else 0)) := hω n
      _ = (c ^ 2 * Λ ^ 2) * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
            (localTime (fun j => X j ω) n z : ℝ) := by
          rw [hcount]
          ring
      _ ≤ 1 * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
            (localTime (fun j => X j ω) n z : ℝ) :=
          mul_le_mul_of_nonneg_right hcΛ2 hS0
      _ = _ := one_mul _
  have hmem' : 2 * (Λ + 1) * C_F * (Real.sqrt (Real.log n *
          ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
          (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
        |driftDynkin ε ξ f X n ω| := by
    rw [← dynkinMart_driftStepProb_eq_driftDynkin hd ε ξ f X n ω]
    exact hmem
  exact absurd hmem' (not_lt.mpr (abs_le_of_rescaled (by linarith) hc1 hC_F hL hbS
    (driftDynkin_zero ε ξ f X ω) hle))

end CERW.Support.Norm.GaugeCoarseVolume.LinearCore

namespace CERW.Support.Norm.GaugeCoarseVolume

open CERW CERW.Support.Norm.MinkowskiGauge CERW.Support.Norm.GaugeModel
  CERW.Support.Norm.GaugePotential

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} {K : Set (EuclideanSpace ℝ (Fin d))}

/-- A simultaneous half-space martingale bound for a deterministic finite family of directions. -/
theorem exists_gauge_linear_martingale_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ξ : Site d → EuclideanSpace ℝ (Fin d)},
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        ∀ Q : Finset (EuclideanSpace ℝ (Fin d)), (∀ q ∈ Q, ‖q‖ ≤ normMax (gauge K)) →
        μ {ω | ∃ q ∈ Q, ∃ k : ℕ, k ≤ n ∧
          C * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
                (fun z => (k : ℝ) * normMax (gauge K) - normMax (gauge K) < inner ℝ q (toSpace z)),
              (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
            |dynkinMart (driftStepProb d ε ξ)
              (fun z => max (inner ℝ q (toSpace z) - k * normMax (gauge K)) 0)
              (fun j => X j ω) n|} ≤
          ENNReal.ofReal (C * ((Q.card : ℝ) * ((n : ℝ) + 1)) * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  have hΛ : 0 ≤ normMax (gauge K) := normMax_gauge_nonneg K
  obtain ⟨C_F, hC_F, hfree⟩ := CERW.Support.Norm.freedman_bound p hp
  refine ⟨(2 * (normMax (gauge K) + 1) + 1) * C_F, mul_pos (by linarith) hC_F, ?_⟩
  intro ξ hξ hξ0 Ω inst μ inst' X hX n hn Q hQ
  have hcoord := drift_coord_bound_gauge hε.le hell hξ hξ0
  have hF := hfree n hn μ (CERW.Support.Law.pathFiltration hX.measurable)
  set E : EuclideanSpace ℝ (Fin d) → ℕ → Set Ω := fun q k =>
    {ω | 2 * (normMax (gauge K) + 1) * C_F * (Real.sqrt (Real.log n *
        ∑ z ∈ (departureRange (fun j => X j ω) n).filter
          (fun z => (k : ℝ) * normMax (gauge K) - normMax (gauge K) < inner ℝ q (toSpace z)),
        (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
      |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * normMax (gauge K)) 0) (fun j => X j ω) n|} with hE
  have key : ∀ q ∈ Q, ∀ k : ℕ, μ (E q k) ≤ ENNReal.ofReal (C_F * (n : ℝ) ^ (-p)) :=
    fun q hq k => LinearCore.measure_linear_le hd1 hε.le hcoord hX hΛ (hQ q hq) k hC_F.le hF
  have hsub : {ω | ∃ q ∈ Q, ∃ k : ℕ, k ≤ n ∧
        (2 * (normMax (gauge K) + 1) + 1) * C_F * (Real.sqrt (Real.log n *
          ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * normMax (gauge K) - normMax (gauge K) < inner ℝ q (toSpace z)),
          (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
        |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax (gauge K)) 0) (fun j => X j ω) n|} ⊆
      ⋃ q ∈ Q, ⋃ k ∈ Finset.range (n + 1), E q k := by
    intro ω hω
    obtain ⟨q, hq, k, hk, hlt⟩ := hω
    simp only [Set.mem_iUnion]
    refine ⟨q, hq, k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), ?_⟩
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hC_F.le) ?_) hlt
    exact add_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n)
  have hR : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine (measure_mono hsub).trans ?_
  calc μ (⋃ q ∈ Q, ⋃ k ∈ Finset.range (n + 1), E q k)
      ≤ ∑ q ∈ Q, μ (⋃ k ∈ Finset.range (n + 1), E q k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Q, ∑ k ∈ Finset.range (n + 1), μ (E q k) :=
        Finset.sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Q, ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (C_F * (n : ℝ) ^ (-p)) :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun k _ => key q hq k
    _ = ENNReal.ofReal ((Q.card : ℝ) * (((n + 1 : ℕ) : ℝ) * (C_F * (n : ℝ) ^ (-p)))) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((2 * (normMax (gauge K) + 1) + 1) * C_F) *
          ((Q.card : ℝ) * ((n : ℝ) + 1)) * (n : ℝ) ^ (-p)) := by
        apply ENNReal.ofReal_le_ofReal
        have hK : 1 ≤ 2 * (normMax (gauge K) + 1) + 1 := by linarith
        have hP : 0 ≤ (Q.card : ℝ) * ((n : ℝ) + 1) * (n : ℝ) ^ (-p) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
            (add_nonneg (Nat.cast_nonneg n) zero_le_one)) hR
        calc (Q.card : ℝ) * (((n + 1 : ℕ) : ℝ) * (C_F * (n : ℝ) ^ (-p)))
            = C_F * ((Q.card : ℝ) * ((n : ℝ) + 1) * (n : ℝ) ^ (-p)) := by
              push_cast
              ring
          _ ≤ ((2 * (normMax (gauge K) + 1) + 1) * C_F) *
              ((Q.card : ℝ) * ((n : ℝ) + 1) * (n : ℝ) ^ (-p)) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hC_F.le hK) hP
          _ = ((2 * (normMax (gauge K) + 1) + 1) * C_F) *
              ((Q.card : ℝ) * ((n : ℝ) + 1)) * (n : ℝ) ^ (-p) := by ring

/-! ## The family of directions -/

/-- The direction `Λ_ψ u_z` of a site `z`, where `u_z = z / |z|` and `u_0 = 0`. -/
noncomputable def capDirection (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (z : Site d) :
    EuclideanSpace ℝ (Fin d) :=
  normMax Ψ • (‖toSpace z‖⁻¹ • toSpace z)

/-- The finite deterministic family `{Λ_ψ u_z : |z| ≤ n}` of directions of the half-space
martingales. -/
noncomputable def capDirections (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  (LatticeProb.ballFinset d (n : ℝ)).image (capDirection Ψ)

/-- Every direction of the family has length at most `Λ_ψ`. -/
theorem norm_capDirection_le (hΛ : 0 ≤ normMax Ψ) (z : Site d) :
    ‖capDirection Ψ z‖ ≤ normMax Ψ := by
  unfold capDirection
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΛ,
    abs_inv, abs_of_nonneg (norm_nonneg _)]
  rcases eq_or_ne ‖toSpace z‖ 0 with h0 | h0
  · rw [h0]
    simpa using hΛ
  · rw [inv_mul_cancel₀ h0, mul_one]

/-- Every vector of the family `capDirections ψ n` has length at most `Λ_ψ`. -/
theorem norm_le_of_mem_capDirections (hΛ : 0 ≤ normMax Ψ) {n : ℕ}
    {q : EuclideanSpace ℝ (Fin d)} (hq : q ∈ capDirections Ψ n) : ‖q‖ ≤ normMax Ψ := by
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
  exact norm_capDirection_le hΛ z

/-- The direction of a site of Euclidean norm at most `n` belongs to the family. -/
theorem capDirection_mem_capDirections {n : ℕ} {z : Site d} (hz : euclidNorm z ≤ n) :
    capDirection Ψ z ∈ capDirections Ψ n :=
  Finset.mem_image_of_mem _ (LatticeProb.mem_ballFinset_iff.mpr hz)

/-- The family has at most `(2n + 1)^d` vectors. -/
theorem card_capDirections_le (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ) :
    ((capDirections Ψ n).card : ℝ) ≤ (2 * (n : ℝ) + 1) ^ d :=
  (Nat.cast_le.mpr Finset.card_image_le).trans
    (LatticeProb.card_ballFinset_le d (Nat.cast_nonneg n))


/-! ## The cap drift alignment -/

/-- The lattice embedding of the origin is the origin. -/
private lemma toSpace_zero_eq : toSpace (0 : Site d) = 0 := by
  ext i
  simp [toSpace]

/-- **The drift in a cap about the farthest direction.** Let `w ≠ 0` have Euclidean norm `R`, let
`q = Λ w / R`, and let `θ = c² / (8 Λ²)`. If `y` has Euclidean norm at most `R` and
`q · y > (1 - θ) Λ R`, then every subgradient `ξ` of the gauge `ψ` at `y` satisfies
`q · ξ ≥ Λ c / 2`: by Euler's relation `ξ · y = ψ(y) ≥ c |y|`, the unit vectors `w / R` and
`y / |y|` differ by less than `c / (2 Λ)`, and `|ξ| ≤ Λ`. -/
private theorem cap_drift_alignment (hd : 1 ≤ d) (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {w y ξ : EuclideanSpace ℝ (Fin d)} (hR : 0 < ‖w‖) (hy : ‖y‖ ≤ ‖w‖)
    (hξ : IsSubgradient (gauge K) y ξ)
    (hcap : (1 - normMin (gauge K) ^ 2 / (8 * normMax (gauge K) ^ 2)) * (normMax (gauge K) * ‖w‖) <
      inner ℝ (normMax (gauge K) • (‖w‖⁻¹ • w)) y) :
    normMax (gauge K) * normMin (gauge K) / 2 ≤ inner ℝ (normMax (gauge K) • (‖w‖⁻¹ • w)) ξ := by
  obtain ⟨hc0, hcle⟩ := normMin_gauge_pos_mul_le hK h0 hd
  have hcΛ : normMin (gauge K) ≤ normMax (gauge K) := normMin_gauge_le_normMax_gauge hK h0 hd
  have hΛ : 0 < normMax (gauge K) := lt_of_lt_of_le hc0 hcΛ
  set c := normMin (gauge K) with hc
  set Λ := normMax (gauge K) with hΛdef
  set R := ‖w‖ with hRdef
  set θ : ℝ := c ^ 2 / (8 * Λ ^ 2) with hθ
  set u : EuclideanSpace ℝ (Fin d) := R⁻¹ • w with hu
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 8 := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : c ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hc0.le hcΛ 2
    linarith
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w)]
    exact inv_mul_cancel₀ hR.ne'
  have hnξ : ‖ξ‖ ≤ Λ := norm_le_normMax_of_isSubgradient hK h0 hξ
  -- the cap hypothesis for `u`
  have hcap' : (1 - θ) * R < inner ℝ u y := by
    have h1 : inner ℝ (Λ • u) y = Λ * inner ℝ u y := real_inner_smul_left _ _ _
    rw [h1] at hcap
    have h2 : Λ * ((1 - θ) * R) < Λ * inner ℝ u y := by linarith
    exact lt_of_mul_lt_mul_left h2 hΛ.le
  have hy0 : 0 < ‖y‖ := by
    rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
    · exfalso
      have hy' : y = 0 := norm_eq_zero.mp h0.symm
      rw [hy', inner_zero_right] at hcap'
      have : 0 < (1 - θ) * R := mul_pos (by linarith) hR
      linarith
    · exact h0
  set v : EuclideanSpace ℝ (Fin d) := ‖y‖⁻¹ • y with hv
  have hnv : ‖v‖ = 1 := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg y)]
    exact inv_mul_cancel₀ hy0.ne'
  have huv : 1 - θ < inner ℝ u v := by
    have h1 : inner ℝ u v = ‖y‖⁻¹ * inner ℝ u y := real_inner_smul_right _ _ _
    rw [h1]
    have h2 : (1 - θ) * ‖y‖ < inner ℝ u y := by
      have : (1 - θ) * ‖y‖ ≤ (1 - θ) * R :=
        mul_le_mul_of_nonneg_left hy (by linarith)
      linarith
    rw [← div_eq_inv_mul, lt_div_iff₀ hy0]
    exact h2
  have hdist : ‖u - v‖ ^ 2 < 2 * θ := by
    rw [norm_sub_sq_real, hnu, hnv]
    linarith
  have hΛd : Λ * ‖u - v‖ < c / 2 := by
    by_contra hcon
    have hcon' : c / 2 ≤ Λ * ‖u - v‖ := not_lt.mp hcon
    have h1 : (c / 2) ^ 2 ≤ (Λ * ‖u - v‖) ^ 2 := pow_le_pow_left₀ (by positivity) hcon' 2
    have h2 : (Λ * ‖u - v‖) ^ 2 = Λ ^ 2 * ‖u - v‖ ^ 2 := by ring
    have h3 : Λ ^ 2 * ‖u - v‖ ^ 2 < Λ ^ 2 * (2 * θ) :=
      mul_lt_mul_of_pos_left hdist (by positivity)
    have h4 : Λ ^ 2 * (2 * θ) = (c / 2) ^ 2 := by
      rw [hθ]
      field_simp
      ring
    linarith
  -- Euler's relation at `y`
  obtain ⟨heuler, -⟩ := (isSubgradient_gauge_iff K).1 hξ
  have hvξ : c ≤ inner ℝ v ξ := by
    have h1 : inner ℝ v ξ = ‖y‖⁻¹ * inner ℝ y ξ := real_inner_smul_left _ _ _
    have h2 : inner ℝ y ξ = gauge K y := by rw [real_inner_comm]; exact heuler
    have h3 : c * ‖y‖ ≤ gauge K y := hcle y
    rw [h1, h2, ← div_eq_inv_mul, le_div_iff₀ hy0]
    exact h3
  have hdiff : -(‖u - v‖ * Λ) ≤ inner ℝ (u - v) ξ := by
    have h1 : |inner ℝ (u - v) ξ| ≤ ‖u - v‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
    have h2 : ‖u - v‖ * ‖ξ‖ ≤ ‖u - v‖ * Λ := mul_le_mul_of_nonneg_left hnξ (norm_nonneg _)
    have h3 := neg_abs_le (inner ℝ (u - v) ξ)
    linarith
  have huξ : c / 2 < inner ℝ u ξ := by
    have h1 : inner ℝ u ξ = inner ℝ v ξ + inner ℝ (u - v) ξ := by
      rw [← inner_add_left]
      congr 1
      abel
    have h2 : ‖u - v‖ * Λ = Λ * ‖u - v‖ := by ring
    linarith
  have h5 : inner ℝ (Λ • u) ξ = Λ * inner ℝ u ξ := real_inner_smul_left _ _ _
  rw [h5]
  have h6 : Λ * (c / 2) ≤ Λ * inner ℝ u ξ := mul_le_mul_of_nonneg_left huξ.le hΛ.le
  linarith

/-! ## The rough outer bound -/

/-- A site whose pairing with a vector `q` of length at most `Λ_ψ` is at least `Λ_ψ a / c_ψ` has
`ψ ≥ a`. -/
private theorem le_norm_of_cap_level (hd : 1 ≤ d) (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {q z : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ normMax (gauge K)) {a : ℝ}
    (hz : normMax (gauge K) * a / normMin (gauge K) ≤ inner ℝ q z) : a ≤ gauge K z := by
  obtain ⟨hc0, hcle⟩ := normMin_gauge_pos_mul_le hK h0 hd
  have hΛ : 0 < normMax (gauge K) := lt_of_lt_of_le hc0 (normMin_gauge_le_normMax_gauge hK h0 hd)
  have h1 : inner ℝ q z ≤ normMax (gauge K) * ‖z‖ :=
    (real_inner_le_norm q z).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg z))
  have h2 : normMax (gauge K) * a / normMin (gauge K) ≤ normMax (gauge K) * ‖z‖ := hz.trans h1
  rw [div_le_iff₀ hc0] at h2
  have h3 : normMax (gauge K) * a ≤ normMax (gauge K) * (normMin (gauge K) * ‖z‖) := by linarith
  have h4 : a ≤ normMin (gauge K) * ‖z‖ := le_of_mul_le_mul_left h3 hΛ
  exact h4.trans (hcle z)

/-- **The rough outer bound for the gauge of every compact convex body and every real level.** There is a constant `C`, chosen
from the body, the drift strength and the constants of the two martingale bounds, such that for
every choice of subgradients `ξ`, every `n ≥ 2` and every nearest-neighbour path from the origin
that satisfies the vector bound with constant `C_V` and the half-space martingale bounds with
constant `C_M` for the finite family `capDirections ψ n`, every real `a ≥ 0` satisfies
`max_{j ≤ n} |x_j| ≤ a / c_ψ + C (1 + max_{ψ(z) ≥ a} ℓ_n(z)) log n`. The crossing lemma is applied
in the direction `Λ_ψ u_{x_*}` of a Euclidean farthest point `x_*` of the path, with
`θ = c_ψ² / (8 Λ_ψ²)`, drift bound `α = Λ_ψ c_ψ / 2` and level `Λ_ψ a / c_ψ`. -/
theorem gauge_rough_outer_bound (hd : 2 ≤ d) (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {C_V C_M : ℝ} (hC_V : 0 < C_V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (n : ℕ), 2 ≤ n → ∀ (x : ℕ → Site d), x 0 = 0 →
      (∀ j, x (j + 1) - x j ∈ unitSteps d) →
      (∀ s t : ℕ, s < t → t ≤ n →
        ‖VectorBound.driftCompensated ε ξ x t - VectorBound.driftCompensated ε ξ x s‖ ≤
          C_V * Real.sqrt (((t : ℝ) - s) * Real.log n)) →
      (∀ q ∈ capDirections (gauge K) n, ∀ k : ℕ, k ≤ n →
        |dynkinMart (driftStepProb d ε ξ)
            (fun z => max (inner ℝ q (toSpace z) - k * normMax (gauge K)) 0) x n| ≤
          C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
              (fun z => (k : ℝ) * normMax (gauge K) - normMax (gauge K) < inner ℝ q (toSpace z)),
            (localTime x n z : ℝ)) + Real.log n)) →
      ∀ a : ℝ, 0 ≤ a →
        maxRadius x n ≤ a / normMin (gauge K) + C * (1 + ((((departureRange x n).filter
          (fun z => a ≤ gauge K (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) * Real.log n := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc0, hcle⟩ := normMin_gauge_pos_mul_le hK h0 hd1
  have hcΛ : normMin (gauge K) ≤ normMax (gauge K) := normMin_gauge_le_normMax_gauge hK h0 hd1
  have hΛ : 0 < normMax (gauge K) := lt_of_lt_of_le hc0 hcΛ
  set θ : ℝ := normMin (gauge K) ^ 2 / (8 * normMax (gauge K) ^ 2) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 8 := by
    rw [hθdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : normMin (gauge K) ^ 2 ≤ normMax (gauge K) ^ 2 := pow_le_pow_left₀ hc0.le hcΛ 2
    linarith
  set α : ℝ := normMax (gauge K) * normMin (gauge K) / 2 with hαdef
  have hα : 0 < α := by positivity
  have hC₁ : 0 < max C_V C_M := lt_max_of_lt_left hC_V
  obtain ⟨C, hCpos, hC⟩ := OuterCore.outer_crossing_core hd1 hε hα hC₁ hΛ
  refine ⟨C * (1 + θ⁻¹) / normMax (gauge K), by positivity, ?_⟩
  intro ξ hξ hξ0 n hn x hx0 hstep hvec hmart a ha
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  set S : ℝ := ((((departureRange x n).filter (fun z => a ≤ gauge K (toSpace z))).sup
    (localTime x n) : ℕ) : ℝ) with hSdef
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  set F : ℝ := C * (1 + S) * Real.log n with hFdef
  have hF0 : 0 ≤ F := by positivity
  have hrhs : C * (1 + θ⁻¹) / normMax (gauge K) * (1 + S) * Real.log n = (1 + θ⁻¹) * F / normMax (gauge K) := by
    rw [hFdef]
    ring
  rw [hrhs]
  have hκ0 : 0 ≤ (1 + θ⁻¹) * F / normMax (gauge K) := by positivity
  by_cases hR : maxRadius x n = 0
  · rw [hR]
    exact add_nonneg (div_nonneg ha hc0.le) hκ0
  have hRpos : 0 < maxRadius x n := by
    have h0 : 0 ≤ maxRadius x n :=
      (by rw [← norm_toSpace]; exact norm_nonneg _ : 0 ≤ euclidNorm (x 0)).trans
        (euclidNorm_le_maxRadius x (Nat.zero_le n))
    exact lt_of_le_of_ne h0 (Ne.symm hR)
  -- a farthest point of the path
  obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun j => euclidNorm (x j)) ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
  have hj₀n : j₀ ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj₀mem)
  have hmax : ∀ j ≤ n, euclidNorm (x j) ≤ euclidNorm (x j₀) :=
    fun j hj => hj₀max j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hRj : maxRadius x n = euclidNorm (x j₀) :=
    le_antisymm
      (Finset.sup'_le _ _ fun j hj => hmax j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
      (euclidNorm_le_maxRadius x hj₀n)
  set w : EuclideanSpace ℝ (Fin d) := toSpace (x j₀) with hw
  have hwR : ‖w‖ = maxRadius x n := by rw [hw, norm_toSpace, hRj]
  have hnorm_le : ∀ j ≤ n, ‖toSpace (x j)‖ ≤ ‖w‖ := fun j hj => by
    rw [norm_toSpace, hwR, hRj]
    exact hmax j hj
  -- the direction `q = Λ u_{x_*}`
  set q : EuclideanSpace ℝ (Fin d) := capDirection (gauge K) (x j₀) with hqdef
  have hqeq : q = normMax (gauge K) • (‖w‖⁻¹ • w) := rfl
  have hqn : ‖q‖ ≤ normMax (gauge K) := norm_capDirection_le hΛ.le _
  have hqmem : q ∈ capDirections (gauge K) n :=
    capDirection_mem_capDirections
      ((CERW.Support.Occupation.euclidNorm_le_of_steps x hx0 hstep j₀).trans
        (by exact_mod_cast hj₀n))
  have hqw : inner ℝ q w = normMax (gauge K) * ‖w‖ := by
    rw [hqeq, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  set T : ℝ := inner ℝ q w with hTdef
  have hT : T = normMax (gauge K) * ‖w‖ := hqw
  have hTpos : 0 < T := by rw [hT]; exact mul_pos hΛ (hwR ▸ hRpos)
  set h : ℝ := θ * T with hhdef
  have hh : 0 < h := mul_pos hθ0 hTpos
  have hThm : T - h = (1 - θ) * (normMax (gauge K) * ‖w‖) := by rw [hhdef, hT]; ring
  have hcap : ∀ j ≤ n, T - h < inner ℝ q (toSpace (x j)) → α ≤ inner ℝ q (ξ (x j)) := by
    intro j hj hlt
    have hxj : x j ≠ 0 := by
      intro h0
      rw [h0, toSpace_zero_eq, inner_zero_right] at hlt
      have : 0 < T - h := by rw [hThm]; exact mul_pos (by linarith) (mul_pos hΛ (hwR ▸ hRpos))
      linarith
    rw [hThm, hqeq] at hlt
    rw [hqeq]
    exact cap_drift_alignment hd1 hK h0 (hwR ▸ hRpos) (hnorm_le j hj) (hξ (x j) hxj) hlt
  -- the crossing lemma, for the vector and martingale bounds with the common constant
  have hvec' : ∀ s t : ℕ, s < t → t ≤ n →
      ‖(toSpace (x t) + ε • ∑ j ∈ Finset.range t,
          if x j ∉ departureRange x j then ξ (x j) else 0) -
        (toSpace (x s) + ε • ∑ j ∈ Finset.range s,
          if x j ∉ departureRange x j then ξ (x j) else 0)‖ ≤
        max C_V C_M * Real.sqrt (((t : ℝ) - s) * Real.log n) := fun s t hst htn =>
    (hvec s t hst htn).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have hmart' : ∀ k : ℕ, k ≤ n →
      |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax (gauge K)) 0) x n| ≤
        max C_V C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
            (fun z => (k : ℝ) * normMax (gauge K) - normMax (gauge K) < inner ℝ q (toSpace z)),
          (localTime x n z : ℝ)) + Real.log n) := fun k hk =>
    (hmart q hqmem k hk).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (add_nonneg (Real.sqrt_nonneg _) hlog))
  have hb : 0 ≤ normMax (gauge K) * a / normMin (gauge K) := by positivity
  have hcross := hC ξ (drift_coord_bound_gauge hε.le hell hξ hξ0) n hn q hqn x hx0 hstep hvec'
    hmart' j₀ hj₀n h hh hcap (normMax (gauge K) * a / normMin (gauge K)) hb
  -- compare the two suprema of local times
  have hsub : ((departureRange x n).filter
      (fun z => normMax (gauge K) * a / normMin (gauge K) ≤ inner ℝ q (toSpace z))) ⊆
        (departureRange x n).filter (fun z => a ≤ gauge K (toSpace z)) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, le_norm_of_cap_level hd1 hK h0 hqn hz.2⟩
  have hsup : ((((departureRange x n).filter
      (fun z => normMax (gauge K) * a / normMin (gauge K) ≤ inner ℝ q (toSpace z))).sup
        (localTime x n) : ℕ) : ℝ) ≤ S := Nat.cast_le.mpr (Finset.sup_mono hsub)
  have hcross' : T ≤ max (T - h) (normMax (gauge K) * a / normMin (gauge K)) + F := by
    refine hcross.trans (add_le_add le_rfl ?_)
    rw [hFdef]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsup) hCpos.le) hlog
  rw [← hwR]
  rcases max_cases (T - h) (normMax (gauge K) * a / normMin (gauge K)) with ⟨hm, -⟩ | ⟨hm, -⟩
  · -- the maximum is `T - h`: `θ Λ R ≤ F`
    rw [hm] at hcross'
    have h1 : θ * (normMax (gauge K) * ‖w‖) ≤ F := by
      have : h ≤ F := by linarith
      rw [hhdef, hT] at this
      exact this
    have h2 : normMax (gauge K) * ‖w‖ ≤ θ⁻¹ * F := by
      have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hθ0.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hθ0.ne', one_mul] at this
    have h3 : ‖w‖ ≤ (1 + θ⁻¹) * F / normMax (gauge K) := by
      rw [le_div_iff₀ hΛ]
      have : (1 + θ⁻¹) * F = F + θ⁻¹ * F := by ring
      linarith
    have h4 : 0 ≤ a / normMin (gauge K) := div_nonneg ha hc0.le
    linarith
  · -- the maximum is the level: `Λ R ≤ Λ a / c + F`
    rw [hm] at hcross'
    have h1 : normMax (gauge K) * ‖w‖ ≤ normMax (gauge K) * a / normMin (gauge K) + F := by
      rw [← hT]
      exact hcross'
    have h2 : ‖w‖ ≤ a / normMin (gauge K) + F / normMax (gauge K) := by
      have h3 : normMax (gauge K) * a / normMin (gauge K) = normMax (gauge K) * (a / normMin (gauge K)) := by ring
      rw [h3] at h1
      have h4 : normMax (gauge K) * ‖w‖ ≤ normMax (gauge K) * (a / normMin (gauge K) + F / normMax (gauge K)) := by
        calc normMax (gauge K) * ‖w‖ ≤ normMax (gauge K) * (a / normMin (gauge K)) + F := h1
          _ = normMax (gauge K) * (a / normMin (gauge K) + F / normMax (gauge K)) := by field_simp
      exact le_of_mul_le_mul_left h4 hΛ
    have h5 : F / normMax (gauge K) ≤ (1 + θ⁻¹) * F / normMax (gauge K) := by
      apply div_le_div_of_nonneg_right _ hΛ.le
      have h6 : 0 ≤ θ⁻¹ * F := mul_nonneg (inv_nonneg.mpr hθ0.le) hF0
      have h7 : (1 + θ⁻¹) * F = F + θ⁻¹ * F := by ring
      linarith
    linarith


/-- The finite supremum of the local times over the sites of the departure range with `ψ ≥ a` is at
most `L` as soon as every site with `ψ ≥ a` has local time at most `L`. -/
theorem sup_localTime_filter_le {a L : ℝ} (hL : 0 ≤ L) (x : ℕ → Site d) (n : ℕ)
    (h : ∀ z : Site d, a ≤ gauge K (toSpace z) → (localTime x n z : ℝ) ≤ L) :
    ((((departureRange x n).filter (fun z => a ≤ gauge K (toSpace z))).sup (localTime x n) : ℕ) : ℝ) ≤
      L := by
  have h1 : ((departureRange x n).filter (fun z => a ≤ gauge K (toSpace z))).sup (localTime x n) ≤
      ⌊L⌋₊ :=
    Finset.sup_le fun z hz => Nat.le_floor (h z (Finset.mem_filter.1 hz).2)
  exact (Nat.cast_le.2 h1).trans (Nat.floor_le hL)

/-- Every site with `ψ ≥ a` has local time at most the finite supremum over the departure range:
off the departure range the local time vanishes. With `sup_localTime_filter_le`, the supremum is
the maximum of `ℓ_n` over the lattice sites with `ψ ≥ a`, as in the paper. -/
theorem localTime_le_sup_filter (x : ℕ → Site d) (n : ℕ) {a : ℝ} {z : Site d}
    (hz : a ≤ gauge K (toSpace z)) :
    localTime x n z ≤
      ((departureRange x n).filter (fun z => a ≤ gauge K (toSpace z))).sup (localTime x n) := by
  by_cases hmem : z ∈ departureRange x n
  · exact Finset.le_sup (f := localTime x n) (Finset.mem_filter.2 ⟨hmem, hz⟩)
  · rw [mem_departureRange_iff, not_lt] at hmem
    exact hmem.trans (Nat.zero_le _)

/-- The path event of the Euclidean cap argument: start at the origin, unit steps, the vector bound
with constant `C_V`, and the half-space martingale bounds with constant `C_M` for every direction
of `capDirections ψ n` and every level `kΛ_ψ`, `k ≤ n`. -/
def CapEvent (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C_V C_M : ℝ) (n : ℕ) (x : ℕ → Site d) : Prop :=
  x 0 = 0 ∧ (∀ j, x (j + 1) - x j ∈ unitSteps d) ∧
  (∀ s t : ℕ, s < t → t ≤ n →
    ‖VectorBound.driftCompensated ε ξ x t - VectorBound.driftCompensated ε ξ x s‖ ≤
      C_V * Real.sqrt (((t : ℝ) - s) * Real.log n)) ∧
  (∀ q ∈ capDirections Ψ n, ∀ k : ℕ, k ≤ n →
    |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) x n| ≤
      C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
          (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
        (localTime x n z : ℝ)) + Real.log n))

/-- The rough outer bound for every real level `a ≥ 0`, as a property of a path. -/
def RoughOuter (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (C : ℝ) (n : ℕ) (x : ℕ → Site d) : Prop :=
  ∀ a : ℝ, 0 ≤ a →
    maxRadius x n ≤ a / normMin Ψ + C * (1 + ((((departureRange x n).filter
      (fun z => a ≤ Ψ (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) * Real.log n

/-- Every path of `CapEvent` satisfies the rough outer bound for every real level, with a constant
chosen before the field, the time and the path. -/
theorem exists_rough_outer_of_capEvent (hd : 2 ≤ d) (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ)) {C_V C_M : ℝ} (hC_V : 0 < C_V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (n : ℕ), 2 ≤ n → ∀ x : ℕ → Site d,
        CapEvent (gauge K) ε ξ C_V C_M n x → RoughOuter (gauge K) C n x := by
  obtain ⟨C, hC, hmain⟩ := gauge_rough_outer_bound hd hK h0 hε hell
    (C_V := C_V) (C_M := C_M) hC_V
  refine ⟨C, hC, fun ξ hξ hξ0 n hn x hx => ?_⟩
  obtain ⟨hx0, hstep, hvec, hmart⟩ := hx
  exact fun a ha => hmain ξ hξ hξ0 n hn x hx0 hstep hvec hmart a ha


/-! ## The failure probability -/

/-- A set covered by two events of small probability and a null event has small probability. -/
private lemma measure_le_of_subset_union_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ N : Set Ω} {a₁ a₂ C : ℝ} (hS : S ⊆ E₁ ∪ E₂ ∪ N)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂) (hN : μ N = 0)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hC : a₁ + a₂ ≤ C) : μ S ≤ ENNReal.ofReal C :=
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ N) := measure_mono hS
    _ ≤ μ (E₁ ∪ E₂) + μ N := measure_union_le _ _
    _ = μ (E₁ ∪ E₂) := by rw [hN, add_zero]
    _ ≤ μ E₁ + μ E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal a₁ + ENNReal.ofReal a₂ := add_le_add h₁ h₂
    _ = ENNReal.ofReal (a₁ + a₂) := (ENNReal.ofReal_add ha₁ ha₂).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-- The count of the directions in the union bound: at most `(2n+1)^d` directions and `n + 1`
levels cost at most `2 · 3^d n^{d+1}`, which `n^{-(p+d+1)}` turns into `n^{-p}`. -/
private lemma union_count_arith {C p : ℝ} (hC : 0 ≤ C) (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : c ≤ (2 * (n : ℝ) + 1) ^ d) :
    C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1)) ≤ (C * 2 * 3 ^ d) * (n : ℝ) ^ (-p) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hrp : 0 ≤ (n : ℝ) ^ (-(p + d + 1)) := Real.rpow_nonneg hnpos.le _
  have h1 : (2 * (n : ℝ) + 1) ^ d ≤ (3 * n) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have h2 : c * ((n : ℝ) + 1) ≤ 3 ^ d * (n : ℝ) ^ d * (2 * n) := by
    calc c * ((n : ℝ) + 1) ≤ (3 * (n : ℝ)) ^ d * (2 * n) :=
          mul_le_mul (hc.trans h1) (by linarith) (by positivity) (by positivity)
      _ = 3 ^ d * (n : ℝ) ^ d * (2 * n) := by rw [mul_pow]
  have h3 : (n : ℝ) ^ (-(p + d + 1)) = (n : ℝ) ^ (-p) * ((n : ℝ) ^ (d + 1))⁻¹ := by
    rw [show -(p + d + 1) = -p + -((d + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hnpos, Real.rpow_neg hnpos.le ((d + 1 : ℕ) : ℝ), Real.rpow_natCast]
  have h4 : (n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹ = 1 := by
    rw [← pow_succ]
    exact mul_inv_cancel₀ (pow_ne_zero _ hnpos.ne')
  calc C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1))
      ≤ C * (3 ^ d * (n : ℝ) ^ d * (2 * n)) * (n : ℝ) ^ (-(p + d + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC) hrp
    _ = (C * 2 * 3 ^ d) * (n : ℝ) ^ (-p) * ((n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹) := by
        rw [h3]
        ring
    _ = (C * 2 * 3 ^ d) * (n : ℝ) ^ (-p) := by rw [h4, mul_one]

/-- **The failure probability of the cap event.** For every `p > 0` there are constants `C_V`,
`C_M` and `C`, chosen from the gauge and the drift strength, such that for every field `ξ` of
subgradients, every probability space carrying the walk and every `n ≥ 2`, the set of sample points
whose path is not in `CapEvent` has probability at most `C n^{-p}`. The bound is on that failure set
only. -/
theorem exists_capEvent_failure_bound (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C_V C_M C : ℝ, 0 < C_V ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ CapEvent (gauge K) ε ξ C_V C_M n (fun j => X j ω)} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  have hΛ : 0 ≤ normMax (gauge K) := normMax_gauge_nonneg K
  obtain ⟨C_V, hC_V, hvec⟩ := VectorBound.exists_driftCompensated_bound.{u} hd1 hε.le hp
  obtain ⟨C_M, hC_M, hmart⟩ := exists_gauge_linear_martingale_bound hd hε hell
    (p := p + d + 1) (by positivity)
  refine ⟨C_V, C_M, C_V + C_M * 2 * 3 ^ d, hC_V, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hξ' := drift_coord_bound_gauge hε.le hell hξ hξ0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  have hQ : ∀ q ∈ capDirections (gauge K) n, ‖q‖ ≤ normMax (gauge K) :=
    fun q hq => norm_le_of_mem_capDirections hΛ hq
  have h₁ := hvec hξ' hξ0 hX n hn
  have h₂ := hmart hξ hξ0 hX n hn (capDirections (gauge K) n) hQ
  have h₂' := h₂.trans (ENNReal.ofReal_le_ofReal
    (union_count_arith (p := p) hC_M.le d (by omega) (card_capDirections_le (gauge K) n)))
  have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d)} = 0 := by
    have hpath : ∀ᵐ ω ∂μ, X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d := by
      have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
        rw [ae_iff]
        exact hX.start
      filter_upwards [h0, ae_all_iff.mpr
        (CERW.Support.Drift.ae_sub_mem_unitSteps_drift hd1 hε.le hξ' hX)] with ω h0 hs
      exact ⟨h0, hs⟩
    exact ae_iff.mp hpath
  refine measure_le_of_subset_union_three ?_ h₁ h₂' hnull (by positivity) (by positivity) ?_
  · intro ω hω
    by_contra hnot
    rw [Set.mem_union, Set.mem_union, not_or, not_or] at hnot
    obtain ⟨⟨hv, hh⟩, hpa⟩ := hnot
    have hP : X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d := by
      by_contra hc
      exact hpa hc
    refine hω ⟨hP.1, hP.2, ?_, ?_⟩
    · intro s t hst htn
      by_contra hcon
      exact hv ⟨s, t, hst, htn, not_le.mp hcon⟩
    · intro q hq k hk
      by_contra hcon
      exact hh ⟨q, hq, k, hk, not_le.mp hcon⟩
  · have : C_V * (n : ℝ) ^ (-p) + C_M * 2 * 3 ^ d * (n : ℝ) ^ (-p) =
        (C_V + C_M * 2 * 3 ^ d) * (n : ℝ) ^ (-p) := by ring
    exact this.le


/-- **The rough outer bound for all real levels, with high probability.** For every `p > 0` there
are constants `C_out` and `C` such that, for every field `ξ` of subgradients, every probability
space carrying the walk and every `n ≥ 2`, the set of sample points whose path fails the rough
outer bound `RoughOuter ψ C_out n` at some real level `a ≥ 0` has probability at most `C n^{-p}`.
The bound is on that failure set only. -/
theorem exists_rough_outer_failure_bound (hd : 2 ≤ d) (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C_out C : ℝ, 0 < C_out ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ RoughOuter (gauge K) C_out n (fun j => X j ω)} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C_V, C_M, C, hC_V, hC, hev⟩ := exists_capEvent_failure_bound.{u} hd hε hell hp
  obtain ⟨C_out, hC_out, hcap⟩ := exists_rough_outer_of_capEvent hd hK h0 hε hell
    (C_V := C_V) (C_M := C_M) hC_V
  refine ⟨C_out, C, hC_out, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  refine le_trans (measure_mono ?_) (hev ξ hξ hξ0 μ X hX n hn)
  intro ω hω hcapω
  exact hω (hcap ξ hξ hξ0 n hn _ hcapω)

/-- The rough outer bound at a real level that depends on the sample point: for every function `a`
of the sample point with values in `[0, ∞)`, with the constants of
`exists_rough_outer_failure_bound`, the set of sample points at which the bound at the level
`a ω` fails has probability at most `C n^{-p}`. No measurability or regularity of `a` is used. -/
theorem exists_rough_outer_failure_bound_at_level (hd : 2 ≤ d) (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ}
    (hε : 0 < ε) (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C_out C : ℝ, 0 < C_out ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        ∀ a : Ω → ℝ, (∀ ω, 0 ≤ a ω) →
        μ {ω | ¬ (maxRadius (fun j => X j ω) n ≤ a ω / normMin (gauge K) + C_out *
          (1 + ((((departureRange (fun j => X j ω) n).filter
            (fun z => a ω ≤ gauge K (toSpace z))).sup (localTime (fun j => X j ω) n) : ℕ) : ℝ)) *
          Real.log n)} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C_out, C, hC_out, hC, hev⟩ := exists_rough_outer_failure_bound.{u} hd hK h0 hε hell hp
  refine ⟨C_out, C, hC_out, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn a ha
  refine le_trans (measure_mono ?_) (hev ξ hξ hξ0 μ X hX n hn)
  intro ω hω hroughω
  exact hω (hroughω (a ω) (ha ω))

/-- The inner radius `inf_{y ∉ D_n} ψ(y)` is nonnegative: the level used for the second application
of the rough outer bound is an admissible level. -/
theorem normInnerRadius_gauge_nonneg (K : Set (EuclideanSpace ℝ (Fin d))) (x : ℕ → Site d)
    (n : ℕ) : 0 ≤ normInnerRadius (gauge K) x n :=
  Real.sInf_nonneg (by
    rintro _ ⟨y, -, rfl⟩
    exact gauge_nonneg y)

/-- The rough outer bound at the random level `inf_{y ∉ D_n} ψ(y)`, the level used in the proof of
the coarse bounds, fails with probability at most `C n^{-p}`, with the constants of
`exists_rough_outer_failure_bound`. -/
theorem exists_rough_outer_failure_bound_at_inner_radius (hd : 2 ≤ d) (hK : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K)
    {ε : ℝ} (hε : 0 < ε) (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C_out C : ℝ, 0 < C_out ∧ 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (maxRadius (fun j => X j ω) n ≤ normInnerRadius (gauge K) (fun j => X j ω) n /
            normMin (gauge K) + C_out * (1 + ((((departureRange (fun j => X j ω) n).filter
            (fun z => normInnerRadius (gauge K) (fun j => X j ω) n ≤ gauge K (toSpace z))).sup
              (localTime (fun j => X j ω) n) : ℕ) : ℝ)) * Real.log n)} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C_out, C, hC_out, hC, hev⟩ :=
    exists_rough_outer_failure_bound_at_level.{u} hd hK h0 hε hell hp
  refine ⟨C_out, C, hC_out, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  exact hev ξ hξ hξ0 μ X hX n hn (fun ω => normInnerRadius (gauge K) (fun j => X j ω) n)
    (fun ω => normInnerRadius_gauge_nonneg K _ n)

/-! ## The event together with the local time potential -/

/-- The three clauses of the local time potential lemma, as a property of a path: the largest local
time and the interval maxima, and the approximation of the cell local time by the potential of the
cell set on `{|y| ≤ 2n}`, with constant `C_L`. -/
def LocalTimeEvent (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (C_L : ℝ) (n : ℕ)
    (x : ℕ → Site d) : Prop :=
  (maxLocalTime x n : ℝ) ≤ C_L * ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) +
      C_L * Real.log n ^ 2 ∧
  (∀ s t : ℕ, s < t → t ≤ n →
    (intervalMax x s t : ℝ) ≤ C_L * (freshCount x s t : ℝ) ^ ((1 : ℝ) / d) +
      C_L * Real.log n ^ 2) ∧
  ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
    |cellLocalTime x n y - normPotential d ε Ψ (cellSet x n) y| ≤ C_L * Real.log n + C_L *
      (if d = 2 then Real.sqrt (maxLocalTime x n) * Real.log n
        else Real.sqrt (maxLocalTime x n * Real.log n))

/-! ## The geometry of the inner radius of the gauge -/

/-- The real volume of the sublevel set `{ψ < ρ}` of the gauge is `ρ^d |B_ψ|`. -/
private theorem real_volume_gauge_sublevel (hd : 1 ≤ d) (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume.real {v : EuclideanSpace ℝ (Fin d) | gauge K v < ρ} = ρ ^ d * normBallVolume (gauge K) := by
  rw [measureReal_def, volume_gauge_sublevel hK h0 hd hρ]
  exact ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hρ _) ENNReal.toReal_nonneg)

/-- The cell set of a path started at the origin, run for at least one step, contains the ball
of radius `1 / 2`: it contains the cell of the origin. -/
private theorem ball_subset_cellSet (X : ℕ → Site d) (n : ℕ) (hX0 : X 0 = 0) (hn : 1 ≤ n) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) ⊆ cellSet X n := by
  intro v hv
  have h0 : (0 : Site d) ∈ departureRange X n :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), hX0⟩
  refine Set.mem_iUnion₂.mpr ⟨0, h0, fun i => ?_⟩
  have hcoord : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  have hv' : ‖v‖ < 1 / 2 := mem_ball_zero_iff.mp hv
  have habs := abs_lt.mp (lt_of_le_of_lt hcoord hv')
  simp only [Pi.zero_apply, Int.cast_zero]
  constructor <;> linarith [habs.1, habs.2]

/-- The inner radius `inf_{y ∉ D} ψ(y)` of a bounded set containing a ball about the origin is
positive, the sublevel set of `ψ` at that radius lies in `D`, and the infimum is attained in the
closure of the complement. -/
private theorem inradius_facts (hd : 1 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDb : Bornology.IsBounded D) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ D) :
    0 < sInf ((gauge K) '' Dᶜ) ∧ {v | (gauge K) v < sInf ((gauge K) '' Dᶜ)} ⊆ D ∧
      ∃ y₀ : EuclideanSpace ℝ (Fin d), (gauge K) y₀ = sInf ((gauge K) '' Dᶜ) ∧ y₀ ∈ closure Dᶜ := by
  obtain ⟨hc, hle⟩ := normMin_gauge_pos_mul_le hK h0 hd
  have hcont : Continuous (gauge K) := (lipschitzWith_gauge hK hcv h0).continuous
  have hnn : ∀ y, 0 ≤ (gauge K) y := fun y => gauge_nonneg y
  have hne : (Dᶜ).Nonempty := by
    haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
    rw [Set.nonempty_compl]
    rintro rfl
    exact NormedSpace.unbounded_univ ℝ _ hDb
  have hbdd : BddBelow ((gauge K) '' Dᶜ) := ⟨0, by rintro _ ⟨y, _, rfl⟩; exact hnn y⟩
  have hge : ∀ y ∈ Dᶜ, sInf ((gauge K) '' Dᶜ) ≤ (gauge K) y := fun y hy =>
    csInf_le hbdd (Set.mem_image_of_mem (gauge K) hy)
  have hpos : 0 < sInf ((gauge K) '' Dᶜ) := by
    refine lt_of_lt_of_le (mul_pos hc hρ) (le_csInf (hne.image (gauge K)) ?_)
    rintro _ ⟨y, hy, rfl⟩
    have hyρ : ρ ≤ ‖y‖ := by
      by_contra h
      exact hy (hball (mem_ball_zero_iff.mpr (not_le.mp h)))
    calc normMin (gauge K) * ρ ≤ normMin (gauge K) * ‖y‖ := mul_le_mul_of_nonneg_left hyρ hc.le
      _ ≤ (gauge K) y := hle y
  refine ⟨hpos, fun v hv => ?_, ?_⟩
  · by_contra hvD
    exact absurd (hge v hvD) (not_le.mpr hv)
  · set Kc : Set (EuclideanSpace ℝ (Fin d)) := closure Dᶜ ∩ {y | (gauge K) y ≤ sInf ((gauge K) '' Dᶜ) + 1} with hKc
    have hKcclosed : IsClosed Kc := isClosed_closure.inter (isClosed_le hcont continuous_const)
    have hKcsub : Kc ⊆ Metric.closedBall 0 ((sInf ((gauge K) '' Dᶜ) + 1) / normMin (gauge K)) := by
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc]
      calc ‖y‖ * normMin (gauge K) = normMin (gauge K) * ‖y‖ := mul_comm _ _
        _ ≤ (gauge K) y := hle y
        _ ≤ sInf ((gauge K) '' Dᶜ) + 1 := hy.2
    have hKccpt : IsCompact Kc := (isCompact_closedBall _ _).of_isClosed_subset hKcclosed hKcsub
    have hlt : ∀ η : ℝ, 0 < η → ∃ y ∈ Dᶜ, (gauge K) y < sInf ((gauge K) '' Dᶜ) + η := fun η hη => by
      obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image (gauge K))
        (by linarith : sInf ((gauge K) '' Dᶜ) < sInf ((gauge K) '' Dᶜ) + η)
      exact ⟨y, hy, hlt⟩
    obtain ⟨y₁, hy₁, hy₁lt⟩ := hlt 1 one_pos
    have hKcne : Kc.Nonempty := ⟨y₁, subset_closure hy₁, hy₁lt.le⟩
    obtain ⟨y₀, hy₀K, hmin⟩ := hKccpt.exists_isMinOn hKcne hcont.continuousOn
    have hclosed : closure Dᶜ ⊆ {y | sInf ((gauge K) '' Dᶜ) ≤ (gauge K) y} :=
      closure_minimal hge (isClosed_le continuous_const hcont)
    have hy₀ge : sInf ((gauge K) '' Dᶜ) ≤ (gauge K) y₀ := hclosed hy₀K.1
    refine ⟨y₀, le_antisymm ?_ hy₀ge, hy₀K.1⟩
    by_contra hgt
    have hgt' : sInf ((gauge K) '' Dᶜ) < (gauge K) y₀ := not_le.mp hgt
    obtain ⟨y, hy, hylt⟩ := hlt (min (((gauge K) y₀ - sInf ((gauge K) '' Dᶜ)) / 2) 1)
      (lt_min (by linarith) one_pos)
    have hyK : y ∈ Kc := ⟨subset_closure hy, (hylt.trans_le (by
      linarith [min_le_right (((gauge K) y₀ - sInf ((gauge K) '' Dᶜ)) / 2) 1])).le⟩
    have h₁ := isMinOn_iff.mp hmin y hyK
    linarith [min_le_left (((gauge K) y₀ - sInf ((gauge K) '' Dᶜ)) / 2) 1]

/-- The inner radius `inf_{y ∉ D} ψ(y)` of a set `D ⊆ B(0, R)` containing a ball about the
origin is at most `Λ_ψ R`. -/
private theorem inradius_le (hd : 1 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDb : Bornology.IsBounded D) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ D) {R : ℝ}
    (hDR : D ⊆ Metric.ball 0 R) : sInf ((gauge K) '' Dᶜ) ≤ normMax (gauge K) * R := by
  obtain ⟨hpos, hsub, -⟩ := inradius_facts hd hK hcv h0 hDb hρ hball
  have hΛ : 0 < normMax (gauge K) := lt_of_lt_of_le (normMin_gauge_pos_mul_le hK h0 hd).1
    (normMin_gauge_le_normMax_gauge hK h0 hd)
  have hR : 0 < R := by
    have h0 := hDR (hball (Metric.mem_ball_self hρ))
    rwa [mem_ball_zero_iff, norm_zero] at h0
  have hcontain : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (sInf ((gauge K) '' Dᶜ) / normMax (gauge K)) ⊆
      Metric.ball 0 R := (ball_subset_gauge_sublevel hK h0 hd _).trans (hsub.trans hDR)
  have hle : sInf ((gauge K) '' Dᶜ) / normMax (gauge K) ≤ R := by
    by_contra h
    have hlt : R < sInf ((gauge K) '' Dᶜ) / normMax (gauge K) := not_le.mp h
    set u : EuclideanSpace ℝ (Fin d) := coordVec (⟨0, by omega⟩ : Fin d) with hu
    have hun : ‖u‖ = 1 := by simp [hu, coordVec, PiLp.norm_single]
    set t : ℝ := (R + sInf ((gauge K) '' Dᶜ) / normMax (gauge K)) / 2 with ht
    have hyn : ‖t • u‖ = t := by
      rw [norm_smul, hun, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hmem : t • u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d))
        (sInf ((gauge K) '' Dᶜ) / normMax (gauge K)) := by
      rw [mem_ball_zero_iff, hyn]
      linarith
    have := mem_ball_zero_iff.mp (hcontain hmem)
    rw [hyn] at this
    linarith
  rw [div_le_iff₀ hΛ] at hle
  linarith

/-- Splitting the potential of the gauge over a measurable subset of finite volume. -/
private lemma normPotential_gauge_sdiff (hd : 1 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε (gauge K) D y = normPotential d ε (gauge K) A y + normPotential d ε (gauge K) (D \ A) y := by
  have hF := integrableOn_potentialIntegrand_gauge hd hK hcv h0 hD hDfin y
  have hFA := hF.mono_set hAD
  have hFE := hF.mono_set (Set.sdiff_subset : D \ A ⊆ D)
  have hsplit : ∫ v in D, inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d =
      (∫ v in A, inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d) +
      (∫ v in D \ A, inner ℝ (gradient (gauge K) v) (v - y) / ‖v - y‖ ^ d) := by
    conv_lhs => rw [← Set.union_sdiff_cancel hAD]
    exact setIntegral_union Set.disjoint_sdiff_right (hD.diff hA) hFA hFE
  unfold normPotential
  rw [hsplit]
  ring

/-- The gauge is integrable (minus a constant) on every bounded set. -/
private lemma integrableOn_gauge_sub_const (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hEb : Bornology.IsBounded E) (b : ℝ) : IntegrableOn (fun v => (gauge K) v - b) E := by
  obtain ⟨r, hr⟩ := hEb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hc : ContinuousOn (fun v => (gauge K) v - b) (Metric.closedBall 0 r) :=
    (((lipschitzWith_gauge hK hcv h0).continuous).sub continuous_const).continuousOn
  exact (hc.integrableOn_compact (isCompact_closedBall 0 r)).mono_set hr

/-- The potential of a set `E ⊆ {b ≤ ψ}` is at most `2dεa` plus the geometric bound for the part of
`E` where `ψ > b + a`, whose volume is at most `(∫_E (ψ - b)) / a`. -/
private lemma abs_potential_le_layer_add_tail (hd : 2 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ}
    (hε : 0 < ε) {Cg : ℝ} (hCg0 : 0 ≤ Cg)
    (hCg : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |normPotential d ε (gauge K) D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d))
    {b : ℝ} (hb : 0 ≤ b) {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hEb : Bornology.IsBounded E) (hEsub : E ⊆ {v | b ≤ (gauge K) v}) (y : EuclideanSpace ℝ (Fin d))
    {a : ℝ} (ha : 0 < a) :
    |normPotential d ε (gauge K) E y| ≤
      2 * d * ε * a + Cg * ε * ((∫ v in E, ((gauge K) v - b)) / a) ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  have hΨc : Continuous (gauge K) := (lipschitzWith_gauge hK hcv h0).continuous
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  have hE₁m : MeasurableSet (E ∩ {v | (gauge K) v ≤ b + a}) :=
    hE.inter (measurableSet_le hΨc.measurable measurable_const)
  have hsplit := normPotential_gauge_sdiff hd1 hK hcv h0 (ε := ε) hE₁m hE hEfin Set.inter_subset_left y
  have h1 : |normPotential d ε (gauge K) (E ∩ {v | (gauge K) v ≤ b + a}) y| ≤ 2 * d * ε * a :=
    gauge_layer_potential hd hK hcv h0 hε hb ha hE₁m (fun v hv => ⟨hEsub hv.1, hv.2⟩) y
  have hE₂m : MeasurableSet (E \ (E ∩ {v | (gauge K) v ≤ b + a})) := hE.diff hE₁m
  have hE₂sub : E \ (E ∩ {v | (gauge K) v ≤ b + a}) ⊆ E := Set.sdiff_subset
  have hE₂b : Bornology.IsBounded (E \ (E ∩ {v | (gauge K) v ≤ b + a})) := hEb.subset hE₂sub
  have hE₂fin : volume (E \ (E ∩ {v | (gauge K) v ≤ b + a})) ≠ ⊤ := hE₂b.measure_lt_top.ne
  have h2 := hCg _ hE₂m hE₂b y
  have hint : IntegrableOn (fun v => (gauge K) v - b) E := integrableOn_gauge_sub_const hK hcv h0 hEb b
  have hmarkov : a * (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal ≤ ∫ v in E, ((gauge K) v - b) := by
    calc a * (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal
        = ∫ _v in E \ (E ∩ {v | (gauge K) v ≤ b + a}), a := by
          rw [setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
      _ ≤ ∫ v in E \ (E ∩ {v | (gauge K) v ≤ b + a}), ((gauge K) v - b) := by
          refine setIntegral_mono_on (integrableOn_const hE₂fin) (hint.mono_set hE₂sub) hE₂m ?_
          intro v hv
          have hlt : b + a < (gauge K) v := by
            by_contra hcon
            exact hv.2 ⟨hv.1, not_lt.mp hcon⟩
          linarith
      _ ≤ ∫ v in E, ((gauge K) v - b) := by
          refine setIntegral_mono_set hint ?_ (Set.sdiff_subset : _ ⊆ E).eventuallyLE
          filter_upwards [ae_restrict_mem hE] with v hv
          exact sub_nonneg.mpr (hEsub hv)
  have hvol : (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal ≤ (∫ v in E, ((gauge K) v - b)) / a := by
    rw [le_div_iff₀ ha, mul_comm]
    exact hmarkov
  have hexp : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have h3 : (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal ^ ((1 : ℝ) / d) ≤
      ((∫ v in E, ((gauge K) v - b)) / a) ^ ((1 : ℝ) / d) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hvol hexp
  have h4 : Cg * ε * (volume (E \ (E ∩ {v | (gauge K) v ≤ b + a}))).toReal ^ ((1 : ℝ) / d) ≤
      Cg * ε * ((∫ v in E, ((gauge K) v - b)) / a) ^ ((1 : ℝ) / d) :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg hCg0 hε.le)
  calc |normPotential d ε (gauge K) E y|
      = |normPotential d ε (gauge K) (E ∩ {v | (gauge K) v ≤ b + a}) y +
          normPotential d ε (gauge K) (E \ (E ∩ {v | (gauge K) v ≤ b + a})) y| := by rw [← hsplit]
    _ ≤ |normPotential d ε (gauge K) (E ∩ {v | (gauge K) v ≤ b + a}) y| +
          |normPotential d ε (gauge K) (E \ (E ∩ {v | (gauge K) v ≤ b + a})) y| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 (h2.trans h4)

/-- The excess `∫_{D \ {ψ < b}} (ψ - b)` of a set `D` containing `{ψ < b}` is at most
`(ω_d / (2ε)) (R₁ + R₂)^d U_D(y₀)` at a point `y₀` with `ψ(y₀) = b`: the subgradient inequality at
`y₀` makes `∇ψ(v) · (v - y₀) ≥ ψ(v) - b` on `D \ {ψ < b}`. -/
private theorem excess_le_potential (hd : 2 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {b R₁ R₂ : ℝ} (hb : 0 < b) (hDR : D ⊆ Metric.ball 0 R₁)
    (hsub : {v | (gauge K) v < b} ⊆ D) {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : (gauge K) y₀ = b)
    (hy₀R : ‖y₀‖ ≤ R₂) :
    ∫ v in D \ {v | (gauge K) v < b}, ((gauge K) v - b) ≤
      unitBallVolume d / (2 * ε) * (R₁ + R₂) ^ d * normPotential d ε (gauge K) D y₀ := by
  have hd1 : 1 ≤ d := by omega
  have hΨc : Continuous (gauge K) := (lipschitzWith_gauge hK hcv h0).continuous
  have hSm : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | (gauge K) v < b} :=
    measurableSet_lt hΨc.measurable measurable_const
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDR
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hEm : MeasurableSet (D \ {v | (gauge K) v < b}) := hD.diff hSm
  have hEb : Bornology.IsBounded (D \ {v | (gauge K) v < b}) := hDb.subset Set.sdiff_subset
  have hEfin : volume (D \ {v | (gauge K) v < b}) ≠ ⊤ := hEb.measure_lt_top.ne
  have hsplit := normPotential_gauge_sdiff hd1 hK hcv h0 (ε := ε) hSm hD hDfin hsub y₀
  rw [gauge_ball_potential hd hK hcv h0 ε hb y₀, hy₀, sub_self, max_self, mul_zero, zero_add] at hsplit
  have hR₁ : 0 < R₁ := by
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ {v | (gauge K) v < b} := by
      show (gauge K) 0 < b
      rw [gauge_zero]
      exact hb
    simpa using hDR (hsub h0)
  have hR : 0 < R₁ + R₂ := add_pos_of_pos_of_nonneg hR₁ ((norm_nonneg y₀).trans hy₀R)
  have hpt : ∀ᵐ v ∂(volume.restrict (D \ {v | (gauge K) v < b})),
      ((gauge K) v - b) / (R₁ + R₂) ^ d ≤ inner ℝ (gradient (gauge K) v) (v - y₀) / ‖v - y₀‖ ^ d := by
    filter_upwards [ae_restrict_mem hEm,
      ae_restrict_of_ae (ae_differentiableAt_gauge hK hcv h0)] with v hvE hvdiff
    by_cases hv0 : v = y₀
    · rw [hv0]
      simp [hy₀]
    · have hvb : b ≤ (gauge K) v := not_lt.mp hvE.2
      have hsg := gradient_isSubgradient_gauge hcv h0 hvdiff y₀
      have hneg : inner ℝ (gradient (gauge K) v) (y₀ - v) = -inner ℝ (gradient (gauge K) v) (v - y₀) := by
        rw [← inner_neg_right, neg_sub]
      have hin : (gauge K) v - b ≤ inner ℝ (gradient (gauge K) v) (v - y₀) := by
        rw [hy₀] at hsg
        linarith
      have hvR : ‖v‖ < R₁ := by simpa using hDR hvE.1
      have hnorm : ‖v - y₀‖ ≤ R₁ + R₂ :=
        (norm_sub_le v y₀).trans (by linarith)
      have hpos : 0 < ‖v - y₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv0)
      calc ((gauge K) v - b) / (R₁ + R₂) ^ d
          ≤ inner ℝ (gradient (gauge K) v) (v - y₀) / (R₁ + R₂) ^ d :=
            div_le_div_of_nonneg_right hin (pow_nonneg hR.le d)
        _ ≤ inner ℝ (gradient (gauge K) v) (v - y₀) / ‖v - y₀‖ ^ d :=
            div_le_div_of_nonneg_left (by linarith) (pow_pos hpos d)
              (pow_le_pow_left₀ hpos.le hnorm d)
  have hint1 : IntegrableOn (fun v => ((gauge K) v - b) / (R₁ + R₂) ^ d) (D \ {v | (gauge K) v < b}) :=
    (integrableOn_gauge_sub_const hK hcv h0 hEb b).div_const _
  have hint2 := integrableOn_potentialIntegrand_gauge hd1 hK hcv h0 hEm hEfin y₀
  have hle := setIntegral_mono_ae_restrict hint1 hint2 hpt
  rw [integral_div] at hle
  have hPpos : 0 < (R₁ + R₂) ^ d := pow_pos hR d
  have hω := unitBallVolume_pos d
  rw [hsplit]
  unfold normPotential
  rw [div_le_iff₀ hPpos] at hle
  calc ∫ v in D \ {v | (gauge K) v < b}, ((gauge K) v - b)
      ≤ (∫ v in D \ {v | (gauge K) v < b}, inner ℝ (gradient (gauge K) v) (v - y₀) / ‖v - y₀‖ ^ d) *
        (R₁ + R₂) ^ d := hle
    _ = _ := by
        field_simp

/-- The potential of a bounded measurable set `E ⊆ {b ≤ ψ}` is at most `C (∫_E (ψ - b))^{1/(d+1)}`
in absolute value: the layer `{ψ ≤ b + a}` contributes at most `2dεa` and the rest has volume at
most `(∫_E (ψ - b)) / a`; take `a = (∫_E (ψ - b))^{1/(d+1)}`. -/
private theorem abs_potential_excess_le (hd : 2 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℝ}, 0 ≤ b → ∀ {E : Set (EuclideanSpace ℝ (Fin d))},
      MeasurableSet E → Bornology.IsBounded E → E ⊆ {v | b ≤ (gauge K) v} →
      ∀ y : EuclideanSpace ℝ (Fin d),
        |normPotential d ε (gauge K) E y| ≤ C * (∫ v in E, ((gauge K) v - b)) ^ ((1 : ℝ) / (d + 1)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  obtain ⟨Cg, hCg, hgeo⟩ := gauge_potential_geometry hd hK hcv h0
  have hCg' : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |normPotential d ε (gauge K) D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d) :=
    fun D hD hDb y => (hgeo ε hε.le D hD hDb).1 y
  refine ⟨2 * d * ε + Cg * ε + 1, by positivity, ?_⟩
  intro b hb E hE hEb hEsub y
  have hI0 : 0 ≤ ∫ v in E, ((gauge K) v - b) :=
    setIntegral_nonneg hE (fun v hv => sub_nonneg.mpr (hEsub hv))
  have key := fun a (ha : 0 < a) =>
    abs_potential_le_layer_add_tail hd hK hcv h0 hε hCg.le hCg' hb hE hEb hEsub y ha
  generalize (∫ v in E, ((gauge K) v - b)) = I at hI0 key ⊢
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity), mul_zero]
    refine _root_.le_of_forall_pos_le_add fun δ hδ => ?_
    have hc : 0 < 2 * (d : ℝ) * ε := by positivity
    have hk := key (δ / (2 * d * ε)) (by positivity)
    rw [← h0, zero_div, Real.zero_rpow (one_div_ne_zero hdpos.ne'), mul_zero, add_zero,
      mul_div_cancel₀ _ hc.ne'] at hk
    linarith
  · obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = I ^ ((1 : ℝ) / (d + 1)) := ⟨_, rfl⟩
    have ha : 0 < a := by
      rw [ha_def]
      exact Real.rpow_pos_of_pos hpos _
    have hIa : a ^ (d + 1) = I := by
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      have : (1 : ℝ) / (d + 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [this, Real.rpow_one]
    have hdiv : I / a = a ^ d := by
      rw [← hIa, pow_succ, mul_div_cancel_right₀ _ ha.ne']
    have hrt : (a ^ d) ^ ((1 : ℝ) / d) = a := by
      rw [one_div]
      exact Real.pow_rpow_inv_natCast ha.le (by omega)
    have hk := key a ha
    rw [hdiv, hrt] at hk
    rw [← ha_def]
    calc |normPotential d ε (gauge K) E y| ≤ 2 * d * ε * a + Cg * ε * a := hk
      _ = (2 * d * ε + Cg * ε) * a := by ring
      _ ≤ (2 * d * ε + Cg * ε + 1) * a :=
          mul_le_mul_of_nonneg_right (by linarith) ha.le

/-- The integral of the cone function `max (b - ψ) 0` over a ball of radius `S ≥ b / c_ψ` is
`|B_ψ| b ^ (d + 1) / (d + 1)`. -/
private theorem integral_cone (hd : 1 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {b S : ℝ} (hb : 0 ≤ b)
    (hS : b / normMin (gauge K) ≤ S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, max (b - (gauge K) y) 0 =
      normBallVolume (gauge K) * b ^ (d + 1) / (d + 1) := by
  obtain ⟨hc, hle⟩ := normMin_gauge_pos_mul_le hK h0 hd
  have hcont : Continuous (gauge K) := (lipschitzWith_gauge hK hcv h0).continuous
  have hnn : ∀ y, 0 ≤ (gauge K) y := fun y => gauge_nonneg y
  have hfcont : Continuous fun y : EuclideanSpace ℝ (Fin d) => max (b - (gauge K) y) 0 :=
    (continuous_const.sub hcont).max continuous_const
  have hfzero : ∀ y : EuclideanSpace ℝ (Fin d), S ≤ ‖y‖ → max (b - (gauge K) y) 0 = 0 := by
    intro y hy
    have hby : b ≤ (gauge K) y := by
      calc b = (b / normMin (gauge K)) * normMin (gauge K) := (div_mul_cancel₀ b hc.ne').symm
        _ ≤ ‖y‖ * normMin (gauge K) := mul_le_mul_of_nonneg_right (hS.trans hy) hc.le
        _ = normMin (gauge K) * ‖y‖ := mul_comm _ _
        _ ≤ (gauge K) y := hle y
    exact max_eq_right (by linarith)
  have hint : Integrable fun y : EuclideanSpace ℝ (Fin d) => max (b - (gauge K) y) 0 := by
    refine hfcont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S) ?_)
    intro y hy
    refine hfzero y ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact hy.le
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hfzero y (by
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hy
    exact hy)),
    hint.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun y => le_max_right _ _)]
  have hlayer : ∀ t ∈ Set.Ioi (0 : ℝ),
      volume.real {a : EuclideanSpace ℝ (Fin d) | t < max (b - (gauge K) a) 0} =
        (max (b - t) 0) ^ d * normBallVolume (gauge K) := by
    intro t ht
    have ht0 : 0 < t := ht
    rcases lt_or_ge t b with htb | htb
    · have hset : {a : EuclideanSpace ℝ (Fin d) | t < max (b - (gauge K) a) 0} =
          {a | (gauge K) a < b - t} := by
        ext a
        simp only [Set.mem_setOf_eq, lt_max_iff]
        constructor
        · rintro (h | h)
          · linarith
          · linarith
        · intro h
          exact Or.inl (by linarith)
      rw [hset, real_volume_gauge_sublevel hd hK h0 (by linarith),
        max_eq_left (by linarith : 0 ≤ b - t)]
    · have hset : {a : EuclideanSpace ℝ (Fin d) | t < max (b - (gauge K) a) 0} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, lt_max_iff, Set.mem_empty_iff_false, iff_false, not_or,
          not_lt]
        exact ⟨by linarith [hnn a], ht0.le⟩
      rw [hset, max_eq_right (by linarith : b - t ≤ 0), zero_pow (by omega)]
      simp
  have hsd : ∫ t in Set.Ioi (0 : ℝ), (max (b - t) 0) ^ d * normBallVolume (gauge K) =
      ∫ t in Set.Ioc (0 : ℝ) b, (max (b - t) 0) ^ d * normBallVolume (gauge K) := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      Set.Ioc_subset_Ioi_self (Filter.Eventually.of_forall fun t ht => ?_)
    have hbt : b < t := by
      by_contra h
      exact ht.2 ⟨ht.1, not_lt.mp h⟩
    rw [max_eq_right (by linarith : b - t ≤ 0), zero_pow (by omega), zero_mul]
  have hcongr : ∫ t in (0 : ℝ)..b, (max (b - t) 0) ^ d * normBallVolume (gauge K) =
      ∫ t in (0 : ℝ)..b, (b - t) ^ d * normBallVolume (gauge K) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hb] at ht
    rw [max_eq_left (by linarith [ht.2])]
  rw [setIntegral_congr_fun measurableSet_Ioi hlayer, hsd, ← intervalIntegral.integral_of_le hb,
    hcongr, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ d) b, sub_self, sub_zero,
    integral_pow, zero_pow (Nat.succ_ne_zero d), sub_zero]
  ring

/-! ## The cell set, the inner radius and the contact bound -/

/-- A point at which the gauge is below the inner radius lies in the cell set. -/
theorem sublevel_subset_cellSet_gauge (K : Set (EuclideanSpace ℝ (Fin d))) (x : ℕ → Site d)
    (n : ℕ) : {y : EuclideanSpace ℝ (Fin d) | gauge K y < normInnerRadius (gauge K) x n} ⊆
      cellSet x n := by
  intro y hy
  by_contra hnot
  have hbdd : BddBelow (gauge K '' (cellSet x n)ᶜ) :=
    ⟨0, by
      rintro _ ⟨z, -, rfl⟩
      exact gauge_nonneg z⟩
  exact absurd hy (not_lt.mpr (csInf_le hbdd ⟨y, hnot, rfl⟩))

/-- The volume of a ball of the gauge inside the cell set is at most the number of departed sites:
`|B_ψ| ρ^d ≤ |A_n|`. -/
theorem normBallVolume_mul_pow_le_card_gauge (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℕ → Site d} {n : ℕ} (hsub : {y : EuclideanSpace ℝ (Fin d) | gauge K y < ρ} ⊆ cellSet x n) :
    normBallVolume (gauge K) * ρ ^ d ≤ ((departureRange x n).card : ℝ) := by
  have h1 : ((volume {y : EuclideanSpace ℝ (Fin d) | gauge K y < ρ}).toReal) ≤
      (volume (cellSet x n)).toReal := by
    refine ENNReal.toReal_mono ?_ (measure_mono hsub)
    rw [CERW.Support.Occupation.volume_cellSet]
    exact ENNReal.natCast_ne_top _
  rw [CERW.Support.Occupation.volume_cellSet, ENNReal.toReal_natCast] at h1
  have hV : 0 ≤ normBallVolume (gauge K) := by
    unfold normBallVolume
    exact ENNReal.toReal_nonneg
  rw [volume_gauge_sublevel hK h0 hd hρ.le, ENNReal.toReal_ofReal (by positivity)] at h1
  linarith

/-- The inner radius `b` of the cell set satisfies `W b ≤ s` for `W^d = |B_ψ|` and `s^d = |A_n|`:
the ball of the gauge of radius `b` lies in the cell set. -/
theorem inner_radius_le_scale_gauge (hK : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) (hd : 1 ≤ d) {W s : ℝ} (hW : 0 < W)
    (hWpow : W ^ d = normBallVolume (gauge K)) (hs0 : 0 ≤ s)
    (x : ℕ → Site d) (n : ℕ) (hspow : s ^ d = ((departureRange x n).card : ℝ)) :
    W * normInnerRadius (gauge K) x n ≤ s := by
  have hb0 := normInnerRadius_gauge_nonneg K x n
  rcases hb0.eq_or_lt with h0' | hpos
  · rw [← h0', mul_zero]
    exact hs0
  · have h := normBallVolume_mul_pow_le_card_gauge hK h0 hd hpos
      (sublevel_subset_cellSet_gauge K x n)
    rw [← hspow, ← hWpow, ← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (by positivity) hs0 (by omega)).1 h

/-- **The contact bound.** If the cell local time approximates the potential of the cell set
within `δ` on `{|y| ≤ 2n}`, then the potential is at most `δ` at every limit point of the
complement of the cell set of Euclidean norm below `2n`: the cell local time vanishes off the
cell set, and the potential is continuous. -/
theorem normPotential_le_of_mem_closure_gauge (hd : 2 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε) {x : ℕ → Site d}
    {n : ℕ} {R δ : ℝ} (hDR : cellSet x n ⊆ Metric.ball 0 R)
    (happrox : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - normPotential d ε (gauge K) (cellSet x n) y| ≤ δ)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : y₀ ∈ closure (cellSet x n)ᶜ) (hn : ‖y₀‖ < 2 * n) :
    normPotential d ε (gauge K) (cellSet x n) y₀ ≤ δ := by
  have hcont := continuous_normPotential_gauge hd hK hcv h0 hε
    (CERW.Support.Occupation.measurableSet_cellSet x n) (Metric.isBounded_ball.subset hDR)
  have hA : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 * n) ∩ (cellSet x n)ᶜ,
      normPotential d ε (gauge K) (cellSet x n) y ≤ δ := by
    rintro y ⟨hyb, hyD⟩
    have h := happrox y (le_of_lt (mem_ball_zero_iff.mp hyb))
    rw [CERW.Support.Occupation.cellLocalTime_eq_zero_of_not_mem x n hyD, zero_sub,
      abs_neg] at h
    exact (le_abs_self _).trans h
  have hy₀' : y₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 * n) ∩ closure (cellSet x n)ᶜ :=
    ⟨mem_ball_zero_iff.mpr hn, hy₀⟩
  have hcl := Metric.isOpen_ball.inter_closure hy₀'
  exact closure_minimal hA (isClosed_le hcont continuous_const) hcl

/-- The hypothesis of the inner geometry at the contact points: every point `y₀` with `ψ y₀` equal
to the inner radius `b` and in the closure of the complement of the cell set has potential at most
`δ`, provided that `b < 2 n c_ψ`, which makes `|y₀| < 2n`. -/
theorem contact_potential_le_gauge (hd : 2 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 ≤ ε) {x : ℕ → Site d}
    {n : ℕ} {R δ : ℝ} (hDR : cellSet x n ⊆ Metric.ball 0 R)
    (happrox : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - normPotential d ε (gauge K) (cellSet x n) y| ≤ δ)
    (hb : normInnerRadius (gauge K) x n < 2 * n * normMin (gauge K)) :
    ∀ y₀ : EuclideanSpace ℝ (Fin d), gauge K y₀ = normInnerRadius (gauge K) x n →
      y₀ ∈ closure (cellSet x n)ᶜ → normPotential d ε (gauge K) (cellSet x n) y₀ ≤ δ := by
  intro y₀ hΨy₀ hcl
  obtain ⟨hc0, hcle⟩ := normMin_gauge_pos_mul_le hK h0 (by omega : 1 ≤ d)
  refine normPotential_le_of_mem_closure_gauge hd hK hcv h0 hε hDR happrox hcl ?_
  have h1 : normMin (gauge K) * ‖y₀‖ ≤ normInnerRadius (gauge K) x n := hΨy₀ ▸ hcle y₀
  by_contra hnot
  have h2 : 2 * (n : ℝ) ≤ ‖y₀‖ := not_lt.mp hnot
  have h3 : normMin (gauge K) * (2 * (n : ℝ)) ≤ normMin (gauge K) * ‖y₀‖ :=
    mul_le_mul_of_nonneg_left h2 hc0.le
  linarith

/-! ## The geometry of the inner radius -/

/-- The conclusions of the inner geometry of the gauge, with the constant `C_L` of the layer bound:
for a cell set `D_n ⊆ B(0, R)` on which the cell local time is within `δ` of the potential and at
whose contact points the potential is at most `H`, the inner radius `b` is positive and at most
`Λ R`, the excess `I = ∫_E (ψ - b)`, `E = D_n \ {ψ < b}`, is controlled by `H`, the mass
inequality holds, and the profile is within `δ + C_L I^{1/(d+1)}` of the cone. -/
def InnerGeometry (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (ε C_L : ℝ) : Prop :=
  ∀ (X : ℕ → Site d) (n : ℕ), X 0 = 0 → 1 ≤ n →
      ∀ {R δ H : ℝ}, cellSet X n ⊆ Metric.ball 0 R →
      (∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R,
        |cellLocalTime X n y - normPotential d ε (gauge K) (cellSet X n) y| ≤ δ) →
      (∀ y₀ : EuclideanSpace ℝ (Fin d), gauge K y₀ = normInnerRadius (gauge K) X n →
        y₀ ∈ closure (cellSet X n)ᶜ → normPotential d ε (gauge K) (cellSet X n) y₀ ≤ H) →
      0 < normInnerRadius (gauge K) X n ∧
      normInnerRadius (gauge K) X n ≤ normMax (gauge K) * R ∧
      0 ≤ (∫ v in cellSet X n \ {v | gauge K v < normInnerRadius (gauge K) X n},
          (gauge K v - normInnerRadius (gauge K) X n)) ∧
      (∫ v in cellSet X n \ {v | gauge K v < normInnerRadius (gauge K) X n},
          (gauge K v - normInnerRadius (gauge K) X n)) ≤
        unitBallVolume d / (2 * ε) *
          ((1 + normMax (gauge K) / normMin (gauge K)) * R) ^ d * H ∧
      2 * ε * (d * normBallVolume (gauge K) * normInnerRadius (gauge K) X n ^ (d + 1) / (d + 1))
        ≤ n + unitBallVolume d * ((1 + normMax (gauge K) / normMin (gauge K)) * R) ^ d *
          (δ + C_L * (∫ v in cellSet X n \ {v | gauge K v < normInnerRadius (gauge K) X n},
            (gauge K v - normInnerRadius (gauge K) X n)) ^ ((1 : ℝ) / (d + 1))) ∧
      ∀ y : EuclideanSpace ℝ (Fin d),
        |cellLocalTime X n y - 2 * d * ε * max (normInnerRadius (gauge K) X n - gauge K y) 0| ≤
          δ + C_L * (∫ v in cellSet X n \ {v | gauge K v < normInnerRadius (gauge K) X n},
            (gauge K v - normInnerRadius (gauge K) X n)) ^ ((1 : ℝ) / (d + 1))

/-- **The geometry of the inner radius of the gauge.** The contact bound controls the excess
`I = ∫_E (ψ - b)`, `E = D_n \ {ψ < b}`, and the layer bound controls the profile; integrating the
profile over a ball containing `D_n` gives the one-sided mass inequality. -/
theorem gauge_inner_geometry (hd : 2 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C_L : ℝ, 0 < C_L ∧ InnerGeometry d K ε C_L := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C_L, hCL, hCLb⟩ := abs_potential_excess_le hd hK hcv h0 hε
  refine ⟨C_L, hCL, ?_⟩
  unfold InnerGeometry
  intro X n hX0 hn R δ H hDR happrox hcon
  set D : Set (EuclideanSpace ℝ (Fin d)) := cellSet X n with hD
  set b : ℝ := normInnerRadius (gauge K) X n with hb
  have hbdef : b = sInf (gauge K '' Dᶜ) := rfl
  have hDmeas : MeasurableSet D := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDR
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hball0 : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) ⊆ D :=
    ball_subset_cellSet X n hX0 hn
  obtain ⟨hb0, hsub, y₀, hy₀, hy₀cl⟩ :=
    inradius_facts (K := K) hd1 hK hcv h0 hDb (ρ := 1 / 2) (by norm_num) hball0
  rw [← hbdef] at hb0 hsub hy₀
  have hbR : b ≤ normMax (gauge K) * R := by
    rw [hbdef]
    exact inradius_le hd1 hK hcv h0 hDb (ρ := 1 / 2) (by norm_num) hball0 hDR
  have hR0 : 0 < R := by
    have h00 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D :=
      hball0 (by rw [Metric.mem_ball, dist_self]; norm_num)
    have := hDR h00
    rwa [Metric.mem_ball, dist_self] at this
  obtain ⟨hc0, hcle⟩ := normMin_gauge_pos_mul_le hK h0 hd1
  have hΛc : 0 < normMax (gauge K) :=
    lt_of_lt_of_le hc0 (normMin_gauge_le_normMax_gauge hK h0 hd1)
  have hy₀R : ‖y₀‖ ≤ normMax (gauge K) / normMin (gauge K) * R := by
    have h1 : normMin (gauge K) * ‖y₀‖ ≤ b := hy₀ ▸ hcle y₀
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    calc ‖y₀‖ * normMin (gauge K) = normMin (gauge K) * ‖y₀‖ := mul_comm _ _
      _ ≤ b := h1
      _ ≤ normMax (gauge K) * R := hbR
  set E : Set (EuclideanSpace ℝ (Fin d)) := D \ {v | gauge K v < b} with hE
  have hSm : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | gauge K v < b} :=
    measurableSet_gauge_sublevel hcv h0 b
  have hEmeas : MeasurableSet E := hDmeas.diff hSm
  have hEb : Bornology.IsBounded E := hDb.subset Set.sdiff_subset
  have hEsub : E ⊆ {v | b ≤ gauge K v} := fun v hv => (not_lt.mp hv.2 : b ≤ gauge K v)
  set I : ℝ := ∫ v in E, (gauge K v - b) with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg hEmeas fun v hv => sub_nonneg.mpr (hEsub hv)
  have hexc := excess_le_potential hd hK hcv h0 hε hDmeas (b := b) (R₁ := R)
    (R₂ := normMax (gauge K) / normMin (gauge K) * R) hb0 hDR hsub hy₀ hy₀R
  have hH := hcon y₀ hy₀ hy₀cl
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hcoef : 0 ≤ unitBallVolume d / (2 * ε) *
      (R + normMax (gauge K) / normMin (gauge K) * R) ^ d := by positivity
  have hrew : (1 + normMax (gauge K) / normMin (gauge K)) * R =
      R + normMax (gauge K) / normMin (gauge K) * R := by ring
  have hδ0 : 0 ≤ δ := by
    have h00 : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R :=
      by rw [Metric.mem_ball, dist_self]; exact hR0
    exact (abs_nonneg _).trans (happrox 0 h00)
  have hIp : 0 ≤ I ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hI0 _
  -- the profile at every point of space
  have hprofile : ∀ y : EuclideanSpace ℝ (Fin d),
      |cellLocalTime X n y - 2 * d * ε * max (b - gauge K y) 0| ≤
        δ + C_L * I ^ ((1 : ℝ) / (d + 1)) := by
    intro y
    by_cases hyD : y ∈ D
    · have hyball : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R := hDR hyD
      have hloc := happrox y hyball
      have hsp := normPotential_gauge_sdiff (ε := ε) hd1 hK hcv h0 hSm hDmeas hDfin hsub y
      have hUb := gauge_ball_potential hd hK hcv h0 ε hb0 y
      have hUE := hCLb hb0.le hEmeas hEb hEsub y
      rw [hUb] at hsp
      have hsplit' : cellLocalTime X n y - 2 * d * ε * max (b - gauge K y) 0 =
          (cellLocalTime X n y - normPotential d ε (gauge K) D y) +
            normPotential d ε (gauge K) E y := by
        rw [hsp]
        ring
      rw [hsplit']
      calc |(cellLocalTime X n y - normPotential d ε (gauge K) D y) +
            normPotential d ε (gauge K) E y|
          ≤ |cellLocalTime X n y - normPotential d ε (gauge K) D y| +
              |normPotential d ε (gauge K) E y| := abs_add_le _ _
        _ ≤ δ + C_L * I ^ ((1 : ℝ) / (d + 1)) := add_le_add hloc hUE
    · have hloc0 : cellLocalTime X n y = 0 :=
        CERW.Support.Occupation.cellLocalTime_eq_zero_of_not_mem X n hyD
      have hbdd : BddBelow (gauge K '' Dᶜ) :=
        ⟨0, by
          rintro _ ⟨v, -, rfl⟩
          exact gauge_nonneg v⟩
      have hby : b ≤ gauge K y := by
        rw [hbdef]
        exact csInf_le hbdd ⟨y, hyD, rfl⟩
      have hmax : max (b - gauge K y) 0 = 0 := max_eq_right (by linarith)
      rw [hloc0, hmax]
      simp only [mul_zero, sub_zero, abs_zero]
      exact add_nonneg hδ0 (mul_nonneg hCL.le hIp)
  refine ⟨hb0, hbR, hI0, ?_, ?_, hprofile⟩
  · rw [hrew]
    calc I ≤ unitBallVolume d / (2 * ε) * (R + normMax (gauge K) / normMin (gauge K) * R) ^ d *
          normPotential d ε (gauge K) D y₀ := hexc
      _ ≤ unitBallVolume d / (2 * ε) * (R + normMax (gauge K) / normMin (gauge K) * R) ^ d * H :=
          mul_le_mul_of_nonneg_left hH hcoef
  · -- the one-sided mass inequality, from the profile on a ball containing the cell set
    set S : ℝ := (1 + normMax (gauge K) / normMin (gauge K)) * R with hS
    have hratio : 0 ≤ normMax (gauge K) / normMin (gauge K) := div_nonneg hΛc.le hc0.le
    have hSR : R ≤ S := by
      rw [hS]
      nlinarith
    have hS0 : 0 < S := lt_of_lt_of_le hR0 hSR
    have hSball : D ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S :=
      hDR.trans (Metric.ball_subset_ball hSR)
    have hbS : b / normMin (gauge K) ≤ S := by
      rw [div_le_iff₀ hc0]
      have hSc : S * normMin (gauge K) = R * normMin (gauge K) + normMax (gauge K) * R := by
        rw [hS]
        field_simp
      have : 0 ≤ R * normMin (gauge K) := mul_nonneg hR0.le hc0.le
      linarith
    have hn_int : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, cellLocalTime X n v = n :=
      CERW.Support.Occupation.setIntegral_cellLocalTime_of_subset X n measurableSet_ball hSball
    have hℓint : IntegrableOn (cellLocalTime X n) (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) := by
      by_contra hnot
      rw [integral_undef hnot] at hn_int
      have : (0 : ℝ) < n := by exact_mod_cast hn
      linarith
    have hcone_cont : Continuous fun y : EuclideanSpace ℝ (Fin d) => max (b - gauge K y) 0 :=
      (continuous_const.sub (lipschitzWith_gauge hK hcv h0).continuous).max continuous_const
    have hcone_int : IntegrableOn (fun y : EuclideanSpace ℝ (Fin d) => max (b - gauge K y) 0)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) :=
      (hcone_cont.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
        Metric.ball_subset_closedBall
    have hcone_val := integral_cone hd1 hK hcv h0 hb0.le hbS
    have hvolfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) ≠ ⊤ :=
      measure_ball_lt_top.ne
    have hvol : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal =
        unitBallVolume d * S ^ d := by
      rw [Measure.addHaar_ball_of_pos _ _ hS0, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg hS0.le _)]
      unfold unitBallVolume
      ring
    set B : ℝ := δ + C_L * I ^ ((1 : ℝ) / (d + 1)) with hB
    have hmono : ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        2 * d * ε * max (b - gauge K y) 0 ≤
        ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, (cellLocalTime X n y + B) := by
      refine setIntegral_mono_on (hcone_int.const_mul _) (hℓint.add (integrableOn_const hvolfin))
        measurableSet_ball fun y _ => ?_
      have h := abs_le.mp (hprofile y)
      linarith [h.1]
    rw [integral_const_mul, hcone_val, integral_add hℓint (integrableOn_const hvolfin), hn_int,
      setIntegral_const, Measure.real_def, hvol, smul_eq_mul] at hmono
    have e1 : 2 * (d : ℝ) * ε * (normBallVolume (gauge K) * b ^ (d + 1) / ((d : ℝ) + 1)) =
        2 * ε * (d * normBallVolume (gauge K) * b ^ (d + 1) / (d + 1)) := by ring
    rw [e1] at hmono
    calc 2 * ε * (d * normBallVolume (gauge K) * b ^ (d + 1) / (d + 1)) ≤
          n + unitBallVolume d * S ^ d * B := by linarith
      _ = n + unitBallVolume d * ((1 + normMax (gauge K) / normMin (gauge K)) * R) ^ d * B := by
          rw [hS]

/-! ## The scale -/

/-- The radius `r_n = ((d+1) n / (2 d ε |B_ψ|))^{1/(d+1)}` of `eq:radius-norm`. -/
noncomputable def coarseScale (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  (((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))

/-- The scale is nonnegative. -/
theorem coarseScale_nonneg {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume Ψ) (n : ℕ) :
    0 ≤ coarseScale Ψ ε n := by
  unfold coarseScale
  exact Real.rpow_nonneg (by positivity) _

/-- The `(d+1)`-st power of the scale: `n = (2 d ε |B_ψ| / (d+1)) r_n^{d+1}`. -/
theorem nat_eq_coarseScale_pow (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume Ψ)
    (n : ℕ) :
    (n : ℝ) = 2 * d * ε * normBallVolume Ψ / (d + 1) * coarseScale Ψ ε n ^ (d + 1) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hX : 0 < 2 * (d : ℝ) * ε * normBallVolume Ψ := by positivity
  have hx : (0 : ℝ) ≤ ((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ) := by positivity
  have h : coarseScale Ψ ε n ^ (d + 1) =
      ((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ) := by
    unfold coarseScale
    rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
      rw [one_div, Nat.cast_add, Nat.cast_one]]
    exact Real.rpow_inv_natCast_pow hx (by omega)
  rw [h]
  field_simp

/-- The scale of a positive time is positive. -/
theorem coarseScale_pos (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume Ψ) {n : ℕ}
    (hn : 1 ≤ n) : 0 < coarseScale Ψ ε n := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  unfold coarseScale
  refine Real.rpow_pos_of_pos ?_ _
  have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- Every power of the logarithm is negligible against the scale: for every `K > 0` and every
`k`, eventually `K (log n)^k ≤ r_n`. -/
theorem eventually_mul_log_pow_le_coarseScale (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hV : 0 < normBallVolume Ψ) {K : ℝ} (hK : 0 < K) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * Real.log n ^ k ≤ coarseScale Ψ ε n := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hX : 0 < 2 * (d : ℝ) * ε * normBallVolume Ψ := by positivity
  set A : ℝ := (((d : ℝ) + 1) / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1)) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hlo := (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := (1 : ℝ) / (d + 1))
    (by positivity)).def (c := A / K) (by positivity)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlo
  filter_upwards [hnat, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hcs : coarseScale Ψ ε n = A * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    unfold coarseScale
    rw [hA, ← Real.mul_rpow (by positivity) hn0.le]
    congr 1
    field_simp
  rw [hcs]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
    Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _), Real.rpow_natCast] at hn
  have h2 : K * (A / K * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) = A * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    field_simp
  calc K * Real.log n ^ k ≤ K * (A / K * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) :=
        mul_le_mul_of_nonneg_left hn hK.le
    _ = _ := h2

/-- A path that runs for a positive time has visited at least one site. -/
theorem one_le_card_departureRange (x : ℕ → Site d) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ (departureRange x n).card :=
  Finset.card_pos.mpr ⟨x 0, Finset.mem_image_of_mem x (Finset.mem_range.mpr (by omega))⟩

/-- The number of departed sites is at most `(2 H_n + 1)^d`. -/
theorem card_le_pow_maxRadius (x : ℕ → Site d) (n : ℕ) :
    ((departureRange x n).card : ℝ) ≤ (2 * maxRadius x n + 1) ^ d := by
  have hR : 0 ≤ maxRadius x n :=
    (by rw [← norm_toSpace]; exact norm_nonneg _ : 0 ≤ euclidNorm (x 0)).trans
      (euclidNorm_le_maxRadius x (Nat.zero_le n))
  exact (Nat.cast_le.mpr (Finset.card_le_card
    (CERW.Support.Occupation.departureRange_subset_ballFinset x n))).trans
    (LatticeProb.card_ballFinset_le d hR)

/-- `|A_n|^{1/d} ≤ 2 H_n + 1`. -/
theorem rpow_card_le (hd : 1 ≤ d) (x : ℕ → Site d) (n : ℕ) :
    ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) ≤ 2 * maxRadius x n + 1 := by
  have hR : 0 ≤ maxRadius x n :=
    (by rw [← norm_toSpace]; exact norm_nonneg _ : 0 ≤ euclidNorm (x 0)).trans
      (euclidNorm_le_maxRadius x (Nat.zero_le n))
  calc ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d)
      ≤ ((2 * maxRadius x n + 1) ^ d) ^ ((1 : ℝ) / d) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (card_le_pow_maxRadius x n) (by positivity)
    _ = 2 * maxRadius x n + 1 := by
        rw [one_div]
        exact Real.pow_rpow_inv_natCast (by positivity) (by omega)

/-! ## Real arithmetic of the coarse bounds

These lemmas only manipulate real numbers. Throughout, `u` is the scale `r_n`, `κ = 2dε|B_Ψ|/(d+1)`
(so that `n = κ u^{d+1}`), `L = log n`, `s = |A_n|^{1/d}`, and `q = s^{1/(4(d+1))}`, so that every
power of `s` that occurs is a natural power of `q`: `√s = q^{2(d+1)}`, `s^{3/4} = q^{3(d+1)}`,
`s^{(2d+1)/(2d+2)} = q^{4d+2}`. -/

/-- The square root of `q^{4(d+1)}` is `q^{2(d+1)}`. -/
theorem sqrt_pow_four {q : ℝ} (hq : 0 ≤ q) (d : ℕ) :
    Real.sqrt (q ^ (4 * (d + 1))) = q ^ (2 * (d + 1)) := by
  rw [show 4 * (d + 1) = 2 * (d + 1) * 2 by ring, pow_mul]
  exact Real.sqrt_sq (by positivity)

/-- **First bound on the number of sites.** If `n ≤ M |A_n|` and `M ≤ C_L s + C_L L²` and
`C_L L² c₁^d ≤ (κ/4) u`, then `s ≥ c₁ u`, where `c₁^{d+1} = κ/(2 C_L)`. -/
theorem scale_le_rpow_card (hd : 1 ≤ d) {κ C_L u s M L : ℝ} (hκ : 0 < κ) (hC : 0 < C_L)
    (hu : 0 < u) (hs : 0 < s) (h1 : κ * u ^ (d + 1) ≤ M * s ^ d)
    (h2 : M ≤ C_L * s + C_L * L ^ 2)
    (hsmall : C_L * L ^ 2 * ((κ / (2 * C_L)) ^ ((1 : ℝ) / (d + 1))) ^ d ≤ κ / 4 * u) :
    (κ / (2 * C_L)) ^ ((1 : ℝ) / (d + 1)) * u ≤ s := by
  set c₁ : ℝ := (κ / (2 * C_L)) ^ ((1 : ℝ) / (d + 1)) with hc₁
  have hc₁0 : 0 < c₁ := Real.rpow_pos_of_pos (by positivity) _
  have hc₁pow : c₁ ^ (d + 1) = κ / (2 * C_L) := by
    rw [hc₁, show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
      rw [one_div, Nat.cast_add, Nat.cast_one]]
    exact Real.rpow_inv_natCast_pow (by positivity) (by omega)
  by_contra hlt
  rw [not_le] at hlt
  have hsd : s ^ d ≤ (c₁ * u) ^ d := pow_le_pow_left₀ hs.le hlt.le d
  have hsd1 : s ^ (d + 1) ≤ (c₁ * u) ^ (d + 1) := pow_le_pow_left₀ hs.le hlt.le (d + 1)
  have hcu : (c₁ * u) ^ (d + 1) = κ / (2 * C_L) * u ^ (d + 1) := by rw [mul_pow, hc₁pow]
  have hcud : (c₁ * u) ^ d = c₁ ^ d * u ^ d := mul_pow _ _ _
  have e1 : M * s ^ d ≤ C_L * s ^ (d + 1) + C_L * L ^ 2 * s ^ d := by
    calc M * s ^ d ≤ (C_L * s + C_L * L ^ 2) * s ^ d :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = C_L * s ^ (d + 1) + C_L * L ^ 2 * s ^ d := by ring
  have e2 : C_L * s ^ (d + 1) ≤ κ / 2 * u ^ (d + 1) := by
    calc C_L * s ^ (d + 1) ≤ C_L * ((c₁ * u) ^ (d + 1)) := mul_le_mul_of_nonneg_left hsd1 hC.le
      _ = κ / 2 * u ^ (d + 1) := by rw [hcu]; field_simp
  have e3 : C_L * L ^ 2 * s ^ d ≤ κ / 4 * u ^ (d + 1) := by
    calc C_L * L ^ 2 * s ^ d ≤ C_L * L ^ 2 * ((c₁ * u) ^ d) :=
          mul_le_mul_of_nonneg_left hsd (by positivity)
      _ = (C_L * L ^ 2 * c₁ ^ d) * u ^ d := by rw [hcud]; ring
      _ ≤ (κ / 4 * u) * u ^ d := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = κ / 4 * u ^ (d + 1) := by ring
  have hpos : 0 < κ * u ^ (d + 1) := by positivity
  linarith


/-- **The error of the local time approximation.** If `M ≤ C₂ q^{4(d+1)}` and `δ` is at most the
error `C_L log n + C_L (√M log n or √(M log n))` of the local time lemma, then
`δ ≤ C_L (1 + √C₂) q^{2(d+1)} log n`. -/
theorem delta_le {q L C_L C₂ M δ : ℝ} (d : ℕ) (hq : 1 ≤ q) (hL : 1 ≤ L) (hC_L : 0 ≤ C_L)
    (hC₂ : 0 ≤ C₂) (hM : M ≤ C₂ * q ^ (4 * (d + 1)))
    (hδ : δ ≤ C_L * L + C_L * (if d = 2 then Real.sqrt M * L else Real.sqrt (M * L))) :
    δ ≤ C_L * (1 + Real.sqrt C₂) * (q ^ (2 * (d + 1)) * L) := by
  have hq0 : 0 ≤ q := by linarith
  have hQ : 1 ≤ q ^ (2 * (d + 1)) := one_le_pow₀ hq
  have hsq : Real.sqrt (C₂ * q ^ (4 * (d + 1))) = Real.sqrt C₂ * q ^ (2 * (d + 1)) := by
    rw [Real.sqrt_mul hC₂, sqrt_pow_four hq0]
  have hsM : Real.sqrt M ≤ Real.sqrt C₂ * q ^ (2 * (d + 1)) := by
    rw [← hsq]
    exact Real.sqrt_le_sqrt hM
  have hsL : Real.sqrt L ≤ L := by
    calc Real.sqrt L ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = L := Real.sqrt_sq (by linarith)
  have hsC : 0 ≤ Real.sqrt C₂ := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := by linarith
  have h0 : L ≤ q ^ (2 * (d + 1)) * L := by nlinarith
  split_ifs at hδ with h2
  · calc δ ≤ C_L * L + C_L * (Real.sqrt M * L) := hδ
      _ ≤ C_L * (q ^ (2 * (d + 1)) * L) + C_L * (Real.sqrt C₂ * q ^ (2 * (d + 1)) * L) := by
          gcongr
      _ = C_L * (1 + Real.sqrt C₂) * (q ^ (2 * (d + 1)) * L) := by ring
  · have hML : Real.sqrt (M * L) ≤ Real.sqrt C₂ * q ^ (2 * (d + 1)) * L := by
      have hM0 : M ≤ C₂ * q ^ (4 * (d + 1)) := hM
      calc Real.sqrt (M * L) ≤ Real.sqrt (C₂ * q ^ (4 * (d + 1)) * L) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hM0 hL0)
        _ = Real.sqrt (C₂ * q ^ (4 * (d + 1))) * Real.sqrt L := Real.sqrt_mul (by positivity) L
        _ = Real.sqrt C₂ * q ^ (2 * (d + 1)) * Real.sqrt L := by rw [hsq]
        _ ≤ Real.sqrt C₂ * q ^ (2 * (d + 1)) * L := by gcongr
    calc δ ≤ C_L * L + C_L * Real.sqrt (M * L) := hδ
      _ ≤ C_L * (q ^ (2 * (d + 1)) * L) + C_L * (Real.sqrt C₂ * q ^ (2 * (d + 1)) * L) := by
          gcongr
      _ = C_L * (1 + Real.sqrt C₂) * (q ^ (2 * (d + 1)) * L) := by ring

/-- The excess integral `I ≤ (ω/(2ε)) ((1 + Λ/c) R)^d H` with `R ≤ C₇ q^{4(d+1)} L` and
`H ≤ C₄ q^{2(d+1)} L` is at most `K_I (q^{4d+2} L)^{d+1}`. -/
theorem excess_le {q L A B R H C₇ C₄ I : ℝ} (d : ℕ) (hq : 1 ≤ q) (hL : 1 ≤ L) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hR0 : 0 ≤ R) (hH0 : 0 ≤ H) (hC₇ : 0 ≤ C₇)
    (hR : R ≤ C₇ * (q ^ (4 * (d + 1)) * L)) (hH : H ≤ C₄ * (q ^ (2 * (d + 1)) * L))
    (hI : I ≤ A * (B * R) ^ d * H) :
    I ≤ A * (B * C₇) ^ d * C₄ * (q ^ (4 * d + 2) * L) ^ (d + 1) := by
  have hq0 : 0 ≤ q := by linarith
  have hL0 : 0 ≤ L := by linarith
  have h1 : (B * R) ^ d ≤ (B * (C₇ * (q ^ (4 * (d + 1)) * L))) ^ d :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hR hB) d
  have e : (q ^ (4 * (d + 1))) ^ d * q ^ (2 * (d + 1)) = (q ^ (4 * d + 2)) ^ (d + 1) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  calc I ≤ A * (B * R) ^ d * H := hI
    _ ≤ A * (B * (C₇ * (q ^ (4 * (d + 1)) * L))) ^ d * (C₄ * (q ^ (2 * (d + 1)) * L)) := by
        gcongr
    _ = A * (B * C₇) ^ d * C₄ * (((q ^ (4 * (d + 1))) ^ d * q ^ (2 * (d + 1))) * L ^ (d + 1)) := by
        rw [show (B * (C₇ * (q ^ (4 * (d + 1)) * L))) = (B * C₇) * (q ^ (4 * (d + 1)) * L) by ring,
          mul_pow, mul_pow]
        ring
    _ = A * (B * C₇) ^ d * C₄ * (q ^ (4 * d + 2) * L) ^ (d + 1) := by
        rw [e, mul_pow (q ^ (4 * d + 2)) L (d + 1)]

/-- The largest local time beyond the inner radius: if `Lb ≤ δ + C_G I^{1/(d+1)}` with
`δ ≤ C₄ q^{2(d+1)} L` and `I ≤ K_I (q^{4d+2} L)^{d+1}`, then `Lb ≤ C₅ q^{4d+2} L`. -/
theorem localTime_beyond_le {q L δ I Lb C₄ K_I C_G : ℝ} (d : ℕ) (hq : 1 ≤ q) (hL : 1 ≤ L)
    (hI0 : 0 ≤ I) (hK : 0 ≤ K_I) (hC_G : 0 ≤ C_G) (hC₄ : 0 ≤ C₄)
    (hLb : Lb ≤ δ + C_G * I ^ ((1 : ℝ) / (d + 1)))
    (hδ : δ ≤ C₄ * (q ^ (2 * (d + 1)) * L)) (hI : I ≤ K_I * (q ^ (4 * d + 2) * L) ^ (d + 1)) :
    Lb ≤ (C₄ + C_G * (K_I + 1)) * (q ^ (4 * d + 2) * L) := by
  have hq0 : 0 ≤ q := by linarith
  have hL0 : 0 ≤ L := by linarith
  set e : ℝ := q ^ (4 * d + 2) * L with he
  have he0 : 0 ≤ e := by positivity
  have hQ : q ^ (2 * (d + 1)) ≤ q ^ (4 * d + 2) := pow_le_pow_right₀ hq (by omega)
  have hδe : δ ≤ C₄ * e := by
    calc δ ≤ C₄ * (q ^ (2 * (d + 1)) * L) := hδ
      _ ≤ C₄ * e := by rw [he]; gcongr
  have hZ : I ≤ ((K_I + 1) * e) ^ (d + 1) := by
    calc I ≤ K_I * e ^ (d + 1) := hI
      _ ≤ (K_I + 1) * e ^ (d + 1) := by
          nlinarith [pow_nonneg he0 (d + 1)]
      _ ≤ (K_I + 1) ^ (d + 1) * e ^ (d + 1) := by
          gcongr
          exact le_self_pow₀ (by linarith) (by omega)
      _ = ((K_I + 1) * e) ^ (d + 1) := (mul_pow (K_I + 1) e (d + 1)).symm
  have hroot : I ^ ((1 : ℝ) / (d + 1)) ≤ (K_I + 1) * e := by
    calc I ^ ((1 : ℝ) / (d + 1)) ≤ (((K_I + 1) * e) ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) :=
          Real.rpow_le_rpow hI0 hZ (by positivity)
      _ = (K_I + 1) * e := by
          rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
            rw [one_div, Nat.cast_add, Nat.cast_one]]
          exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
  calc Lb ≤ δ + C_G * I ^ ((1 : ℝ) / (d + 1)) := hLb
    _ ≤ C₄ * e + C_G * ((K_I + 1) * e) := add_le_add hδe (mul_le_mul_of_nonneg_left hroot hC_G)
    _ = (C₄ + C_G * (K_I + 1)) * e := by ring

/-- **A lower bound for the inner radius.** From `s ≤ 2 R₀ + 1`, the rough outer bound at the inner
radius `R₀ ≤ b/c + C_out (1 + Lb) L`, `Lb ≤ C₅ q^{4d+2} L` and `8 C_out (1 + C₅) L² ≤ q²`, with
`s = q^{4(d+1)}` and `q ≥ 2`, the inner radius satisfies `c s/4 ≤ b`, and `R₀ ≤ b/c + s/8`. -/
theorem inner_radius_lower {q L c b R₀ s Lb C_out C₅ : ℝ} (d : ℕ) (hq : 2 ≤ q) (hL : 1 ≤ L)
    (hc : 0 < c) (hC_out : 0 ≤ C_out) (hs : s = q ^ (4 * (d + 1)))
    (hcount : s ≤ 2 * R₀ + 1) (hrough : R₀ ≤ b / c + C_out * (1 + Lb) * L)
    (hLb : Lb ≤ C₅ * (q ^ (4 * d + 2) * L))
    (hsmall : 8 * (C_out * (1 + C₅)) * L ^ 2 ≤ q ^ 2) :
    c * s / 4 ≤ b ∧ R₀ ≤ b / c + s / 8 := by
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hL0 : 0 ≤ L := by linarith
  have he1 : 1 ≤ q ^ (4 * d + 2) * L := by
    have := one_le_pow₀ (n := 4 * d + 2) hq1
    nlinarith
  set e : ℝ := q ^ (4 * d + 2) * L with he
  have h1 : C_out * (1 + Lb) * L ≤ C_out * (1 + C₅) * (e * L) := by
    have : 1 + Lb ≤ (1 + C₅) * e := by nlinarith
    calc C_out * (1 + Lb) * L ≤ C_out * ((1 + C₅) * e) * L := by gcongr
      _ = C_out * (1 + C₅) * (e * L) := by ring
  have h2 : 8 * (C_out * (1 + C₅) * (e * L)) ≤ s := by
    have e2 : e * L = q ^ (4 * d + 2) * L ^ 2 := by rw [he]; ring
    have e3 : s = q ^ (4 * d + 2) * q ^ 2 := by rw [hs, ← pow_add]; congr 1
    rw [e2, e3]
    calc 8 * (C_out * (1 + C₅) * (q ^ (4 * d + 2) * L ^ 2))
        = q ^ (4 * d + 2) * (8 * (C_out * (1 + C₅)) * L ^ 2) := by ring
      _ ≤ q ^ (4 * d + 2) * q ^ 2 := mul_le_mul_of_nonneg_left hsmall (by positivity)
  have h4 : 4 ≤ s := by
    have : q ^ 4 ≤ q ^ (4 * (d + 1)) := pow_le_pow_right₀ hq1 (by omega)
    have h16 : (2 : ℝ) ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ (by norm_num) hq 4
    rw [hs]
    linarith
  have hR₀ : R₀ ≤ b / c + s / 8 := by
    linarith
  have hbc : b / c = b * c⁻¹ := div_eq_mul_inv _ _
  have h5 : s ≤ 2 * (b / c) + s / 4 + 1 := by linarith
  have h6 : s ≤ 4 * (b / c) := by linarith
  rw [div_eq_mul_inv] at h6
  have h7 : c * s ≤ 4 * b := by
    have := mul_le_mul_of_nonneg_left h6 hc.le
    calc c * s ≤ c * (4 * (b * c⁻¹)) := this
      _ = 4 * b := by field_simp
  exact ⟨by linarith, hR₀⟩

/-- A natural number at most `n` has square root at most `n`. -/
theorem sqrt_cast_le_of_le {a n : ℕ} (h : a ≤ n) : Real.sqrt (a : ℝ) ≤ n :=
  Real.sqrt_le_iff.mpr ⟨Nat.cast_nonneg _, by
    exact_mod_cast h.trans (Nat.le_self_pow two_ne_zero n)⟩

/-- For `n ≥ 3`, `log n ≥ 1`. -/
theorem one_le_log_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith [Real.exp_one_lt_three]

/-- The inner radius is below `2 n c_ψ`, so the contact points lie in `{|y| < 2n}`, as soon as
`s² ≤ n` and `((W c)⁻¹)² ≤ n`. -/
theorem contact_level_lt {W c s n b : ℝ} (hW : 0 < W) (hc : 0 < c) (hn : 0 < n) (hs0 : 0 ≤ s)
    (hs2 : s ^ 2 ≤ n) (hE : ((W * c)⁻¹) ^ 2 ≤ n) (hb : W * b ≤ s) : b < 2 * n * c := by
  have hWc : 0 < W * c := mul_pos hW hc
  have ht0 : 0 ≤ (W * c)⁻¹ := inv_nonneg.mpr hWc.le
  have h1 : (s * (W * c)⁻¹) ^ 2 ≤ n ^ 2 := by
    calc (s * (W * c)⁻¹) ^ 2 = s ^ 2 * ((W * c)⁻¹) ^ 2 := mul_pow _ _ _
      _ ≤ n * n := mul_le_mul hs2 hE (by positivity) hn.le
      _ = n ^ 2 := (sq n).symm
  have h2 : s * (W * c)⁻¹ ≤ n :=
    (pow_le_pow_iff_left₀ (by positivity) hn.le (by norm_num)).1 h1
  have h3 : s ≤ n * (W * c) := by
    have := mul_le_mul_of_nonneg_right h2 hWc.le
    calc s = s * (W * c)⁻¹ * (W * c) := by field_simp
      _ ≤ n * (W * c) := this
  have h4 : W * b ≤ W * (n * c) := by
    calc W * b ≤ s := hb
      _ ≤ n * (W * c) := h3
      _ = W * (n * c) := by ring
  have h5 : b ≤ n * c := le_of_mul_le_mul_left h4 hW
  have : 0 < n * c := mul_pos hn hc
  linarith

/-- The local time beyond the level `b` is at most `B` as soon as the profile of the cell local time
is within `B` of the cone `2 d ε (b - ψ)_+` everywhere. -/
theorem localTime_filter_le_of_profile (x : ℕ → Site d) (n : ℕ) {b ε B : ℝ}
    (hprof : ∀ y : EuclideanSpace ℝ (Fin d),
      |cellLocalTime x n y - 2 * d * ε * max (b - (gauge K) y) 0| ≤ B) (hB : 0 ≤ B) :
    ((((departureRange x n).filter (fun z => b ≤ (gauge K) (toSpace z))).sup (localTime x n) : ℕ) : ℝ) ≤
      B := by
  refine sup_localTime_filter_le hB x n fun z hz => ?_
  have h := hprof (toSpace z)
  rw [CERW.cellLocalTime_of_mem_cell x n (toSpace_mem_cell z), max_eq_right (by linarith),
    mul_zero, sub_zero] at h
  exact (le_abs_self _).trans h

/-- Absorbing the constant of an eventual condition: `(K / c₁) P ≤ u` and `c₁ u ≤ s` give
`K P ≤ s`. -/
theorem scaled_le_scale {K P c₁ u s : ℝ} (hc₁ : 0 < c₁) (h : K / c₁ * P ≤ u)
    (hA : c₁ * u ≤ s) : K * P ≤ s := by
  have := mul_le_mul_of_nonneg_left h hc₁.le
  calc K * P = c₁ * (K / c₁ * P) := by field_simp
    _ ≤ c₁ * u := this
    _ ≤ s := hA

/-- **First stage.** The number of departed sites is at least of order `r_n^d`, the largest local
time is `O(s)` and the farthest radius is `O(s log n)`, where `s = |A_n|^{1/d}`. -/
theorem stage_one (hd1 : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hV : 0 < normBallVolume (gauge K))
    {C_L C_out κ c₁ s : ℝ} (hC_L : 0 < C_L) (hC_out : 0 < C_out) (hκ : 0 < κ)
    (hc₁ : c₁ = (κ / (2 * C_L)) ^ ((1 : ℝ) / ((d : ℝ) + 1)))
    (hκdef : κ = 2 * (d : ℝ) * ε * normBallVolume (gauge K) / ((d : ℝ) + 1))
    {n : ℕ} (hn3 : 3 ≤ n) (x : ℕ → Site d)
    (hs : s = ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / (d : ℝ)))
    (hloc1 : (maxLocalTime x n : ℝ) ≤ C_L * s + C_L * Real.log n ^ 2)
    (hrough : RoughOuter (gauge K) C_out n x)
    (hE2 : (4 * C_L * c₁ ^ d / κ) * Real.log n ^ 2 ≤ coarseScale (gauge K) ε n)
    (hE3 : (1 / c₁) * Real.log n ^ 2 ≤ coarseScale (gauge K) ε n) :
    1 ≤ s ∧ c₁ * coarseScale (gauge K) ε n ≤ s ∧ (maxLocalTime x n : ℝ) ≤ 2 * C_L * s ∧
      maxRadius x n ≤ C_out * (1 + 2 * C_L) * (s * Real.log n) := by
  have hn1 : 1 ≤ n := by omega
  have hu0 : 0 < coarseScale (gauge K) ε n := coarseScale_pos hd1 hε hV hn1
  have hS1 : (1 : ℝ) ≤ ((departureRange x n).card : ℝ) := by
    exact_mod_cast one_le_card_departureRange x hn1
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Real.one_le_rpow hS1 (by positivity)
  have hspow : s ^ d = ((departureRange x n).card : ℝ) := by
    rw [hs, one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  have hnκ : (n : ℝ) = κ * coarseScale (gauge K) ε n ^ (d + 1) := by
    rw [hκdef]
    exact nat_eq_coarseScale_pow hd1 hε hV n
  have hMn : (n : ℝ) ≤ (maxLocalTime x n : ℝ) * ((departureRange x n).card : ℝ) := by
    exact_mod_cast CERW.Support.Occupation.le_maxLocalTime_mul_card x n
  have hM0 : (0 : ℝ) ≤ (maxLocalTime x n : ℝ) := Nat.cast_nonneg _
  have hc₁0 : 0 < c₁ := by rw [hc₁]; exact Real.rpow_pos_of_pos (by positivity) _
  have hsmall : C_L * Real.log n ^ 2 * c₁ ^ d ≤ κ / 4 * coarseScale (gauge K) ε n := by
    have h := mul_le_mul_of_nonneg_left hE2 (by positivity : 0 ≤ κ / 4)
    calc C_L * Real.log n ^ 2 * c₁ ^ d
        = κ / 4 * (4 * C_L * c₁ ^ d / κ * Real.log n ^ 2) := by field_simp
      _ ≤ κ / 4 * coarseScale (gauge K) ε n := h
  have hA : c₁ * coarseScale (gauge K) ε n ≤ s := by
    rw [hc₁] at hsmall ⊢
    refine scale_le_rpow_card hd1 hκ hC_L hu0 (by linarith) ?_ hloc1 hsmall
    rw [← hnκ, hspow]
    exact hMn
  have hL2 : Real.log n ^ 2 ≤ s := by
    have h := mul_le_mul_of_nonneg_left hE3 hc₁0.le
    have : Real.log n ^ 2 ≤ c₁ * coarseScale (gauge K) ε n := by
      calc Real.log n ^ 2 = c₁ * (1 / c₁ * Real.log n ^ 2) := by field_simp
        _ ≤ c₁ * coarseScale (gauge K) ε n := h
    linarith
  have hM : (maxLocalTime x n : ℝ) ≤ 2 * C_L * s := by
    have : C_L * Real.log n ^ 2 ≤ C_L * s := mul_le_mul_of_nonneg_left hL2 hC_L.le
    linarith
  have hsup : ((((departureRange x n).filter (fun z => 0 ≤ (gauge K) (toSpace z))).sup
      (localTime x n) : ℕ) : ℝ) ≤ (maxLocalTime x n : ℝ) :=
    sup_localTime_filter_le hM0 x n fun z _ => by
      exact_mod_cast CERW.localTime_le_maxLocalTime x n z
  have hR := hrough 0 le_rfl
  rw [zero_div, zero_add] at hR
  refine ⟨hs1, hA, hM, ?_⟩
  have hLog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have h1 : 1 + ((((departureRange x n).filter (fun z => 0 ≤ (gauge K) (toSpace z))).sup
      (localTime x n) : ℕ) : ℝ) ≤ (1 + 2 * C_L) * s := by nlinarith
  calc maxRadius x n ≤ C_out * (1 + ((((departureRange x n).filter
        (fun z => 0 ≤ (gauge K) (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) * Real.log n := hR
    _ ≤ C_out * ((1 + 2 * C_L) * s) * Real.log n := by gcongr
    _ = C_out * (1 + 2 * C_L) * (s * Real.log n) := by ring

/-- **The six bounds from the scale facts.** The bounds `c₁ u ≤ s ≤ 2 u/c₂`, `M ≤ 2 C_L s`,
`s ≥ 2`, `R₀ ≤ (1/(W c) + 1/8) s`, `s ≤ 2 R₀ + 1`, the identities `s^d = |A_n|` and
`n = κ u^{d+1}` and `n ≤ M |A_n|` give the six bounds with the constants `c_f`, `C_f`. -/
theorem final_bounds {d : ℕ} {u s S M R₀ n κ C_L c₂ W c c₁ c_f C_f : ℝ} (hu : 0 < u)
    (hC_L : 0 < C_L) (hc₂ : 0 < c₂) (hc₁ : 0 < c₁) (hM0 : 0 ≤ M) (hspow : s ^ d = S)
    (hnκ : n = κ * u ^ (d + 1)) (hMn : n ≤ M * S) (hA : c₁ * u ≤ s) (hB : s ≤ 2 * u / c₂)
    (hM : M ≤ 2 * C_L * s) (hs2 : 2 ≤ s) (hR : R₀ ≤ (1 / (W * c) + 1 / 8) * s)
    (hcount : s ≤ 2 * R₀ + 1)
    (hc_f : c_f = min (min (c₁ ^ d) (κ * (c₂ / 2) ^ d)) (c₁ / 4))
    (hC_f : C_f = max (max ((2 / c₂) ^ d + 1) (2 * C_L * (2 / c₂) + 1))
      ((1 / (W * c) + 1 / 8) * (2 / c₂) + 1))
    (hWc : 0 ≤ 1 / (W * c)) :
    c_f * u ^ d ≤ S ∧ S ≤ C_f * u ^ d ∧ c_f * u ≤ M ∧ M ≤ C_f * u ∧ c_f * u ≤ R₀ ∧
      R₀ ≤ C_f * u := by
  have hcf1 : c_f ≤ c₁ ^ d := by rw [hc_f]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hcf2 : c_f ≤ κ * (c₂ / 2) ^ d := by
    rw [hc_f]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hcf3 : c_f ≤ c₁ / 4 := by rw [hc_f]; exact min_le_right _ _
  have hCf1 : (2 / c₂) ^ d + 1 ≤ C_f := by
    rw [hC_f]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hCf2 : 2 * C_L * (2 / c₂) + 1 ≤ C_f := by
    rw [hC_f]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hCf3 : (1 / (W * c) + 1 / 8) * (2 / c₂) + 1 ≤ C_f := by rw [hC_f]; exact le_max_right _ _
  have hud : 0 < u ^ d := pow_pos hu d
  have hs0 : 0 ≤ s := by linarith
  have e2 : 2 * u / c₂ = 2 / c₂ * u := by ring
  have hSle : s ^ d ≤ (2 / c₂) ^ d * u ^ d := by
    calc s ^ d ≤ (2 * u / c₂) ^ d := pow_le_pow_left₀ hs0 hB d
      _ = (2 / c₂) ^ d * u ^ d := by rw [e2, mul_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc c_f * u ^ d ≤ c₁ ^ d * u ^ d := mul_le_mul_of_nonneg_right hcf1 hud.le
      _ = (c₁ * u) ^ d := (mul_pow _ _ _).symm
      _ ≤ s ^ d := pow_le_pow_left₀ (by positivity) hA d
      _ = S := hspow
  · calc S = s ^ d := hspow.symm
      _ ≤ (2 / c₂) ^ d * u ^ d := hSle
      _ ≤ C_f * u ^ d := mul_le_mul_of_nonneg_right (by linarith) hud.le
  · have h1 : κ * u ^ (d + 1) ≤ M * ((2 / c₂) ^ d * u ^ d) := by
      calc κ * u ^ (d + 1) = n := hnκ.symm
        _ ≤ M * S := hMn
        _ = M * s ^ d := by rw [hspow]
        _ ≤ M * ((2 / c₂) ^ d * u ^ d) := mul_le_mul_of_nonneg_left hSle hM0
    have h2 : κ * u ≤ M * (2 / c₂) ^ d := by
      have : (κ * u) * u ^ d ≤ (M * (2 / c₂) ^ d) * u ^ d := by
        calc (κ * u) * u ^ d = κ * u ^ (d + 1) := by ring
          _ ≤ M * ((2 / c₂) ^ d * u ^ d) := h1
          _ = (M * (2 / c₂) ^ d) * u ^ d := by ring
      exact le_of_mul_le_mul_right this hud
    have hp : (c₂ / 2) ^ d * (2 / c₂) ^ d = 1 := by
      have : c₂ / 2 * (2 / c₂) = 1 := by field_simp
      rw [← mul_pow, this, one_pow]
    have h3 : κ * (c₂ / 2) ^ d * u ≤ M := by
      calc κ * (c₂ / 2) ^ d * u = (c₂ / 2) ^ d * (κ * u) := by ring
        _ ≤ (c₂ / 2) ^ d * (M * (2 / c₂) ^ d) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = M * ((c₂ / 2) ^ d * (2 / c₂) ^ d) := by ring
        _ = M := by rw [hp, mul_one]
    exact (mul_le_mul_of_nonneg_right hcf2 hu.le).trans h3
  · calc M ≤ 2 * C_L * s := hM
      _ ≤ 2 * C_L * (2 / c₂ * u) := by
          rw [← e2]
          exact mul_le_mul_of_nonneg_left hB (by positivity)
      _ = (2 * C_L * (2 / c₂)) * u := by ring
      _ ≤ C_f * u := mul_le_mul_of_nonneg_right (by linarith) hu.le
  · have h1 : c_f * u ≤ c₁ / 4 * u := mul_le_mul_of_nonneg_right hcf3 hu.le
    have h2 : c₁ / 4 * u = c₁ * u / 4 := by ring
    linarith
  · have hK : 0 ≤ 1 / (W * c) + 1 / 8 := by positivity
    calc R₀ ≤ (1 / (W * c) + 1 / 8) * s := hR
      _ ≤ (1 / (W * c) + 1 / 8) * (2 / c₂ * u) := by
          rw [← e2]
          exact mul_le_mul_of_nonneg_left hB hK
      _ = ((1 / (W * c) + 1 / 8) * (2 / c₂)) * u := by ring
      _ ≤ C_f * u := mul_le_mul_of_nonneg_right (by linarith) hu.le

/-- **The upper bound for the scale from the mass inequality.** With `s = q^{4(d+1)}`, the inner
radius `b ≥ c₂ s`, the mass inequality `κ b^{d+1} ≤ n + A` for `n = κ u^{d+1}`, the bound
`A ≤ K_M s^d q^{4d+2} L` and `K_M L ≤ (κ c₂^{d+1}/2) q²`, the scale satisfies `c₂ s ≤ 2 u`. -/
theorem scale_upper_profile {d : ℕ} {q L s u κ c₂ b n A K_M : ℝ} (hq : 1 ≤ q)
    (hs : s = q ^ (4 * (d + 1))) (hu : 0 < u) (hκ : 0 < κ) (hc₂ : 0 < c₂)
    (hnκ : n = κ * u ^ (d + 1)) (hb : c₂ * s ≤ b) (hmass : κ * b ^ (d + 1) ≤ n + A)
    (hA : A ≤ K_M * (s ^ d * (q ^ (4 * d + 2) * L)))
    (hsmall : K_M * L ≤ (κ * c₂ ^ (d + 1) / 2) * q ^ 2) : c₂ * s ≤ 2 * u := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by rw [hs]; positivity
  have hq2 : 0 < q ^ 2 := by positivity
  have hexp : 4 * d + 2 + 2 = 4 * (d + 1) := by ring
  have hrel : q ^ (4 * d + 2) * q ^ 2 = s := by
    rw [hs, ← pow_add, hexp]
  set θ : ℝ := κ * c₂ ^ (d + 1) / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  have hA' : A * q ^ 2 ≤ θ * s ^ (d + 1) * q ^ 2 := by
    calc A * q ^ 2 ≤ K_M * (s ^ d * (q ^ (4 * d + 2) * L)) * q ^ 2 :=
          mul_le_mul_of_nonneg_right hA hq2.le
      _ = s ^ (d + 1) * (K_M * L) := by
          calc K_M * (s ^ d * (q ^ (4 * d + 2) * L)) * q ^ 2
              = K_M * L * s ^ d * (q ^ (4 * d + 2) * q ^ 2) := by ring
            _ = s ^ (d + 1) * (K_M * L) := by rw [hrel]; ring
      _ ≤ s ^ (d + 1) * (θ * q ^ 2) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = θ * s ^ (d + 1) * q ^ 2 := by ring
  have hA'' : A ≤ θ * s ^ (d + 1) := le_of_mul_le_mul_right hA' hq2
  have h1 : κ * (c₂ * s) ^ (d + 1) ≤ κ * b ^ (d + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) hκ.le
  have h2 : θ * s ^ (d + 1) = κ * (c₂ * s) ^ (d + 1) / 2 := by
    rw [hθ, mul_pow]
    ring
  have h3 : κ * (c₂ * s) ^ (d + 1) / 2 ≤ κ * u ^ (d + 1) := by
    rw [h2] at hA''
    rw [hnκ] at hmass
    linarith
  have h4 : (c₂ * s) ^ (d + 1) ≤ 2 * u ^ (d + 1) := by
    have : κ * ((c₂ * s) ^ (d + 1)) ≤ κ * (2 * u ^ (d + 1)) := by linarith
    exact le_of_mul_le_mul_left this hκ
  have h5 : 2 * u ^ (d + 1) ≤ (2 * u) ^ (d + 1) := by
    rw [mul_pow]
    have h2d : (2 : ℝ) ≤ 2 ^ (d + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [pow_pos hu (d + 1)]
  exact le_of_pow_le_pow_left₀ (by omega) (by positivity) (h4.trans h5)

/-- **The scale of a path.** Fix the constants, as real numbers related by the displayed
equations, and let `x` be a nearest-neighbour path from the origin with the local time event with
constant `C_L` and the rough outer bound for every real level with constant `C_out`, at a time `n`
that satisfies the finitely many conditions `hE₂, …, hE₇` (each says that a constant times a power
of `log n`, or a fixed constant, is at most the scale `r_n` or at most `n`). Let `hIG` be the
inner-geometry statement with constant `C_G`. Then, with `s = |A_n|^{1/d}`: `c₁ r_n ≤ s`,
`s ≤ 2 r_n / c₂`, the largest local time is at most `2 C_L s`, `s ≥ 2` and the farthest radius is at
most `(1/(W c_ψ) + 1/8) s`. -/
theorem gauge_coarse_path {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hd : 2 ≤ m + 1) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    {C_L C_out C_G κ W c₁ C₂ C₃ C₇ C₄ K_I C₅ C₆ c₂ C_R K_M θ : ℝ}
    (hC_L : 0 < C_L) (hC_out : 0 < C_out) (hC_G : 0 < C_G) (hκ : 0 < κ)
    (hκdef : κ = 2 * ((m + 1 : ℕ) : ℝ) * ε * normBallVolume (gauge K) /
      (((m + 1 : ℕ) : ℝ) + 1))
    (hW0 : 0 < W) (hWpow : W ^ (m + 1) = normBallVolume (gauge K))
    (hc₁def : c₁ = (κ / (2 * C_L)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)))
    (hC₂ : C₂ = 2 * C_L) (hC₃ : C₃ = C_out * (1 + C₂))
    (hC₇ : C₇ = C₃ + Real.sqrt ((m + 1 : ℕ) : ℝ)) (hC₄ : C₄ = C_L * (1 + Real.sqrt C₂))
    (hK_I : K_I = unitBallVolume (m + 1) / (2 * ε) *
      ((1 + normMax (gauge K) / normMin (gauge K)) * C₇) ^ (m + 1) * C₄)
    (hC₅ : C₅ = C₄ + C_G * (K_I + 1)) (hC₆ : C₆ = C_out * (1 + C₅))
    (hc₂ : c₂ = normMin (gauge K) / 4)
    (hC_R : C_R = 1 / (W * normMin (gauge K)) + 1 / 8 + Real.sqrt ((m + 1 : ℕ) : ℝ))
    (hK_M : K_M = unitBallVolume (m + 1) *
      ((1 + normMax (gauge K) / normMin (gauge K)) * C_R) ^ (m + 1) * C₅)
    (hθ : θ = κ * c₂ ^ (m + 1 + 1) / 2)
    (hIG : InnerGeometry (m + 1) K ε C_G)
    {n : ℕ} (hn4 : m + 4 ≤ n)
    (hE₂ : (4 * C_L * c₁ ^ (m + 1) / κ) * Real.log n ^ 2 ≤ coarseScale (gauge K) ε n)
    (hE₃ : (1 / c₁) * Real.log n ^ 2 ≤ coarseScale (gauge K) ε n)
    (hE₄ : (2 ^ (4 * (m + 1 + 1)) / c₁) * Real.log n ^ 0 ≤ coarseScale (gauge K) ε n)
    (hE₅ : ((8 * C₆) ^ (2 * (m + 1 + 1)) / c₁) * Real.log n ^ (4 * (m + 1 + 1)) ≤
      coarseScale (gauge K) ε n)
    (hE₆ : ((K_M / θ) ^ (2 * (m + 1 + 1)) / c₁) * Real.log n ^ (2 * (m + 1 + 1)) ≤
      coarseScale (gauge K) ε n)
    (hE₇ : ((W * normMin (gauge K))⁻¹) ^ 2 ≤ (n : ℝ))
    {x : ℕ → Site (m + 1)} (hx0 : x 0 = 0) (hstep : ∀ j, x (j + 1) - x j ∈ unitSteps (m + 1))
    (hloc : LocalTimeEvent (gauge K) ε C_L n x) (hrough : RoughOuter (gauge K) C_out n x) :
    c₁ * coarseScale (gauge K) ε n ≤ ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) ∧
    ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤
      2 * coarseScale (gauge K) ε n / c₂ ∧
    (maxLocalTime x n : ℝ) ≤
      2 * C_L * ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) ∧
    2 ≤ ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) ∧
    maxRadius x n ≤ (1 / (W * normMin (gauge K)) + 1 / 8) *
      ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  have hd1 : 1 ≤ m + 1 := by omega
  obtain ⟨hc0, -⟩ := normMin_gauge_pos_mul_le hK h0 hd1
  have hcΛ : normMin (gauge K) ≤ normMax (gauge K) :=
    normMin_gauge_le_normMax_gauge hK h0 hd1
  have hΛ : 0 < normMax (gauge K) := lt_of_lt_of_le hc0 hcΛ
  have hV : 0 < normBallVolume (gauge K) :=
    normBallVolume_gauge_pos hK hcv h0
  have hω : 0 < unitBallVolume (m + 1) := unitBallVolume_pos _
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hL1 : 1 ≤ Real.log n := one_le_log_of_three_le hn3
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 < C₃ := by rw [hC₃]; positivity
  have hC₇0 : 0 < C₇ := by rw [hC₇]; positivity
  have hC₄0 : 0 < C₄ := by rw [hC₄]; positivity
  have hK_I0 : 0 ≤ K_I := by rw [hK_I]; positivity
  have hC₅0 : 0 < C₅ := by rw [hC₅]; positivity
  have hC₆0 : 0 < C₆ := by rw [hC₆]; positivity
  have hc₂0 : 0 < c₂ := by rw [hc₂]; positivity
  have hC_R0 : 0 < C_R := by rw [hC_R]; positivity
  have hK_M0 : 0 ≤ K_M := by rw [hK_M]; positivity
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hc₁0 : 0 < c₁ := by rw [hc₁def]; exact Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨hloc1, -, hloc3⟩ := hloc
  obtain ⟨s, hs⟩ : ∃ s : ℝ,
      s = ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  rw [← hs]
  have hloc1' : (maxLocalTime x n : ℝ) ≤ C_L * s + C_L * Real.log n ^ 2 := by
    rw [hs]
    exact hloc1
  obtain ⟨hs1, hA, hM, hRad⟩ :=
    stage_one hd1 hε hV hC_L hC_out hκ hc₁def hκdef hn3 x hs hloc1' hrough hE₂ hE₃
  have hRad' : maxRadius x n ≤ C₃ * (s * Real.log n) := by
    rw [hC₃, hC₂]
    exact hRad
  have hspow : s ^ (m + 1) = ((departureRange x n).card : ℝ) := by
    rw [hs, one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  have hnκ : (n : ℝ) = κ * coarseScale (gauge K) ε n ^ (m + 1 + 1) := by
    rw [hκdef]
    exact nat_eq_coarseScale_pow hd1 hε hV n
  -- the fourth root of the number of departed sites
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = s ^ (((4 * (m + 1 + 1) : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.rpow_nonneg (by linarith) _
  have hqs : q ^ (4 * (m + 1 + 1)) = s := by
    rw [hq]
    exact Real.rpow_inv_natCast_pow (by linarith) (by omega)
  have hq2 : 2 ≤ q := by
    have h := scaled_le_scale hc₁0 hE₄ hA
    rw [pow_zero, mul_one, ← hqs] at h
    exact (pow_le_pow_iff_left₀ (by norm_num) hq0 (by omega)).1 h
  have hq1 : 1 ≤ q := by linarith
  have hs2' : 2 ≤ s := by
    rw [← hqs]
    calc (2 : ℝ) ≤ q ^ 1 := by rw [pow_one]; exact hq2
      _ ≤ q ^ (4 * (m + 1 + 1)) := pow_le_pow_right₀ hq1 (by omega)
  have hsmall₁ : 8 * (C_out * (1 + C₅)) * Real.log n ^ 2 ≤ q ^ 2 := by
    have h := scaled_le_scale hc₁0 hE₅ hA
    rw [← hqs] at h
    have h2 : (8 * C₆ * Real.log n ^ 2) ^ (2 * (m + 1 + 1)) ≤ (q ^ 2) ^ (2 * (m + 1 + 1)) := by
      calc (8 * C₆ * Real.log n ^ 2) ^ (2 * (m + 1 + 1))
          = (8 * C₆) ^ (2 * (m + 1 + 1)) * Real.log n ^ (4 * (m + 1 + 1)) := by
            rw [mul_pow, ← pow_mul]
            ring
        _ ≤ q ^ (4 * (m + 1 + 1)) := h
        _ = (q ^ 2) ^ (2 * (m + 1 + 1)) := by
            rw [← pow_mul]
            ring
    have h3 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).1 h2
    rw [hC₆] at h3
    exact h3
  have hsmall₂ : K_M * Real.log n ≤ θ * q ^ 2 := by
    have h := scaled_le_scale hc₁0 hE₆ hA
    rw [← hqs] at h
    have h2 : (K_M / θ * Real.log n) ^ (2 * (m + 1 + 1)) ≤ (q ^ 2) ^ (2 * (m + 1 + 1)) := by
      calc (K_M / θ * Real.log n) ^ (2 * (m + 1 + 1))
          = (K_M / θ) ^ (2 * (m + 1 + 1)) * Real.log n ^ (2 * (m + 1 + 1)) := mul_pow _ _ _
        _ ≤ q ^ (4 * (m + 1 + 1)) := h
        _ = (q ^ 2) ^ (2 * (m + 1 + 1)) := by
            rw [← pow_mul]
            ring_nf
    have h3 := (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).1 h2
    rw [div_mul_eq_mul_div, div_le_iff₀ hθ0] at h3
    linarith
  -- the contact bound
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = maxRadius x n + Real.sqrt ((m + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hDR : cellSet x n ⊆ Metric.ball 0 R := by
    rw [hRdef]
    exact CERW.Support.Occupation.cellSet_subset_ball hd1 x n
  have hR2n : R ≤ 2 * n := by
    have h1 : maxRadius x n ≤ n := CERW.Support.Occupation.maxRadius_le_of_steps x hx0 hstep n
    have h2 := sqrt_cast_le_of_le (a := m + 1) (n := n) (by omega)
    rw [hRdef]
    linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = C_L * Real.log n + C_L *
      (if m + 1 = 2 then Real.sqrt (maxLocalTime x n) * Real.log n
        else Real.sqrt (maxLocalTime x n * Real.log n)) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]
    split_ifs <;> positivity
  have happrox : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - normPotential (m + 1) ε (gauge K) (cellSet x n) y| ≤ δ := by
    intro y hy
    rw [hδdef]
    exact hloc3 y hy
  have hWb : W * normInnerRadius (gauge K) x n ≤ s :=
    inner_radius_le_scale_gauge hK h0 hd1 hW0 hWpow (by linarith) x n hspow
  have hs2n : s ^ 2 ≤ (n : ℝ) := by
    calc s ^ 2 ≤ s ^ (m + 1) := pow_le_pow_right₀ hs1 hd
      _ = ((departureRange x n).card : ℝ) := hspow
      _ ≤ n := by exact_mod_cast CERW.Support.Occupation.card_departureRange_le x n
  have hb : normInnerRadius (gauge K) x n < 2 * n * normMin (gauge K) :=
    contact_level_lt hW0 hc0 (by exact_mod_cast hn1) (by linarith) hs2n hE₇ hWb
  have hcon := contact_potential_le_gauge hd hK hcv h0 hε.le hDR happrox hb
  obtain ⟨hb0, -, hI0, hIle, hmass, hprof⟩ :=
    hIG x n hx0 hn1 hDR (fun y hy => happrox y (by
      have := mem_ball_zero_iff.mp hy
      linarith)) hcon
  -- the numerical bounds
  have hsL : 1 ≤ s * Real.log n := one_le_mul_of_one_le_of_one_le hs1 hL1
  have hR : R ≤ C₇ * (q ^ (4 * (m + 1 + 1)) * Real.log n) := by
    rw [hqs, hC₇, hRdef]
    have h1 : Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * (s * Real.log n) :=
      le_mul_of_one_le_right (Real.sqrt_nonneg _) hsL
    calc maxRadius x n + Real.sqrt ((m + 1 : ℕ) : ℝ)
        ≤ C₃ * (s * Real.log n) + Real.sqrt ((m + 1 : ℕ) : ℝ) * (s * Real.log n) :=
          add_le_add hRad' h1
      _ = (C₃ + Real.sqrt ((m + 1 : ℕ) : ℝ)) * (s * Real.log n) := by ring
  have hcount : s ≤ 2 * maxRadius x n + 1 := by
    rw [hs]
    exact rpow_card_le hd1 x n
  have hmr0 : 0 ≤ maxRadius x n := by linarith
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hMq : (maxLocalTime x n : ℝ) ≤ C₂ * q ^ (4 * (m + 1 + 1)) := by
    rw [hqs, hC₂]
    exact hM
  have hδ : δ ≤ C₄ * (q ^ (2 * (m + 1 + 1)) * Real.log n) := by
    have := delta_le (m + 1) hq1 hL1 hC_L.le hC₂0.le hMq hδdef.le
    rw [hC₄]
    exact this
  have hIex := excess_le (m + 1) hq1 hL1 (by positivity) (by positivity) hR0 hδ0 hC₇0.le hR hδ hIle
  have hI' : (∫ v in cellSet x n \ {v | (gauge K) v < normInnerRadius (gauge K) x n},
      ((gauge K) v - normInnerRadius (gauge K) x n)) ≤
      K_I * (q ^ (4 * (m + 1) + 2) * Real.log n) ^ (m + 1 + 1) := by
    rw [hK_I]
    exact hIex
  have hB0 : 0 ≤ δ + C_G * (∫ v in cellSet x n \ {v | (gauge K) v < normInnerRadius (gauge K) x n},
      ((gauge K) v - normInnerRadius (gauge K) x n)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)) :=
    add_nonneg hδ0 (mul_nonneg hC_G.le (Real.rpow_nonneg hI0 _))
  have hLbprof := localTime_filter_le_of_profile x n hprof hB0
  have hLb := localTime_beyond_le (m + 1) hq1 hL1 hI0 hK_I0 hC_G.le hC₄0.le hLbprof hδ hI'
  rw [← hC₅] at hLb
  have hrb := hrough (normInnerRadius (gauge K) x n) hb0.le
  obtain ⟨hbc₀, hR₀⟩ :=
    inner_radius_lower (m + 1) hq2 hL1 hc0 hC_out.le hqs.symm hcount hrb hLb hsmall₁
  have hbs₀ : normInnerRadius (gauge K) x n ≤ s / W := by
    rw [le_div_iff₀ hW0]
    linarith
  have hbc₁ : normInnerRadius (gauge K) x n / normMin (gauge K) ≤ 1 / (W * normMin (gauge K)) * s := by
    calc normInnerRadius (gauge K) x n / normMin (gauge K) ≤ s / W / normMin (gauge K) :=
          div_le_div_of_nonneg_right hbs₀ hc0.le
      _ = 1 / (W * normMin (gauge K)) * s := by field_simp
  have hR₀s : maxRadius x n ≤ (1 / (W * normMin (gauge K)) + 1 / 8) * s := by
    calc maxRadius x n ≤ normInnerRadius (gauge K) x n / normMin (gauge K) + s / 8 := hR₀
      _ ≤ 1 / (W * normMin (gauge K)) * s + s / 8 := by linarith
      _ = (1 / (W * normMin (gauge K)) + 1 / 8) * s := by ring
  have hRCs : R ≤ C_R * s := by
    rw [hRdef, hC_R]
    have h1 : Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * s :=
      le_mul_of_one_le_right (Real.sqrt_nonneg _) hs1
    calc maxRadius x n + Real.sqrt ((m + 1 : ℕ) : ℝ)
        ≤ (1 / (W * normMin (gauge K)) + 1 / 8) * s +
          Real.sqrt ((m + 1 : ℕ) : ℝ) * s := add_le_add hR₀s h1
      _ = (1 / (W * normMin (gauge K)) + 1 / 8 + Real.sqrt ((m + 1 : ℕ) : ℝ)) * s := by ring
  have hBle : δ + C_G * (∫ v in cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n},
      (gauge K v - normInnerRadius (gauge K) x n)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)) ≤
      C₅ * (q ^ (4 * (m + 1) + 2) * Real.log n) := by
    have h := localTime_beyond_le (m + 1) hq1 hL1 hI0 hK_I0 hC_G.le hC₄0.le
      (le_refl (δ + C_G * (∫ v in cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n},
      (gauge K v - normInnerRadius (gauge K) x n)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)))) hδ hI'
    rw [hC₅]
    exact h
  have hmass' : κ * normInnerRadius (gauge K) x n ^ (m + 1 + 1) ≤ (n : ℝ) +
      unitBallVolume (m + 1) * ((1 + normMax (gauge K) / normMin (gauge K)) * R) ^ (m + 1) *
        (δ + C_G * (∫ v in cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n},
          (gauge K v - normInnerRadius (gauge K) x n)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1))) := by
    have e : 2 * ε * (((m + 1 : ℕ) : ℝ) * normBallVolume (gauge K) *
        normInnerRadius (gauge K) x n ^ (m + 1 + 1) / (((m + 1 : ℕ) : ℝ) + 1)) =
        κ * normInnerRadius (gauge K) x n ^ (m + 1 + 1) := by
      rw [hκdef]
      ring
    rw [e] at hmass
    exact hmass
  have hA' : unitBallVolume (m + 1) *
      ((1 + normMax (gauge K) / normMin (gauge K)) * R) ^ (m + 1) *
        (δ + C_G * (∫ v in cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n},
          (gauge K v - normInnerRadius (gauge K) x n)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1))) ≤
      K_M * (s ^ (m + 1) * (q ^ (4 * (m + 1) + 2) * Real.log n)) := by
    have hr0 : 0 ≤ 1 + normMax (gauge K) / normMin (gauge K) := by positivity
    have hr1 : (1 + normMax (gauge K) / normMin (gauge K)) * R ≤
        (1 + normMax (gauge K) / normMin (gauge K)) * C_R * s := by
      calc (1 + normMax (gauge K) / normMin (gauge K)) * R
          ≤ (1 + normMax (gauge K) / normMin (gauge K)) * (C_R * s) :=
            mul_le_mul_of_nonneg_left hRCs hr0
        _ = (1 + normMax (gauge K) / normMin (gauge K)) * C_R * s := by ring
    have hr2 : ((1 + normMax (gauge K) / normMin (gauge K)) * R) ^ (m + 1) ≤
        ((1 + normMax (gauge K) / normMin (gauge K)) * C_R) ^ (m + 1) * s ^ (m + 1) := by
      calc ((1 + normMax (gauge K) / normMin (gauge K)) * R) ^ (m + 1)
          ≤ ((1 + normMax (gauge K) / normMin (gauge K)) * C_R * s) ^ (m + 1) :=
            pow_le_pow_left₀ (by positivity) hr1 _
        _ = ((1 + normMax (gauge K) / normMin (gauge K)) * C_R) ^ (m + 1) * s ^ (m + 1) :=
            mul_pow _ _ _
    calc unitBallVolume (m + 1) * ((1 + normMax (gauge K) / normMin (gauge K)) * R) ^ (m + 1) *
          (δ + C_G * (∫ v in cellSet x n \ {v | gauge K v < normInnerRadius (gauge K) x n},
            (gauge K v - normInnerRadius (gauge K) x n)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)))
        ≤ unitBallVolume (m + 1) * (((1 + normMax (gauge K) / normMin (gauge K)) * C_R) ^ (m + 1) *
            s ^ (m + 1)) * (C₅ * (q ^ (4 * (m + 1) + 2) * Real.log n)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hr2 hω.le) hBle hB0
            (mul_nonneg hω.le
              (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by linarith) _)))
      _ = K_M * (s ^ (m + 1) * (q ^ (4 * (m + 1) + 2) * Real.log n)) := by
          rw [hK_M]
          ring
  have hu0 : 0 < coarseScale (gauge K) ε n := coarseScale_pos hd1 hε hV hn1
  have hscale' := scale_upper_profile (d := m + 1) hq1 hqs.symm hu0 hκ hc₂0 hnκ
    (by rw [hc₂]; linarith) hmass' hA' (by rw [hθ] at hsmall₂; exact hsmall₂)
  have hscale : s ≤ 2 * coarseScale (gauge K) ε n / c₂ := by
    rw [le_div_iff₀ hc₂0]
    linarith
  exact ⟨hA, hscale, hM, hs2', hR₀s⟩

/-- **The coarse bounds of a path.** Let `K` be a compact convex set with the origin in its
interior, `m + 1 ≥ 2`, `ε > 0`, and let `C_L`, `C_out` be positive constants. There are `c, C > 0`
and `n₀` such that, for every `n ≥ n₀` and every nearest-neighbour path from the origin that
satisfies the local time event `LocalTimeEvent` with constant `C_L` and the rough outer bound
`RoughOuter` for every real level with constant `C_out`, the number of departed sites, the largest
local time and the largest radius are of order `r_n^{m+1}`, `r_n`, `r_n`, with constants `c` and
`C`. The geometry enters only through `gauge_inner_geometry`; no evenness of `K` and no coarse,
radial or Moreau estimate is used. -/
theorem gauge_coarse_deterministic {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (hd : 2 ≤ m + 1) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈ interior K) {ε : ℝ} (hε : 0 < ε) {C_L C_out : ℝ}
    (hC_L : 0 < C_L) (hC_out : 0 < C_out) :
    ∃ c C : ℝ, ∃ n₀ : ℕ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, n₀ ≤ n → ∀ x : ℕ → Site (m + 1), x 0 = 0 →
      (∀ j, x (j + 1) - x j ∈ unitSteps (m + 1)) → LocalTimeEvent (gauge K) ε C_L n x →
      RoughOuter (gauge K) C_out n x →
      c * coarseScale (gauge K) ε n ^ (m + 1) ≤ ((departureRange x n).card : ℝ) ∧
      ((departureRange x n).card : ℝ) ≤ C * coarseScale (gauge K) ε n ^ (m + 1) ∧
      c * coarseScale (gauge K) ε n ≤ (maxLocalTime x n : ℝ) ∧
      (maxLocalTime x n : ℝ) ≤ C * coarseScale (gauge K) ε n ∧
      c * coarseScale (gauge K) ε n ≤ maxRadius x n ∧
      maxRadius x n ≤ C * coarseScale (gauge K) ε n := by
  have hd1 : 1 ≤ m + 1 := by omega
  obtain ⟨hc0, hcle⟩ := normMin_gauge_pos_mul_le hK h0 hd1
  have hcΛ : normMin (gauge K) ≤ normMax (gauge K) :=
    normMin_gauge_le_normMax_gauge hK h0 hd1
  have hΛ : 0 < normMax (gauge K) := lt_of_lt_of_le hc0 hcΛ
  have hV : 0 < normBallVolume (gauge K) := normBallVolume_gauge_pos hK hcv h0
  have hω : 0 < unitBallVolume (m + 1) := unitBallVolume_pos _
  obtain ⟨C_G, hC_G, hIG⟩ := gauge_inner_geometry hd hK hcv h0 hε
  have hdR0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 2 * ((m + 1 : ℕ) : ℝ) * ε * normBallVolume (gauge K) /
      (((m + 1 : ℕ) : ℝ) + 1) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = normBallVolume (gauge K) ^ (((m + 1 : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
  have hW0 : 0 < W := by rw [hWdef]; exact Real.rpow_pos_of_pos hV _
  have hWpow : W ^ (m + 1) = normBallVolume (gauge K) := by
    rw [hWdef]; exact Real.rpow_inv_natCast_pow hV.le (by omega)
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : ℝ, c₁ = (κ / (2 * C_L)) ^ ((1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1)) :=
    ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁def]; exact Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 2 * C_L := ⟨_, rfl⟩
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = C_out * (1 + C₂) := ⟨_, rfl⟩
  obtain ⟨C₇, hC₇⟩ : ∃ C₇ : ℝ, C₇ = C₃ + Real.sqrt ((m + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨C₄, hC₄⟩ : ∃ C₄ : ℝ, C₄ = C_L * (1 + Real.sqrt C₂) := ⟨_, rfl⟩
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 < C₃ := by rw [hC₃]; positivity
  have hC₇0 : 0 < C₇ := by rw [hC₇]; positivity
  have hC₄0 : 0 < C₄ := by rw [hC₄]; positivity
  obtain ⟨K_I, hK_I⟩ : ∃ K_I : ℝ, K_I = unitBallVolume (m + 1) / (2 * ε) *
      ((1 + normMax (gauge K) / normMin (gauge K)) * C₇) ^ (m + 1) * C₄ := ⟨_, rfl⟩
  have hK_I0 : 0 ≤ K_I := by rw [hK_I]; positivity
  obtain ⟨C₅, hC₅⟩ : ∃ C₅ : ℝ, C₅ = C₄ + C_G * (K_I + 1) := ⟨_, rfl⟩
  have hC₅0 : 0 < C₅ := by rw [hC₅]; positivity
  obtain ⟨C₆, hC₆⟩ : ∃ C₆ : ℝ, C₆ = C_out * (1 + C₅) := ⟨_, rfl⟩
  have hC₆0 : 0 < C₆ := by rw [hC₆]; positivity
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = normMin (gauge K) / 4 := ⟨_, rfl⟩
  have hc₂0 : 0 < c₂ := by rw [hc₂]; positivity
  obtain ⟨C_R, hC_R⟩ : ∃ C_R : ℝ, C_R = 1 / (W * normMin (gauge K)) + 1 / 8 +
      Real.sqrt ((m + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hC_R0 : 0 < C_R := by rw [hC_R]; positivity
  obtain ⟨K_M, hK_M⟩ : ∃ K_M : ℝ, K_M = unitBallVolume (m + 1) *
      ((1 + normMax (gauge K) / normMin (gauge K)) * C_R) ^ (m + 1) * C₅ := ⟨_, rfl⟩
  have hK_M0 : 0 < K_M := by rw [hK_M]; positivity
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = κ * c₂ ^ (m + 1 + 1) / 2 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  -- the final constants
  obtain ⟨c_f, hc_f⟩ : ∃ c_f : ℝ, c_f = min (min (c₁ ^ (m + 1)) (κ * (c₂ / 2) ^ (m + 1)))
      (c₁ / 4) := ⟨_, rfl⟩
  obtain ⟨C_f, hC_f⟩ : ∃ C_f : ℝ, C_f = max (max ((2 / c₂) ^ (m + 1) + 1)
      (2 * C_L * (2 / c₂) + 1)) ((1 / (W * normMin (gauge K)) + 1 / 8) * (2 / c₂) + 1) := ⟨_, rfl⟩
  have hc_f0 : 0 < c_f := by rw [hc_f]; positivity
  have hC_f0 : 0 < C_f := by
    rw [hC_f]
    exact lt_max_of_lt_left (lt_max_of_lt_left (by positivity))
  -- the conditions on `n`
  have hev : ∀ᶠ n : ℕ in atTop, m + 4 ≤ n ∧
      (4 * C_L * c₁ ^ (m + 1) / κ) * Real.log n ^ 2 ≤ coarseScale (gauge K) ε n ∧
      (1 / c₁) * Real.log n ^ 2 ≤ coarseScale (gauge K) ε n ∧
      (2 ^ (4 * (m + 1 + 1)) / c₁) * Real.log n ^ 0 ≤ coarseScale (gauge K) ε n ∧
      ((8 * C₆) ^ (2 * (m + 1 + 1)) / c₁) * Real.log n ^ (4 * (m + 1 + 1)) ≤
        coarseScale (gauge K) ε n ∧
      ((K_M / θ) ^ (2 * (m + 1 + 1)) / c₁) * Real.log n ^ (2 * (m + 1 + 1)) ≤
        coarseScale (gauge K) ε n ∧
      ((W * normMin (gauge K))⁻¹) ^ 2 ≤ (n : ℝ) := by
    have e1 := eventually_mul_log_pow_le_coarseScale (Ψ := gauge K) hd1 hε hV
      (K := 4 * C_L * c₁ ^ (m + 1) / κ) (by positivity) 2
    have e2 := eventually_mul_log_pow_le_coarseScale (Ψ := gauge K) hd1 hε hV
      (K := 1 / c₁) (by positivity) 2
    have e3 := eventually_mul_log_pow_le_coarseScale (Ψ := gauge K) hd1 hε hV
      (K := 2 ^ (4 * (m + 1 + 1)) / c₁) (by positivity) 0
    have e4 := eventually_mul_log_pow_le_coarseScale (Ψ := gauge K) hd1 hε hV
      (K := (8 * C₆) ^ (2 * (m + 1 + 1)) / c₁) (by positivity) (4 * (m + 1 + 1))
    have e5 := eventually_mul_log_pow_le_coarseScale (Ψ := gauge K) hd1 hε hV
      (K := (K_M / θ) ^ (2 * (m + 1 + 1)) / c₁) (by positivity) (2 * (m + 1 + 1))
    have e6 : ∀ᶠ n : ℕ in atTop, ((W * normMin (gauge K))⁻¹) ^ 2 ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventually_ge_atTop (((W * normMin (gauge K))⁻¹) ^ 2))
    filter_upwards [eventually_ge_atTop (m + 4), e1, e2, e3, e4, e5, e6] with n h0 h1 h2 h3 h4 h5 h6
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨c_f, C_f, n₀, hc_f0, hC_f0, ?_⟩
  intro n hn x hx0 hstep hloc hrough
  obtain ⟨hn4, hE₂, hE₃, hE₄, hE₅, hE₆, hE₇⟩ := hn₀ n hn
  have hn1 : 1 ≤ n := by omega
  have hu0 : 0 < coarseScale (gauge K) ε n := coarseScale_pos hd1 hε hV hn1
  obtain ⟨hA, hB, hM, hs2, hR⟩ := gauge_coarse_path hd hK hcv h0 hε hC_L hC_out hC_G hκ hκdef hW0 hWpow
    hc₁def hC₂ hC₃ hC₇ hC₄ hK_I hC₅ hC₆ hc₂ hC_R hK_M hθ hIG hn4 hE₂ hE₃ hE₄ hE₅ hE₆ hE₇ hx0
    hstep hloc hrough
  obtain ⟨s, hs⟩ : ∃ s : ℝ,
      s = ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  rw [← hs] at hA hB hM hs2 hR
  have hspow : s ^ (m + 1) = ((departureRange x n).card : ℝ) := by
    rw [hs, one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  have hnκ : (n : ℝ) = κ * coarseScale (gauge K) ε n ^ (m + 1 + 1) := by
    rw [hκdef]
    exact nat_eq_coarseScale_pow hd1 hε hV n
  have hMn : (n : ℝ) ≤ (maxLocalTime x n : ℝ) * ((departureRange x n).card : ℝ) := by
    exact_mod_cast CERW.Support.Occupation.le_maxLocalTime_mul_card x n
  have hcount : s ≤ 2 * maxRadius x n + 1 := by
    rw [hs]
    exact rpow_card_le hd1 x n
  have hWc : 0 ≤ 1 / (W * normMin (gauge K)) := by positivity
  exact final_bounds hu0 hC_L hc₂0 hc₁0 (Nat.cast_nonneg _) hspow hnκ hMn hA hB hM hs2 hR hcount
    hc_f hC_f hWc

/-! ## The statements and the assembly -/

/-- The statement of the local time potential lemma (Lemma 3.1) for the Minkowski functional of a
compact convex body `K` with the origin in its interior: with probability at least `1 - C n^{-p}`
the largest local time, the interval local times and the approximation of the cell local time by
the potential of the cell set hold, for every subgradient selection of `ψ_K` and every walk with
that drift field. Its proof, for the gauge, is not part of this module: it enters the assembly
below only as the hypothesis `hlocal` of `gauge_coarse_bounds_of_local_time`. -/
def GaugeLocalTimePotential : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}, IsCompact K → Convex ℝ K →
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K →
    ∀ ε : ℝ, 0 < ε →
    (∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ)) →
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ((maxLocalTime (X · ω) n : ℝ)
                    ≤ C * ((departureRange (X · ω) n).card : ℝ) ^ ((1 : ℝ) / d)
                      + C * Real.log n ^ 2 ∧
                  (∀ s t : ℕ, s < t → t ≤ n →
                    (intervalMax (X · ω) s t : ℝ)
                      ≤ C * (freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / d)
                        + C * Real.log n ^ 2) ∧
                  ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
                    |cellLocalTime (X · ω) n y
                        - normPotential d ε (gauge K) (cellSet (X · ω) n) y|
                      ≤ C * Real.log n + C *
                        (if d = 2 then Real.sqrt (maxLocalTime (X · ω) n) * Real.log n
                          else Real.sqrt (maxLocalTime (X · ω) n * Real.log n)))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- The statement of the coarse bounds (Proposition 4.1) for the Minkowski functional of a compact
convex body `K` with the origin in its interior: with probability at least `1 - C n^{-p}`, the
number of departed sites, the largest local time and the largest radius are of order `r_n^d`,
`r_n`, `r_n`, for every subgradient selection of `ψ_K` and every walk with that drift field. -/
def GaugeCoarseBounds : Prop :=
  ∀ {d : ℕ} (_ : 2 ≤ d) {K : Set (EuclideanSpace ℝ (Fin d))}, IsCompact K → Convex ℝ K →
    (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K →
    ∀ ε : ℝ, 0 < ε →
    (∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * normBallVolume (gauge K))) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (c * r n ^ d ≤ ((departureRange (X · ω) n).card : ℝ) ∧
                  ((departureRange (X · ω) n).card : ℝ) ≤ C * r n ^ d ∧
                  c * r n ≤ (maxLocalTime (X · ω) n : ℝ) ∧
                  (maxLocalTime (X · ω) n : ℝ) ≤ C * r n ∧
                  c * r n ≤ maxRadius (X · ω) n ∧ maxRadius (X · ω) n ≤ C * r n)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))

/-- **The cap event together with the local time potential.** Given the local time potential lemma
as the hypothesis `hlocal`, for every `p > 0` there are constants such that, for every subgradient
selection, every probability space carrying the walk and every `n ≥ 2`, the set of sample points
whose path is not in both `CapEvent` and `LocalTimeEvent` has probability at most `C n^{-p}`. The
bound is on that failure set only. -/
theorem exists_gauge_cap_local_failure_bound (hlocal : GaugeLocalTimePotential.{u})
    (hd : 2 ≤ d) (hK : IsCompact K) (hcv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ interior K) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d,
      ε * gauge K (coordVec i) < 1 / (d : ℝ) ∧ ε * gauge K (-coordVec i) < 1 / (d : ℝ))
    {p : ℝ} (hp : 0 < p) :
    ∃ C_V C_M C_L C : ℝ, 0 < C_V ∧ 0 < C_L ∧ 0 < C ∧
      ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient (gauge K) (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (CapEvent (gauge K) ε ξ C_V C_M n (fun j => X j ω) ∧
            LocalTimeEvent (gauge K) ε C_L n (fun j => X j ω))} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨C_V, C_M, C₁, hC_V, hC₁, hev⟩ := exists_capEvent_failure_bound.{u} hd hε hell hp
  obtain ⟨C_L, hC_L, hloc⟩ := hlocal hd hK hcv h0 ε hε hell p hp
  refine ⟨C_V, C_M, C_L, C₁ + C_L, hC_V, hC_L, by positivity, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have h₁ := hev ξ hξ hξ0 μ X hX n hn
  have h₂ := hloc ξ hξ hξ0 μ X hX n hn
  have hnp : 0 ≤ (n : ℝ) ^ (-p) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc μ {ω | ¬ (CapEvent (gauge K) ε ξ C_V C_M n (fun j => X j ω) ∧
          LocalTimeEvent (gauge K) ε C_L n (fun j => X j ω))}
      ≤ μ ({ω | ¬ CapEvent (gauge K) ε ξ C_V C_M n (fun j => X j ω)} ∪
          {ω | ¬ LocalTimeEvent (gauge K) ε C_L n (fun j => X j ω)}) := by
        refine measure_mono fun ω hω => ?_
        by_contra hnot
        rw [Set.mem_union, not_or] at hnot
        exact hω ⟨not_not.mp hnot.1, not_not.mp hnot.2⟩
    _ ≤ μ {ω | ¬ CapEvent (gauge K) ε ξ C_V C_M n (fun j => X j ω)} +
          μ {ω | ¬ LocalTimeEvent (gauge K) ε C_L n (fun j => X j ω)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (-p)) + ENNReal.ofReal (C_L * (n : ℝ) ^ (-p)) :=
        add_le_add h₁ h₂
    _ = ENNReal.ofReal ((C₁ + C_L) * (n : ℝ) ^ (-p)) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hC₁.le hnp) (mul_nonneg hC_L.le hnp)]
        congr 1
        ring

/-- **The coarse bounds of the gauge, from the cap event and the local time potential lemma.**
The six bounds for the number of departed sites, the largest local time and the largest radius
follow, with probability at least `1 - C n^{-p}`, from the vector and half-space martingale bounds
(the cap event: no producer is assumed), the geometry of the gauge (`gauge_inner_geometry`) and the
local time potential lemma, which enters as the hypothesis `hlocal` and is **not** proved in this
module. The constants `c`, `C` are chosen before the field of subgradients, the probability space,
the walk and `n`. -/
theorem gauge_coarse_bounds_of_local_time (hlocal : GaugeLocalTimePotential.{u}) :
    GaugeCoarseBounds.{u} := by
  intro d hd K hK hcv h0 ε hε hell r p hp
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨C_V, C_M, C_L, C₁, hC_V, hC_L, hC₁, hev⟩ :=
    exists_gauge_cap_local_failure_bound hlocal hd hK hcv h0 hε hell hp
  obtain ⟨C_out, hC_out, hrough⟩ := exists_rough_outer_of_capEvent hd hK h0 hε hell
    (C_M := C_M) hC_V
  obtain ⟨c, C, n₀, hc, hC, hdet⟩ := gauge_coarse_deterministic hd hK hcv h0 hε hC_L hC_out
  have hV : 0 < normBallVolume (gauge K) := normBallVolume_gauge_pos hK hcv h0
  have hn₀p : 0 ≤ (n₀ : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨c, max C (C₁ + (n₀ : ℝ) ^ p), hc, lt_max_of_lt_left hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  by_cases hn₀le : n₀ ≤ n
  · refine le_trans (measure_mono fun ω hω => ?_)
      ((hev ξ hξ hξ0 μ X hX n hn).trans (ENNReal.ofReal_le_ofReal ?_))
    · intro hcap
      apply hω
      obtain ⟨hcapE, hloc⟩ := hcap
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hdet n hn₀le (fun j => X j ω) hcapE.1 hcapE.2.1 hloc
        (hrough ξ hξ hξ0 n hn (fun j => X j ω) hcapE)
      have hr0 : 0 ≤ coarseScale (gauge K) ε n := coarseScale_nonneg hε hV n
      have hCm : C ≤ max C (C₁ + (n₀ : ℝ) ^ p) := le_max_left _ _
      exact ⟨h₁, h₂.trans (mul_le_mul_of_nonneg_right hCm (pow_nonneg hr0 _)), h₃,
        h₄.trans (mul_le_mul_of_nonneg_right hCm hr0), h₅,
        h₆.trans (mul_le_mul_of_nonneg_right hCm hr0)⟩
    · refine mul_le_mul_of_nonneg_right ?_ hnp
      exact le_max_of_le_right (by linarith)
  · rw [not_le] at hn₀le
    refine le_trans prob_le_one ?_
    rw [ENNReal.one_le_ofReal]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have h1 : (n : ℝ) ^ p ≤ (n₀ : ℝ) ^ p :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast hn₀le.le) hp.le
    have h2 : 1 ≤ (n₀ : ℝ) ^ p * (n : ℝ) ^ (-p) := by
      rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hnpos p)]
      exact h1
    calc (1 : ℝ) ≤ (n₀ : ℝ) ^ p * (n : ℝ) ^ (-p) := h2
      _ ≤ max C (C₁ + (n₀ : ℝ) ^ p) * (n : ℝ) ^ (-p) :=
        mul_le_mul_of_nonneg_right (le_max_of_le_right (by linarith)) hnp

end CERW.Support.Norm.GaugeCoarseVolume
