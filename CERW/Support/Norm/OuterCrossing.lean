import CERW.Support.Statements
import CERW.Support.Drift
import CERW.Generic.Norm
import CERW.Support.Occupation.FreshSum
import CERW.Support.Occupation.SiteArith
import CERW.Support.Crossing.LastEntrance
import CERW.Support.Law.Moments

/-!
# The outer crossing lemma

`lem:outer-crossing` of the revised paper, for a deterministic path of the walk with drift field
`ξ`. The argument has four steps.

* The Dynkin martingale of the ramp `z ↦ (q · z - a)₊` is, beyond the level `a + Λ`, minus `ε`
  times the drift `q · ξ` at each first departure, and it vanishes below `a - Λ`. So on the
  grid `a ∈ Λ ℕ` the number of sites above `a + Λ` is controlled by the number of sites between
  `a - Λ` and `a + Λ` and by the martingale bound (`level_inequality`).
* Along every second level this gives a contraction up to an error of order `L log n`
  (`recurrence_step`), so that after `O(L log n)` levels only `O(L log n)` sites remain
  (`exists_small_level`).
* After the last entrance of the path into the half-space above that level, the path crosses
  through the few remaining sites, each with small local time. The duration is at most the number of
  sites times the largest local time, and the drift has the right sign, so the vector bound
  controls the gain (`top_bound`).
* The constants are collected in `final_arithmetic`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

open CERW.Support.Statements

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

/-- The outer crossing lemma (`lem:outer-crossing`): a path of the walk with a drift field that
satisfies the vector bound and the linear martingale bound, and that has drift at least `α` in the
direction `q` above `T - h`, reaches the height `T` at most `C L_b log n` above `max {T - h, b}`,
where `L_b` is one more than the largest local time above `b`. -/
theorem outer_crossing_holds : outer_crossing := by
  intro d hd Ψ hΨ ε hε hell α hα C₁ hC₁
  have hd1 : 1 ≤ d := by omega
  have hΛ : 0 < normMax Ψ := by
    obtain ⟨hcpos, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
    have hn1 : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
      simp [coordVec, PiLp.norm_single]
    have h2 := CERW.Generic.Norm.le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
    have h3 := hcle (coordVec (⟨0, by omega⟩ : Fin d))
    rw [hn1] at h2 h3
    linarith
  obtain ⟨C, hC, hmain⟩ := outer_crossing_core hd1 hε hα hC₁ hΛ
  refine ⟨C, hC, ?_⟩
  intro ξ hξ hξ0 n hn q hq x hx0 hstep Λ Z hZ hmart j₀ hj₀ hmax T h hh hα' b hb
  have hξbd : ∀ (z : Site d) (i : Fin d), ε * |ξ z i| ≤ 1 / (d : ℝ) := by
    intro z i
    by_cases hz : z = 0
    · rw [hz, hξ0]
      simp only [PiLp.zero_apply, abs_zero, mul_zero]
      positivity
    · have := CERW.Generic.Norm.subgradient_abs_coord_le hΨ (hξ z hz) i
      exact (mul_le_mul_of_nonneg_left this hε.le).trans (hell i).le
  exact hmain ξ hξbd n hn q hq x hx0 hstep hZ hmart j₀ hj₀ h hh hα' b hb

end CERW.Support.Norm
