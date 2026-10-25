module

public import CERW.Support.Outer.Radius.EuclideanCrossing

@[expose] public section

/-!
# Ramp Martingale

Ramp increments and their occupation counts control the Dynkin martingale. A bounded representative
agrees with that martingale on legal paths.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

section

open CERW.Support.Law CERW.Support.LocalTime
open LatticeProb (ballFinset mem_ballFinset_iff card_ballFinset_le)

/-- The embedding of lattice sites is additive. -/
lemma lm_toSpace_add (x y : Site d) : toSpace (x + y) = toSpace x + toSpace y := by
  ext i
  simp [toSpace]

/-- A unit step changes a projection `q · z` by at most one when `‖q‖ ≤ 1`. -/
lemma lm_abs_inner_le {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) {e : Site d}
    (he : e ∈ unitSteps d) : |inner ℝ q (toSpace e)| ≤ 1 := by
  calc |inner ℝ q (toSpace e)| ≤ ‖q‖ * ‖toSpace e‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 := by
      rw [norm_toSpace, euclidNorm_of_mem_unitSteps he, mul_one]
      exact hq

/-- One unit step changes the ramp `(q · z - a)₊` by at most one. -/
lemma lm_ramp_step_abs {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) (a : ℝ)
    (z : Site d) {e : Site d} (he : e ∈ unitSteps d) :
    |max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0| ≤ 1 := by
  calc |max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0|
      ≤ |(inner ℝ q (toSpace (z + e)) - a) - (inner ℝ q (toSpace z) - a)| :=
        abs_max_sub_max_le_abs _ _ _
    _ = |inner ℝ q (toSpace e)| := by
        rw [lm_toSpace_add, inner_add_right]
        congr 1
        ring
    _ ≤ 1 := lm_abs_inner_le hq he

/-- At `z` with `q · z ≤ a - 1` the ramp vanishes after every unit step. -/
lemma lm_ramp_step_zero {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) (a : ℝ)
    {z e : Site d} (he : e ∈ unitSteps d) (hz : inner ℝ q (toSpace z) ≤ a - 1) :
    max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0 = 0 := by
  have h2 := abs_le.mp (lm_abs_inner_le hq he)
  rw [lm_toSpace_add, inner_add_right, max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

/-- The squared increment of the ramp over a unit step is at most the indicator of the
half-space `q · z > a - 1`. -/
lemma lm_ramp_step_sq {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) (a : ℝ)
    (z : Site d) {e : Site d} (he : e ∈ unitSteps d) :
    (max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0) ^ 2 ≤
      if a - 1 < inner ℝ q (toSpace z) then 1 else 0 := by
  split_ifs with h
  · exact (sq_le_one_iff_abs_le_one _).mpr (lm_ramp_step_abs hq a z he)
  · rw [lm_ramp_step_zero hq a he (not_lt.mp h)]
    norm_num

/-- The number of times `j < t` at which the path lies in the half-space `q · z > a - 1`. -/
noncomputable def lm_count {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range t, if a - 1 < inner ℝ q (toSpace (X j ω)) then 1 else 0

/-- The count starts at `0`. -/
lemma lm_count_zero {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (ω : Ω) : lm_count q a X 0 ω = 0 := by
  simp [lm_count]

/-- The increment of the count is the indicator of the half-space at the current position. -/
lemma lm_count_succ_sub {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (j : ℕ) (ω : Ω) :
    lm_count q a X (j + 1) ω - lm_count q a X j ω =
      if a - 1 < inner ℝ q (toSpace (X j ω)) then 1 else 0 := by
  simp only [lm_count, Finset.sum_range_succ]
  ring

/-- The count is nondecreasing. -/
lemma lm_count_mono {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (j : ℕ) (ω : Ω) : lm_count q a X j ω ≤ lm_count q a X (j + 1) ω := by
  have h := lm_count_succ_sub q a X j ω
  split_ifs at h <;> linarith

/-- The count up to time `t` is at most `t`. -/
lemma lm_count_le {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (t : ℕ) (ω : Ω) : lm_count q a X t ω ≤ t := by
  calc lm_count q a X t ω ≤ ∑ _j ∈ Finset.range t, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => by split_ifs <;> norm_num
    _ = t := by simp

/-- The count at time `j + 1` is a function of the past path up to time `j`. -/
lemma lm_stronglyMeasurable_count {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (j : ℕ) : StronglyMeasurable[pathFiltration hX j] (lm_count q a X (j + 1)) := by
  have h := stronglyMeasurable_comp_pastPath hX j
    (fun p => ∑ i ∈ Finset.range (j + 1),
      if a - 1 < inner ℝ q (toSpace (extendPath p i)) then (1 : ℝ) else 0)
  have heq : lm_count q a X (j + 1) = fun ω => ∑ i ∈ Finset.range (j + 1),
      if a - 1 < inner ℝ q (toSpace (extendPath (pastPath X j ω) i)) then (1 : ℝ) else 0 := by
    funext ω
    simp only [lm_count]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [extendPath_pastPath X (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) ω]
  rw [heq]
  exact h

/-- The count up to time `n` is the sum of the local times over the part of the departure range
in the half-space `q · z > a - 1`. -/
lemma lm_count_eq_sum {Ω : Type*} (q : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (X : ℕ → Ω → Site d) (n : ℕ) (ω : Ω) :
    lm_count q a X n ω = ∑ z ∈ (departureRange (fun j => X j ω) n).filter
        (fun z => a - 1 < inner ℝ q (toSpace z)), (localTime (fun j => X j ω) n z : ℝ) := by
  rw [lm_count, sum_range_eq_sum_localTime (fun j => X j ω) n
    (fun z => if a - 1 < inner ℝ q (toSpace z) then 1 else 0), Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp

/-- The pathwise Dynkin martingale for the drift law of the field `x ↦ u_x` is the Dynkin
martingale of the Euclidean walk. -/
lemma lm_dynkinMart_eq (hd : 1 ≤ d) (ε : ℝ) (f : Site d → ℝ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (n : ℕ) (ω : Ω) :
    dynkinMart (driftStepProb d ε (fun z => unitDir (toSpace z))) f (fun j => X j ω) n =
      dynkin ε f X n ω := by
  have h : stepProb d ε = driftStepProb d ε (fun z => unitDir (toSpace z)) := by
    funext x n e
    exact CERW.Support.Drift.stepProb_eq_driftStepProb ε x n e
  rw [← h]
  exact CERW.Support.Drift.dynkinMart_stepProb_eq_dynkin hd ε f X n ω

/-- The Dynkin martingale of a ramp agrees almost surely with a martingale whose increments are
at most `2` everywhere and whose conditional variances are at most the increments of the count. -/
lemma lm_exists_clamped (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ)) {X : ℕ → Ω → Site d}
    (hX : IsCERW μ ε X) {q : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ 1) (a : ℝ) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun ω => lm_count q a X (j + 1) ω - lm_count q a X j ω) ∧
      ∀ᵐ ω ∂μ, ∀ i,
        M i ω = dynkin ε (fun z => max (inner ℝ q (toSpace z) - a) 0) X i ω := by
  set f : Site d → ℝ := fun z => max (inner ℝ q (toSpace z) - a) 0 with hf
  have hmart := martingale_dynkin hd hε hεd hX f
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |dynkin ε f X (i + 1) ω - dynkin ε f X i ω| ≤ 2 := fun i =>
    (ae_abs_dynkin_succ_sub_le hd hε hεd hX f).mono fun ω hω => by
      simpa using hω i 1 fun e he => lm_ramp_step_abs hq a (X i ω) he
  obtain ⟨M, hM, hbd, -, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart
    (b := 2) (by norm_num) hinc
  refine ⟨M, hM, hbd, fun j => ?_, hae⟩
  have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
      fun ω => (dynkin ε f X (j + 1) ω - dynkin ε f X j ω) ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω, hω]
  refine (condExp_congr_ae hsq).trans_le ?_
  filter_upwards [condExp_sq_dynkin_succ_sub_le hd hε hεd hX f j] with ω hω
  refine hω.trans ?_
  rw [lm_count_succ_sub]
  calc ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e * (f (X j ω + e) - f (X j ω)) ^ 2
      ≤ ∑ e ∈ unitSteps d, stepProb d ε (fun i => X i ω) j e *
          (if a - 1 < inner ℝ q (toSpace (X j ω)) then 1 else 0) :=
        Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left (lm_ramp_step_sq hq a _ he)
          (stepProb_nonneg hε hεd _ j e)
    _ = if a - 1 < inner ℝ q (toSpace (X j ω)) then 1 else 0 := by
        rw [← Finset.sum_mul, sum_stepProb hd ε _ j, one_mul]

end

end CERW.Support.Outer.Radius
