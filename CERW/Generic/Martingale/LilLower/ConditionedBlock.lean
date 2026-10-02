import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import CERW.Generic.Martingale.ExpMart

/-!
# A martingale between two stopping times, conditioned on an earlier event

For stopping times `σ ≤ ρ` and an event `F` that is determined by time `σ`, the increments of a
martingale `M` at the times `σ ≤ t < ρ`, kept on `F`, form a sequence of conditionally centred
increments for the conditioned measure `μ[|F]`. Their conditional variances under `μ[|F]` are those
of `M` under `μ`, restricted to the same times. The sum of the increments telescopes to the
increment of `M` between the stopped times.
-/

namespace CERW.Generic.Martingale.LilLower

open MeasureTheory ProbabilityTheory
open CERW.Generic.Martingale.ExpMart

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The increment of `M` at time `t`, kept when `σ ≤ t < ρ` and the point lies in `F`. -/
noncomputable def blockIncrement (M : ℕ → Ω → ℝ) (σ ρ : Ω → WithTop ℕ) (F : Set Ω) (t : ℕ)
    (ω : Ω) : ℝ :=
  F.indicator (fun ω =>
    (if σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω then (1 : ℝ) else 0) *
      (M (t + 1) ω - M t ω)) ω

/-- The cut-off of a stopping value at `n + 1` agrees with the cut-off at `n` when the value is at
most `n`. -/
private lemma untopA_min_succ_of_le {x : WithTop ℕ} {n : ℕ} (h : x ≤ (n : WithTop ℕ)) :
    (min x ((n + 1 : ℕ) : WithTop ℕ)).untopA = (min x (n : WithTop ℕ)).untopA := by
  have h2 : x ≤ ((n + 1 : ℕ) : WithTop ℕ) := h.trans (WithTop.coe_le_coe.mpr (Nat.le_succ n))
  rw [min_eq_left h, min_eq_left h2]

/-- If the value exceeds `n`, its cut-offs at `n` and at `n + 1` are `n` and `n + 1`. -/
private lemma untopA_min_of_lt {x : WithTop ℕ} {n : ℕ} (h : (n : WithTop ℕ) < x) :
    (min x (n : WithTop ℕ)).untopA = n ∧ (min x ((n + 1 : ℕ) : WithTop ℕ)).untopA = n + 1 := by
  induction x using WithTop.recTopCoe with
  | top => exact ⟨by rw [min_eq_right le_top]; rfl, by rw [min_eq_right le_top]; rfl⟩
  | coe k =>
    have hk : n < k := WithTop.coe_lt_coe.mp h
    refine ⟨?_, ?_⟩
    · rw [min_eq_right h.le]; rfl
    · rw [min_eq_right (WithTop.coe_le_coe.mpr hk)]; rfl

/-- The gated increments of a real sequence telescope between two ordered times. -/
private lemma gate_sum_aux (f : ℕ → ℝ) (a r : WithTop ℕ) (har : a ≤ r) (n : ℕ) :
    ∑ t ∈ Finset.range n, (if a ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < r then (1 : ℝ) else 0) *
        (f (t + 1) - f t) =
      f (min r (n : WithTop ℕ)).untopA - f (min a (n : WithTop ℕ)).untopA := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hr : r ≤ (n : WithTop ℕ)
    · have hnr : ¬ (n : WithTop ℕ) < r := not_lt.mpr hr
      rw [if_neg (fun h => hnr h.2), untopA_min_succ_of_le hr,
        untopA_min_succ_of_le (har.trans hr)]
      ring
    · have hnr : (n : WithTop ℕ) < r := not_le.mp hr
      obtain ⟨hr1, hr2⟩ := untopA_min_of_lt hnr
      by_cases ha : a ≤ (n : WithTop ℕ)
      · rw [if_pos ⟨ha, hnr⟩, untopA_min_succ_of_le ha, hr1, hr2]
        simp
      · have han : (n : WithTop ℕ) < a := not_le.mp ha
        obtain ⟨ha1, ha2⟩ := untopA_min_of_lt han
        rw [if_neg (fun h => ha h.1), hr1, hr2, ha1, ha2]
        simp

/-- Integrals over a measurable set for the conditioned measure, as integrals for `μ`. -/
private lemma setIntegral_cond_eq (μ : Measure Ω) {F s : Set Ω} (hs : MeasurableSet s)
    (φ : Ω → ℝ) :
    ∫ x in s, φ x ∂(μ[|F]) = ((μ F)⁻¹).toReal * ∫ x in s ∩ F, φ x ∂μ := by
  rw [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure,
    Measure.restrict_restrict hs]
  rfl

/-- A function integrable for `μ` is integrable for the conditioned measure. -/
private lemma integrable_cond {μ : Measure Ω} {F : Set Ω} (hμF : μ F ≠ 0) {φ : Ω → ℝ}
    (hφ : Integrable φ μ) : Integrable φ (μ[|F]) :=
  hφ.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hμF)

/-- The conditional expectation, for the conditioned measure, of a function that is supported on
`F ∩ S` and equals an integrable function `U` there, where `F ∩ S` and `S` are measurable for the
sub-σ-algebra `m`. -/
private lemma condExp_cond_indicator (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) {F S : Set Ω} (hF : MeasurableSet[m0] F)
    (hμF : μ F ≠ 0)
    (hS : MeasurableSet[m] S) (hFS : MeasurableSet[m] (F ∩ S)) {U : Ω → ℝ}
    (hU : Integrable U μ) {Z : Ω → ℝ} (hZ : ∀ ω, Z ω = F.indicator (S.indicator U) ω) :
    (μ[|F])[Z | m] =ᵐ[μ[|F]] S.indicator (μ[U | m]) := by
  haveI : IsProbabilityMeasure (μ[|F]) := cond_isProbabilityMeasure hμF
  have hZ' : Z = F.indicator (S.indicator U) := funext hZ
  have hS0 : MeasurableSet[m0] S := hm S hS
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (f := Z) ?_ ?_ ?_ ?_).symm
  · rw [hZ']
    exact integrable_cond hμF ((hU.indicator hS0).indicator hF)
  · intro s _ _
    exact (integrable_cond hμF (integrable_condExp.indicator hS0)).integrableOn
  · intro s hs _
    have hs0 : MeasurableSet[m0] s := hm s hs
    rw [setIntegral_cond_eq μ hs0, setIntegral_cond_eq μ hs0]
    congr 1
    have h1 : ∫ x in s ∩ F, Z x ∂μ = ∫ x in s ∩ F, S.indicator U x ∂μ :=
      setIntegral_congr_fun (hs0.inter hF) fun x hx => by
        rw [hZ', Set.indicator_of_mem hx.2]
    rw [h1, setIntegral_indicator hS0, setIntegral_indicator hS0, Set.inter_assoc,
      setIntegral_condExp hm hU (hs.inter hFS)]
  · exact (stronglyMeasurable_condExp.indicator hS).aestronglyMeasurable

/-- The event `{t < ρ}` is measurable for `ℱ t` when `ρ` is a stopping time. -/
private lemma measurableSet_lt_stopping (ℱ : Filtration ℕ m0) {ρ : Ω → WithTop ℕ}
    (hρ : IsStoppingTime ℱ ρ) (t : ℕ) : MeasurableSet[ℱ t] {ω | (t : WithTop ℕ) < ρ ω} := by
  have h : MeasurableSet[ℱ t] {ω | ρ ω ≤ (t : WithTop ℕ)}ᶜ := (hρ t).compl
  convert h using 1
  ext ω
  simp

/-- The event `{σ ≤ t < ρ}` is measurable for `ℱ t`. -/
private lemma measurableSet_gate (ℱ : Filtration ℕ m0) {σ ρ : Ω → WithTop ℕ}
    (hσ : IsStoppingTime ℱ σ) (hρ : IsStoppingTime ℱ ρ) (t : ℕ) :
    MeasurableSet[ℱ t] {ω | σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω} :=
  (hσ t).inter (measurableSet_lt_stopping ℱ hρ t)

/-- An event determined by time `σ`, intersected with `{σ ≤ t < ρ}`, is measurable for `ℱ t`. -/
private lemma measurableSet_inter_gate (ℱ : Filtration ℕ m0) {σ ρ : Ω → WithTop ℕ}
    (hσ : IsStoppingTime ℱ σ) (hρ : IsStoppingTime ℱ ρ) {F : Set Ω}
    (hF : MeasurableSet[hσ.measurableSpace] F) (t : ℕ) :
    MeasurableSet[ℱ t] (F ∩ {ω | σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω}) := by
  have h : MeasurableSet[ℱ t] ((F ∩ {ω | σ ω ≤ (t : WithTop ℕ)}) ∩
      {ω | (t : WithTop ℕ) < ρ ω}) :=
    (((hσ.measurableSet F).1 hF).2 t).inter (measurableSet_lt_stopping ℱ hρ t)
  convert h using 1
  ext ω
  simp [and_assoc]

/-- An event determined by time `σ` is measurable. -/
private lemma measurableSet_of_stopping (ℱ : Filtration ℕ m0) {σ : Ω → WithTop ℕ}
    (hσ : IsStoppingTime ℱ σ) {F : Set Ω} (hF : MeasurableSet[hσ.measurableSpace] F) :
    MeasurableSet F :=
  ((hσ.measurableSet F).1 hF).1

/-- The block increment as a doubly gated increment of `M`. -/
private lemma blockIncrement_eq (M : ℕ → Ω → ℝ) (σ ρ : Ω → WithTop ℕ) (F : Set Ω) (t : ℕ)
    (ω : Ω) :
    blockIncrement M σ ρ F t ω = F.indicator
      ({ω | σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω}.indicator
        (fun ω => M (t + 1) ω - M t ω)) ω := by
  by_cases hF : ω ∈ F
  · by_cases hS : σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω
    · simp [blockIncrement, hF, hS]
    · simp [blockIncrement, hF, hS]
  · simp [blockIncrement, hF]

/-- The square of the block increment as a doubly gated squared increment of `M`. -/
private lemma blockIncrement_sq_eq (M : ℕ → Ω → ℝ) (σ ρ : Ω → WithTop ℕ) (F : Set Ω) (t : ℕ)
    (ω : Ω) :
    blockIncrement M σ ρ F t ω ^ 2 = F.indicator
      ({ω | σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω}.indicator
        (fun ω => (M (t + 1) ω - M t ω) ^ 2)) ω := by
  by_cases hF : ω ∈ F
  · by_cases hS : σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω
    · simp [blockIncrement, hF, hS]
    · simp [blockIncrement, hF, hS]
  · simp [blockIncrement, hF]

/-- The block increment is the increment of `M` on `F ∩ {σ ≤ t < ρ}`. -/
private lemma blockIncrement_eq_indicator (M : ℕ → Ω → ℝ) (σ ρ : Ω → WithTop ℕ) (F : Set Ω)
    (t : ℕ) :
    blockIncrement M σ ρ F t =
      (F ∩ {ω | σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω}).indicator
        (fun ω => M (t + 1) ω - M t ω) := by
  funext ω
  rw [blockIncrement_eq, Set.indicator_indicator]

/-- The conditional expectation of the increment of a martingale vanishes. -/
private lemma condExp_increment_ae_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ μ) (t : ℕ) :
    μ[fun ω => M (t + 1) ω - M t ω | ℱ t] =ᵐ[μ] 0 := by
  have hsub := condExp_sub (hM.integrable (t + 1)) (hM.integrable t) (ℱ t)
  have hstep := hM.2 t (t + 1) (Nat.le_succ t)
  have hself := condExp_of_stronglyMeasurable (ℱ.le t) (hM.1 t) (hM.integrable t)
  filter_upwards [hsub, hstep] with ω h1 h2
  rw [Pi.zero_apply]
  change (μ[M (t + 1) - M t | ℱ t]) ω = 0
  rw [h1, Pi.sub_apply, h2, hself]
  ring

/-- The block increments of a martingale between stopping times `σ` and `ρ`, kept on an event
`F` before `σ`, are bounded and conditionally centred for the conditioned measure. -/
theorem increments_blockIncrement (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ μ)
    {σ ρ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ) (hρ : IsStoppingTime ℱ ρ) {F : Set Ω}
    (hF : MeasurableSet[hσ.measurableSpace] F) (hμF : μ F ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ (t : ℕ) (ω : Ω), σ ω ≤ (t : WithTop ℕ) → (t : WithTop ℕ) < ρ ω →
      |M (t + 1) ω - M t ω| ≤ b) (n : ℕ) :
    Increments (μ[|F]) ℱ (blockIncrement M σ ρ F) b n := by
  refine ⟨hb, fun t _ => ?_, fun t _ ω => ?_, fun t _ => ?_⟩
  · rw [blockIncrement_eq_indicator]
    exact ((((hM.1 (t + 1)).sub ((hM.1 t).mono (ℱ.mono (Nat.le_succ t))))).indicator
      (ℱ.mono (Nat.le_succ t) _ (measurableSet_inter_gate ℱ hσ hρ hF t)))
  · by_cases hωF : ω ∈ F
    · by_cases hωS : σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω
      · simp only [blockIncrement, Set.indicator_of_mem hωF, if_pos hωS, one_mul]
        exact hbound t ω hωS.1 hωS.2
      · simp only [blockIncrement, Set.indicator_of_mem hωF, if_neg hωS, zero_mul, abs_zero]
        exact hb
    · simp only [blockIncrement, Set.indicator_of_notMem hωF, abs_zero]
      exact hb
  · have h := condExp_cond_indicator μ (ℱ.le t) (measurableSet_of_stopping ℱ hσ hF) hμF
      (measurableSet_gate ℱ hσ hρ t) (measurableSet_inter_gate ℱ hσ hρ hF t)
      ((hM.integrable (t + 1)).sub (hM.integrable t)) (Z := blockIncrement M σ ρ F t)
      (blockIncrement_eq M σ ρ F t)
    refine h.trans ?_
    filter_upwards [(cond_absolutelyContinuous (μ := μ) (s := F)).ae_eq
      (condExp_increment_ae_zero μ ℱ hM t)] with ω hω
    simp only [Set.indicator_apply]
    split_ifs
    · exact hω
    · rfl

/-- Under the conditioned measure, the conditional second moment of a block increment is the
conditional second moment of the increment of `M` under `μ`, restricted to the times `σ ≤ t < ρ`. -/
theorem condExp_sq_blockIncrement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {M : ℕ → Ω → ℝ}
    (hL2 : ∀ n, MemLp (M n) 2 μ) {σ ρ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ)
    (hρ : IsStoppingTime ℱ ρ) {F : Set Ω} (hF : MeasurableSet[hσ.measurableSpace] F)
    (hμF : μ F ≠ 0) (t : ℕ) :
    (μ[|F])[fun ω => blockIncrement M σ ρ F t ω ^ 2 | ℱ t] =ᵐ[μ[|F]]
      fun ω => (if σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω then (1 : ℝ) else 0) *
        (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω := by
  have h := condExp_cond_indicator μ (ℱ.le t) (measurableSet_of_stopping ℱ hσ hF) hμF
    (measurableSet_gate ℱ hσ hρ t) (measurableSet_inter_gate ℱ hσ hρ hF t)
    (((hL2 (t + 1)).sub (hL2 t)).integrable_sq)
    (Z := fun ω => blockIncrement M σ ρ F t ω ^ 2) (blockIncrement_sq_eq M σ ρ F t)
  refine h.trans (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hS : σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω
  · simp [hS]
  · simp [hS]

/-- The total conditional variance of the block increments under the conditioned measure is the
sum of the conditional variances of `M` over the times `σ ≤ t < ρ`. -/
theorem varSum_blockIncrement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {M : ℕ → Ω → ℝ}
    (hL2 : ∀ n, MemLp (M n) 2 μ) {σ ρ : Ω → WithTop ℕ} (hσ : IsStoppingTime ℱ σ)
    (hρ : IsStoppingTime ℱ ρ) {F : Set Ω} (hF : MeasurableSet[hσ.measurableSpace] F)
    (hμF : μ F ≠ 0) (n : ℕ) :
    varSum (μ[|F]) ℱ (blockIncrement M σ ρ F) n =ᵐ[μ[|F]]
      fun ω => ∑ t ∈ Finset.range n,
        (if σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω then (1 : ℝ) else 0) *
          (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω := by
  have h : ∀ᵐ ω ∂(μ[|F]), ∀ t ∈ Finset.range n,
      condVar (μ[|F]) ℱ (blockIncrement M σ ρ F) t ω =
        (if σ ω ≤ (t : WithTop ℕ) ∧ (t : WithTop ℕ) < ρ ω then (1 : ℝ) else 0) *
          (μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t]) ω :=
    (Filter.eventually_all_finset _).2 fun t _ =>
      condExp_sq_blockIncrement μ ℱ hL2 hσ hρ hF hμF t
  filter_upwards [h] with ω hω
  exact Finset.sum_congr rfl hω

/-- The sum of the block increments telescopes to the increment of `M` between the stopping times
`σ ≤ ρ` cut off at time `n`, on the event `F`. -/
theorem sum_blockIncrement (M : ℕ → Ω → ℝ) {σ ρ : Ω → WithTop ℕ} (hσρ : ∀ ω, σ ω ≤ ρ ω)
    (F : Set Ω) (n : ℕ) (ω : Ω) :
    ∑ t ∈ Finset.range n, blockIncrement M σ ρ F t ω =
      F.indicator (fun ω => stoppedValue M (fun ω => min (ρ ω) (n : WithTop ℕ)) ω -
        stoppedValue M (fun ω => min (σ ω) (n : WithTop ℕ)) ω) ω := by
  by_cases hω : ω ∈ F
  · simp only [blockIncrement, Set.indicator_of_mem hω]
    exact gate_sum_aux (fun t => M t ω) (σ ω) (ρ ω) (hσρ ω) n
  · simp [blockIncrement, Set.indicator_of_notMem hω]

end CERW.Generic.Martingale.LilLower
