module

public import CERW.LimitShapes.Event

@[expose] public section

/-!
# The quadratic process stopped at the first exit is a martingale

The full prefix guard in Section `sec:norm-event` is measurable at the departure time.
Its bounded predictable transform of the quadratic Dynkin martingale agrees almost surely
with the explicit stopped sum. Finite past paths give adaptation of that sum everywhere.
-/

open MeasureTheory Filter LatticeProb

namespace CERW.LimitShapes.StoppedQuadraticMartingale

open CERW CERW.Support.Law CERW.Support.Drift CERW.Support.Norm.ContactEvent
open private quadraticMartingale_eq_driftDynkin from CERW.Support.Norm.ContactEvent

/-- The explicit stopped sum depends only on positions through its terminal time. -/
theorem stoppedQuadratic_congr {d : ℕ} (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (R : ℝ) {x y : ℕ → Site d} {n : ℕ}
    (h : ∀ j ≤ n, x j = y j) : stoppedQuadratic ε ξ R x n =
      stoppedQuadratic ε ξ R y n := by
  classical
  unfold stoppedQuadratic
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j < n := Finset.mem_range.mp hj
  have hg : (∀ k ≤ j, euclidNorm (x k) < R) ↔ ∀ k ≤ j, euclidNorm (y k) < R := by
    constructor <;> intro hg k hk
    · rw [← h k (hk.trans hjn.le)]
      exact hg k hk
    · rw [h k (hk.trans hjn.le)]
      exact hg k hk
  have hdep : departureRange x j = departureRange y j := by
    unfold departureRange
    exact Finset.image_congr fun k hk => h k (by
      have := Finset.mem_range.mp hk
      omega)
  simp only [hg, h j hjn.le, h (j + 1) hjn, hdep]

/-- Every value of the explicit stopped process is measurable for the finite past filtration. -/
theorem stronglyAdapted_stoppedQuadratic {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    StronglyAdapted (pathFiltration hX)
      (fun n ω => stoppedQuadratic ε ξ R (X · ω) n) := by
  intro n
  change StronglyMeasurable[pathFiltration hX n]
    (fun ω => stoppedQuadratic ε ξ R (X · ω) n)
  have heq : (fun ω => stoppedQuadratic ε ξ R (X · ω) n) =
      (fun ω => stoppedQuadratic ε ξ R (extendPath (pastPath X n ω)) n) := by
    funext ω
    exact stoppedQuadratic_congr ε ξ R fun j hj => (extendPath_pastPath X hj ω).symm
  rw [heq]
  exact stronglyMeasurable_comp_pastPath hX n
    (fun p => stoppedQuadratic ε ξ R (extendPath p) n)

/-- The full prefix guard gives the actual stopped quadratic martingale, with no
pathwise legality assumption outside the almost sure set supplied by the walk law. -/
theorem martingale_stoppedQuadratic
    {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : LatticeProb.Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) (hξ0 : ξ 0 = 0) (R : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {X : ℕ → Ω → LatticeProb.Site d}
    (hX : CERW.IsDriftCERW μ ε ξ X) :
    MeasureTheory.Martingale
      (fun n ω => CERW.LimitShapes.stoppedQuadratic ε ξ R (X · ω) n)
      (CERW.Support.Law.pathFiltration hX.measurable) μ := by
  classical
  let Q := driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X
  have hQ : Martingale Q (pathFiltration hX.measurable) μ :=
    martingale_driftDynkin hd hε hξ hX (fun z : Site d => euclidNorm z ^ 2)
  let I : ℕ → Ω → ℝ := fun j ω => if ∀ k ≤ j, euclidNorm (X k ω) < R then 1 else 0
  have hI : ∀ j, StronglyMeasurable[pathFiltration hX.measurable j] (I j) := by
    intro j
    have heq : I j = (fun ω =>
        if ∀ k : Finset.Iic j, euclidNorm (pastPath X j ω k) < R then (1 : ℝ) else 0) := by
      funext ω
      have hg : (∀ k ≤ j, euclidNorm (X k ω) < R) ↔
          ∀ k : Finset.Iic j, euclidNorm (pastPath X j ω k) < R := by
        constructor
        · intro h k
          exact h k (Finset.mem_Iic.mp k.property)
        · intro h k hk
          exact h ⟨k, Finset.mem_Iic.mpr hk⟩
      simp only [I, hg]
    rw [heq]
    exact stronglyMeasurable_comp_pastPath hX.measurable j
      (fun p => if ∀ k : Finset.Iic j, euclidNorm (p k) < R then (1 : ℝ) else 0)
  have hIb : ∀ j ω, ‖I j ω‖ ≤ 1 := by
    intro j ω
    dsimp [I]
    split_ifs <;> norm_num
  let S : ℕ → Ω → ℝ := fun n ω => ∑ j ∈ Finset.range n,
    I j ω * (Q (j + 1) ω - Q j ω)
  have hSad : StronglyAdapted (pathFiltration hX.measurable) S := by
    intro n
    refine Finset.stronglyMeasurable_fun_sum _ fun j hj => ?_
    have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
    exact ((hI j).mono ((pathFiltration hX.measurable).mono (by omega))).mul
      (((hQ.stronglyMeasurable (j + 1)).mono ((pathFiltration hX.measurable).mono hjn)).sub
        ((hQ.stronglyMeasurable j).mono ((pathFiltration hX.measurable).mono (by omega))))
  have hSint : ∀ n, Integrable (S n) μ := by
    intro n
    refine integrable_finsetSum (Finset.range n) fun j _ => ?_
    exact Integrable.bdd_mul ((hQ.integrable (j + 1)).sub (hQ.integrable j))
      (((hI j).mono ((pathFiltration hX.measurable).le j))).aestronglyMeasurable
      (c := 1) (Eventually.of_forall (hIb j))
  have hScond : ∀ j, μ[S (j + 1) - S j | pathFiltration hX.measurable j] =ᵐ[μ] 0 := by
    intro j
    have hdiff : S (j + 1) - S j = I j * (Q (j + 1) - Q j) := by
      funext ω
      simp only [S, Finset.sum_range_succ, Pi.sub_apply, Pi.mul_apply, add_sub_cancel_left]
    rw [hdiff]
    have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ)
      ((pathFiltration hX.measurable).le j) (hI j)
      ((hQ.integrable (j + 1)).sub (hQ.integrable j)) 1 (Eventually.of_forall (hIb j))
    have hcent : μ[Q (j + 1) - Q j | pathFiltration hX.measurable j] =ᵐ[μ] 0 := by
      have hsub := condExp_sub (hQ.integrable (j + 1)) (hQ.integrable j)
        (pathFiltration hX.measurable j)
      have hnext := hQ.condExp_ae_eq (Nat.le_succ j)
      have hnow := condExp_of_stronglyMeasurable ((pathFiltration hX.measurable).le j)
        (hQ.stronglyMeasurable j) (hQ.integrable j)
      filter_upwards [hsub, hnext] with ω hs hn
      rw [hs, Pi.sub_apply, hn, hnow, sub_self]
      rfl
    filter_upwards [hpull, hcent] with ω hp hc
    rw [hp, Pi.mul_apply, hc, Pi.zero_apply, mul_zero]
  have hS : Martingale S (pathFiltration hX.measurable) μ :=
    martingale_of_condExp_sub_eq_zero_nat hSad hSint hScond
  apply hS.congr (stronglyAdapted_stoppedQuadratic hX.measurable ε ξ R)
  intro n
  filter_upwards [ae_all_iff.mpr (ae_sub_mem_unitSteps_drift hd hε hξ hX)] with ω hs
  have heq (t : ℕ) := quadraticMartingale_eq_driftDynkin hd ε ξ hξ0 X ω hs t
  dsimp [S]
  unfold stoppedQuadratic
  refine Finset.sum_congr rfl fun j _ => ?_
  change I j ω * (driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X (j + 1) ω -
    driftDynkin ε ξ (fun z : Site d => euclidNorm z ^ 2) X j ω) = _
  rw [← heq (j + 1), ← heq j]
  simp only [quadraticMartingale, Finset.sum_range_succ, add_sub_cancel_left]
  dsimp [I]
  split_ifs <;> simp only [one_mul, zero_mul]

end CERW.LimitShapes.StoppedQuadraticMartingale
