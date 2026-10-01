import CERW.Generic.Martingale.Lil.Statements

/-!
# Freedman's inequality for the running maximum

On the event of a small bracket, the running maximum of a martingale with bounded increments has
the tail of Freedman's inequality. The proof stops the martingale predictably once the bracket
would exceed `v`, then at its first passage above `r`, and applies `LatticeProb.freedman_upper` at
the final time.
-/

universe u

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology

/-- The running maximum of an adapted process is adapted. -/
theorem stronglyMeasurable_runMax {Ω : Type*} {m0 : MeasurableSpace Ω} {ℱ : Filtration ℕ m0}
    {X : ℕ → Ω → ℝ} (hX : StronglyAdapted ℱ X) (k : ℕ) :
    StronglyMeasurable[ℱ k] (runMax X k) := by
  induction k with
  | zero => exact hX 0
  | succ k ih =>
      have h1 : StronglyMeasurable[ℱ (k + 1)] (runMax X k) := ih.mono (ℱ.mono (Nat.le_succ k))
      exact Measurable.stronglyMeasurable (Measurable.max h1.measurable (hX (k + 1)).measurable)

/-- An adapted process from `0` with increments at most `b` is in `L²` at every time. -/
theorem memLp_two_of_increments {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hX : StronglyAdapted ℱ X) (hX0 : ∀ ω, X 0 ω = 0) {b : ℝ}
    (hinc : ∀ i ω, |X (i + 1) ω - X i ω| ≤ b) (k : ℕ) : MemLp (X k) 2 μ := by
  refine MemLp.of_bound ((hX k).mono (ℱ.le k)).aestronglyMeasurable (k * b)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact LatticeProb.abs_le_of_increments hX0 (n := k) (fun i _ ω => hinc i ω) k le_rfl ω

/-- Freedman's inequality for the running maximum on the event of a small bracket. -/
theorem maximalFreedman_of (hGV : GatedVariance.{u}) (hFP : FirstPassage.{u}) :
    MaximalFreedman.{u} := by
  intro Ω m0 μ _ ℱ M V hM hM0 hVpred hV0 hVmono hVdom b v r hb hv hr hinc n
  have hM1 : Martingale (predictableStop M V v) ℱ μ := martingale_predictableStop hM hVpred
  have hM1ad : StronglyAdapted ℱ (predictableStop M V v) :=
    stronglyAdapted_predictableStop hM hVpred
  have hM10 : ∀ ω, predictableStop M V v 0 ω = 0 := predictableStop_zero M V v
  have hinc1 : ∀ i ω, |predictableStop M V v (i + 1) ω - predictableStop M V v i ω| ≤ b :=
    fun i ω => abs_predictableStop_succ_sub_le (V := V) (v := v) (n := i + 1)
      (fun j _ ω' => hinc j ω') i (Nat.lt_succ_self i) ω
  have hpass : ∀ k, StronglyMeasurable[ℱ k] (passLevel (predictableStop M V v) (k + 1)) :=
    fun k => stronglyMeasurable_runMax hM1ad k
  have hM2 : Martingale (firstPassage (predictableStop M V v) r) ℱ μ :=
    martingale_predictableStop hM1 hpass
  have hM20 : ∀ ω, firstPassage (predictableStop M V v) r 0 ω = 0 :=
    predictableStop_zero _ _ r
  have hinc2 : ∀ i, i < n → ∀ ω,
      |firstPassage (predictableStop M V v) r (i + 1) ω
        - firstPassage (predictableStop M V v) r i ω| ≤ b :=
    abs_predictableStop_succ_sub_le (fun j _ ω => hinc1 j ω)
  have hL2 : ∀ k, MemLp (predictableStop M V v k) 2 μ :=
    memLp_two_of_increments hM1ad hM10 hinc1
  have hqv1 := condQvar_predictableStop_le hM hVpred hV0 hVmono hVdom
    (fun i _ ω => hinc i ω) hv (n := n)
  have hqv2 : ∀ᵐ ω ∂μ, LatticeProb.condQvar μ ℱ (firstPassage (predictableStop M V v) r) n ω
      ≤ v := by
    have hall : ∀ᵐ ω ∂μ, ∀ i : ℕ,
        (μ[fun ω' => (firstPassage (predictableStop M V v) r (i + 1) ω'
          - firstPassage (predictableStop M V v) r i ω') ^ 2 | ℱ i]) ω
        ≤ (μ[fun ω' => (predictableStop M V v (i + 1) ω'
          - predictableStop M V v i ω') ^ 2 | ℱ i]) ω :=
      ae_all_iff.mpr fun i => hGV μ ℱ _ _ r hM1 hL2 hpass i
    filter_upwards [hall, hqv1] with ω h1 h2
    refine le_trans (Finset.sum_le_sum fun i _ => h1 i) h2
  have hup := LatticeProb.freedman_upper hM2 hM20 hb hv hinc2 hqv2 hr
  have hsub : {ω | ∃ i ≤ n, V i ω ≤ v ∧ r < M i ω}
      ⊆ {ω | r ≤ firstPassage (predictableStop M V v) r n ω} := by
    rintro ω ⟨i, hi, hVi, hMi⟩
    have hs : predictableStop M V v i ω = M i ω := predictableStop_eq_of_le hM0 hVmono hVi
    exact (hFP (predictableStop M V v) r ω n (hM10 ω) ⟨i, hi, hs ▸ hMi⟩).le
  exact (measure_mono hsub).trans
    ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr hup)

end CERW.Generic.Martingale.Lil
