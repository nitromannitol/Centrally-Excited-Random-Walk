import CERW.Generic.Martingale.Lil.Statements

/-!
# Freedman's inequality for the truncated martingale

The martingale truncated predictably where the bound `B_{n+1}` on its increments exceeds `b` has
increments at most `b` almost surely. It agrees almost surely with a martingale whose increments
are surely at most `b` (`exists_martingale_clamp`), to which the maximal inequality applies at
every horizon.
-/

universe u

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology

/-- Freedman's inequality for the running maximum of the truncated martingale. -/
theorem truncatedBlock_of (hGV : GatedVariance.{u}) (hMF : MaximalFreedman.{u}) :
    TruncatedBlock.{u} := by
  intro Ω m0 μ _ ℱ S B V hS hL2 _ hBpred hinc hVpred hV0 hVmono hVdom b v r hb hv hr
  have hTmart : Martingale (predictableStop S B b) ℱ μ := martingale_predictableStop hS hBpred
  have hTinc : ∀ i, ∀ᵐ ω ∂μ, |predictableStop S B b (i + 1) ω - predictableStop S B b i ω| ≤ b :=
    fun i => (hinc.mono fun ω hω => hω i).mono fun ω hω => by
      rw [predictableStop_succ_sub, abs_mul, abs_of_nonneg (bracketIndicator_nonneg B b i ω)]
      rcases le_or_gt (B (i + 1) ω) b with h | h
      · rw [bracketIndicator_of_le h, one_mul]
        exact hω.trans h
      · rw [bracketIndicator_of_lt h, zero_mul]
        exact hb.le
  obtain ⟨T, hTm, hTb, hT0, hTae⟩ := exists_martingale_clamp hTmart hb.le hTinc
  have hT00 : ∀ ω, T 0 ω = 0 := fun ω => (hT0 ω).trans (predictableStop_zero S B b ω)
  have hdom : ∀ k, μ[fun ω => (T (k + 1) ω - T k ω) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun ω => V (k + 1) ω - V k ω := by
    intro k
    have hcongr : μ[fun ω => (T (k + 1) ω - T k ω) ^ 2 | ℱ k]
        =ᵐ[μ] μ[fun ω => (predictableStop S B b (k + 1) ω - predictableStop S B b k ω) ^ 2
          | ℱ k] :=
      condExp_congr_ae (hTae.mono fun ω hω => by simp only [hω (k + 1), hω k])
    exact (hcongr.trans_le (hGV μ ℱ S B b hS hL2 hBpred k)).trans (hVdom k)
  have hunion : ∀ n, μ {ω | ∃ i ≤ n, V i ω ≤ v ∧ r < T i ω} ≤
      ENNReal.ofReal (Real.exp (-(r ^ 2 / (2 * (v + b * r / 3))))) :=
    fun n => hMF μ ℱ T V hTm hT00 hVpred hV0 hVmono hdom hb hv hr hTb n
  have hmono : Monotone fun n => {ω | ∃ i ≤ n, V i ω ≤ v ∧ r < T i ω} :=
    fun m n hmn ω ⟨i, hi, h⟩ => ⟨i, hi.trans hmn, h⟩
  have hiUnion : (⋃ n, {ω | ∃ i ≤ n, V i ω ≤ v ∧ r < T i ω})
      = {ω | ∃ i, V i ω ≤ v ∧ r < T i ω} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun ⟨_, i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, i, le_rfl, h⟩⟩
  have hT' : μ {ω | ∃ i, V i ω ≤ v ∧ r < T i ω} ≤
      ENNReal.ofReal (Real.exp (-(r ^ 2 / (2 * (v + b * r / 3))))) := by
    rw [← hiUnion, hmono.measure_iUnion]
    exact iSup_le hunion
  refine le_trans (measure_mono_ae ?_) hT'
  filter_upwards [hTae] with ω hω ⟨n, hn, h⟩
  exact ⟨n, hn, by rw [hω n]; exact h⟩

end CERW.Generic.Martingale.Lil
