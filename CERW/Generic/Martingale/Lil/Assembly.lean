import CERW.Generic.Martingale.Lil.Statements

/-!
# The assembly of the upper half

Borel–Cantelli over the blocks, the pathwise step along almost every path, and a countable
intersection over `δ = 1/(m+1)`.
-/

universe u

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology

/-- Borel–Cantelli over the blocks: almost surely only finitely many blocks are hit. -/
theorem blockHit_ae_eventually_not (h5 : TruncatedBlock.{u}) (h7 : BlockSummable)
    {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S B V : ℕ → Ω → ℝ) (hS : Martingale S ℱ μ)
    (hL2 : ∀ n, MemLp (S n) 2 μ) (hS0 : ∀ ω, S 0 ω = 0)
    (hBpred : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)))
    (hBinc : ∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ B (n + 1) ω)
    (hVpred : ∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) (hV0 : ∀ ω, V 0 ω = 0)
    (hVmono : ∀ k ω, V k ω ≤ V (k + 1) ω)
    (hVdom : ∀ k, μ[fun ω => (S (k + 1) ω - S k ω) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun ω => V (k + 1) ω - V k ω)
    {θ ε δ η : ℝ} (hpar : LilParams θ ε δ η) :
    ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ¬ BlockHit S B V θ ε δ k ω := by
  obtain ⟨hK, hsum⟩ := h7 θ ε δ η hpar
  obtain ⟨K, hK⟩ := eventually_atTop.1 hK
  obtain ⟨hθ, -, hδ, -, -⟩ := hpar
  have hmu : ∀ k, K ≤ k → μ {ω | BlockHit S B V θ ε δ k ω} ≤
      ENNReal.ofReal (Real.exp (-(blockRadius θ δ k ^ 2 /
        (2 * (θ ^ (k + 1) + blockTrunc θ ε k * blockRadius θ δ k / 3))))) := by
    intro k hk
    exact h5 μ ℱ S B V hS hL2 hS0 hBpred hBinc hVpred hV0 hVmono hVdom (hK k hk)
      (pow_nonneg (by linarith) _)
      (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  have hsum' : ∑' k : ℕ, μ {ω | BlockHit S B V θ ε δ (k + K) ω} ≠ ⊤ := by
    refine ne_top_of_le_ne_top hsum ?_
    calc ∑' k : ℕ, μ {ω | BlockHit S B V θ ε δ (k + K) ω}
        ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(blockRadius θ δ (k + K) ^ 2 /
          (2 * (θ ^ (k + K + 1) + blockTrunc θ ε (k + K) * blockRadius θ δ (k + K) / 3))))) :=
          ENNReal.tsum_le_tsum fun k => hmu (k + K) (by omega)
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective K)
          (fun k => ENNReal.ofReal (Real.exp (-(blockRadius θ δ k ^ 2 /
            (2 * (θ ^ (k + 1) + blockTrunc θ ε k * blockRadius θ δ k / 3))))))
  filter_upwards [ae_eventually_notMem hsum'] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine eventually_atTop.2 ⟨N + K, fun k hk => ?_⟩
  have h := hN (k - K) (by omega)
  rwa [Nat.sub_add_cancel (by omega : K ≤ k)] at h

/-- The upper half for one fixed `δ > 0`. -/
theorem stoutUpper_delta (h1 : RegBracket.{u}) (h5 : TruncatedBlock.{u}) (hA : LilArith)
    (h7 : BlockSummable) (h8 : PathwiseUpper.{u})
    {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (hS : Martingale S ℱ μ)
    (hL2 : ∀ n, MemLp (S n) 2 μ) (hS0 : ∀ ω, S 0 ω = 0) (B : ℕ → Ω → ℝ)
    (hBpred : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1)))
    (hBinc : ∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ B (n + 1) ω)
    (hP : ∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω) atTop atTop)
    (hBt : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω *
        Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ S S n ω)
          (Real.exp (Real.exp 1))))) / Real.sqrt (CERW.predBracket μ ℱ S S n ω))
      atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, S n ω ≤ (1 + δ) * Real.sqrt (2 * CERW.predBracket μ ℱ S S n ω *
        Real.log (Real.log (CERW.predBracket μ ℱ S S n ω))) := by
  obtain ⟨V, hVpred, hV0, hVmono, hVdom, hVeq⟩ := h1 μ ℱ S
  obtain ⟨θ, ε, η, hpar⟩ := hA.1 δ hδ
  filter_upwards [blockHit_ae_eventually_not h5 h7 μ ℱ S B V hS hL2 hS0 hBpred hBinc hVpred hV0
    hVmono hVdom hpar, hVeq, hP, hBt] with ω hblk hV hP' hBt'
  have hP'' : Tendsto (fun n => V n ω) atTop atTop := by simpa only [hV] using hP'
  have hB'' : Tendsto (fun n => B n ω * Real.sqrt (Real.log (Real.log (max (V n ω)
      (Real.exp (Real.exp 1))))) / Real.sqrt (V n ω)) atTop (𝓝 0) := by
    simpa only [hV] using hBt'
  have h := h8 S B V ω θ ε δ η hpar (hS0 ω) (fun n => hVmono n ω) (hV0 ω) hP'' hB'' hblk
  simpa only [hV] using h

/-- The upper half of Stout's law of the iterated logarithm, from its steps. -/
theorem stoutUpper_of (h1 : RegBracket.{u}) (h5 : TruncatedBlock.{u}) (hA : LilArith)
    (h7 : BlockSummable) (h8 : PathwiseUpper.{u}) : StoutUpper.{u} := by
  intro Ω m0 μ _ ℱ S hS hL2 hS0 B hBpred hBinc hP hBt
  have hall : ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ n : ℕ in atTop,
      S n ω ≤ (1 + 1 / ((m : ℝ) + 1)) * Real.sqrt (2 * CERW.predBracket μ ℱ S S n ω *
        Real.log (Real.log (CERW.predBracket μ ℱ S S n ω))) :=
    ae_all_iff.2 fun m => stoutUpper_delta h1 h5 hA h7 h8 μ ℱ S hS hL2 hS0 B hBpred hBinc hP hBt
      (Nat.one_div_pos_of_nat)
  filter_upwards [hall] with ω hω δ hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  filter_upwards [hω m] with n hn
  exact hn.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

end CERW.Generic.Martingale.Lil
