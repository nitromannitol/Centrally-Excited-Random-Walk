import CERW.Generic.Martingale.LilAssembly.Core
import CERW.Generic.Martingale.LilAssembly.LevyBlocks
import CERW.Generic.Martingale.LilAssembly.PassageWindow
import CERW.Generic.Martingale.LilAssembly.PathCombine
import CERW.Generic.Martingale.Lil

/-!
# The lower bound for padded data

`NiceLower` from `BlockLower`:
* Lévy's lemma along the blocks (`levy_blocks`) makes the block events occur infinitely often;
* the passage times are finite and tend to infinity with the bracket in its window
  (`passage_window`);
* the upper half of Stout's law for `-M` (`CERW.Generic.Martingale.Lil.stout_upper`) bounds `M`
  from below at the passage times;
* `path_combine` turns this into `M_n ≥ (1 - δ) ψ(V_n)` infinitely often.
-/

universe u

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology CERW.Generic.Martingale.LilLower

/-- Negating a process does not change its predictable bracket. -/
theorem predBracket_neg {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) :
    CERW.predBracket μ ℱ (-M) (-M) = CERW.predBracket μ ℱ M M := by
  funext n
  unfold CERW.predBracket
  refine Finset.sum_congr rfl fun t _ => ?_
  have h : (fun ω => ((-M) (t + 1) ω - (-M) t ω) * ((-M) (t + 1) ω - (-M) t ω)) =
      fun ω => (M (t + 1) ω - M t ω) * (M (t + 1) ω - M t ω) := by
    funext ω
    simp only [Pi.neg_apply]
    ring
  rw [h]

/-- Step 0: the upper half of Stout's law for `-M` gives a lower bound for `M`. -/
theorem neg_lower_ae {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (M B V : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ)
    (hPD : PaddedData μ ℱ M B V εg N) {δ' : ℝ} (hδ' : 0 < δ') :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, -((1 + δ') * lilScale (V n ω)) ≤ M n ω := by
  have hbInc : ∀ᵐ ω ∂μ, ∀ n, |(-M) (n + 1) ω - (-M) n ω| ≤ B (n + 1) ω := by
    filter_upwards [hPD.bInc] with ω h n
    simp only [Pi.neg_apply, neg_sub_neg]
    rw [abs_sub_comm]
    exact h n
  have hbr : ∀ᵐ ω ∂μ, ∀ n, CERW.predBracket μ ℱ (-M) (-M) n ω = V n ω := by
    filter_upwards [hPD.vBracket] with ω h n
    rw [predBracket_neg]
    exact (h n).symm
  have hinf : ∀ᵐ ω ∂μ,
      Tendsto (fun n => CERW.predBracket μ ℱ (-M) (-M) n ω) atTop atTop := by
    filter_upwards [hbr, hPD.vInf] with ω h1 h2
    exact h2.congr fun n => (h1 n).symm
  have hrat : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω *
      Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ (-M) (-M) n ω)
        (Real.exp (Real.exp 1))))) / Real.sqrt (CERW.predBracket μ ℱ (-M) (-M) n ω))
      atTop (𝓝 0) := by
    filter_upwards [hbr, hPD.bRatio] with ω h1 h2
    refine h2.congr fun n => ?_
    rw [h1 n]
  have hup := CERW.Generic.Martingale.Lil.stout_upper.{u} μ ℱ (-M) hPD.mart.neg
    (fun n => (hPD.memLp n).neg) (fun ω => by simp [hPD.zero ω]) B hPD.bPred hbInc hinf hrat
  filter_upwards [hup, hbr] with ω h1 h2
  filter_upwards [h1 δ' hδ'] with n hn
  rw [h2 n] at hn
  have : -M n ω ≤ (1 + δ') * lilScale (V n ω) := hn
  linarith

/-- A frequent property along `k + 1` from one along `k` that fails at `0`. -/
theorem frequently_succ_of_frequently {p : ℕ → Prop} (h : ∃ᶠ k in atTop, p k) (h0 : ¬ p 0) :
    ∃ᶠ k in atTop, p (k + 1) := by
  rw [Filter.frequently_atTop] at h ⊢
  intro a
  obtain ⟨b, hb, hpb⟩ := h (a + 1)
  cases b with
  | zero => exact absurd hpb h0
  | succ c => exact ⟨c, by omega, hpb⟩

/-- Membership in the block event `k + 1`, in terms of the martingale at the passage times. -/
theorem mem_blockEvent_succ {Ω : Type*} (M V : ℕ → Ω → ℝ) (θ δ : ℝ) (k : ℕ) (ω : Ω) :
    ω ∈ blockEvent M V θ δ (k + 1) ↔
      (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale (θ ^ (k + 1)) ≤
        M (firstPassage V (θ ^ (k + 1)) ω).untopA ω - M (firstPassage V (θ ^ k) ω).untopA ω := by
  simp only [blockEvent, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Set.mem_setOf_eq]
  rfl

/-- The lower bound for padded data, from the conditional lower bound for the blocks. -/
theorem niceLower_of (hBL : BlockLower.{u}) : NiceLower.{u} := by
  intro δ hδ hδ1
  obtain ⟨θ, δ', εs, hθ, hδ', hεs, hcond, hall⟩ := hBL δ hδ hδ1
  refine ⟨min εs (1 / 2), lt_min hεs (by norm_num), ?_⟩
  intro Ω m0 μ _ ℱ M B V εg N hεg hle hPD
  obtain ⟨hτ, k₀, q, -, hq1, hdiv, hEm, hbound⟩ :=
    hall μ ℱ M B V εg N hεg (hle.trans (min_le_left _ _)) hPD
  have hmono : ∀ k ω, firstPassage V (θ ^ k) ω ≤ firstPassage V (θ ^ (k + 1)) ω :=
    fun k ω => firstPassage_mono (pow_le_pow_right₀ hθ.le (Nat.le_succ k))
  have hN : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, (N : WithTop ℕ) ≤ firstPassage V (θ ^ k) ω :=
    Filter.Eventually.of_forall fun ω =>
      eventually_le_firstPassage (tendsto_pow_atTop_atTop_of_one_lt hθ) N
  have hlevy := levy_blocks μ ℱ (fun k => firstPassage V (θ ^ k)) hτ hmono hEm hq1 hdiv N k₀
    hN hbound
  have hneg := neg_lower_ae μ ℱ M B V εg N hPD hδ'
  filter_upwards [hlevy, hneg, hPD.vInf, hPD.jump] with ω hω hnegω hinf hjump
  obtain ⟨-, hτt, hwin⟩ := passage_window V εg θ N ω hθ hεg (hle.trans (min_le_right _ _))
    hinf hjump
  have hfreq : ∃ᶠ k in atTop, ω ∈ blockEvent M V θ δ k :=
    Filter.mem_limsup_iff_frequently_mem.1 hω
  have hfreq' := frequently_succ_of_frequently hfreq (by simp [blockEvent])
  exact path_combine (fun n => M n ω) (fun n => V n ω)
    (fun k => (firstPassage V (θ ^ k) ω).untopA) (fun k => θ ^ k)
    (fun k => (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale (θ ^ (k + 1))) θ δ δ' hθ hδ hδ1 hδ'
    hcond (fun k => pow_succ' θ k) (tendsto_pow_atTop_atTop_of_one_lt hθ) hτt hwin
    (Filter.Eventually.of_forall fun k => le_refl _) (hτt.eventually hnegω)
    (hfreq'.mono fun k hk => (mem_blockEvent_succ M V θ δ k ω).1 hk)

end CERW.Generic.Martingale.LilAssembly
