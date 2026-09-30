import CERW.Support.LocalTime.Bracket
import CERW.Generic.Martingale.Dyadic
import CERW.Generic.Martingale.Clamp
import CERW.Support.Law.ScaleArith

/-!
# The predictable bracket of the local martingales

The bracket `C_g² Σ_{j<t} (1 + |X_j - y|)^{2-2d}` of the Dynkin martingale of the translated kernel
`b(· - y)`, its one-step increment, monotonicity and interval increments, its measurability, and
the clamped translate of the martingale whose increments it controls. Shared by the local and the
interval martingale bounds.
-/

namespace CERW.Support.LocalTime

open MeasureTheory ProbabilityTheory LatticeProb Finset CERW CERW.Support.Law
open CERW.Support.Law

variable {d : ℕ}

/-- A power of `1 + ρ` with nonpositive exponent is at most `1`. -/
theorem rpow_one_add_le_one {ρ z : ℝ} (hρ : 0 ≤ ρ) (hz : z ≤ 0) : (1 + ρ) ^ z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hz

/-- The predictable bracket `C_g² Σ_{j<t} (1 + |X_j - y|)^{2-2d}` of the translated Dynkin
martingale `𝓜^y`. -/
noncomputable def bracket {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d)
    (t : ℕ) (ω : Ω) : ℝ :=
  Cg ^ 2 * ∑ j ∈ range t, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))


/-- The increment of the bracket is `C_g² (1 + |X_j - y|)^{2-2d}`. -/
theorem bracket_succ_sub {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : bracket Cg y X (j + 1) ω - bracket Cg y X j ω =
      Cg ^ 2 * (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) := by
  simp only [bracket, sum_range_succ]
  ring

/-- The bracket is nondecreasing. -/
theorem bracket_mono {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) (j : ℕ)
    (ω : Ω) : bracket Cg y X j ω ≤ bracket Cg y X (j + 1) ω := by
  have h := bracket_succ_sub Cg y X j ω
  have h0 : 0 ≤ Cg ^ 2 * (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) :=
    mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (by linarith [euclidNorm_nonneg (X j ω - y)]) _)
  linarith

/-- The bracket increment over `[s, t)` is `C_g²` times the sum over `s ≤ j < t`. -/
theorem bracket_sub {Ω : Type*} (Cg : ℝ) (y : Site d) (X : ℕ → Ω → Site d) {s t : ℕ}
    (hst : s ≤ t) (ω : Ω) : bracket Cg y X t ω - bracket Cg y X s ω =
      Cg ^ 2 * ∑ j ∈ Ico s t, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ)) := by
  rw [bracket, bracket, ← mul_sub, ← sum_Ico_eq_sub _ hst]

/-- The bracket increment over `s < t ≤ n` is at most `C_g² n`, as `1 ≤ d`. -/
theorem bracket_sub_le (hd : 1 ≤ d) {Ω : Type*} (Cg : ℝ) (y : Site d)
    (X : ℕ → Ω → Site d) {s t n : ℕ} (hst : s ≤ t) (htn : t ≤ n) (ω : Ω) :
    bracket Cg y X t ω - bracket Cg y X s ω ≤ Cg ^ 2 * n := by
  rw [bracket_sub Cg y X hst]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  calc ∑ j ∈ Ico s t, (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))
      ≤ ∑ _j ∈ Ico s t, (1 : ℝ) := by
        refine sum_le_sum fun j _ => rpow_one_add_le_one (euclidNorm_nonneg _) ?_
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
    _ = ((t - s : ℕ) : ℝ) := by simp
    _ ≤ n := by
        have : t - s ≤ n := by omega
        exact_mod_cast this

/-- The bracket at time `j + 1` is a function of the past path up to time `j`. -/
theorem stronglyMeasurable_bracket_succ {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ n, Measurable (X n)) (Cg : ℝ) (y : Site d) (j : ℕ) :
    StronglyMeasurable[pathFiltration hX j] (bracket Cg y X (j + 1)) := by
  have h := stronglyMeasurable_comp_pastPath hX j
    (fun q => Cg ^ 2 * ∑ i ∈ range (j + 1),
      (1 + euclidNorm (extendPath q i - y)) ^ (2 - 2 * (d : ℝ)))
  have heq : bracket Cg y X (j + 1) = fun ω => Cg ^ 2 * ∑ i ∈ range (j + 1),
      (1 + euclidNorm (extendPath (pastPath X j ω) i - y)) ^ (2 - 2 * (d : ℝ)) := by
    funext ω
    simp only [bracket]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [extendPath_pastPath X (Nat.lt_succ_iff.mp (mem_range.mp hi)) ω]
  rw [heq]
  exact h

/-- The translated Dynkin martingale `𝓜^y` agrees almost surely with a martingale whose increments
are at most `2 C_g + 1` everywhere and whose conditional variances are at most the bracket
increments. -/
theorem exists_clamped_translate (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (y : Site d) :
    ∃ M : ℕ → Ω → ℝ, Martingale M (pathFiltration hX.measurable) μ ∧
      (∀ i ω, |M (i + 1) ω - M i ω| ≤ 2 * Cg + 1) ∧
      (∀ j, μ[fun ω => (M (j + 1) ω - M j ω) ^ 2 | pathFiltration hX.measurable j] ≤ᵐ[μ]
        fun ω => bracket Cg y X (j + 1) ω - bracket Cg y X j ω) ∧
      ∀ᵐ ω ∂μ, ∀ i, M i ω = dynkin ε (fun z => b (z - y)) X i ω := by
  have hCg := cg_nonneg hd hgrad
  have hmart := martingale_dynkin hd hε hεd hX (fun z => b (z - y))
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |dynkin ε (fun z => b (z - y)) X (i + 1) ω -
      dynkin ε (fun z => b (z - y)) X i ω| ≤ 2 * Cg + 1 := fun i =>
    (ae_abs_dynkin_translate_succ_sub_le hd hε hεd hX hgrad y).mono fun ω hω => by
      have h1 : (1 + euclidNorm (X i ω - y)) ^ (1 - (d : ℝ)) ≤ 1 :=
        rpow_one_add_le_one (euclidNorm_nonneg _) (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      have h2 := hω i
      nlinarith
  obtain ⟨M, hM, hbd, -, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart
    (b := 2 * Cg + 1) (by linarith) hinc
  refine ⟨M, hM, hbd, fun j => ?_, hae⟩
  have hsq : (fun ω => (M (j + 1) ω - M j ω) ^ 2) =ᵐ[μ]
      fun ω => (dynkin ε (fun z => b (z - y)) X (j + 1) ω -
        dynkin ε (fun z => b (z - y)) X j ω) ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω, hω]
  refine (condExp_congr_ae hsq).trans_le ?_
  filter_upwards [condExp_sq_dynkin_translate_le hd hε hεd hX hgrad y j] with ω hω
  rw [bracket_succ_sub]
  exact hω

end CERW.Support.LocalTime
