import CERW.Generic.Martingale.FreedmanEvent
import CERW.Generic.Martingale.Clamp
import CERW.Model.Bracket

/-!
# The upper half of the martingale law of the iterated logarithm: the statements

The statements of the steps of the proof of the upper half of Stout's law of the iterated
logarithm (Stout 1970, Theorem 1), with an `ℱ_n`-measurable bound `B_{n+1}` on the increments. Each
step is a `Prop`, so that the proof of one step can assume the steps it uses; `StoutUpper` is the
conclusion. The route:

* `RegBracket`: a version `V` of the predictable bracket that is surely nondecreasing, predictable
  and from `0`, and dominates the conditional variances.
* `GatedVariance`, `FirstPassage`, `MaximalFreedman`: Freedman's inequality for the running
  maximum on the event of a small bracket, by stopping predictably at the first passage.
* `TruncatedBlock`: the same for the martingale truncated predictably where `B_{n+1} > b`.
* `LilArith`, `BlockSummable`: the parameters `θ, ε, η` of the geometric blocks `θ^k`, and the
  summability of the block bounds.
* `PathwiseUpper`: along one path, if only finitely many blocks are hit, the upper bound holds.
-/

universe u

namespace CERW.Generic.Martingale.Lil

open MeasureTheory ProbabilityTheory Filter Topology

/-- The truncation level of block `k`: `b_k = ε √(θ^{k+1} / log log θ^k)`. -/
noncomputable def blockTrunc (θ ε : ℝ) (k : ℕ) : ℝ :=
  ε * Real.sqrt (θ ^ (k + 1) / Real.log (Real.log (θ ^ k)))

/-- The radius of block `k`: `r_k = (1 + δ) √(2 θ^k log log θ^k)`. -/
noncomputable def blockRadius (θ δ : ℝ) (k : ℕ) : ℝ :=
  (1 + δ) * Real.sqrt (2 * θ ^ k * Real.log (Real.log (θ ^ k)))

/-- The parameters of the blocks: `θ > 1`, `ε, δ, η > 0`, and
`(1 + η)(θ + ε (1 + δ) √(2θ) / 3) ≤ (1 + δ)²`. -/
def LilParams (θ ε δ η : ℝ) : Prop :=
  1 < θ ∧ 0 < ε ∧ 0 < δ ∧ 0 < η ∧
    (1 + η) * (θ + ε * (1 + δ) * Real.sqrt (2 * θ) / 3) ≤ (1 + δ) ^ 2

/-- Block `k` is hit along `ω`: at some time `n` with bracket `V n ω ≤ θ^{k+1}`, the martingale
truncated at level `b_k` exceeds `r_k`. -/
def BlockHit {Ω : Type*} (S B V : ℕ → Ω → ℝ) (θ ε δ : ℝ) (k : ℕ) (ω : Ω) : Prop :=
  ∃ n, V n ω ≤ θ ^ (k + 1) ∧ blockRadius θ δ k < predictableStop S B (blockTrunc θ ε k) n ω

/-- A version of the predictable bracket that is surely nondecreasing, predictable and from `0`,
and dominates the conditional variances of the increments. -/
def RegBracket : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ),
    ∃ V : ℕ → Ω → ℝ, (∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) ∧ (∀ ω, V 0 ω = 0) ∧
      (∀ k ω, V k ω ≤ V (k + 1) ω) ∧
      (∀ k, μ[fun ω => (S (k + 1) ω - S k ω) ^ 2 | ℱ k] ≤ᵐ[μ]
        fun ω => V (k + 1) ω - V k ω) ∧
      ∀ᵐ ω ∂μ, ∀ k, V k ω = CERW.predBracket μ ℱ S S k ω

/-- A predictable gate does not increase the conditional variances of the increments. -/
def GatedVariance : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (M W : ℕ → Ω → ℝ) (w : ℝ), Martingale M ℱ μ →
    (∀ n, MemLp (M n) 2 μ) → (∀ k, StronglyMeasurable[ℱ k] (W (k + 1))) →
    ∀ k, μ[fun ω => (predictableStop M W w (k + 1) ω - predictableStop M W w k ω) ^ 2 | ℱ k]
      ≤ᵐ[μ] μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k]

/-- `runMax X k ω = max_{i ≤ k} X i ω`. -/
noncomputable def runMax {Ω : Type*} (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => X 0
  | k + 1 => fun ω => max (runMax X k ω) (X (k + 1) ω)

/-- The gate level of the first passage: `passLevel X (k + 1) = runMax X k`. -/
noncomputable def passLevel {Ω : Type*} (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => X 0
  | k + 1 => runMax X k

/-- `X` stopped predictably at its first passage strictly above `r`: the increment from `j` to
`j + 1` is kept exactly when `max_{i ≤ j} X i ≤ r`. -/
noncomputable def firstPassage {Ω : Type*} (X : ℕ → Ω → ℝ) (r : ℝ) : ℕ → Ω → ℝ :=
  predictableStop X (passLevel X) r

/-- If `X` from `0` exceeds `r` by time `n`, then so does `X` stopped at its first passage. -/
def FirstPassage : Prop :=
  ∀ {Ω : Type u} (X : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) (n : ℕ), X 0 ω = 0 →
    (∃ i ≤ n, r < X i ω) → r < firstPassage X r n ω

/-- Freedman's inequality for the running maximum on the event of a small bracket. -/
def MaximalFreedman : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (M V : ℕ → Ω → ℝ), Martingale M ℱ μ → (∀ ω, M 0 ω = 0) →
    (∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) → (∀ ω, V 0 ω = 0) →
    (∀ k ω, V k ω ≤ V (k + 1) ω) →
    (∀ k, μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun ω => V (k + 1) ω - V k ω) →
    ∀ {b v r : ℝ}, 0 < b → 0 ≤ v → 0 ≤ r → (∀ i ω, |M (i + 1) ω - M i ω| ≤ b) →
    ∀ n, μ {ω | ∃ i ≤ n, V i ω ≤ v ∧ r < M i ω} ≤
      ENNReal.ofReal (Real.exp (-(r ^ 2 / (2 * (v + b * r / 3)))))

/-- Freedman's inequality for the running maximum, on the event of a small bracket, of the
martingale truncated predictably where the bound `B_{n+1}` on its increments exceeds `b`. -/
def TruncatedBlock : Prop :=
  ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S B V : ℕ → Ω → ℝ), Martingale S ℱ μ → (∀ n, MemLp (S n) 2 μ) →
    (∀ ω, S 0 ω = 0) → (∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) →
    (∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ B (n + 1) ω) →
    (∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) → (∀ ω, V 0 ω = 0) →
    (∀ k ω, V k ω ≤ V (k + 1) ω) →
    (∀ k, μ[fun ω => (S (k + 1) ω - S k ω) ^ 2 | ℱ k] ≤ᵐ[μ]
      fun ω => V (k + 1) ω - V k ω) →
    ∀ {b v r : ℝ}, 0 < b → 0 ≤ v → 0 ≤ r →
    μ {ω | ∃ n, V n ω ≤ v ∧ r < predictableStop S B b n ω} ≤
      ENNReal.ofReal (Real.exp (-(r ^ 2 / (2 * (v + b * r / 3)))))

/-- The arithmetic of the blocks: parameters exist for every `δ > 0`, and the two monotonicity
facts of the pathwise step. -/
def LilArith : Prop :=
  (∀ δ : ℝ, 0 < δ → ∃ θ ε η : ℝ, LilParams θ ε δ η) ∧
    MonotoneOn (fun x : ℝ => x / Real.log (Real.log (max x (Real.exp (Real.exp 1)))))
      (Set.Ici 0) ∧
    MonotoneOn (fun y : ℝ => y * Real.log (Real.log y)) (Set.Ici (Real.exp 1))

/-- The truncation levels are eventually positive, and the block bounds are summable. -/
def BlockSummable : Prop :=
  ∀ θ ε δ η : ℝ, LilParams θ ε δ η →
    (∀ᶠ k in atTop, 0 < blockTrunc θ ε k) ∧
      ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(blockRadius θ δ k ^ 2 /
        (2 * (θ ^ (k + 1) + blockTrunc θ ε k * blockRadius θ δ k / 3))))) ≠ ⊤

/-- Along one path: if only finitely many blocks are hit, the bracket tends to infinity and
`B_n √(log log (V_n ∨ e^e)) / √V_n → 0`, then eventually `S_n ≤ (1 + δ) √(2 V_n log log V_n)`. -/
def PathwiseUpper : Prop :=
  ∀ {Ω : Type u} (S B V : ℕ → Ω → ℝ) (ω : Ω) (θ ε δ η : ℝ), LilParams θ ε δ η →
    S 0 ω = 0 → (∀ n, V n ω ≤ V (n + 1) ω) → V 0 ω = 0 →
    Tendsto (fun n => V n ω) atTop atTop →
    Tendsto (fun n => B n ω * Real.sqrt (Real.log (Real.log (max (V n ω)
      (Real.exp (Real.exp 1))))) / Real.sqrt (V n ω)) atTop (𝓝 0) →
    (∀ᶠ k in atTop, ¬ BlockHit S B V θ ε δ k ω) →
    ∀ᶠ n in atTop, S n ω ≤ (1 + δ) * Real.sqrt (2 * V n ω * Real.log (Real.log (V n ω)))

/-- The upper half of Stout's law of the iterated logarithm: the first conjunct of
`CERW.External.StoutLIL`, under the same hypotheses. -/
def StoutUpper : Prop :=
  ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ), Martingale S ℱ μ → (∀ n, MemLp (S n) 2 μ) →
    (∀ ω, S 0 ω = 0) → ∀ B : ℕ → Ω → ℝ, (∀ n, StronglyMeasurable[ℱ n] (B (n + 1))) →
    (∀ᵐ ω ∂μ, ∀ n, |S (n + 1) ω - S n ω| ≤ B (n + 1) ω) →
    (∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω) atTop atTop) →
    (∀ᵐ ω ∂μ, Tendsto (fun n => B n ω *
        Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ S S n ω)
          (Real.exp (Real.exp 1))))) / Real.sqrt (CERW.predBracket μ ℱ S S n ω))
      atTop (𝓝 0)) →
    ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, S n ω ≤ (1 + δ) * Real.sqrt (2 * CERW.predBracket μ ℱ S S n ω *
        Real.log (Real.log (CERW.predBracket μ ℱ S S n ω)))

end CERW.Generic.Martingale.Lil
