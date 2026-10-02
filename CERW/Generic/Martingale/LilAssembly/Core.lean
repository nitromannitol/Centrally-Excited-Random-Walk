import CERW.External.StoutLIL
import CERW.Generic.Martingale.LilLower
import CERW.Generic.Martingale.Tilt.LimitStatements
import CERW.Generic.Martingale.LilAssembly.Statements

/-!
# The assembly of the lower half of Stout's law: the interface

The lower half of the law is reduced, in steps, to a statement about a martingale `M` that comes
with everything the blocks need, `PaddedData`:

* `BlockLower`: for the blocks between the passage times of the bracket `V` over the levels
  `θ^k`, the event that the increment of `M` over block `k` is at least `a_k` has conditional
  probability at least `q_k`, with `∑ q_k = ∞`, given every event before block `k` on which the
  start time `N` has passed.
* Lévy's Borel–Cantelli lemma along the passage times then gives that those events occur
  infinitely often almost surely, and the passage times are finite, tend to infinity, and have a
  bracket between `e^e` and `θ^k` eventually. These are theorems of their own, not stated here.
* `NiceLower`: with the upper half for `-M`, these give `M_n ≥ (1 - δ) ψ(V_n)` infinitely often,
  for padded data with a small gate level.
* `Reduction`: the law of the iterated logarithm follows, by clamping, padding, gating and
  transferring back from the product.

Each is a proposition, so that each piece can be proved on its own against the others.
-/

universe u v

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower

/-- A martingale `M` with a predictable bound `B` on its increments and a predictable
nondecreasing bracket `V`, prepared for the blocks: after the start time `N`, wherever the bracket
is at least one, the increments are bounded by the gate level `εg` times the scale of the bracket,
and the bracket jumps by at most the square of that. -/
structure PaddedData {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (M B V : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ) : Prop where
  /-- `M` is a martingale. -/
  mart : Martingale M ℱ μ
  /-- `M` is square integrable. -/
  memLp : ∀ n, MemLp (M n) 2 μ
  /-- `M` starts at zero. -/
  zero : ∀ ω, M 0 ω = 0
  /-- The bound `B (n + 1)` is measurable at time `n`. -/
  bPred : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1))
  /-- The increments are bounded by `B`, almost surely. -/
  bInc : ∀ᵐ ω ∂μ, ∀ n, |M (n + 1) ω - M n ω| ≤ B (n + 1) ω
  /-- The ratio of the hypothesis of the law of the iterated logarithm tends to zero. -/
  bRatio : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω *
    Real.sqrt (Real.log (Real.log (max (V n ω) (Real.exp (Real.exp 1))))) /
      Real.sqrt (V n ω)) atTop (𝓝 0)
  /-- The bracket `V (n + 1)` is measurable at time `n`. -/
  vPred : ∀ n, StronglyMeasurable[ℱ n] (V (n + 1))
  /-- The bracket starts at zero. -/
  vZero : ∀ ω, V 0 ω = 0
  /-- The bracket is nondecreasing at every point. -/
  vMono : ∀ n ω, V n ω ≤ V (n + 1) ω
  /-- The bracket is the predictable bracket of `M`, almost surely. -/
  vBracket : ∀ᵐ ω ∂μ, ∀ n, V n ω = CERW.predBracket μ ℱ M M n ω
  /-- The bracket tends to infinity, almost surely. -/
  vInf : ∀ᵐ ω ∂μ, Tendsto (fun n => V n ω) atTop atTop
  /-- After the start time, where the bracket at the next time is at least one, the increment is
  bounded by `εg` times the scale of the bracket, at every point. -/
  blockInc : ∀ (t : ℕ) (ω : Ω), N ≤ t → 1 ≤ V (t + 1) ω →
    |M (t + 1) ω - M t ω| ≤ max 1 (εg * Real.sqrt (V (t + 1) ω /
      Real.log (Real.log (max (V (t + 1) ω) (Real.exp (Real.exp 1))))))
  /-- After the start time the bracket jumps by at most the square of that, almost surely. -/
  jump : ∀ᵐ ω ∂μ, ∀ t, N ≤ t → V (t + 1) ω - V t ω ≤
    max 1 (εg ^ 2 * V (t + 1) ω /
      Real.log (Real.log (max (V (t + 1) ω) (Real.exp (Real.exp 1)))))

/-- The event that the increment of `M` over block `k`, between the passage times of `V` over
`θ^(k-1)` and `θ^k`, is at least `a_(k-1) = (1 - δ/2) √(1 - 1/θ) ψ(θ^k)`. It is empty for
`k = 0`. -/
noncomputable def blockEvent {Ω : Type*} (M V : ℕ → Ω → ℝ) (θ δ : ℝ) (k : ℕ) : Set Ω :=
  if k = 0 then ∅ else
    {ω | (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale (θ ^ k) ≤
      stoppedValue M (firstPassage V (θ ^ k)) ω -
        stoppedValue M (firstPassage V (θ ^ (k - 1))) ω}

/-- **The conditional lower bound for the blocks.** For every `δ` there are `θ`, `δ'` and a gate
level `εs` such that, for padded data with a gate level `εg ≤ εs`, the passage times of `V` over
`θ^k` are stopping times, the block events are measurable at their passage times, and there are
weights `0 ≤ q k ≤ 1` with divergent sum such that, from some `k₀` on, `q k` times the
probability of any event `F` before block `k` on which `N` has passed is at most the probability
that `F` is followed by the block event `k + 1`. -/
def BlockLower : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ θ δ' εs : ℝ, 1 < θ ∧ 0 < δ' ∧ 0 < εs ∧
    1 - δ ≤ (1 - δ / 2) * Real.sqrt (1 - 1 / θ) - (1 + δ') / Real.sqrt θ ∧
    ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M B V : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ),
      0 < εg → εg ≤ εs → PaddedData μ ℱ M B V εg N →
      ∃ (hτ : ∀ k, IsStoppingTime ℱ (firstPassage V (θ ^ k))) (k₀ : ℕ) (q : ℕ → ℝ),
        (∀ k, 0 ≤ q k) ∧ (∀ k, q k ≤ 1) ∧
        Tendsto (fun n => ∑ k ∈ Finset.range n, q k) atTop atTop ∧
        (∀ k, MeasurableSet[(hτ k).measurableSpace] (blockEvent M V θ δ k)) ∧
        ∀ k, k₀ ≤ k → ∀ F : Set Ω, MeasurableSet[(hτ k).measurableSpace] F →
          F ⊆ {ω | (N : WithTop ℕ) ≤ firstPassage V (θ ^ k) ω} →
          q k * (μ F).toReal ≤ (μ (F ∩ blockEvent M V θ δ (k + 1))).toReal

/-- **The lower bound for padded data.** For every `δ` there is a gate level `εs` such that, for
padded data with a gate level `εg ≤ εs`, almost surely `M_n ≥ (1 - δ) ψ(V_n)` infinitely often. -/
def NiceLower : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ εs : ℝ, 0 < εs ∧
    ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
      (ℱ : Filtration ℕ m0) (M B V : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ),
      0 < εg → εg ≤ εs → PaddedData μ ℱ M B V εg N →
      ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, (1 - δ) * lilScale (V n ω) ≤ M n ω

/-- **The reduction.** The lower bound for padded data gives the lower half of the law of the
iterated logarithm, the cited result. -/
def Reduction : Prop := NiceLower.{u} → CERW.External.StoutLIL.{u}

end CERW.Generic.Martingale.LilAssembly
