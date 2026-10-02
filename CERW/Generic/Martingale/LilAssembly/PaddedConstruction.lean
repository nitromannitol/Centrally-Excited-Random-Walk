import CERW.Generic.Martingale.LilAssembly.Core
import CERW.Generic.Martingale.LilLower
import CERW.Generic.Martingale.CLT.Interfaces

/-!
# The padded process of a martingale with a sure bound on its increments

The objects that make a martingale `S` with a predictable bound `B` on its increments into padded
data (`PaddedData`) on the product with a coin space: the ratio `gateRatio` that controls the
gate, the gate `padGate` that is open before the start time and from then on until the ratio
exceeds the level, the conditional variances `clipVar` clipped at zero, the padded process
`padded S (padGate ..) ε`, its bound `padBound` and its bracket `padBracket`.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower
open CERW.Generic.Martingale.CLT (pathBracket)

/-- A martingale `S` with a predictable bound `B` such that the increment of `S` at time `n + 1` is
surely at most `B (n + 1)` or `0`, whose bracket tends to infinity and for which the ratio of the
hypothesis of the law of the iterated logarithm tends to zero, almost surely. -/
structure SureData {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (S B : ℕ → Ω → ℝ) : Prop where
  /-- `S` is a martingale. -/
  mart : Martingale S ℱ μ
  /-- `S` is square integrable. -/
  memLp : ∀ n, MemLp (S n) 2 μ
  /-- `S` starts at zero. -/
  zero : ∀ ω, S 0 ω = 0
  /-- The bound `B (n + 1)` is measurable at time `n`. -/
  bPred : ∀ n, StronglyMeasurable[ℱ n] (B (n + 1))
  /-- The increments are surely bounded by `B` or `0`. -/
  bInc : ∀ n ω, |S (n + 1) ω - S n ω| ≤ max (B (n + 1) ω) 0
  /-- The predictable bracket tends to infinity, almost surely. -/
  vInf : ∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω) atTop atTop
  /-- The ratio of the hypothesis of the law tends to zero, almost surely. -/
  bRatio : ∀ᵐ ω ∂μ, Tendsto (fun n => B n ω *
    Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ S S n ω) (Real.exp (Real.exp 1))))) /
      Real.sqrt (CERW.predBracket μ ℱ S S n ω)) atTop (𝓝 0)

/-- The ratio `B_{i+1} √(log log (P_{i+1} ∨ e^e)) / √P_{i+1}`, with `P` the nondecreasing bracket
`pathBracket`, that controls the gate. -/
noncomputable def gateRatio {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  B (i + 1) ω * Real.sqrt (Real.log (Real.log (max (pathBracket μ ℱ S (i + 1) ω)
    (Real.exp (Real.exp 1))))) / Real.sqrt (pathBracket μ ℱ S (i + 1) ω)

/-- The conditional variance of the increment of `S` at time `j`, clipped at zero. -/
noncomputable def clipVar {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  max ((μ[fun ω => (S (j + 1) ω - S j ω) ^ 2 | ℱ j]) ω) 0

/-- The gate: open before the start time `N` and from then on until the ratio exceeds `εg`. -/
noncomputable def padGate {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ) : ℕ → Ω → ℝ :=
  levelGate (gateRatio μ ℱ S B) εg N

/-- The bound on the increments of the padded process: `B (n + 1) ∨ 0` while the gate is open and
`1` once it has closed. -/
noncomputable def padBound {Ω Ξ : Type*} (G B : ℕ → Ω → ℝ) : ℕ → Ω × Ξ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun z => G n z.1 * max (B (n + 1) z.1) 0 + (1 - G n z.1)

/-- The bracket of the padded process, at the first coordinate. -/
noncomputable def padBracket {Ω Ξ : Type*} (c G : ℕ → Ω → ℝ) (n : ℕ) (z : Ω × Ξ) : ℝ :=
  paddedBracket c G n z.1

/-- The padded process of `S`, with the gate `padGate`, on the product with the coin space. -/
noncomputable abbrev padProc {Ω Ξ : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ) (ε : ℕ → Ξ → ℝ) :
    ℕ → Ω × Ξ → ℝ :=
  padded S (padGate μ ℱ S B εg N) ε

/-- The bracket of the padded process of `S`. -/
noncomputable abbrev padVar {Ω Ξ : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ) : ℕ → Ω × Ξ → ℝ :=
  padBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N)

/-- The bound on the increments of the padded process of `S`. -/
noncomputable abbrev padB {Ω Ξ : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (S B : ℕ → Ω → ℝ) (εg : ℝ) (N : ℕ) : ℕ → Ω × Ξ → ℝ :=
  padBound (padGate μ ℱ S B εg N) B

end CERW.Generic.Martingale.LilAssembly
