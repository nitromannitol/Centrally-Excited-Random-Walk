import CERW.LimitShapes.LocalTime
import CERW.Support.Norm.ContactEvent

/-!
# The common martingale event

The event at `sec:norm-event` consists of six estimates.
Its local-time constituent is the approximation alone. Both Freedman constituents
use the actual predictable bracket computed from the transition kernel.
-/

open MeasureTheory
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes

open CERW
open CERW.Support.Norm.ContactEvent (scale CoarseBounds quadraticMartingale)

/-- The constants in the six estimates defining the common event. -/
structure EventConstants where
  cCo : ℝ
  CCo : ℝ
  CLoc : ℝ
  CQuad : ℝ
  CSquare : ℝ
  CMart : ℝ
  CCross : ℝ

/-- The stopped quadratic martingale, with stopping at the first exit from the open ball
of radius `R`. The summand is included exactly when the exit has not yet occurred. -/
noncomputable def stoppedQuadratic {d : ℕ} (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (R : ℝ) (X : ℕ → Site d) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n,
    if ∀ k ≤ j, euclidNorm (X k) < R then
      2 * inner ℝ (toSpace (X j))
        (toSpace (X (j + 1)) - toSpace (X j) +
          ε • (if X j ∉ departureRange X j then ξ (X j) else 0))
    else 0

/-- The planar centering of the kernel in the squared test function. -/
noncomputable def kernelShift (d : ℕ) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (ε : ℝ) (n : ℕ) : ℝ :=
  if d = 2 then (2 / Real.pi) * Real.log (scale d Ψ ε n) else 0

/-- The test function `(g(· - y) - γ)²` used for the energy estimate. -/
noncomputable def squareKernel {d : ℕ} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (ε : ℝ) (n : ℕ) (y z : Site d) : ℝ :=
  (latticeKernel d (z - y) - kernelShift d Ψ ε n) ^ 2

/-- The local martingale estimate with the predictable quadratic variation of `g(· - y)`. -/
def LocalMartingaleBound {d : ℕ} (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (C : ℝ) (X : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ y : Site d, euclidNorm y ≤ 3 * n →
    let g : Site d → ℝ := fun z => latticeKernel d (z - y)
    |dynkinMart (driftStepProb d ε ξ) g X n| ≤
      C * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ) g g X n * Real.log n) +
        Real.log n)

/-- Freedman's estimate for the shifted-square test functions, simultaneously for all targets
within distance `3n` of the origin. -/
def SquareMartingaleBound {d : ℕ} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (C : ℝ) (X : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ y : Site d, euclidNorm y ≤ 3 * n →
    let f : Site d → ℝ := squareKernel Ψ ε n y
    |dynkinMart (driftStepProb d ε ξ) f X n| ≤
      C * (Real.sqrt (dynkinBracket (driftStepProb d ε ξ) f f X n * Real.log n) +
        (if d = 2 then Real.log n else 1) * Real.log n)

/-- The largest local time outside the open norm ball of radius `a`.
Sites outside the departure range have local time zero. -/
noncomputable def exteriorLocalTime {d : ℕ} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (X : ℕ → Site d) (t : ℕ) (a : ℝ) : ℕ :=
  ((departureRange X t).filter (fun z => a ≤ Ψ (toSpace z))).sup (localTime X t)

/-- The distance crossing estimate, at all times through `N` and every real norm level. -/
def DistanceCrossingBound {d : ℕ} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (C : ℝ)
    (X : ℕ → Site d) (N : ℕ) : Prop :=
  ∀ t : ℕ, t ≤ N → ∀ a : ℝ, 0 ≤ a → ∀ j : ℕ, j ≤ t →
    Metric.infDist (toSpace (X j)) {v | Ψ v ≤ a} ≤
      C * (1 + (exteriorLocalTime Ψ X t a : ℝ)) * Real.log N

/-- The six estimates whose intersection defines the event in `sec:norm-event`.
The stopping radius is `(C_co + 1) r_n`, as permitted by the coarse outer bound. -/
def EventEstimates {d : ℕ} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants)
    (X : ℕ → Site d) (n : ℕ) : Prop :=
  CoarseBounds d Ψ ε K.cCo K.CCo X n ∧
    LocalApproximation Ψ ε K.CLoc X n ∧
    |stoppedQuadratic ε ξ ((K.CCo + 1) * scale d Ψ ε n) X n| ≤
      K.CQuad * scale d Ψ ε n * Real.sqrt (n * Real.log n) ∧
    SquareMartingaleBound Ψ ε ξ K.CSquare X n ∧
    LocalMartingaleBound ε ξ K.CMart X n ∧
    DistanceCrossingBound Ψ K.CCross X n

/-- The literal event of `sec:norm-event`. Path legality belongs to the model assumptions. -/
def section5Event {d : ℕ} {Ω : Type*} (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants)
    (X : ℕ → Ω → Site d) (n : ℕ) : Set Ω :=
  {ω | EventEstimates Ψ ε ξ K (X · ω) n}

end CERW.LimitShapes
