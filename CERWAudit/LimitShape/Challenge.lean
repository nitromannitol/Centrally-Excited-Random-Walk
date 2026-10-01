import Mathlib

/-!
# Ball shape — comparator challenge

Mathlib-only comparator challenge for the limit shape theorem `thm:shape`
(`paper/limit-shapes.tex:103-116`), the headline theorem of *Limit shapes of centrally excited
random walks* (Ahmed Bou-Rabee and Yuval Peres).  The library's frozen statement is
`CERW.Frozen.limit_shape` in `CERW/Frozen/LimitShape.lean`.

This file imports only `Mathlib` — no repository module — and rebuilds from Mathlib
primitives every definition needed to read the theorem: the lattice `Site d = Fin d → ℤ`,
the Euclidean norm `euclidNorm`, the one-step kernel (`unit`, `unitSteps`, `firstStep`,
`srwStep`, `stepProb`), the CERW law `IsCERW`, the departure local time `localTime`, the
departure range `A_n = departureRange`, and the visited range `V_n = visitedRange`.  The
definitions are statement-level copies of the repository's, token for token.  The sole
intentional `sorry` is the proof of the final theorem.

The vocabulary between `VOCABULARY-BEGIN` and `VOCABULARY-END` is copied verbatim into
`SolutionBasic.lean`; the two must stay byte-identical so that the comparator's
constant-by-constant closure check passes.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise

namespace CERW
namespace StatementAudit
namespace LimitShape

-- VOCABULARY-BEGIN
/-! ## The lattice and the Euclidean norm (`LatticeProb/Site.lean`, `LatticeProb/Walk/Ball.lean`) -/

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The Euclidean norm `|x|` of a lattice site. -/
noncomputable def euclidNorm {d : ℕ} (x : Site d) : ℝ := Real.sqrt (∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2)

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

/-! ## The one-step kernel (`CERW/Model/Kernel.lean`) -/

/-- The `2d` unit steps `±e_i` of `ℤ^d`. -/
def unitSteps (d : ℕ) : Finset (Site d) :=
  Finset.univ.biUnion fun i : Fin d => {unit i, -unit i}

/-- The first-departure probabilities `q_x(±e_i) = 1/(2d) ∓ (ε/2) x_i/|x|`, and `0` at
every `e` that is not a unit step. -/
noncomputable def firstStep (d : ℕ) (ε : ℝ) (x e : Site d) : ℝ :=
  ∑ i : Fin d,
    ((if e = unit i then (1 : ℝ) / (2 * d) - ε / 2 * (((x i : ℤ) : ℝ) / euclidNorm x) else 0) +
      (if e = -unit i then (1 : ℝ) / (2 * d) + ε / 2 * (((x i : ℤ) : ℝ) / euclidNorm x) else 0))

/-- The simple random walk step probabilities: `1/(2d)` at each unit step, `0` elsewhere. -/
noncomputable def srwStep (d : ℕ) (e : Site d) : ℝ :=
  ∑ i : Fin d,
    ((if e = unit i then (1 : ℝ) / (2 * d) else 0) +
      (if e = -unit i then (1 : ℝ) / (2 * d) else 0))

/-- The probability that the walk whose path so far is `x 0, …, x n` steps by `e` at time
`n`: `firstStep` on a first departure from a nonzero site, `srwStep` otherwise. -/
noncomputable def stepProb (d : ℕ) (ε : ℝ) (x : ℕ → Site d) (n : ℕ) (e : Site d) : ℝ :=
  if x n ≠ 0 ∧ x n ∉ (Finset.range n).image x then firstStep d ε (x n) e else srwStep d e

/-! ## The CERW law (`CERW/Model/Law.lean`) -/

/-- The process `X` under `μ` is centrally excited random walk on `ℤ^d` with parameter `ε`,
started at the origin. -/
structure IsCERW {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ε : ℝ)
    (X : ℕ → Ω → Site d) : Prop where
  /-- Each position is a random variable. -/
  measurable : ∀ n, Measurable (X n)
  /-- The walk starts at the origin. -/
  start : μ {ω | X 0 ω ≠ 0} = 0
  /-- The law of the next step given the whole past is `stepProb`. -/
  step : ∀ (n : ℕ) (x : ℕ → Site d),
    μ {ω | ∀ j ≤ n + 1, X j ω = x j} =
      μ {ω | ∀ j ≤ n, X j ω = x j} * ENNReal.ofReal (stepProb d ε x n (x (n + 1) - x n))

/-! ## Local times and ranges (`CERW/Model/Occupation.lean`) -/

variable {d : ℕ}

/-- The departure local time `ℓ_n(x) = #{j < n : X_j = x}`. -/
def localTime (X : ℕ → Site d) (n : ℕ) (x : Site d) : ℕ :=
  ((Finset.range n).filter fun j => X j = x).card

/-- The departure range `A_n`, the sites visited at times `0, …, n-1`. -/
def departureRange (X : ℕ → Site d) (n : ℕ) : Finset (Site d) :=
  (Finset.range n).image X

/-- The range `V_n = {X_0, …, X_n}`. -/
def visitedRange (X : ℕ → Site d) (n : ℕ) : Finset (Site d) :=
  (Finset.range (n + 1)).image X
-- VOCABULARY-END

/-! ## The theorem -/

/-- **Limit shape** (`thm:shape`, `limit-shapes.tex:103-116`): for `d ≥ 2` and `0 < ε < 1/d`,
almost surely, with `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}`: for every `0 < η < 1` and all
sufficiently large `n` the departure range contains the Euclidean ball of radius
`(1 - η) r_n` and is contained in the ball of radius `(1 + η) r_n`; the departure local times
converge to the cone `2 d ε (r_n - |x|)_+` at rate `η r_n`; and every site is visited
infinitely often. -/
theorem limit_shape {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | euclidNorm x < (1 - η) * r n} ⊆ ↑(departureRange (X · ω) n) ∧
        (↑(departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | euclidNorm x < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)
    := by
  sorry

end LimitShape
end StatementAudit
end CERW
