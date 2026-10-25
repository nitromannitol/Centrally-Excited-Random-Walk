module

public import Mathlib

@[expose] public section

/-!
# NormShape: comparator vocabulary

This Mathlib-only surface states the introduction's results using explicit
copies of the lattice, occupation, and transition-law definitions.
-/

universe u

namespace CERW.StatementAudit.NormShape

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal

-- VOCABULARY-BEGIN
/-! ## The lattice and the Euclidean norm (`LatticeProb/Site.lean`, `LatticeProb/Walk/Ball.lean`) -/

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The Euclidean norm `|x|` of a lattice site. -/
noncomputable def euclidNorm {d : ℕ} (x : Site d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2)

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

/-- The embedding of the lattice in Euclidean space. -/
noncomputable def toSpace (x : Site d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ((x i : ℤ) : ℝ))

/-- The largest Euclidean distance of a position through time `n`. -/
noncomputable def maxRadius (X : ℕ → Site d) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    fun j => euclidNorm (X j)

/-- The half-open unit cell centered at a lattice site. -/
def cell (x : Site d) : Set (EuclideanSpace ℝ (Fin d)) :=
  {v | ∀ i, ((x i : ℤ) : ℝ) - 1 / 2 ≤ v i ∧ v i < ((x i : ℤ) : ℝ) + 1 / 2}

/-- The union of departure cells. -/
def cellSet (X : ℕ → Site d) (n : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ x ∈ departureRange X n, cell x

/-- The inner radius of the departure cells. -/
noncomputable def innerRadius (X : ℕ → Site d) (n : ℕ) : ℝ :=
  sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet X n)ᶜ)

/-- The axioms of a norm on Euclidean space. -/
structure IsNorm (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  /-- Subadditivity. -/
  add_le : ∀ x y, Ψ (x + y) ≤ Ψ x + Ψ y
  /-- Absolute homogeneity. -/
  smul : ∀ (t : ℝ) x, Ψ (t • x) = |t| * Ψ x
  /-- Nondegeneracy. -/
  eq_zero : ∀ x, Ψ x = 0 → x = 0

/-- The subgradient inequality. -/
def IsSubgradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (x ξ : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ y, Ψ x + inner ℝ ξ (y - x) ≤ Ψ y

/-- A Euclidean coordinate vector. -/
noncomputable def coordVec (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single i 1

/-- The Lebesgue volume of the norm's open unit ball. -/
noncomputable def normBallVolume (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  (volume {y | Ψ y < 1}).toReal

/-- The first-departure transition probabilities with drift direction `w`. -/
noncomputable def driftFirstStep (d : ℕ) (ε : ℝ) (w : EuclideanSpace ℝ (Fin d)) (e : Site d) : ℝ :=
  ∑ i : Fin d,
    ((if e = unit i then (1 : ℝ) / (2 * d) - ε / 2 * w i else 0) +
      (if e = -unit i then (1 : ℝ) / (2 * d) + ε / 2 * w i else 0))

/-- The transition kernel with the fixed drift field at each fresh departure. -/
noncomputable def driftStepProb (d : ℕ) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) (n : ℕ) (e : Site d) : ℝ :=
  if x n ≠ 0 ∧ x n ∉ (Finset.range n).image x then driftFirstStep d ε (ξ (x n)) e
  else srwStep d e

/-- The cylinder-factorization law for the norm-directed walk. -/
structure IsDriftCERW {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (X : ℕ → Ω → Site d) : Prop where
  /-- Measurability of positions. -/
  measurable : ∀ n, Measurable (X n)
  /-- The starting point is the origin almost surely. -/
  start : μ {ω | X 0 ω ≠ 0} = 0
  /-- The law of the next step given the whole past. -/
  step : ∀ (n : ℕ) (x : ℕ → Site d),
    μ {ω | ∀ j ≤ n + 1, X j ω = x j} =
      μ {ω | ∀ j ≤ n, X j ω = x j} * ENNReal.ofReal (driftStepProb d ε ξ x n (x (n + 1) - x n))
-- VOCABULARY-END

end CERW.StatementAudit.NormShape
