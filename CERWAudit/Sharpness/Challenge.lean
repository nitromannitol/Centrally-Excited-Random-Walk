import Mathlib

/-!
# Sharpness: comparator vocabulary

This Mathlib-only surface states the introduction's results using explicit
copies of the lattice, occupation, and transition-law definitions.
-/

universe u

namespace CERW.StatementAudit.Sharpness

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

/-- The `sharp_radii` assertion of the introduction, with all clauses. -/
theorem sharp_radii {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let Ein : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ r n - innerRadius (X · ω) n}
        let Eout : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ maxRadius (X · ω) n - r n}
        MeasurableSet Ein ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Ein ∧
          MeasurableSet Eout ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Eout
:= by
  sorry

/-- The `sharp_radii_lil` assertion of the introduction, with all clauses. -/
theorem sharp_radii_lil {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ →
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ r n - innerRadius (X · ω) n) ∧
        (∃ᶠ n : ℕ in atTop,
          (1 / Real.sqrt (10 * Real.pi * ε) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ maxRadius (X · ω) n - r n)
:= by
  sorry

/-- The `sharp_bulk` assertion of the introduction, with all clauses. -/
theorem sharp_bulk {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∃ x : Site d, euclidNorm x ≤ Real.sqrt (r n) ∧
            c * (if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n))
              ≤ |(localTime (X · ω) n x : ℝ) - 2 * d * ε * (r n - euclidNorm x)|}
          ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))
:= by
  sorry

/-- The `sharp_width` assertion of the introduction, with all clauses. -/
theorem sharp_width {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    (∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let E : Set Ω := {ω | c * Real.sqrt (r n * Real.log n)
          ≤ maxRadius (X · ω) n - innerRadius (X · ω) n}
        MeasurableSet E ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ E) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
        (Real.sqrt (Real.pi / (3 * ε)) - δ) * Real.sqrt (r n * Real.log (Real.log n))
          ≤ maxRadius (X · ω) n - innerRadius (X · ω) n) ∧
    (∀ a : ℝ, 0 ≤ a →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), IsCERW μ ε X →
        limsup (fun n => μ {ω | maxRadius (X · ω) n - innerRadius (X · ω) n
          ≤ a * Real.sqrt (r n)}) atTop ≤
          ENNReal.ofReal (1 - Real.exp (-(3 * ε * a ^ 2 / Real.pi))))
:= by
  sorry


end CERW.StatementAudit.Sharpness
