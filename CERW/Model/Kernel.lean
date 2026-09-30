import CERW.Model.Space

/-!
# The first-departure kernel

The one-step law of centrally excited random walk (`eq:kernel`). On the first departure from
a nonzero site `x` the walk steps to `x ± e_i` with probability
`q_x(±e_i) = 1/(2d) ∓ (ε/2) x_i/|x|`, whose mean is `-ε x/|x|`; every later departure, and
every departure from the origin, is a simple random walk step. `stepProb` reads which case
applies from the past of the path. Nothing here assumes `0 < ε < 1/d`; positivity of the
probabilities is a lemma under that hypothesis, not part of the definitions.
-/

namespace CERW

open LatticeProb

variable {d : ℕ}

/-- The `2d` unit steps `±e_i` of `ℤ^d`. -/
def unitSteps (d : ℕ) : Finset (Site d) :=
  Finset.univ.biUnion fun i : Fin d => {unit i, -unit i}

/-- A step is a unit step exactly when it is `e_i` or `-e_i` for some coordinate `i`. -/
theorem mem_unitSteps {e : Site d} : e ∈ unitSteps d ↔ ∃ i, e = unit i ∨ e = -unit i := by
  simp [unitSteps]

/-- The first-departure probabilities `q_x(±e_i) = 1/(2d) ∓ (ε/2) x_i/|x|` of `eq:kernel`,
and `0` at every `e` that is not a unit step. -/
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
`n`. It is `firstStep` when `x n` is nonzero and is being departed for the first time, that is
`x n ∉ {x 0, …, x (n-1)}`, and `srwStep` otherwise (`eq:kernel` and the sentence after it).
Only `x 0, …, x n` enter. -/
noncomputable def stepProb (d : ℕ) (ε : ℝ) (x : ℕ → Site d) (n : ℕ) (e : Site d) : ℝ :=
  if x n ≠ 0 ∧ x n ∉ (Finset.range n).image x then firstStep d ε (x n) e else srwStep d e

end CERW
