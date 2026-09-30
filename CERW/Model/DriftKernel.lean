import CERW.Model.Kernel

/-!
# The first-departure kernel of a walk with a drift field

The one-step law of the centrally excited random walk with norm `Ψ` (`eq:kernel` of the revised
paper). A drift field `ξ : ℤ^d → ℝ^d` is fixed; for a norm, `ξ(x)` is a chosen subgradient of `Ψ`
at `x`. On the first departure from a nonzero site `x` the walk steps to `x ± e_i` with
probability `1/(2d) ∓ (ε/2) ξ_i(x)`, whose mean is `-ε ξ(x)`; every later departure, and every
departure from the origin, is a simple random walk step. The Euclidean walk of `Kernel.lean` is
the drift field `ξ(x) = x/|x|`. Nothing here assumes that the probabilities are nonnegative;
that is a lemma under the ellipticity condition.
-/

namespace CERW

open LatticeProb

variable {d : ℕ}

/-- The first-departure probabilities `1/(2d) ∓ (ε/2) w_i` at `±e_i` for a drift direction `w`,
and `0` at every `e` that is not a unit step. -/
noncomputable def driftFirstStep (d : ℕ) (ε : ℝ) (w : EuclideanSpace ℝ (Fin d)) (e : Site d) :
    ℝ :=
  ∑ i : Fin d,
    ((if e = unit i then (1 : ℝ) / (2 * d) - ε / 2 * w i else 0) +
      (if e = -unit i then (1 : ℝ) / (2 * d) + ε / 2 * w i else 0))

/-- The probability that the walk with drift field `ξ`, whose path so far is `x 0, …, x n`, steps
by `e` at time `n`: `driftFirstStep` with direction `ξ (x n)` when `x n` is nonzero and is being
departed for the first time, and `srwStep` otherwise. -/
noncomputable def driftStepProb (d : ℕ) (ε : ℝ) (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (x : ℕ → Site d) (n : ℕ) (e : Site d) : ℝ :=
  if x n ≠ 0 ∧ x n ∉ (Finset.range n).image x then driftFirstStep d ε (ξ (x n)) e
  else srwStep d e

end CERW
