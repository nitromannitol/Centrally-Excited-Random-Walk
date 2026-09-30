import CERW.Model.Kernel
import CERW.Model.Occupation
import LatticeProb.Walk.SRW
import LatticeProb.Walk.SimpleTransfer

/-!
# The martingales of the limit laws, pathwise

Every quantity here is a function of the path, computed from a step law
`p : (ℕ → ℤ^d) → ℕ → ℤ^d → ℝ` such as `stepProb d ε`; the statements that use them need no
conditional expectation.

* The quadratic martingale `Q_n = 2ε Σ_{x ∈ A_n} |x| - n + |X_n|²` (`eq:moment-martingale`).
* The Dynkin martingale `M^f_t = f(X_t) - f(X_0) - Σ_{j<t} E(f(X_{j+1}) - f(X_j) | ℱ_j)` of
  `sec:dynkin`, with the conditional expectation written as `Σ_e p(e) (f(X_j + e) - f(X_j))`.
* Its bracket `⟨M^f, M^g⟩_t = Σ_{j<t} Cov(f(X_{j+1}) - f(X_j), g(X_{j+1}) - g(X_j) | ℱ_j)`, the
  conditional covariance written from the step law.
* The lattice kernel `g` of `sec:dynkin`: the potential kernel, normalized by `g(0) = 0`, when
  `d = 2`, and `-G` when `d ≥ 3`. The planar kernel is the limit of the partial sums
  `Σ_{j<M} [P^j(0,0) - P^j(0,x)]`, which exists (`LatticeProb.tendsto_potentialKernel`).
-/

namespace CERW

open LatticeProb Filter

variable {d : ℕ}

/-- The quadratic martingale `Q_n = 2ε Σ_{x ∈ A_n} |x| - n + |X_n|²` of the Euclidean walk. -/
noncomputable def quadraticMart (ε : ℝ) (X : ℕ → Site d) (n : ℕ) : ℝ :=
  2 * ε * ∑ x ∈ departureRange X n, euclidNorm x - n + euclidNorm (X n) ^ 2

/-- The conditional mean `Σ_e p(e) (f(X_j + e) - f(X_j))` of the increment of `f(X)` at time `j`
under the step law `p`. -/
noncomputable def stepMean (p : (ℕ → Site d) → ℕ → Site d → ℝ) (f : Site d → ℝ)
    (X : ℕ → Site d) (j : ℕ) : ℝ :=
  ∑ e ∈ unitSteps d, p X j e * (f (X j + e) - f (X j))

/-- The Dynkin martingale `M^f_t = f(X_t) - f(X_0) - Σ_{j<t} E(f(X_{j+1}) - f(X_j) | ℱ_j)`. -/
noncomputable def dynkinMart (p : (ℕ → Site d) → ℕ → Site d → ℝ) (f : Site d → ℝ)
    (X : ℕ → Site d) (t : ℕ) : ℝ :=
  f (X t) - f (X 0) - ∑ j ∈ Finset.range t, stepMean p f X j

/-- The bracket `⟨M^f, M^g⟩_t`: the sum over `j < t` of the conditional covariances of the
increments of `f(X)` and `g(X)` at time `j`. -/
noncomputable def dynkinBracket (p : (ℕ → Site d) → ℕ → Site d → ℝ) (f g : Site d → ℝ)
    (X : ℕ → Site d) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t,
    (∑ e ∈ unitSteps d, p X j e * ((f (X j + e) - f (X j)) * (g (X j + e) - g (X j))) -
      stepMean p f X j * stepMean p g X j)

/-- The lattice kernel `g`: the potential kernel `lim_M Σ_{j<M} [P^j(0,0) - P^j(0,x)]` when
`d = 2`, and `-G(x)` when `d ≥ 3`. -/
noncomputable def latticeKernel (d : ℕ) (x : Site d) : ℝ :=
  if d = 2 then limUnder atTop (fun M : ℕ => srwGreen d M 0 - srwGreen d M x)
  else -srwGreenInf d x

end CERW
