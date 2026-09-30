import CERW.Model.Occupation
import CERW.Model.Potential

/-!
# The radii of the range

The inner radius `R_in(n) = inf_{y ∉ D_n} |y|` and the outer radius `R_out(n) = max_{j ≤ n} |X_j|`
of `eq:radii`; the outer radius is `maxRadius`. For a norm `Ψ`, `inf_{y ∉ D_n} Ψ(y)` and
`max_{j ≤ n} Ψ(X_j)` (`prop:norm-shape`). The radius
`R_mom(n) = ((d+1)/(dω_d) Σ_{x ∈ A_n} |x|)^{1/(d+1)}` of `eq:radial-moment-def`.

`D_n` is bounded, so its complement is nonempty and the infima are infima of nonempty sets of
nonnegative numbers.
-/

namespace CERW

open LatticeProb

variable {d : ℕ}

/-- The inner radius `R_in(n) = inf_{y ∉ D_n} |y|`. -/
noncomputable def innerRadius (X : ℕ → Site d) (n : ℕ) : ℝ :=
  sInf ((fun y : EuclideanSpace ℝ (Fin d) => ‖y‖) '' (cellSet X n)ᶜ)

/-- The inner radius for a norm, `inf_{y ∉ D_n} Ψ(y)`. -/
noncomputable def normInnerRadius (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (X : ℕ → Site d) (n : ℕ) :
    ℝ :=
  sInf (Ψ '' (cellSet X n)ᶜ)

/-- The outer radius for a norm, `max_{0 ≤ j ≤ n} Ψ(X_j)`. -/
noncomputable def normMaxRadius (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (X : ℕ → Site d) (n : ℕ) :
    ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    fun j => Ψ (toSpace (X j))

/-- The radius `R_mom(n) = ((d+1)/(dω_d) Σ_{x ∈ A_n} |x|)^{1/(d+1)}` of the centred ball on which
the integral of `|v|` equals `Σ_{x ∈ A_n} |x|`. -/
noncomputable def momentRadius (X : ℕ → Site d) (n : ℕ) : ℝ :=
  ((d + 1) / (d * unitBallVolume d) * ∑ x ∈ departureRange X n, euclidNorm x) ^
    ((1 : ℝ) / (d + 1))

end CERW
