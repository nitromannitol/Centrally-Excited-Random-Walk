import CERW.Support.Main.GoodEvent
import CERW.Support.Coarse.Vector
import CERW.Support.Law.Dynkin

/-!
# The event of the fluctuation theorem's proof

`fluctEvent d ε b C₀ C₁ bd r₀ X ω n` is the intersection, at time `n`, of the events used in
Sections 4 and 5. It consists of the path being a nearest-neighbour path from the origin, the
upper bounds of `prop:coarse` (constant `C₀`), and seven further bounds, each with constant `C₁`:
the interval and global bounds of `lem:local`, the pointwise decomposition `eq:pointwise` for the
kernel `b`, the local martingales `eq:localmart`, the quadratic error `eq:quadraticerror`, the
vector bound `eq:vector`, and the radial inequality of `lem:radial` with half-width `bd` from
radius `r₀`.
-/

namespace CERW.Support.Main

open MeasureTheory LatticeProb CERW CERW.Support.Law

/-- The intersection of the good events of Sections 3–5 at time `n`. -/
def fluctEvent (d : ℕ) (ε : ℝ) (b : Site d → ℝ) (C₀ C₁ : ℝ) (bd r₀ : ℕ) {Ω : Type*}
    (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ) : Prop :=
  let Y : ℕ → Site d := fun j => X j ω
  let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
  let L : ℝ := Real.log (n + 2)
  let lam : ℝ := if d = 2 then L ^ 2 else L
  let e : ℝ → ℝ := fun m => if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L
  let F : ℝ → ℝ := tail d (cellSet Y n)
  (X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d) ∧
  ((departureRange Y n).card : ℝ) ≤ C₀ * N ^ d ∧ (maxLocalTime Y n : ℝ) ≤ C₀ * N ∧
  maxRadius Y n ≤ C₀ * N ∧
  (∀ s t : ℕ, s < t → t ≤ n →
    (intervalMax Y s t : ℝ) ≤ C₁ * ε * (freshCount Y s t : ℝ) ^ ((1 : ℝ) / d) + C₁ * lam) ∧
  (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
    |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ C₁ * e (maxLocalTime Y n)) ∧
  (∀ y : Site d, euclidNorm y ≤ 3 * n →
    |(localTime Y n y : ℝ) - potential d ε (cellSet Y n) (toSpace y)
        + dynkin ε (fun z => b (z - y)) X n ω| ≤ C₁ * L) ∧
  (∀ y : Site d, euclidNorm y ≤ 3 * n →
    |dynkin ε (fun z => b (z - y)) X n ω| ≤
      C₁ * (Real.sqrt ((∑ j ∈ Finset.range n,
        (1 + euclidNorm (X j ω - y)) ^ (2 - 2 * (d : ℝ))) * L) + L)) ∧
  |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|
    ≤ C₁ * (N * Real.sqrt (n * L) + N * L) ∧
  (∀ s t : ℕ, s < t → t ≤ n →
    ‖Support.Coarse.compensated ε X t ω - Support.Coarse.compensated ε X s ω‖ ≤
      C₁ * Real.sqrt (((t : ℝ) - s) * L)) ∧
  (∀ r : ℕ, r₀ ≤ r → r ≤ n →
    F ((r : ℝ) + bd) ≤ C₁ * shellMax Y n r * (F ((r : ℝ) - bd) - F ((r : ℝ) + bd)) +
      C₁ * (Real.sqrt ((maxLocalTime Y n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ)) * F ((r : ℝ) - bd) * L)
        + (r : ℝ) ^ (1 - (d : ℝ)) * L))

end CERW.Support.Main
