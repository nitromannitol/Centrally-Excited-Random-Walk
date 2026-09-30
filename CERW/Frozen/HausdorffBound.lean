import CERW.External.LatticePotentialKernel
import Mathlib.Topology.MetricSpace.HausdorffDistance
import CERW.Support.LocalTime.KernelExternal
import CERW.Support.Main.KernelAnchors

/-!
# The Hausdorff bound

`eq:hausdorff` and the planar remark of the paper (`paper/cerw-flat.tex:215-225`). The bytes
between the markers are the frozen contract recorded in `ledger/manifest.yaml`.

The planar remark is stated in its two-sided reading: the inner radius is at least
`aN - C n^{1/6} √L`, and some unvisited site lies within `aN + C n^{1/6} √L`.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

/-- `eq:hausdorff` and the planar remark (`cerw-flat.tex:215-225`):

```latex
On the event in Theorem~\ref{thm:fluctuations}, the Euclidean Hausdorff
distance satisfies
\begin{equation}\label{eq:hausdorff}
d_H(N^{-1}V_n,\overline B(0,a))\leq C
\begin{cases}
n^{-1/12}L^{5/4},&d=2,\\
n^{-1/((d+1)(2d-1))}L^{2d/(2d-1)},&d\geq3
\end{cases}\, .
\end{equation}
The inner-radius error in the plane is at most
$Cn^{1/6}\sqrt{\log(n+2)}$ in lattice units.
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.hausdorff_bound {d : ℕ} (hd : 2 ≤ d)
    (hK : CERW.External.LatticePotentialKernel d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        let L : ℝ := Real.log (n + 2)
        μ {ω | ¬ (Metric.hausdorffEDist
                    ((fun x => N⁻¹ • CERW.toSpace x) '' ↑(CERW.visitedRange (X · ω) n))
                    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) a)
                  ≤ ENNReal.ofReal (C * (if d = 2 then (n : ℝ) ^ (-(1 : ℝ) / 12) * L ^ ((5 : ℝ) / 4)
                      else (n : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
                        * L ^ ((2 * d : ℝ) / (2 * d - 1)))) ∧
                  (d = 2 → {x : Site d | euclidNorm x < a * N - C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
                    ∃ x : Site d, euclidNorm x < a * N + C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L ∧ x ∉ CERW.departureRange (X · ω) n))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨b, h, hF⟩ := CERW.Support.LocalTime.exists_kernelFacts hd hK
  exact CERW.Support.Main.hausdorff_bound_of_kernelFacts hd hF
