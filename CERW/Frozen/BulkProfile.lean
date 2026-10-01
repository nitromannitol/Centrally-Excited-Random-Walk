import CERW.Model
import CERW.Support.Inner.InnerRadius
import CERW.Support.Lower.BulkProfile
import CERW.Support.Lower.ExpDeviation
import CERW.Support.Main.LimitShape
import CERW.Support.Norm.BallLayer
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.Coarse
import CERW.Support.Norm.ContactPotential
import CERW.Support.Norm.Crossing
import CERW.Support.Norm.Geometry
import CERW.Support.Norm.LocalTime
import CERW.Support.Norm.OuterCrossing
import CERW.Support.Norm.Radial
import CERW.Support.Outer.NearFar
import CERW.Support.Outer.OuterRadius

/-!
# prop:bulk-profile

`prop:bulk-profile` of the revised paper (`limit-shapes.tex:1655-1662`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `prop:bulk-profile`:

```latex
\begin{proposition}\label{prop:bulk-profile}
Let $\gauge$ be the Euclidean norm, let $0<\drift<\nf1d$, and let $0<\theta<1$ and $p>0$. There exists $C(d,\drift,\theta,p)<\infty$ such that, for every integer~$n\geq2$, with probability at least $1-Cn^{-p}$,
\begin{equation}\label{eq:bulk-profile}
\max_{\substack{y\in\Z^d\\|y|\leq\theta r_n}}\bigl|\ell_n(y)-2d\drift(r_n-|y|)\bigr|
\leq C\begin{cases}\sqrt{r_n}\log n,&d=2,\\\sqrt{r_n\log n},&d\geq3\end{cases}\, .
\end{equation}
The same bound holds for all sufficiently large~$n$ almost surely.
\end{proposition}
Definitions the statement relies on (verbatim):
\textit{the radius $r_n$ (eq:radius, lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\nf{1}{(d+1)}}\, ,
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.bulk_profile {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      let Good : (ℕ → Site d) → ℕ → Prop := fun Y n =>
        ∀ y : Site d, euclidNorm y ≤ θ * r n →
          |(CERW.localTime Y n y : ℝ) - 2 * d * ε * (r n - euclidNorm y)|
            ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n)
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good (X · ω) n)
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact (CERW.Support.Lower.bulk_profile_of (CERW.Support.Outer.fluctuation_rates_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) (CERW.Support.Outer.outer_radius_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) CERW.Support.Outer.near_far_holds CERW.Support.Norm.outer_crossing_holds) CERW.Support.Outer.near_far_holds))
