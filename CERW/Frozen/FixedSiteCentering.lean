import CERW.Model
import CERW.Support.Inner.InnerRadius
import CERW.Support.Limit.FixedSiteCentering
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
# lem:fixed-site-centering

`lem:fixed-site-centering` of the revised paper (`limit-shapes.tex:1430-1436`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:fixed-site-centering`:

```latex
\begin{lemma}\label{lem:fixed-site-centering}
Let $\gauge$ be the Euclidean norm, let $0<\drift<\nf1d$, and let $y\in\Z^d$. There exists $C(d,\drift,y)<\infty$ such that, almost surely, for all sufficiently large~$n$,
\begin{equation}\label{eq:fixed-site-centering}
\left|U_{D_n}(y)-2d\drift(r_n-|y|)-\frac{\mathcal Q_n}{\omega_dr_n^d}\right|\leq C\begin{cases}(\log n)^3,&d=2,\\1,&d\geq3\end{cases}\, ,
\end{equation}
where $\mathcal Q$ is the martingale of~\eqref{eq:quadratic}.
\end{lemma}
Definitions the statement relies on (verbatim):
\textit{the radius $r_n$ (eq:radius, lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\nf{1}{d+1}}\, ,
\end{equation}
\textit{the potential (eq:potential-intro, lines 217--219)}
\begin{equation}\label{eq:potential-intro}
U_D(y)\coloneqq\frac{2\drift}{\omega_d}\int_D\frac{v}{|v|}\cdot\frac{v-y}{|v-y|^d}\dd v
\end{equation}
\textit{$\mathcal Q_n$ (eq:moment-martingale, lines 1346--1349)}
For the Euclidean norm, \eqref{eq:quadratic} reads
\begin{equation}\label{eq:moment-martingale}
\mathcal Q_n=2\drift\sum_{x\in A_n}|x|-n+|X_n|^2\, .
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.fixed_site_centering {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ y : Site d, ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          |CERW.potential d ε (CERW.cellSet (X · ω) n) (CERW.toSpace y)
              - 2 * d * ε * (r n - euclidNorm y)
              - CERW.quadraticMart ε (X · ω) n / (ωd * r n ^ d)|
            ≤ C * if d = 2 then Real.log n ^ 3 else 1
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact (CERW.Support.Limit.fixed_site_centering_of (CERW.Support.Outer.fluctuation_rates_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) (CERW.Support.Outer.outer_radius_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) CERW.Support.Outer.near_far_holds CERW.Support.Norm.outer_crossing_holds) CERW.Support.Outer.near_far_holds))
