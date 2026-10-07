import CERW.Model
import CERW.Support.Inner.InnerRadius
import CERW.Support.Lower.ExpDeviation
import CERW.Support.Main.LimitShape
import CERW.Support.Norm.BallLayer
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.CoarseVolume
import CERW.Support.Norm.ContactPotential
import CERW.Support.Norm.Geometry
import CERW.Support.Norm.LocalTime
import CERW.Support.Norm.OuterCrossing
import CERW.Support.Outer.NearFar
import CERW.Support.Outer.OuterRadius

/-!
# thm:fluctuations

`thm:fluctuations` of the revised paper (`limit-shapes.tex:130-152`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `thm:fluctuations`:

```latex
Definitions used (lines 98--101--127):
\begin{verbatim}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\frac{1}{d+1}}\, ,
\end{equation}
so that the cone $2d\drift(r_n-|v|)_+$ has integral~$n$ over~$\R^d$. Informally, after $n$~steps the range contains essentially every site~$x$ with $|x|<r_n$ and essentially no site with $|x|>r_n$, and the local time at each site~$x$ is about $2d\drift(r_n-|x|)_+$. This profile determines~$r_n$: the local times sum to~$n$, and the slope~$2d\drift$ of the cone is the slope of the potential of a ball, computed in~\eqref{eq:ballpotential-euclid} below.
...

Replace each site~$x\in A_n$ by the unit cell~$C_x\coloneqq x+[- \frac12, \frac12)^d$, and let $D_n\coloneqq\bigcup_{x\in A_n}C_x$. The \defn{inner radius} and the \defn{outer radius} are
\begin{equation}\label{eq:radii}
\Rin(n)\coloneqq\inf_{y\notin D_n}|y|
\qquad\text{and}\qquad
\Rout(n)\coloneqq\max_{0\leq j\leq n}|X_j|\, .
\end{equation}
\end{verbatim}
Theorem (lines 130--152):
\begin{verbatim}
\begin{theorem}[Fluctuation bounds]\label{thm:fluctuations}
Let $d\geq2$ and $0<\drift<1/d$. For every $p>0$ there exists $C(d,\drift,p)<\infty$ such that, for every integer~$n\geq2$, the following bounds hold simultaneously with probability at least $1-Cn^{-p}$.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Radii}}:
\begin{equation*}
\begin{aligned}
|\Rin(n)-r_n|&\leq C\sqrt{r_n\log n}&&\text{and}\quad&\Rout(n)-r_n&\leq C\sqrt{r_n}(\log n)^{\nf52}&&\text{if } d=2\, ,\\
|\Rin(n)-r_n|&\leq C\log n&&\text{and}\quad&\Rout(n)-r_n&\leq C(\log n)^{d+1}&&\text{if } d\geq3\, .
\end{aligned}
\end{equation*}
\item \underline{\emph{Volume}}:
\begin{equation*}
\bigl|r_n^{-1}D_n\mathbin{\triangle}B(0,1)\bigr|
\leq C\begin{dcases}\sqrt{\frac{\log n}{r_n}},&d=2,\\\frac{\log n}{r_n},&d\geq3\end{dcases}\, .
\end{equation*}
\item \underline{\emph{Local times}}:
\begin{equation*}
\max_{x\in\Z^d}\bigl|\ell_n(x)-2d\drift(r_n-|x|)_+\bigr|
\leq C\begin{cases}\sqrt{r_n}(\log n)^{\nf32},&d=2,\\\sqrt{r_n\log n},&d\geq3\end{cases}\, .
\end{equation*}
\end{enumerate}
In particular, these bounds hold for all sufficiently large~$n$ almost surely. 
\end{theorem}
\end{verbatim}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.fluctuation_rates {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      (if d = 2 then
          |CERW.innerRadius Y n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
            CERW.maxRadius Y n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        else
          |CERW.innerRadius Y n - r n| ≤ C * Real.log n ∧
            CERW.maxRadius Y n - r n ≤ C * Real.log n ^ ((d : ℝ) + 1)) ∧
      volume (((r n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          ≤ ENNReal.ofReal
            (C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) ∧
      ∀ x : Site d,
        |(CERW.localTime Y n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (r n * Real.log n)
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good C (X · ω) n)
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact (CERW.Support.Outer.fluctuation_rates_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.CoarseVolume.norm_coarse_bounds_closed @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) (CERW.Support.Outer.outer_radius_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.CoarseVolume.norm_coarse_bounds_closed @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) CERW.Support.Outer.near_far_holds CERW.Support.Norm.outer_crossing_holds) CERW.Support.Outer.near_far_holds)
