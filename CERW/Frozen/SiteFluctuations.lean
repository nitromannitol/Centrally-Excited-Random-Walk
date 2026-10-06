import CERW.Generic.Martingale.CLT.Statement
import CERW.Generic.Martingale.CLT.Proved
import CERW.Generic.Martingale.Lil.LowerStatement
import CERW.Generic.Martingale.LilAssembly.StoutLower
import CERW.Support.Stout
import CERW.Model
import CERW.Support.Inner.InnerRadius
import CERW.Support.Limit.FixedSiteCentering
import CERW.Support.Limit.MomentFluctuations
import CERW.Support.Limit.SiteFluctuations
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
# thm:site-fluctuations

`thm:site-fluctuations` of the revised paper (`limit-shapes.tex:1302-1327`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `thm:site-fluctuations`:

```latex
\begin{theorem}[Local times at fixed sites]\label{thm:site-fluctuations}
Let $\gauge$ be the Euclidean norm, and let $0<\drift<\nf1d$. Then the following hold.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Central limit theorem}}: for every $y\in\Z^d$, as $n\to\infty$,
\begin{equation}\label{eq:site-clt}
\begin{aligned}
\frac{\ell_n(y)-2d\drift(r_n-|y|)}{\sqrt{r_n\log r_n}}&\xrightarrow{\mathrm d}\mathcal N\Bigl(0,\frac{16\drift}{\pi}\Bigr)&&\text{if } d=2\, ,\\
\frac{\ell_n(y)-2d\drift(r_n-|y|)}{\sqrt{r_n}}&\xrightarrow{\mathrm d}\mathcal N\bigl(0,2d\drift(2G(0)-1)\bigr)&&\text{if } d\geq3\, .
\end{aligned}
\end{equation}
\item \underline{\emph{Law of the iterated logarithm}}: for every $y\in\Z^d$ and each choice of sign, almost surely,
\begin{equation*}
\begin{aligned}
\limsup_{n\to\infty}\frac{\pm(\ell_n(y)-2d\drift(r_n-|y|))}{\sqrt{2r_n\log r_n\log\log n}}&=\Bigl(\frac{16\drift}{\pi}\Bigr)^{\nf12}&&\text{if } d=2\, ,\\
\limsup_{n\to\infty}\frac{\pm(\ell_n(y)-2d\drift(r_n-|y|))}{\sqrt{2r_n\log\log n}}&=\bigl(2d\drift(2G(0)-1)\bigr)^{\nf12}&&\text{if } d\geq3\, .
\end{aligned}
\end{equation*}
\item \underline{\emph{Joint limits}}: for all $y_1,\ldots,y_k\in\Z^d$, the convergence in~\eqref{eq:site-clt} holds jointly for $y=y_1,\ldots,y_k$, and the limit is a centered Gaussian vector whose covariance matrix has $(i,j)$ entry
\begin{equation}\label{eq:site-covariance}
\begin{cases}
16\drift/\pi,&d=2,\\
2d\drift\bigl(2G(y_i-y_j)-\ind_{\{y_i=y_j\}}\bigr),&d\geq3
\end{cases}\, .
\end{equation}
\end{enumerate}
\end{theorem}
Definitions the statement relies on (verbatim):
\textit{the radius $r_n$ (eq:radius, lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\frac{1}{d+1}}\, ,
\end{equation}
\textit{$g$ and $G$ (line 415)}
Let $\Delta f(x)\coloneqq(2d)^{-1}\sum_{|e|=1}(f(x+e)-f(x))$, summed over the unit vectors $e\in\Z^d$, be the discrete Laplacian. For $d=2$, let $g$ be the potential kernel of simple random walk, normalized by $g(0)=0$. For $d\geq3$, let $g\coloneqq-G$, where the Green function~$G(x)$ is the expected number of visits to~$x$ by simple random walk from the origin. In both cases $\Delta g=\ind_{\{0\}}$; for $d=2$ see \citet*[Proposition~4.4.2]{LawlerLimic2010}. By \citet[Theorems~4.3.1 and~4.4.4]{LawlerLimic2010}, as $|x|\to\infty$,
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.site_fluctuations {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let G : Site d → ℝ := LatticeProb.srwGreenInf d
    let σ : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (r n * Real.log (r n)) else Real.sqrt (r n)
    let lil : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (2 * r n * Real.log (r n) * Real.log (Real.log n))
      else Real.sqrt (2 * r n * Real.log (Real.log n))
    let v : ℝ := if d = 2 then 16 * ε / Real.pi else 2 * d * ε * (2 * G 0 - 1)
    let cov : Site d → Site d → ℝ := fun y z =>
      if d = 2 then 16 * ε / Real.pi else 2 * d * ε * (2 * G (y - z) - if y = z then 1 else 0)
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      let dev : Site d → ℕ → Ω → ℝ := fun y n ω =>
        (CERW.localTime (X · ω) n y : ℝ) - 2 * d * ε * (r n - euclidNorm y)
      (∀ y : Site d,
        TendstoInDistribution (fun n ω => dev y n ω / σ n) atTop id (fun _ => μ)
          (gaussianReal 0 v.toNNReal)) ∧
      (∀ y : Site d, ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ s : ℝ, s = 1 ∨ s = -1 →
        (∀ᶠ n : ℕ in atTop, s * dev y n ω ≤ (Real.sqrt v + δ) * lil n) ∧
        (∃ᶠ n : ℕ in atTop, (Real.sqrt v - δ) * lil n ≤ s * dev y n ω)) ∧
      (∀ (k : ℕ) (y : Fin k → Site d),
        TendstoInDistribution
          (fun n ω => (WithLp.toLp 2 (fun i => dev (y i) n ω / σ n) : EuclideanSpace ℝ (Fin k)))
          atTop id (fun _ => μ)
          (multivariateGaussian 0 (Matrix.of fun i j => cov (y i) (y j))))
-- FROZEN-STATEMENT-END
:= by
  have hCLT : CERW.Generic.Martingale.CLT.MartingaleCLT.{u} :=
    CERW.Generic.Martingale.CLT.martingaleCLT_proved
  have hLIL : CERW.Support.Statements.StoutLIL.{u} :=
    CERW.Support.stoutLIL_full CERW.Generic.Martingale.LilAssembly.stout_lower
  revert hLIL hCLT hd d
  exact (CERW.Support.Limit.site_fluctuations_of @CERW.Support.Main.limit_shape (CERW.Support.Outer.fluctuation_rates_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.CoarseVolume.norm_coarse_bounds_closed @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) (CERW.Support.Outer.outer_radius_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.CoarseVolume.norm_coarse_bounds_closed @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) CERW.Support.Outer.near_far_holds CERW.Support.Norm.outer_crossing_holds) CERW.Support.Outer.near_far_holds) (CERW.Support.Limit.fixed_site_centering_of (CERW.Support.Outer.fluctuation_rates_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.CoarseVolume.norm_coarse_bounds_closed @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) (CERW.Support.Outer.outer_radius_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.CoarseVolume.norm_coarse_bounds_closed @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) CERW.Support.Outer.near_far_holds CERW.Support.Norm.outer_crossing_holds) CERW.Support.Outer.near_far_holds)) (CERW.Support.Limit.moment_fluctuations_of @CERW.Support.Main.limit_shape (CERW.Support.Outer.fluctuation_rates_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.CoarseVolume.norm_coarse_bounds_closed @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) (CERW.Support.Outer.outer_radius_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.CoarseVolume.norm_coarse_bounds_closed @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) CERW.Support.Outer.near_far_holds CERW.Support.Norm.outer_crossing_holds) CERW.Support.Outer.near_far_holds)))
