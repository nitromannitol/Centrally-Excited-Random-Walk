import CERW.Model
import CERW.Support.Norm.BallLayer
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.Coarse
import CERW.Support.Norm.ContactPotential
import CERW.Support.Norm.Crossing
import CERW.Support.Norm.Geometry
import CERW.Support.Norm.LocalTime
import CERW.Support.Norm.MoreauCap
import CERW.Support.Norm.OuterCrossing
import CERW.Support.Norm.Radial
import CERW.Support.Norm.ShapeRates

/-!
# thm:norm-shape

`thm:norm-shape` of the revised paper (`limit-shapes.tex:330-343`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `thm:norm-shape`:

```latex
\begin{theorem}[Limit shape for a norm]\label{thm:norm-shape}
Let $d\geq2$, let $\gauge$ be a norm on~$\R^d$, let $\xi(x)\in\partial \gauge(x)$ be chosen at the sites $x\in\Z^d\setminus\{0\}$, let $\drift>0$ satisfy~\eqref{eq:ellipticity}, and let $r_n$ be as in~\eqref{eq:radius-norm}. Then, almost surely, the centrally excited random walk with norm~$\gauge$ has the following properties.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Shape}}: for all $0<\eta<1$ and all sufficiently large~$n$,
\begin{equation*}
\{x\in\Z^d:\gauge(x)<(1-\eta)r_n\}\subset A_n\subset\{x\in\Z^d:\gauge(x)<(1+\eta)r_n\}\, .
\end{equation*}
\item \underline{\emph{Local times}}: as $n\to\infty$,
\begin{equation*}
\frac1{r_n}\max_{x\in\Z^d}\bigl|\ell_n(x)-2d\drift(r_n-\gauge(x))_+\bigr|\longrightarrow0\, .
\end{equation*}
\item \underline{\emph{Recurrence}}: the walk visits every site of~$\Z^d$ infinitely often.
\end{enumerate}
\end{theorem}
Definitions the statement relies on (verbatim):
\textit{eq:kernel and eq:ellipticity (lines 313--321)}
Let $\gauge$ be a norm on~$\R^d$, let $B_\gauge$ be its unit ball, and let $\partial\gauge(x)$ be the set of subgradients of~$\gauge$ at~$x$, as in Section~\ref{sec:norms-intro}. If $\gauge$ is differentiable at~$x$, then $\partial\gauge(x)=\{\nabla\gauge(x)\}$. At each site~$x\neq0$ fix $\xi(x)\in\partial\gauge(x)$, with coordinates~$\xi_i(x)$. The \defn{centrally excited random walk with norm~$\gauge$} moves like simple random walk, except that on its first departure from each site~$x\neq0$ it moves to $x\pm e_i$ with probability
\begin{equation}\label{eq:kernel}
\frac1{2d}\mp\frac\drift2\xi_i(x)
\qquad\text{for } 1\leq i\leq d\, .
\end{equation}
We assume that
\begin{equation}\label{eq:ellipticity}
\drift\max_{1\leq i\leq d}\gauge(e_i)<\frac1d\, .
\end{equation}
\textit{eq:radius-norm (lines 323--326)}
\begin{equation}\label{eq:radius-norm}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift|B_\gauge|}\right)^{\nf{1}{(d+1)}}\, ,
\end{equation}
which is~\eqref{eq:radius} when $\gauge$ is the Euclidean norm. The cone $2d\drift(r_n-\gauge(v))_+$ has integral~$n$ over~$\R^d$.
\textit{subgradient (lines 196--196)}
The potential that identifies the ball in Theorem~\ref{thm:shape} also identifies the limit shape for other drifts. Let $\gauge$ be a norm on~$\R^d$, with unit ball $B_\gauge\coloneqq\{y\in\R^d:\gauge(y)<1\}$ of volume~$|B_\gauge|$. A \defn{subgradient} of~$\gauge$ at~$x$ is a vector~$\xi$ with $\gauge(y)\geq\gauge(x)+\xi\cdot(y-x)$ for all $y\in\R^d$. Where $\gauge$ is differentiable it is the gradient. In particular, for the Euclidean norm it is~$x/|x|$. We suppose that at each site~$x\neq0$ a subgradient~$\xi(x)$ of~$\gauge$ at~$x$ is fixed, and that the walk uses $\xi(x)$ in place of~$x/|x|$ in its transition probabilities at the first departure from~$x$, so that this step has mean~$-\drift\xi(x)$. We assume that $\drift\max_i\gauge(e_i)<\nf1d$, which makes these probabilities positive. Then, almost surely, the conclusions of Theorem~\ref{thm:shape} hold with $\gauge(x)$ in place of~$|x|$ and with $r_n$ defined by~\eqref{eq:radius} with $|B_\gauge|$ in place of~$\omega_d$: the range approximates the ball $\{\gauge<r_n\}$, and the local times approximate the cone $2d\drift(r_n-\gauge(x))_+$ (Theorem~\ref{thm:norm-shape}).
\textit{$\ell_n$ and $A_n$ (lines 91--96)}
For an integer~$n\geq0$ let
\begin{equation*}
\ell_n(x)\coloneqq\sum_{j=0}^{n-1}\ind_{\{X_j=x\}}
\qquad\text{and}\qquad
A_n\coloneqq\{x:\ell_n(x)>0\}\, .
\end{equation*}
\textit{notation $\xi(0)$ (lines 295--295)}
\item Let $u_x\coloneqq x/|x|$ for $x\in\R^d\setminus\{0\}$ and $u_0\coloneqq0$. Let $\xi(0)\coloneqq0$.
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.norm_shape {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hεΨ : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsDriftCERW μ ε ξ X) :
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | Ψ (CERW.toSpace x) < (1 - η) * r n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | Ψ (CERW.toSpace x) < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - Ψ (CERW.toSpace x)) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)
-- FROZEN-STATEMENT-END
:= by
  revert hX X μ Ω hεΨ hε ε hξ0 hξ ξ hΨ Ψ hd d
  exact (CERW.Support.Norm.norm_shape_of (CERW.Support.Norm.norm_shape_rates_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.layer_potential @CERW.Support.Norm.moreau_cap CERW.Support.Norm.outer_crossing_holds @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential))
