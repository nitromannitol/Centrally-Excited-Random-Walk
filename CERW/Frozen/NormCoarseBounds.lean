import CERW.Model
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.CoarseVolume
import CERW.Support.Norm.LocalTime

/-!
# prop:coarse

`prop:coarse` of the revised paper (`limit-shapes.tex:538-545`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `prop:coarse`:

```latex
\begin{proposition}\label{prop:coarse}
Let $p>0$. There exist $c(d,\drift,\gauge,p)>0$ and $C(d,\drift,\gauge,p)<\infty$ such that, for every integer~$n\geq2$, with probability at least $1-Cn^{-p}$,
\begin{equation*}
cr_n^d\leq|A_n|\leq Cr_n^d,\qquad
cr_n\leq\max_{x\in\Z^d}\ell_n(x)\leq Cr_n,\qquad
cr_n\leq\Rout(n)\leq Cr_n\, .
\end{equation*}
\end{proposition}
Definitions the statement relies on (verbatim): $\ell_n,A_n$ (lines 92--96), the radii (lines 123--127),
the norm setting (lines 322--333) and the conventions $\xi(0)=0$ and on constants (lines 303--304).
\begin{equation*}
\ell_n(x)\coloneqq\sum_{j=0}^{n-1}\ind_{\{X_j=x\}}
\qquad\text{and}\qquad
A_n\coloneqq\{x:\ell_n(x)>0\}\, .
\end{equation*}
\begin{equation}\label{eq:radii}
\Rin(n)\coloneqq\inf_{y\notin D_n}|y|
\qquad\text{and}\qquad
\Rout(n)\coloneqq\max_{0\leq j\leq n}|X_j|\, .
\end{equation}
\begin{equation}\label{eq:kernel}
\frac1{2d}\mp\frac\drift2\xi_i(x)
\qquad\text{for } 1\leq i\leq d\, .
\end{equation}
We assume that
\begin{equation}\label{eq:ellipticity}
\drift\max_{1\leq i\leq d}\gauge(e_i)<\frac1d\, .
\end{equation}
Every $\xi\in\partial\gauge(x)$ satisfies $\xi\cdot y\leq\gauge(y)$ for every~$y$, with equality at $y=x$ (Euler's relation); so $|\xi_i(x)|\leq\gauge(e_i)$, and~\eqref{eq:ellipticity} makes the probabilities~\eqref{eq:kernel} positive. The step at the first departure from~$x$ has conditional mean~$-\drift\xi(x)$, whose inner product with~$x$ is $-\drift\gauge(x)<0$. The Euclidean norm, with $\xi(x)=x/|x|$, gives the walk of Section~\ref{sec:introduction}, and then~\eqref{eq:ellipticity} reads $\drift<\nf1d$. Let
\begin{equation}\label{eq:radius-norm}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift|B_\gauge|}\right)^{\nf{1}{(d+1)}}\, ,
\end{equation}
\begin{itemize}
\item Let $u_x\coloneqq x/|x|$ for $x\in\R^d\setminus\{0\}$ and $u_0\coloneqq0$, and let $\xi(0)\coloneqq0$.
\item The letters $c>0$ and $C>0$ denote constants depending only on $d$, $\drift$ and the exponent~$p$ of the failure probability under discussion, and in Sections~\ref{sec:norm-setup}--\ref{sec:norms} also on the norm~$\gauge$, but not on the choice of the subgradients~$\xi(x)$; they may change from line to line. Every further dependence is stated, and a subscript on~$O$, as in~$O_y$, means that the implied constant also depends on~$y$. We write $a_n\asymp b_n$ if $c\leq a_n/b_n\leq C$, and $O_{\P}(a_n)$ for random variables~$Y_n$ such that $Y_n/a_n$ is tight.
\end{itemize}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.norm_coarse_bounds {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (c * r n ^ d ≤ ((CERW.departureRange (X · ω) n).card : ℝ) ∧
                  ((CERW.departureRange (X · ω) n).card : ℝ) ≤ C * r n ^ d ∧
                  c * r n ≤ (CERW.maxLocalTime (X · ω) n : ℝ) ∧
                  (CERW.maxLocalTime (X · ω) n : ℝ) ≤ C * r n ∧
                  c * r n ≤ CERW.maxRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ C * r n)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact CERW.Support.Norm.CoarseVolume.norm_coarse_bounds_closed
