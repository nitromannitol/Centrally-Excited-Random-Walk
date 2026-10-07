import CERW.Model
import CERW.Support.Norm.CellGradient

/-!
# lem:cell

`lem:cell` of the revised paper (`limit-shapes.tex:466-471`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:cell`:

```latex
\begin{lemma}\label{lem:cell}
There exists $C(d)<\infty$ such that, for every $x\in\Z^d$,
\begin{equation*}
\int_{C_x}|\nabla \gauge(v)-\xi(x)|\dd v\leq C\mu\bigl(B(x,6\sqrt d)\bigr)\, .
\end{equation*}
\end{lemma}
Definitions the statement relies on (verbatim):
\textit{$\mu$ and eq:hessian-growth (lines 458--461)}
Let $\mu$ be the distributional Laplacian of~$\gauge$ on~$\R^d$, so that $\int\phi\dd\mu=\int \gauge(v)\sum_{i=1}^d\partial_i^2\phi(v)\dd v$ for every smooth compactly supported function~$\phi$ on~$\R^d$. The distributional Laplacian~$\mu$ is a positive Radon measure, because the smooth convex functions obtained by mollifying~$\gauge$ have nonnegative Laplacian. For $y\in\R^d$ and $R>0$, let $\phi$ be smooth with $0\leq\phi\leq1$, $\phi=1$ on~$B(y,R)$, support in~$B(y,2R)$ and $|\nabla\phi|\leq2/R$. Integrating by parts and using $|\nabla \gauge|\leq\Lambda_\gauge$ gives
\begin{equation}\label{eq:hessian-growth}
\mu(B(y,R))\leq\int\phi\dd\mu=-\int\nabla \gauge\cdot\nabla\phi\leq2^{d+1}\omega_d\Lambda_\gauge R^{d-1}\, .
\end{equation}
\textit{$C_x$ and $D_n$ (line 122)}
Replace each site~$x\in A_n$ by the unit cell~$C_x\coloneqq x+[- \frac12, \frac12)^d$, and let $D_n\coloneqq\bigcup_{x\in A_n}C_x$. The \defn{inner radius} and the \defn{outer radius} are
\textit{notation $\xi(0)$ (line 303)}
\item Let $u_x\coloneqq x/|x|$ for $x\in\R^d\setminus\{0\}$ and $u_0\coloneqq0$, and let $\xi(0)\coloneqq0$.
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.cell_gradient {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ m : Measure (EuclideanSpace ℝ (Fin d)), IsLocallyFiniteMeasure m →
        CERW.IsDistribLaplacian Ψ m →
      ∀ x : Site d,
        ENNReal.ofReal (∫ v in CERW.cell x, ‖gradient Ψ v - ξ x‖)
          ≤ ENNReal.ofReal C * m (Metric.ball (CERW.toSpace x) (6 * Real.sqrt d))
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact CERW.Support.Norm.cell_gradient_holds
