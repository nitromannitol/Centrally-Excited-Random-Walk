import CERW.Model
import CERW.Support.Norm.MoreauCap

/-!
# lem:cap

`lem:cap` of the revised paper (`limit-shapes.tex:810-815`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:cap`:

```latex
\begin{lemma}\label{lem:cap}
Let $\eta\coloneqq c_\gauge^4/(8\Lambda_\gauge^2)$ and $\tau>0$. Let $x,y\in\R^d$ satisfy $F_\tau(y)\leq F_\tau(x)$, $q\cdot y>q\cdot x-\eta\tau$ and $|y|>\tau\Lambda_\gauge$, where $q\coloneqq\nabla F_\tau(x)$. Then every $\xi\in\partial \gauge(y)$ satisfies
\begin{equation*}
q\cdot\xi\geq\frac{c_\gauge^2}2\, .
\end{equation*}
\end{lemma}
Definitions the statement relies on (verbatim): $F_\tau,z_x,p_x$ (lines 795--800), $\Lambda_\gauge,c_\gauge$ (line 328),
and the first-order condition and gradient formula $\nabla F_\tau(x)=p_x$ (lines 801 and 805).
For the outer bound we use the Moreau envelope of~$\gauge$ \citep{Moreau1965}. Let $\tau>0$. For $x\in\R^d$, the function $z\mapsto \gauge(z)+|x-z|^2/(2\tau)$ is continuous and strictly convex, and tends to infinity as $|z|\to\infty$. Let $z_x$ be its minimizer, and let
\begin{equation*}
F_\tau(x)\coloneqq\min_{z\in\R^d}\Bigl\{\gauge(z)+\frac{|x-z|^2}{2\tau}\Bigr\}
\qquad\text{and}\qquad
p_x\coloneqq\frac{x-z_x}\tau\, .
\end{equation*}
\begin{quote}
In Sections~\ref{sec:norm-setup}--\ref{sec:norms}, $\gauge$ is a norm, $\drift>0$ satisfies~\eqref{eq:ellipticity}, $r_n$ is given by~\eqref{eq:radius-norm}, and $U_D$ is the potential~\eqref{eq:potential-norm} defined below. At a point~$v\in\R^d$, $\nabla\gauge(v)$ is the gradient, which exists for almost every~$v$. Let $\Lambda_\gauge\coloneqq\max_{|u|=1}\gauge(u)$ and $c_\gauge\coloneqq\min_{|u|=1}\gauge(u)$. Every $\xi\in\partial\gauge(x)$ satisfies $\xi\cdot x=\gauge(x)$ and $|\xi|\leq\Lambda_\gauge$. In Sections~\ref{sec:contact}--\ref{sec:lower}, $\gauge$ is the Euclidean norm, so that $\xi(x)=u_x$, $r_n$ is given by~\eqref{eq:radius}, and $U_D$ is the potential~\eqref{eq:potential-intro}.
The function~$F_\tau$ is convex, as a partial minimum of a jointly convex function of~$(x,z)$. The first-order condition for~$z_x$ is $p_x\in\partial \gauge(z_x)$, so~\eqref{eq:convexity} gives $|p_x|\leq\Lambda_\gauge$, $p_x\cdot z_x=\gauge(z_x)$, and $p_x\cdot y\leq \gauge(y)$ for all $y\in\R^d$. Evaluating the function minimized in the definition of~$F_\tau(x+h)$ at $z=z_x$, and the one for~$F_\tau(x)$ at $z=z_{x+h}$, gives, for all $x,h\in\R^d$,
Monotonicity of the subdifferential, $(p_x-p_w)\cdot(z_x-z_w)\geq0$, and $z_x=x-\tau p_x$ give $\tau|p_x-p_w|^2\leq(p_x-p_w)\cdot(x-w)$, so $|p_x-p_w|\leq|x-w|/\tau$ for $x,w\in\R^d$. With~\eqref{eq:moreau-taylor}, this shows that $F_\tau$ is continuously differentiable, with $\nabla F_\tau(x)=p_x$, and that $\nabla F_\tau$ is $\nf1\tau$-Lipschitz. Taking $z=x$ in the definition of~$F_\tau$ gives $F_\tau\leq \gauge$. The bound $\gauge(z)\geq \gauge(x)-\Lambda_\gauge|x-z|$ and the inequality $\Lambda_\gauge s-s^2/(2\tau)\leq\tau\Lambda_\gauge^2/2$ for $s\geq0$ give $F_\tau\geq \gauge-\tau\Lambda_\gauge^2/2$, and $F_\tau(x)=\gauge(z_x)+\nf\tau2|p_x|^2$ is at most $p_x\cdot x=\gauge(z_x)+\tau|p_x|^2$. So, for all $x\in\R^d$,
\end{quote}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.moreau_cap {d : ℕ} (hd : 2 ≤ d)
    {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : CERW.IsNorm Ψ) {τ : ℝ} (hτ : 0 < τ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    let η : ℝ := CERW.normMin Ψ ^ 4 / (8 * CERW.normMax Ψ ^ 2)
    let q : EuclideanSpace ℝ (Fin d) := gradient (CERW.moreauEnvelope Ψ τ) x
    CERW.moreauEnvelope Ψ τ y ≤ CERW.moreauEnvelope Ψ τ x →
    inner ℝ q x - η * τ < inner ℝ q y →
    τ * CERW.normMax Ψ < ‖y‖ →
    ∀ ξ : EuclideanSpace ℝ (Fin d), CERW.IsSubgradient Ψ y ξ →
      CERW.normMin Ψ ^ 2 / 2 ≤ inner ℝ q ξ
-- FROZEN-STATEMENT-END
:= by
  revert y x hτ τ hΨ Ψ hd d
  exact @CERW.Support.Norm.moreau_cap
