import CERW.Model
import CERW.Support.RevisedPaperCarrier

/-!
# lem-outer-crossing

The statement of `limit-shapes.tex:575-580 (label lem:outer-crossing)`.
-/ 

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:outer-crossing` with the constants of the events of `eq:vector` and `eq:linear-mart` and
the probability of
their intersection:

```latex
\begin{lemma}\label{lem:outer-crossing}
Let $\alpha>0$. There exists $C(d,\drift,\gauge,\alpha,p)<\infty$ with the following property. Let
$q\in\R^d$ satisfy $|q|\leq\Lambda_\gauge$, and consider a path of the walk that
satisfies~\eqref{eq:vector}, and~\eqref{eq:linear-mart} for this~$q$ and every
$a\in\Lambda_\gauge\Z\cap[0,\Lambda_\gauge n]$. Let $x_*$ be one of the sites $X_0,\ldots,X_n$ with
$q\cdot X_j\leq T\coloneqq q\cdot x_*$ for $0\leq j\leq n$, and let $h>0$ be such that
$q\cdot\xi(X_j)\geq\alpha$ for every $0\leq j\leq n$ with $q\cdot X_j>T-h$. For $b\geq0$ let
$L_b\coloneqq1+\max\{\ell_n(x):x\in\Z^d,\ q\cdot x\geq b\}$. Then every $b\geq0$ satisfies
\begin{equation}\label{eq:outer-crossing}
T\leq\max\{T-h,b\}+CL_b\log n\, .
\end{equation}
\end{lemma}
Definitions the statement relies on (verbatim):
\textit{the martingales $\mathcal M^{q,a}$ and eq:linear-mart (lines 570--573)}
The martingales of the functions $(q\cdot x-a)_+$ bound the number of sites~$x\in A_n$ at which
$q\cdot x$ exceeds a given level (Step~2 of the proof of Lemma~\ref{lem:outer-crossing}); we bound
them simultaneously for all vectors~$q$ in a finite deterministic set, because $q$ will depend on
the path. For $q\in\R^d$ and $a\in\R$, let $\mathcal M^{q,a}$ be the martingale~$\mathcal M^f$ of
Section~\ref{sec:dynkin} with $f(x)=(q\cdot x-a)_+$. If $|q|\leq\Lambda_\gauge$, then one step
changes $q\cdot X_j$ by at most~$\Lambda_\gauge$, so the increments of~$\mathcal M^{q,a}$ are at
most~$C$, and the bracket of~$\mathcal M^{q,a}$ through time~$n$ is at most $C\sum_{x:q\cdot
x>a-\Lambda_\gauge}\ell_n(x)$, because $f$ is constant on $x$ and its neighbors unless $q\cdot
x>a-\Lambda_\gauge$. Fix $p>0$. Lemma~\ref{lem:freedman} and a union bound over the $O(n^{d+1})$
pairs~$(q,a)$ with $q=\Lambda_\gauge u_x$ for some $x\in\Z^d$ with $0<|x|\leq n$ and
$a\in\Lambda_\gauge\Z\cap[0,\Lambda_\gauge n]$ give, with probability at least $1-Cn^{-p}$,
simultaneously for all these pairs,
\begin{equation}\label{eq:linear-mart}
|\mathcal M^{q,a}_n|\leq C\biggl(\sqrt{\log n\sum_{x:q\cdot x>a-\Lambda_\gauge}\ell_n(x)}+\log
n\biggr)\, .
\end{equation}
\textit{$Z$, the event and the constant of eq:vector (lines 549--557)}
A crossing against the drift requires a large increment of the martingale
\begin{equation}\label{eq:vector-def}
Z_t\coloneqq X_t+\drift\sum_{j<t}I_j\xi(X_j)\, ,
\end{equation}
which takes values in~$\R^d$ and has bounded increments. Azuma's inequality in each coordinate and a
union bound over the pairs $s<t$ give, for every $p>0$, with probability at least $1-Cn^{-p}$,
\begin{equation}\label{eq:vector}
|Z_t-Z_s|\leq C\sqrt{(t-s)\log n}
\qquad\text{for } 0\leq s<t\leq n\, .
\end{equation}
\textit{$\mathcal M^f$ (lines 430--435)}
For $f\colon\Z^d\to\R$ with bounded nearest-neighbor increments, let
\begin{equation*}
\mathcal M^f_t\coloneqq f(X_t)-f(X_0)-\sum_{j<t}\E\bigl(f(X_{j+1})-f(X_j)\bigm|\mathcal F_j\bigr)
\end{equation*}
be the martingale in Dynkin's formula for~$f$. By~\eqref{eq:kernel}, the conditional expectation in
the sum is $\Delta f(X_j)-\drift I_j\xi(X_j)\cdot\bar\nabla f(X_j)$, with $\bar\nabla f$ defined
like~$\bar\nabla g$. For $y\in\Z^d$ write $g_y\coloneqq g(\cdot-y)$ and $\mathcal
M^y\coloneqq\mathcal M^{g_y}$. Since $\Delta g_y=\ind_{\{y\}}$ and each site of~$A_n$ has its first
departure before time~$n$,
\begin{equation}\label{eq:dynkin}
\textit{the norm, the subgradients, eq:kernel and eq:ellipticity (lines 321--330)}
Let $\gauge$ be a norm on~$\R^d$, let $B_\gauge$ be its unit ball, and let $\partial\gauge(x)$ be
the set of subgradients of~$\gauge$ at~$x$, as in Section~\ref{sec:norms-intro}; if $\gauge$ is
differentiable at~$x$, then $\partial\gauge(x)=\{\nabla\gauge(x)\}$. At each site~$x\neq0$ fix
$\xi(x)\in\partial\gauge(x)$, with coordinates~$\xi_i(x)$. The \defn{centrally excited random walk
with norm~$\gauge$} moves like simple random walk, except that on its first departure from each
site~$x\neq0$ it moves to $x\pm e_i$ with probability
\begin{equation}\label{eq:kernel}
\frac1{2d}\mp\frac\drift2\xi_i(x)
\qquad\text{for } 1\leq i\leq d\, .
\end{equation}
We assume that
\begin{equation}\label{eq:ellipticity}
\drift\max_{1\leq i\leq d}\gauge(e_i)<\frac1d\, .
\end{equation}
Every $\xi\in\partial\gauge(x)$ satisfies $\xi\cdot y\leq\gauge(y)$ for every~$y$, with equality at
$y=x$ (Euler's relation); so $|\xi_i(x)|\leq\gauge(e_i)$, and~\eqref{eq:ellipticity} makes the
probabilities~\eqref{eq:kernel} positive. The step at the first departure from~$x$ has conditional
mean~$-\drift\xi(x)$, whose inner product with~$x$ is $-\drift\gauge(x)<0$. The Euclidean norm, with
$\xi(x)=x/|x|$, gives the walk of Section~\ref{sec:introduction}, and then~\eqref{eq:ellipticity}
reads $\drift<\nf1d$. Let
\textit{$\Lambda_\gauge$ and $c_\gauge$ (line 336)}
In Sections~\ref{sec:norm-setup}--\ref{sec:norms}, $\gauge$ is a norm, $\drift>0$
satisfies~\eqref{eq:ellipticity}, $r_n$ is given by~\eqref{eq:radius-norm}, and $U_D$ is the
potential~\eqref{eq:potential-norm} defined below; at a point~$v\in\R^d$, $\nabla\gauge(v)$ is the
gradient, which exists for almost every~$v$. Let $\Lambda_\gauge\coloneqq\max_{|u|=1}\gauge(u)$ and
$c_\gauge\coloneqq\min_{|u|=1}\gauge(u)$; every $\xi\in\partial\gauge(x)$ satisfies $\xi\cdot
x=\gauge(x)$ and $|\xi|\leq\Lambda_\gauge$. In Sections~\ref{sec:contact}--\ref{sec:lower}, $\gauge$
is the Euclidean norm, so that $\xi(x)=u_x$, $r_n$ is given by~\eqref{eq:radius}, and $U_D$ is the
potential~\eqref{eq:potential-intro}.
\textit{notation $u_x$ and $\xi(0)$, the constants, $I_j$ and $n\geq2$ (lines 303--308)}
\item Let $u_x\coloneqq x/|x|$ for $x\in\R^d\setminus\{0\}$ and $u_0\coloneqq0$, and let
$\xi(0)\coloneqq0$.
\item The letters $c>0$ and $C>0$ denote constants depending only on $d$, $\drift$ and the
exponent~$p$ of the failure probability under discussion, and in
Sections~\ref{sec:norm-setup}--\ref{sec:norms} also on the norm~$\gauge$, but not on the choice of
the subgradients~$\xi(x)$; they may change from line to line. Every further dependence is stated,
and a subscript on~$O$, as in~$O_y$, means that the implied constant also depends on~$y$. We write
$a_n\asymp b_n$ if $c\leq a_n/b_n\leq C$, and $O_{\P}(a_n)$ for random variables~$Y_n$ such that
$Y_n/a_n$ is tight.
\item The $\sigma$-field generated by $X_0,\ldots,X_j$ is~$\mathcal F_j$. For martingales $Z_1$
and~$Z_2$, the brackets $\langle Z_1\rangle_n$ and~$\langle Z_1,Z_2\rangle_n$ are the predictable
quadratic variation and covariation through time~$n$.
\item The indicator that the step at time~$j$ is a first departure is $I_j\coloneqq\ind_{\{X_j\notin
A_j\}}$, so that $\E(X_{j+1}-X_j\mid\mathcal F_j)=-\drift I_j\xi(X_j)$, where $\xi(x)=u_x$ for the
Euclidean norm.
\item The function~$\widetilde\ell_n$ on~$\R^d$ equals $\ell_n(x)$ on~$C_x$ for every $x\in\Z^d$; it
vanishes off~$D_n$.
\item All estimates concern integers~$n\geq2$, so that $\log n>0$. In a statement that holds with
probability at least $1-Cn^{-p}$ for all sufficiently large~$n$, enlarging~$C$ makes it hold for
every $n\geq2$.
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.outer_crossing {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    ∀ p : ℝ, 0 < p → ∃ C₁ : ℝ, 0 < C₁ ∧
      (∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        let Λ : ℝ := CERW.normMax Ψ
        let Z : Ω → ℕ → EuclideanSpace ℝ (Fin d) := fun ω t => CERW.toSpace (X t ω) + ε •
          ∑ j ∈ Finset.range t,
            if X j ω ∉ CERW.departureRange (X · ω) j then ξ (X j ω) else 0
        let E : Set Ω := {ω | (∀ s t : ℕ, s < t → t ≤ n →
            ‖Z ω t - Z ω s‖ ≤ C₁ * Real.sqrt ((t - s : ℝ) * Real.log n)) ∧
          ∀ q ∈ ((LatticeProb.ballFinset d (n : ℝ)).filter (fun x => x ≠ 0)).image
              (fun x => (Λ / ‖CERW.toSpace x‖) • CERW.toSpace x),
          ∀ k : ℕ, k ≤ n →
            |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
                (fun z => max (inner ℝ q (CERW.toSpace z) - k * Λ) 0) (X · ω) n|
              ≤ C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (CERW.departureRange (X · ω) n).filter
                    (fun z => k * Λ - Λ < inner ℝ q (CERW.toSpace z)),
                    (CERW.localTime (X · ω) n z : ℝ)) + Real.log n)}
        μ Eᶜ ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (-p))) ∧
      ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ n : ℕ, 2 ≤ n → ∀ q : EuclideanSpace ℝ (Fin d), ‖q‖ ≤ CERW.normMax Ψ →
      ∀ x : ℕ → Site d, x 0 = 0 → (∀ j, x (j + 1) - x j ∈ CERW.unitSteps d) →
        let Λ : ℝ := CERW.normMax Ψ
        let Z : ℕ → EuclideanSpace ℝ (Fin d) := fun t => CERW.toSpace (x t) + ε •
          ∑ j ∈ Finset.range t, if x j ∉ CERW.departureRange x j then ξ (x j) else 0
        (∀ s t : ℕ, s < t → t ≤ n →
          ‖Z t - Z s‖ ≤ C₁ * Real.sqrt ((t - s : ℝ) * Real.log n)) →
        (∀ k : ℕ, k ≤ n →
          |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
              (fun z => max (inner ℝ q (CERW.toSpace z) - k * Λ) 0) x n|
            ≤ C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (CERW.departureRange x n).filter
                  (fun z => k * Λ - Λ < inner ℝ q (CERW.toSpace z)),
                  (CERW.localTime x n z : ℝ)) + Real.log n)) →
        ∀ j₀ : ℕ, j₀ ≤ n →
        (∀ j ≤ n, inner ℝ q (CERW.toSpace (x j)) ≤ inner ℝ q (CERW.toSpace (x j₀))) →
        let T : ℝ := inner ℝ q (CERW.toSpace (x j₀))
        ∀ h : ℝ, 0 < h →
        (∀ j ≤ n, T - h < inner ℝ q (CERW.toSpace (x j)) → α ≤ inner ℝ q (ξ (x j))) →
        ∀ b : ℝ, 0 ≤ b →
          T ≤ max (T - h) b + C * (1 + ((((CERW.departureRange x n).filter
              (fun z => b ≤ inner ℝ q (CERW.toSpace z))).sup (CERW.localTime x n) : ℕ) : ℝ))
            * Real.log n
-- FROZEN-STATEMENT-END
:= by
  intro Ψ hΨ ε hε hell p hp
  exact CERW.Support.RevisedPaper.outer_crossing_on_source_events hd hΨ hε hell hp
