import CERW.Model
import CERW.Support.RevisedPaperContact

/-!
# lem-contact

The statement of `limit-shapes.tex:774-779 (label lem:contact)`.
-/ 

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:contact` on the event of Section 5.1, almost surely, with positive constants of the event
and the nearest-point
projection onto `{Ψ ≤ r_n}`:

```latex
\begin{lemma}\label{lem:contact}
There exists $C(d,\drift,\gauge,p)<\infty$ such that, on the event of Section~\ref{sec:norm-event},
for large~$n$,
\begin{equation*}
H\leq Cr_nq_n=C\begin{cases}\sqrt{r_n\log n},&d=2,\\\log n,&d\geq3\end{cases}\, .
\end{equation*}
\end{lemma}
Definitions the statement relies on (verbatim):
\textit{$r_n$ (eq:radius-norm) (lines 331--333)}
\begin{equation}\label{eq:radius-norm}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift|B_\gauge|}\right)^{\nf{1}{(d+1)}}\, ,
\end{equation}
\textit{$q_n$ (eq:qn) (lines 719--721)}
\begin{equation}\label{eq:qn}
q_n\coloneqq\begin{dcases}\sqrt{\frac{\log n}{r_n}},&d=2,\\\frac{\log n}{r_n},&d\geq3\end{dcases}\,
.
\end{equation}
\textit{the event of Section 5.1: the quadratic martingale, the projection $\Pi_n$ and the
intersection of the events (lines 726--741)}
We collect on one event the martingale bounds used in Sections~\ref{sec:norms}--\ref{sec:outer}. Fix
$p>0$. Since every step has squared length one and conditional mean $-\drift I_j\xi(X_j)$
given~$\mathcal F_j$, the process
\begin{equation*}
\mathcal Q_t\coloneqq\sum_{j<t}2X_j\cdot\bigl(X_{j+1}-X_j+\drift I_j\xi(X_j)\bigr)
\end{equation*}
is a martingale, and Euler's relation gives
\begin{equation}\label{eq:quadratic}
|X_n|^2=n-2\drift\sum_{x\in A_n}\gauge(x)+\mathcal Q_n\, .
\end{equation}
For every integer $1\leq k\leq n+1$, the martingale~$\mathcal Q$ stopped when the walk first
leaves~$B(0,k)$ has increments at most~$Ck$. By Azuma's inequality and a union bound over~$k$, there
is an event of probability at least $1-Cn^{-p}$ on which the value at time~$n$ of each of these
stopped martingales is at most $Ck\sqrt{n\log n}$ in absolute value. For the least integer
$k>\max_{j<n}|X_j|$, which satisfies $k\leq\Rout(n)+1\leq n+1$, the walk does not leave~$B(0,k)$
before time~$n$, so the stopped martingale coincides with~$\mathcal Q$ up to time~$n$. Hence, on
this event,
\begin{equation}\label{eq:quadratic-coarse}
|\mathcal Q_n|\leq C\bigl(\Rout(n)+1\bigr)\sqrt{n\log n}\, .
\end{equation}

We also use the martingales~$\mathcal M^{q,a}$ of Section~\ref{sec:crossing} in the directions of
Euclidean projections. For $x\in\R^d$, let $\Pi_n(x)$ be the point of the closed convex
set~$\{\gauge\leq r_n\}$ nearest to~$x$ in Euclidean distance. Lemma~\ref{lem:freedman} and a union
bound over the $O(n^{d+1})$ pairs~$(q,a)$ with $q=\Lambda_\gauge u_{x-\Pi_n(x)}$ for some $x\in\Z^d$
with $|x|\leq n$ and $\gauge(x)>r_n$, and $a\in\Lambda_\gauge\Z\cap[0,\Lambda_\gauge n]$,
give~\eqref{eq:linear-mart} also for these pairs, with probability at least $1-Cn^{-p}$.

Intersect the events of Proposition~\ref{prop:coarse} and Lemma~\ref{lem:local} with the events on
which~\eqref{eq:vector}, \eqref{eq:localmart} and~\eqref{eq:quadratic-coarse} hold and on
which~\eqref{eq:linear-mart} holds for the pairs of Section~\ref{sec:crossing} and for those above;
the complement has probability at most $Cn^{-p}$, and the arguments of
Sections~\ref{sec:norms}--\ref{sec:outer} are deterministic on this event. Let $K$ be a constant
with $\Rout(n)\leq(K-1)r_n$ on the event of Proposition~\ref{prop:coarse}; then $D_n\subset
B(0,Kr_n)$ for large~$n$, and~\eqref{eq:quadratic-coarse} gives
\textit{$b$, $E$, $y_0$, $C_z$ and $H$ (lines 641--648)}
b\coloneqq\inf\{\gauge(y):y\in\R^d\setminus D_n\}\qquad\text{and}\qquad
E\coloneqq D_n\setminus\{\gauge<b\}\, ,
\end{equation*}
so that $\{\gauge<b\}\subset D_n$. Choose a point~$y_0$ with $\gauge(y_0)=b$ that is the limit of a
sequence of points outside~$D_n$. Since the sequence is bounded, some cell~$C_z$ disjoint from~$D_n$
contains infinitely many points of the sequence. Then $\ell_n(z)=0$, the closure of~$C_z$
contains~$y_0$, and $\gauge(z)\geq b$ because $z\in C_z$ lies outside~$D_n$. Let
\begin{equation*}
H\coloneqq U_{D_n}(y_0)\qquad\text{and}\qquad \mathcal I\coloneqq\int_E(\gauge(v)-b)\dd v\, .
\end{equation*}
Lemma~\ref{lem:ballpotential} gives $U_{\{\gauge<b\}}(y_0)=0$, so $H=U_E(y_0)$. For almost every
$v\in E$, the inequality~\eqref{eq:convexity} at~$v$, with $\nabla \gauge(v)$ in place of~$\xi$,
gives
\textit{Proposition 4.1 (lines 538--545)}
\begin{proposition}\label{prop:coarse}
Let $p>0$. There exist $c(d,\drift,\gauge,p)>0$ and $C(d,\drift,\gauge,p)<\infty$ such that, for
every integer~$n\geq2$, with probability at least $1-Cn^{-p}$,
\begin{equation*}
cr_n^d\leq|A_n|\leq Cr_n^d,\qquad
cr_n\leq\max_{x\in\Z^d}\ell_n(x)\leq Cr_n,\qquad
cr_n\leq\Rout(n)\leq Cr_n\, .
\end{equation*}
\end{proposition}
\textit{Lemma 3.1 (lines 393--409)}
\begin{lemma}\label{lem:local}
Let $p>0$. There exists $C(d,\drift,\gauge,p)<\infty$ such that, for every integer~$n\geq2$, the
following estimates hold simultaneously with probability at least $1-Cn^{-p}$.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Largest local time}}:
\begin{equation}\label{eq:M}
\max_{x\in\Z^d}\ell_n(x)\leq C|A_n|^{\nf{1}{d}}+C(\log n)^2\, .
\end{equation}
\item \underline{\emph{Local times on time intervals}}: for all integers~$0\leq s<t\leq n$,
\begin{equation}\label{eq:interval}
M_{s,t}\leq Ck_{s,t}^{\nf{1}{d}}+C(\log n)^2\, .
\end{equation}
\item \underline{\emph{Approximation by the potential}}: for every $y\in\R^d$ with $|y|\leq2n$,
\begin{equation}\label{eq:approx}
|\widetilde\ell_n(y)-U_{D_n}(y)|\leq C\log n+C\begin{cases}\bigl(\max_x\ell_n(x)\bigr)^{\nf12}\log
n,&d=2,\\\bigl(\max_x\ell_n(x)\log n\bigr)^{\nf12},&d\geq3\end{cases}\, .
\end{equation}
\end{enumerate}
\end{lemma}
\textit{$W_y$ (eq:bracket) (lines 441--442)}
\langle\mathcal M^y\rangle_n\leq CW_y,\qquad\text{where}\quad
W_y\coloneqq\sum_{x\in\Z^d}\ell_n(x)(1+|x-y|)^{2-2d}\, .
\textit{eq:localmart (lines 496--499)}
For every $p>0$, Lemma~\ref{lem:freedman} and~\eqref{eq:bracket} give, with probability at least
$1-Cn^{-p}$, simultaneously for all $y\in\Z^d$ with $|y|\leq3n$,
\begin{equation}\label{eq:localmart}
|\mathcal M_n^y|\leq C\bigl(\sqrt{W_y\log n}+\log n\bigr)\, .
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
\textit{eq:vector (lines 549--557)}
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
\textit{eq:linear-mart (lines 570--573)}
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
\textit{notation (lines 303--308)}
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
theorem CERW.Frozen.contact_potential {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    let q : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
    (∀ n : ℕ, ∃! P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ y, Ψ (P y) ≤ r n) ∧ ∀ y v, Ψ v ≤ r n → ‖y - P y‖ ≤ ‖y - v‖) ∧
    ∀ p : ℝ, 0 < p →
    ∃ c_co C_co C_loc C_vec C_mart C_quad C_lin C : ℝ,
      0 < c_co ∧ 0 < C_co ∧ 0 < C_loc ∧ 0 < C_vec ∧ 0 < C_mart ∧ 0 < C_quad ∧ 0 < C_lin ∧
      0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        ∀ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          (∀ y, Ψ (P y) ≤ r n) → (∀ y v, Ψ v ≤ r n → ‖y - P y‖ ≤ ‖y - v‖) →
        let Λ : ℝ := CERW.normMax Ψ
        let Z : (ℕ → Site d) → ℕ → EuclideanSpace ℝ (Fin d) := fun x t =>
          CERW.toSpace (x t) + ε •
            ∑ j ∈ Finset.range t, if x j ∉ CERW.departureRange x j then ξ (x j) else 0
        let Q : (ℕ → Site d) → ℕ → ℝ := fun x t =>
          ∑ j ∈ Finset.range t, 2 * inner ℝ (CERW.toSpace (x j))
            (CERW.toSpace (x (j + 1)) - CERW.toSpace (x j) +
              ε • (if x j ∉ CERW.departureRange x j then ξ (x j) else 0))
        let lin : Finset (EuclideanSpace ℝ (Fin d)) → (ℕ → Site d) → Prop := fun S x =>
          ∀ v ∈ S, ∀ k : ℕ, k ≤ n →
            |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
                (fun z => max (inner ℝ v (CERW.toSpace z) - k * Λ) 0) x n|
              ≤ C_lin * (Real.sqrt (Real.log n * ∑ z ∈ (CERW.departureRange x n).filter
                    (fun z => k * Λ - Λ < inner ℝ v (CERW.toSpace z)),
                    (CERW.localTime x n z : ℝ)) + Real.log n)
        let E : Set Ω := {ω |
          (c_co * r n ^ d ≤ ((CERW.departureRange (X · ω) n).card : ℝ) ∧
            ((CERW.departureRange (X · ω) n).card : ℝ) ≤ C_co * r n ^ d ∧
            c_co * r n ≤ (CERW.maxLocalTime (X · ω) n : ℝ) ∧
            (CERW.maxLocalTime (X · ω) n : ℝ) ≤ C_co * r n ∧
            c_co * r n ≤ CERW.maxRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ C_co * r n) ∧
          ((CERW.maxLocalTime (X · ω) n : ℝ)
              ≤ C_loc * ((CERW.departureRange (X · ω) n).card : ℝ) ^ ((1 : ℝ) / d)
                + C_loc * Real.log n ^ 2 ∧
            (∀ s t : ℕ, s < t → t ≤ n →
              (CERW.intervalMax (X · ω) s t : ℝ)
                ≤ C_loc * (CERW.freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / d)
                  + C_loc * Real.log n ^ 2) ∧
            ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
              |CERW.cellLocalTime (X · ω) n y
                  - CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y|
                ≤ C_loc * Real.log n + C_loc * (if d = 2 then
                    Real.sqrt (CERW.maxLocalTime (X · ω) n) * Real.log n
                  else Real.sqrt (CERW.maxLocalTime (X · ω) n * Real.log n))) ∧
          (∀ s t : ℕ, s < t → t ≤ n →
            ‖Z (X · ω) t - Z (X · ω) s‖ ≤ C_vec * Real.sqrt ((t - s : ℝ) * Real.log n)) ∧
          (∀ y : Site d, euclidNorm y ≤ 3 * n →
            |CERW.dynkinMart (CERW.driftStepProb d ε ξ)
                (fun z => CERW.latticeKernel d (z - y)) (X · ω) n|
              ≤ C_mart * (Real.sqrt ((∑ x ∈ CERW.departureRange (X · ω) n,
                    (CERW.localTime (X · ω) n x : ℝ)
                      * (1 + euclidNorm (x - y)) ^ (2 - 2 * (d : ℝ))) * Real.log n)
                  + Real.log n)) ∧
          |Q (X · ω) n| ≤ C_quad * (CERW.maxRadius (X · ω) n + 1) * Real.sqrt (n * Real.log n) ∧
          lin (((LatticeProb.ballFinset d (n : ℝ)).filter (fun x => x ≠ 0)).image
              (fun x => (Λ / ‖CERW.toSpace x‖) • CERW.toSpace x)) (X · ω) ∧
          lin (((LatticeProb.ballFinset d (n : ℝ)).filter
              (fun x => r n < Ψ (CERW.toSpace x))).image
              (fun x => (Λ / ‖CERW.toSpace x - P (CERW.toSpace x)‖) •
                (CERW.toSpace x - P (CERW.toSpace x)))) (X · ω)}
        μ Eᶜ ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) ∧
        ∀ᵐ ω ∂μ, ω ∈ E → ∀ y₀ : EuclideanSpace ℝ (Fin d),
          Ψ y₀ = CERW.normInnerRadius Ψ (X · ω) n →
          y₀ ∈ closure (CERW.cellSet (X · ω) n)ᶜ →
            CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y₀ ≤ C * r n * q n
-- FROZEN-STATEMENT-END
:= by
  intro Ψ hΨ ε hε hell r q
  let S : CERW.Support.RevisedPaper.SourceSetting d := ⟨Ψ, hΨ, ε, hε, hell⟩
  refine ⟨fun n => ?_, fun p hp => ?_⟩
  · obtain ⟨P, hP⟩ := CERW.Support.RevisedPaper.existsUnique_nearestProjection hΨ
      (S.radius_nonneg n)
    exact ⟨P.toFun, ⟨P.mem, P.min⟩, fun P' hP' =>
      congrArg CERW.Support.RevisedPaper.NearestProjection.toFun (hP ⟨P', hP'.1, hP'.2⟩)⟩
  · obtain ⟨K, C, hC, n₀, hn₀, h⟩ :=
      CERW.Support.RevisedPaper.contact_on_source_carrier hd S hp
    refine ⟨K.c_co, K.C_co, K.C_loc, K.C_vec, K.C_mart, K.C_quad, K.C_lin, C, K.c_co_pos,
      K.C_co_pos, K.C_loc_pos, K.C_vec_pos, K.C_mart_pos, K.C_quad_pos, K.C_lin_pos, hC, n₀, hn₀,
      fun ξ hξ hξ0 Ω _ μ _ X hX n hn P hmem hmin => ?_⟩
    exact h ξ hξ hξ0 μ X hX n hn ⟨P, hmem, hmin⟩
