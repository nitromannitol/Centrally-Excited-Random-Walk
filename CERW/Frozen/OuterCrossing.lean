import CERW.Model
import CERW.Support.Norm.OuterCrossing

/-!
# lem:outer-crossing

`lem:outer-crossing` of the revised paper (`limit-shapes.tex:988-993`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:outer-crossing`:

```latex
\begin{lemma}\label{lem:outer-crossing}
Let $\alpha>0$. There exists $C(d,\drift,\gauge,\alpha,p)<\infty$ with the following property. Let $q\in\R^d$ satisfy $|q|\leq\Lambda_\gauge$, and consider a path of the walk that satisfies~\eqref{eq:vector}, and~\eqref{eq:linear-mart} for this~$q$ and every $a\in\Lambda_\gauge\Z\cap[0,\Lambda_\gauge n]$. Let $x_*$ be one of the sites $X_0,\ldots,X_n$ with $q\cdot X_j\leq T\coloneqq q\cdot x_*$ for $0\leq j\leq n$, and let $h>0$ be such that $q\cdot\xi(X_j)\geq\alpha$ for every $0\leq j\leq n$ with $q\cdot X_j>T-h$. For $b\geq0$ let $L_b\coloneqq1+\max\{\ell_n(x):x\in\Z^d,\ q\cdot x\geq b\}$. Then every $b\geq0$ satisfies
\begin{equation}\label{eq:outer-crossing}
T\leq\max\{T-h,b\}+CL_b\log n\, .
\end{equation}
\end{lemma}
Definitions the statement relies on (verbatim): $\mathcal M^f$ (lines 421--425), $\mathcal M^{q,a}$ and eq:linear-mart
(lines 831--839), $Z$ and eq:vector (lines 651--659), and $\Lambda_\gauge$ (line 327).
For $f\colon\Z^d\to\R$ with bounded nearest-neighbor increments, let
\begin{equation*}
\mathcal M^f_t\coloneqq f(X_t)-f(X_0)-\sum_{j<t}\E\bigl(f(X_{j+1})-f(X_j)\bigm|\mathcal F_j\bigr)
\end{equation*}
be the martingale in Dynkin's formula for~$f$. By~\eqref{eq:kernel}, the conditional expectation in the sum is $\Delta f(X_j)-\drift I_j\xi(X_j)\cdot\bar\nabla f(X_j)$, with $\bar\nabla f$ defined like~$\bar\nabla g$. For $y\in\Z^d$ write $g_y\coloneqq g(\cdot-y)$ and $\mathcal M^y\coloneqq\mathcal M^{g_y}$. Since $\Delta g_y=\ind_{\{y\}}$ and each site of~$A_n$ has its first departure before time~$n$,
\begin{quote}
For $q\in\R^d$ and $a\in\R$, let $\mathcal M^{q,a}$ be the martingale~$\mathcal M^f$ of Section~\ref{sec:dynkin} with $f(x)=(q\cdot x-a)_+$. If $|q|\leq\Lambda_\gauge$, then one step changes $q\cdot X_j$ by at most~$\Lambda_\gauge$, so the increments of~$\mathcal M^{q,a}$ are at most~$C$, and its bracket through time~$n$ is at most $C\sum_{x:q\cdot x>a-\Lambda_\gauge}\ell_n(x)$, because $f$ is constant on $x$ and its neighbors unless $q\cdot x>a-\Lambda_\gauge$. Let
\begin{equation}\label{eq:tn}
\tau_n\coloneqq K_1\bar L_n\log n,\qquad\text{where}\quad\bar L_n\coloneqq1+C_0r_nq_n^{\nf{1}{d+1}}\, ,
\end{equation}
$C_0$ is the constant in~\eqref{eq:norm-profile}, and $K_1>0$ is the constant, depending only on $d$, $\drift$, $\gauge$ and~$p$, chosen in the proof of Proposition~\ref{prop:norm-shape}. The vectors $\xi(x)$ and~$\nabla F_{\tau_n}(x)$ are deterministic and have length at most~$\Lambda_\gauge$. So Lemma~\ref{lem:freedman} and a union bound over the $O(n^{d+1})$ pairs~$(q,a)$ with $q\in\{\xi(x),\nabla F_{\tau_n}(x)\}$ for some $x\in\Z^d$ with $0<|x|\leq n$ and $a\in\Lambda_\gauge\Z\cap[0,\Lambda_\gauge n]$ give, with probability at least $1-Cn^{-p}$, simultaneously for all these pairs,
\begin{equation}\label{eq:linear-mart}
|\mathcal M^{q,a}_n|\leq C\biggl(\sqrt{\log n\sum_{x:q\cdot x>a-\Lambda_\gauge}\ell_n(x)}+\log n\biggr)\, .
\end{equation}
Neither this constant~$C$ nor the probability bound depends on $C_0$ or~$K_1$.
In Sections~\ref{sec:norm-setup}--\ref{sec:norms}, $\gauge$ is a norm, $\drift$ satisfies~\eqref{eq:ellipticity}, $r_n$ is given by~\eqref{eq:radius-norm}, and $U_D$ is the potential~\eqref{eq:potential-norm} defined below; at a point~$v\in\R^d$, $\nabla\gauge(v)$ is the gradient, which exists for almost every~$v$. Let $\Lambda_\gauge\coloneqq\max_{|u|=1}\gauge(u)$ and $c_\gauge\coloneqq\min_{|u|=1}\gauge(u)$; every $\xi\in\partial\gauge(x)$ satisfies $\xi\cdot x=\gauge(x)$ and $|\xi|\leq\Lambda_\gauge$. In Sections~\ref{sec:contact}--\ref{sec:lower}, $\gauge$ is the Euclidean norm, so that $\xi(x)=u_x$, $r_n$ is given by~\eqref{eq:radius}, and $U_D$ is the potential~\eqref{eq:potential-intro}.
\end{quote}
A crossing against the drift requires a large increment of the martingale
\begin{equation}\label{eq:vector-def}
Z_t\coloneqq X_t+\drift\sum_{j<t}I_j\xi(X_j)\, ,
\end{equation}
which takes values in~$\R^d$ and has bounded increments. Azuma's inequality in each coordinate and a union bound over the pairs $s<t$ give, for every $p>0$, with probability at least $1-Cn^{-p}$,
\begin{equation}\label{eq:vector}
|Z_t-Z_s|\leq C\sqrt{(t-s)\log n}
\qquad\text{for } 0\leq s<t\leq n\, .
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.outer_crossing {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    ∀ α : ℝ, 0 < α → ∀ C₁ : ℝ, 0 < C₁ → ∃ C : ℝ, 0 < C ∧
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
  revert hd d
  exact CERW.Support.Norm.outer_crossing_holds
