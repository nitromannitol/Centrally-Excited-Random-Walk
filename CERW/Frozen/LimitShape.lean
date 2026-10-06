import CERW.Model
import CERW.Support.Main.LimitShape

/-!
# thm:shape

`thm:shape` of the revised paper (`limit-shapes.tex:103-116`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `thm:shape`:

```latex
Definitions used (lines 90--101):
\begin{verbatim}

For an integer~$n\geq0$ let
\begin{equation*}
\ell_n(x)\coloneqq\sum_{j=0}^{n-1}\ind_{\{X_j=x\}}
\qquad\text{and}\qquad
A_n\coloneqq\{x:\ell_n(x)>0\}\, .
\end{equation*}
The \defn{local time}~$\ell_n(x)$ is the number of departures from~$x$ before time~$n$, and $A_n$ is the \defn{range}; the set of sites visited by time~$n$ is~$A_{n+1}$. Write $B(y,\rho)$ for the open Euclidean ball of radius~$\rho$ about~$y$ and $\omega_d$ for the volume of~$B(0,1)$, and let
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\frac{1}{d+1}}\, ,
\end{equation}
so that the cone $2d\drift(r_n-|v|)_+$ has integral~$n$ over~$\R^d$. Informally, after $n$~steps the range contains essentially every site~$x$ with $|x|<r_n$ and essentially no site with $|x|>r_n$, and the local time at each site~$x$ is about $2d\drift(r_n-|x|)_+$. This profile determines~$r_n$: the local times sum to~$n$, and the slope~$2d\drift$ of the cone is the slope of the potential of a ball, computed in~\eqref{eq:ballpotential-euclid} below.
\end{verbatim}
Theorem (lines 103--116):
\begin{verbatim}
\begin{theorem}[Limit shape]\label{thm:shape}
Let $d\geq2$ and $0<\drift< \frac1d$. Then, almost surely, the centrally excited random walk has the following properties.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Shape}}: for every $0<\eta<1$ and all sufficiently large~$n$,
\begin{equation*}
\{x\in\Z^d:|x|<(1-\eta)r_n\}\subset A_n\subset\{x\in\Z^d:|x|<(1+\eta)r_n\}\, .
\end{equation*}
\item \underline{\emph{Local times}}: as $n\to\infty$,
\begin{equation*}
\frac1{r_n}\max_{x\in\Z^d}\bigl|\ell_n(x)-2d\drift(r_n-|x|)_+\bigr|\longrightarrow0\, .
\end{equation*}
\item \underline{\emph{Recurrence}}: the walk visits every site of~$\Z^d$ infinitely often.
\end{enumerate}
\end{theorem}
\end{verbatim}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.limit_shape {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | euclidNorm x < (1 - η) * r n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | euclidNorm x < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)
-- FROZEN-STATEMENT-END
:= by
  revert hX X μ Ω hεd hε ε hd d
  exact @CERW.Support.Main.limit_shape
