import CERW.Model
import CERW.Support.Lower.LogLower

/-!
# prop:log-lower

`prop:log-lower` of the revised paper (`limit-shapes.tex:1602-1616`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `prop:log-lower`:

```latex
\begin{proposition}[Lower bounds for the radii]\label{prop:log-lower}
Let $\gauge$ be the Euclidean norm, and let $0<\drift<\nf1d$. There exist $c(d,\drift)>0$, $C(d,\drift)<\infty$ and $h_0(d,\drift)>0$ such that the following hold.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Tail bounds}}: for all sufficiently large~$n$ and every real~$h$ with $h_0\leq h\leq\nf{r_n}{8}$,
\begin{align}
\P\bigl(\Rin(n)\geq r_n-h\text{ and }\Rout(n)\leq r_n+h\bigr)&\leq\exp\bigl\{-cr_n^{d-1}e^{-Ch}\bigr\}\, ,\label{eq:log-lower-tail}\\
\P\bigl(\Rout(n)\leq r_n+h\bigr)&\leq\exp\bigl\{-cr_n^{d-1}e^{-Ch}\bigr\}+\exp\bigl\{-cr_n^{d-3}h^2\bigr\}\, .\label{eq:outer-lower-tail}
\end{align}
\item \underline{\emph{Almost-sure bounds}}: almost surely, for all sufficiently large~$n$,
\begin{equation}\label{eq:log-lower-as}
\max\{r_n-\Rin(n),\Rout(n)-r_n\}>c\log n\, ,
\end{equation}
and, if $d\geq3$, also $\Rout(n)-r_n>c\log n$.
\end{enumerate}
\end{proposition}
Definitions the statement relies on (verbatim):
\textit{the radius $r_n$ (eq:radius, lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\frac{1}{d+1}}\, ,
\end{equation}
\textit{$D_n$, $\Rin$, $\Rout$ (eq:radii, lines 122--127)}
Replace each site~$x\in A_n$ by the unit cell~$C_x\coloneqq x+[- \frac12, \frac12)^d$, and let $D_n\coloneqq\bigcup_{x\in A_n}C_x$. The \defn{inner radius} and the \defn{outer radius} are
\begin{equation}\label{eq:radii}
\Rin(n)\coloneqq\inf_{y\notin D_n}|y|
\qquad\text{and}\qquad
\Rout(n)\coloneqq\max_{0\leq j\leq n}|X_j|\, .
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.log_lower_bounds {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ c C h₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < h₀ ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        (∀ n : ℕ, n₀ ≤ n → ∀ h : ℝ, h₀ ≤ h → h ≤ r n / 8 →
          μ {ω | r n - h ≤ CERW.innerRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ r n + h}
            ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (d - 1) * Real.exp (-(C * h))))) ∧
          μ {ω | CERW.maxRadius (X · ω) n ≤ r n + h}
            ≤ ENNReal.ofReal (Real.exp (-(c * r n ^ (d - 1) * Real.exp (-(C * h))))
              + Real.exp (-(c * r n ^ ((d : ℝ) - 3) * h ^ 2)))) ∧
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          c * Real.log n < max (r n - CERW.innerRadius (X · ω) n)
            (CERW.maxRadius (X · ω) n - r n) ∧
          (3 ≤ d → c * Real.log n < CERW.maxRadius (X · ω) n - r n)
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact CERW.Support.Lower.log_lower_bounds_holds
