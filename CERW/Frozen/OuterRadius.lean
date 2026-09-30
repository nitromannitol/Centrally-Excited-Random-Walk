import CERW.Model

/-!
# prop:stronger-outer

`prop:stronger-outer` of the revised paper (`limit-shapes.tex:1174-1179`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `prop:stronger-outer`:

```latex
\begin{proposition}[Outer radius]\label{prop:stronger-outer}
Let $\gauge$ be the Euclidean norm, and let $0<\drift<\nf{1}{d}$. For every $p>0$ there exists $C(d,\drift,p)<\infty$ such that, for every integer~$n\geq2$, with probability at least $1-Cn^{-p}$,
\begin{equation*}
\Rout(n)\leq r_n+C\begin{cases}\sqrt{r_n}(\log n)^{\nf52},&d=2,\\(\log n)^{d+1},&d\geq3\end{cases}\, .
\end{equation*}
\end{proposition}
Definitions the statement relies on (verbatim):
\textit{the radius $r_n$ (eq:radius, lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\nf{1}{d+1}}\, ,
\end{equation}
\textit{$D_n$, $\Rin$, $\Rout$ (eq:radii, lines 122--127)}
Replace each site~$x\in A_n$ by the unit cell~$C_x\coloneqq x+[-\nf12,\nf12)^d$, and let $D_n\coloneqq\bigcup_{x\in A_n}C_x$. The \defn{inner radius} and the \defn{outer radius} are
\begin{equation}\label{eq:radii}
\Rin(n)\coloneqq\inf_{y\notin D_n}|y|
\qquad\text{and}\qquad
\Rout(n)\coloneqq\max_{0\leq j\leq n}|X_j|\, .
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.outer_radius {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ CERW.maxRadius (X · ω) n ≤ r n + C *
            (if d = 2 then Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
              else Real.log n ^ ((d : ℝ) + 1))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  sorry
