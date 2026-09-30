import CERW.Model

/-!
# thm:sharp, part (i)

`thm:sharp` of the revised paper (`limit-shapes.tex:159-164`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `thm:sharp` part (i):

```latex
Theorem environment (lines 156--188); this node is part (i), lines 159--164:
\begin{verbatim}
\begin{theorem}[Sharpness]\label{thm:sharp}
Let $d\geq2$ and $0<\drift<\nf{1}{d}$, and consider the centrally excited random walk.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Radii in the plane}}: let $d=2$. For every $p>0$ there exists $c(\drift,p)>0$ such that, for all sufficiently large~$n$,
\begin{equation}\label{eq:planar-polynomial-lower}
\P\bigl(r_n-\Rin(n)\geq c\sqrt{r_n\log n}\bigr)\geq n^{-p}
\qquad\text{and}\qquad
\P\bigl(\Rout(n)-r_n\geq c\sqrt{r_n\log n}\bigr)\geq n^{-p}\, .
\end{equation}
\item \underline{\emph{Iterated logarithm for the radii in the plane}}: let $d=2$. Almost surely,
\begin{equation}\label{eq:planar-lil-lower}
\limsup_{n\to\infty}\frac{r_n-\Rin(n)}{\sqrt{r_n\log\log n}}\geq\frac1{\sqrt{10\pi\drift}}
\qquad\text{and}\qquad
\limsup_{n\to\infty}\frac{\Rout(n)-r_n}{\sqrt{r_n\log\log n}}\geq\frac1{\sqrt{10\pi\drift}}\, .
\end{equation}
\item \underline{\emph{Local times near the origin}}: there exists $c(d,\drift)>0$ such that, for all sufficiently large~$n$, with probability at least $1-n^{-c}$,
\begin{equation}\label{eq:sharp-bulk}
\max_{\substack{x\in\Z^d\\|x|\leq r_n^{\nf12}}}\bigl|\ell_n(x)-2d\drift(r_n-|x|)\bigr|
\geq c\begin{cases}\sqrt{r_n}\log n,&d=2,\\\sqrt{r_n\log n},&d\geq3\end{cases}\, .
\end{equation}
\item \underline{\emph{Difference of the radii in the plane}}: let $d=2$.
\begin{enumerate}[label=\textup{(\alph*)}]
\item For every $p>0$ there exists $c(\drift,p)>0$ such that, for all sufficiently large~$n$,
\begin{equation}\label{eq:planar-width-polynomial}
\P\bigl(\Rout(n)-\Rin(n)\geq c\sqrt{r_n\log n}\bigr)\geq n^{-p}\, .
\end{equation}
\item Almost surely,
\begin{equation}\label{eq:planar-width-lil}
\limsup_{n\to\infty}\frac{\Rout(n)-\Rin(n)}{\sqrt{r_n\log\log n}}\geq\sqrt{\frac{\pi}{3\drift}}\, .
\end{equation}
\end{enumerate}
\end{enumerate}
\end{theorem}
\end{verbatim}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.sharp_radii {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let Ein : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ r n - CERW.innerRadius (X · ω) n}
        let Eout : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ CERW.maxRadius (X · ω) n - r n}
        MeasurableSet Ein ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Ein ∧
          MeasurableSet Eout ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Eout
-- FROZEN-STATEMENT-END
:= by
  sorry
