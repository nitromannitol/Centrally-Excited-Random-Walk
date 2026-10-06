import CERW.Model
import CERW.Support.RevisedPaperWidth

/-!
# thm-sharp-width

The statement of `limit-shapes.tex:176-189 (label thm:sharp, part (iv)(a), (iv)(b) and (iv)(c))`.
-/ 

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `thm:sharp` part (iv), the difference of the radii in the plane, parts (a), (b) and (c):

```latex
Theorem environment (lines 156--192); this node is part (iv), lines 176--189:
\begin{theorem}[Sharpness]\label{thm:sharp}
Let $d\geq2$ and $0<\drift<\nf{1}{d}$, and consider the centrally excited random walk.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Radii in the plane}}: let $d=2$. For every $p>0$ there exists $c(\drift,p)>0$
such that, for all sufficiently large~$n$,
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
\item \underline{\emph{Local times near the origin}}: there exists $c(d,\drift)>0$ such that, for
all sufficiently large~$n$, with probability at least $1-n^{-c}$,
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
\item For every $a\geq0$,
\begin{equation}\label{eq:planar-width-small}
\limsup_{n\to\infty}\P\bigl(\Rout(n)-\Rin(n)\leq a\sqrt{r_n}\bigr)\leq1-\exp\Bigl(-\frac{3\drift
a^2}{\pi}\Bigr)\, .
\end{equation}
\end{enumerate}
\end{enumerate}
\end{theorem}
Definitions the statement relies on (verbatim):
\textit{the centrally excited random walk (line 85)}
Let $d\geq2$ and $0<\drift<1/d$. A \defn{centrally excited random walk} $X_0=0,X_1,X_2,\ldots$
on~$\Z^d$ moves like simple random walk, except that on its first departure from each site~$x\neq0$
it moves to $x\pm e_i$ with probability~$1/(2d)\mp\drift x_i/(2|x|)$ for $1\leq i\leq d$, where
$e_1,\ldots,e_d$ is the standard basis of~$\R^d$. Given the path up to that departure, this step has
mean~$-\drift x/|x|$, a drift of size~$\drift$ toward the origin (Figure~\ref{fig:mechanism}).
\textit{$\ell_n$ and $A_n$ (lines 91--96)}
For an integer~$n\geq0$ let
\begin{equation*}
\ell_n(x)\coloneqq\sum_{j=0}^{n-1}\ind_{\{X_j=x\}}
\qquad\text{and}\qquad
A_n\coloneqq\{x:\ell_n(x)>0\}\, .
\end{equation*}
\textit{the radius $r_n$ (eq:radius) (lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\frac{1}{d+1}}\, ,
\end{equation}
\textit{$D_n$, $\Rin$, $\Rout$ (eq:radii) (lines 122--127)}
Replace each site~$x\in A_n$ by the unit cell~$C_x\coloneqq x+[- \frac12, \frac12)^d$, and let
$D_n\coloneqq\bigcup_{x\in A_n}C_x$. The \defn{inner radius} and the \defn{outer radius} are
\begin{equation}\label{eq:radii}
\Rin(n)\coloneqq\inf_{y\notin D_n}|y|
\qquad\text{and}\qquad
\Rout(n)\coloneqq\max_{0\leq j\leq n}|X_j|\, .
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.sharp_width {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    (∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let E : Set Ω := {ω | c * Real.sqrt (r n * Real.log n)
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n}
        MeasurableSet E ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ E) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
        (Real.sqrt (Real.pi / (3 * ε)) - δ) * Real.sqrt (r n * Real.log (Real.log n))
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n) ∧
    (∀ a : ℝ, 0 ≤ a →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        limsup (fun n => μ {ω | CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n
          ≤ a * Real.sqrt (r n)}) atTop ≤
          ENNReal.ofReal (1 - Real.exp (-(3 * ε * a ^ 2 / Real.pi))))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Support.RevisedPaper.sharp_width_extended hd
