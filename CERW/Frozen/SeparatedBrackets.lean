import CERW.Model
import CERW.Support.Inner.InnerRadius
import CERW.Support.Lower.ExpDeviation
import CERW.Support.Lower.SeparatedBrackets
import CERW.Support.Main.LimitShape
import CERW.Support.Norm.BallLayer
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.Coarse
import CERW.Support.Norm.ContactPotential
import CERW.Support.Norm.Crossing
import CERW.Support.Norm.Geometry
import CERW.Support.Norm.LocalTime
import CERW.Support.Norm.OuterCrossing
import CERW.Support.Norm.Radial
import CERW.Support.Outer.NearFar
import CERW.Support.Outer.OuterRadius

/-!
# lem:separated-brackets

`lem:separated-brackets` of the revised paper (`limit-shapes.tex:1689-1696`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:separated-brackets`:

```latex
\begin{lemma}\label{lem:separated-brackets}
Let $\gauge$ be the Euclidean norm. Let $0<\drift<\nf1d$. There exist $0<c_0(d,\drift)\leq C_0(d,\drift)$ and $C(d,\drift)<\infty$ such that, for all sufficiently large~$n$, with probability $\geq 1-Cn^{-10}$, simultaneously for $1\leq i\leq m$ and $1\leq j\leq m$ with $j\neq i$,
\begin{equation*}
c_0\leq\langle S^i\rangle_n\leq C_0
\qquad\text{and}\qquad
|\langle S^i,S^j\rangle_n|\leq Cr_n^{-\nf14}\, .
\end{equation*}
\end{lemma}
Definitions the statement relies on (verbatim):
\textit{the radius $r_n$ (eq:radius, lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\nf{1}{(d+1)}}\, ,
\end{equation}
\textit{$g$ and $G$ (line 407)}
Let $\Delta f(x)\coloneqq(2d)^{-1}\sum_{|e|=1}(f(x+e)-f(x))$, summed over the unit vectors $e\in\Z^d$, be the discrete Laplacian. For $d=2$, let $g$ be the potential kernel of simple random walk, normalized by $g(0)=0$. For $d\geq3$, let $g\coloneqq-G$, where the Green function~$G(x)$ is the expected number of visits to~$x$ by simple random walk from the origin. In both cases $\Delta g=\ind_{\{0\}}$. For $d=2$ see \citet*[Proposition~4.4.2]{LawlerLimic2010}. By \citet[Theorems~4.3.1 and~4.4.4]{LawlerLimic2010}, as $|x|\to\infty$,
\textit{$\mathcal M^f$ (lines 422--426)}
For $f\colon\Z^d\to\R$ with bounded nearest-neighbor increments, let
\begin{equation*}
\mathcal M^f_t\coloneqq f(X_t)-f(X_0)-\sum_{j<t}\E\bigl(f(X_{j+1})-f(X_j)\bigm|\mathcal F_j\bigr)
\end{equation*}
be the martingale in Dynkin's formula for~$f$. By~\eqref{eq:kernel}, the conditional expectation in the sum is $\Delta f(X_j)-\drift I_j\xi(X_j)\cdot\bar\nabla f(X_j)$, with $\bar\nabla f$ defined like~$\bar\nabla g$. For $y\in\Z^d$ we write $g_y\coloneqq g(\cdot-y)$ and $\mathcal M^y\coloneqq\mathcal M^{g_y}$. Since $\Delta g_y=\ind_{\{y\}}$ and each site of~$A_n$ has its first departure before time~$n$,
\textit{$\Omega_n$ (line 1532)}
Throughout this section $0<\drift<\nf1d$, and $\Omega_n$ is the intersection of the events of Section~\ref{sec:norm-event} and Lemma~\ref{lem:contact} with $p=10$, so $\P(\Omega_n^c)=O(n^{-10})$ and the estimates of Sections~\ref{sec:local}--\ref{sec:outer} used below hold on~$\Omega_n$ for large~$n$. In particular, by Section~\ref{sec:global-profile}, on~$\Omega_n$ for large~$n$,
\textit{$\sigma_n,k,m,y_i,f_i,S^i$ (lines 1680--1687)}
Recall the martingales~$\mathcal M^f$ of Section~\ref{sec:dynkin} and the function~$\Gamma(f_1,f_2)$ of~\eqref{eq:site-gamma}. Let $\sigma_n\coloneqq(r_n\log r_n)^{\nf12}$ and $k\coloneqq\lfloor r_n^{\nf18}\rfloor$ when $d=2$, and $\sigma_n\coloneqq r_n^{\nf12}$ when $d\geq3$. Let $m\coloneqq\lfloor r_n^{\nf18}\rfloor$, and for $1\leq i\leq m$ let
\begin{equation*}
y_i\coloneqq i\lceil r_n^{\nf14}\rceil e_1\, ,\qquad
f_i\coloneqq\begin{cases}g_{y_i+ke_1}-g_{y_i},&d=2,\\g_{y_i},&d\geq3\end{cases}
\qquad\text{and}\qquad
S^i\coloneqq-\frac{\mathcal M^{f_i}}{\sigma_n}\, .
\end{equation*}
Then $|y_i|\leq m\lceil r_n^{\nf14}\rceil\leq r_n^{\nf12}/2$ for large~$n$.
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.separated_brackets {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let e₁ : Site d := LatticeProb.unit ⟨0, by omega⟩
    let g : Site d → ℝ := CERW.latticeKernel d
    let σ : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (r n * Real.log (r n)) else Real.sqrt (r n)
    let k : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let m : ℕ → ℕ := fun n => ⌊r n ^ ((1 : ℝ) / 8)⌋₊
    let y : ℕ → ℕ → Site d := fun n i => ((i * ⌈r n ^ ((1 : ℝ) / 4)⌉₊ : ℕ) : ℤ) • e₁
    let f : ℕ → ℕ → Site d → ℝ := fun n i z =>
      if d = 2 then g (z - (y n i + (k n : ℤ) • e₁)) - g (z - y n i) else g (z - y n i)
    ∃ c₀ C₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∀ i j : ℕ, 1 ≤ i → i ≤ m n → 1 ≤ j → j ≤ m n →
            let B : ℝ := CERW.dynkinBracket (CERW.stepProb d ε) (f n i) (f n j) (X · ω) n /
              σ n ^ 2
            (i = j → c₀ ≤ B ∧ B ≤ C₀) ∧ (i ≠ j → |B| ≤ C * r n ^ (-(1 : ℝ) / 4))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(10 : ℝ)))
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact (CERW.Support.Lower.separated_brackets_of (CERW.Support.Outer.fluctuation_rates_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) (CERW.Support.Outer.outer_radius_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) CERW.Support.Outer.near_far_holds CERW.Support.Norm.outer_crossing_holds) CERW.Support.Outer.near_far_holds))
