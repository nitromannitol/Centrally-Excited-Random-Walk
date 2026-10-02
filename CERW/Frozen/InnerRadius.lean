import CERW.Model
import CERW.Support.Inner.InnerRadius
import CERW.Support.Norm.BallLayer
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.Coarse
import CERW.Support.Norm.ContactPotential
import CERW.Support.Norm.Crossing
import CERW.Support.Norm.Geometry
import CERW.Support.Norm.LocalTime
import CERW.Support.Norm.Radial

/-!
# prop:inner

`prop:inner` of the revised paper (`limit-shapes.tex:1060-1076`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `prop:inner`:

```latex
\begin{proposition}[Inner radius]\label{prop:inner}
Let $\gauge$ be the Euclidean norm. Let $0<\drift<\nf1d$. For every $p>0$ there exists $C(d,\drift,p)<\infty$ such that, for every integer~$n\geq2$, with probability at least $1-Cn^{-p}$, the following hold simultaneously, where $q_n$ is defined in~\eqref{eq:qn}.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Inner radius}}:
\begin{equation}\label{eq:inradius}
|\Rin(n)-r_n|\leq Cr_nq_n\, .
\end{equation}
\item \underline{\emph{Volume}}:
\begin{equation*}
\bigl|r_n^{-1}D_n\mathbin{\triangle}B(0,1)\bigr|\leq Cq_n\, .
\end{equation*}
\item \underline{\emph{Local times}}:
\begin{equation*}
\sup_{y\in\R^d}\bigl|\widetilde\ell_n(y)-2d\drift(r_n-|y|)_+\bigr|\leq Cr_nq_n^{\nf1d}\, .
\end{equation*}
\end{enumerate}
\end{proposition}
Definitions the statement relies on (verbatim):
\textit{the radius $r_n$ (eq:radius, lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\nf{1}{(d+1)}}\, ,
\end{equation}
\textit{$D_n$, $\Rin$, $\Rout$ (eq:radii, lines 122--127)}
Replace each site~$x\in A_n$ by the unit cell~$C_x\coloneqq x+[-\nf12,\nf12)^d$. Let $D_n\coloneqq\bigcup_{x\in A_n}C_x$. The \defn{inner radius} and the \defn{outer radius} are
\begin{equation}\label{eq:radii}
\Rin(n)\coloneqq\inf_{y\notin D_n}|y|
\qquad\text{and}\qquad
\Rout(n)\coloneqq\max_{0\leq j\leq n}|X_j|\, .
\end{equation}
\textit{$q_n$ (eq:qn, lines 764--767)}
Throughout the rest of the paper let
\begin{equation}\label{eq:qn}
q_n\coloneqq\begin{dcases}\sqrt{\frac{\log n}{r_n}},&d=2,\\\frac{\log n}{r_n},&d\geq3\end{dcases}\, .
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.inner_radius {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let q : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (|CERW.innerRadius (X · ω) n - r n| ≤ C * r n * q n ∧
                  volume (((r n)⁻¹ • CERW.cellSet (X · ω) n) ∆
                      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
                    ≤ ENNReal.ofReal (C * q n) ∧
                  ∀ y : EuclideanSpace ℝ (Fin d),
                    |CERW.cellLocalTime (X · ω) n y - 2 * d * ε * max (r n - ‖y‖) 0|
                      ≤ C * r n * q n ^ ((1 : ℝ) / d))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry)
