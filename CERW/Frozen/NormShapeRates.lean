import CERW.Model
import CERW.Support.Norm.BallLayer
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.Coarse
import CERW.Support.Norm.ContactPotential
import CERW.Support.Norm.Crossing
import CERW.Support.Norm.Geometry
import CERW.Support.Norm.LocalTime
import CERW.Support.Norm.MoreauCap
import CERW.Support.Norm.OuterCrossing
import CERW.Support.Norm.Radial
import CERW.Support.Norm.ShapeRates

/-!
# prop:norm-shape

`prop:norm-shape` of the revised paper (`limit-shapes.tex:746-762`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `prop:norm-shape`:

```latex
\begin{proposition}\label{prop:norm-shape}
Let $\gauge$ be a norm, let $\xi(x)\in\partial \gauge(x)$ be subgradients chosen at the sites $x\in\Z^d\setminus\{0\}$, and let $\drift>0$ satisfy~\eqref{eq:ellipticity}. For every $p>0$ there exists $C(d,\drift,\gauge,p)<\infty$, not depending on the choice of the subgradients, such that, for every integer~$n\geq2$, with probability at least $1-Cn^{-p}$ the following hold simultaneously.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Radii}}:
\begin{equation}\label{eq:norm-shape}
\Bigl|\inf_{y\notin D_n}\gauge(y)-r_n\Bigr|\leq C\begin{cases}r_n^{\nf34}(\log n)^{\nf14},&d=2,\\(r_n\log n)^{\nf12},&d\geq3\end{cases}
\end{equation}
and
\begin{equation}\label{eq:norm-outer}
\max_{0\leq j\leq n}\gauge(X_j)-r_n\leq C\begin{cases}r_n^{\nf56}(\log n)^{\nf76},&d=2,\\r_n^{\nf{d}{(d+1)}}(\log n)^{\nf{(d+2)}{(d+1)}},&d\geq3\end{cases}\, .
\end{equation}
\item \underline{\emph{Local times}}:
\begin{equation}\label{eq:norm-local}
\max_{x\in\Z^d}|\ell_n(x)-2d\drift(r_n-\gauge(x))_+|\leq C\begin{cases}r_n^{\nf56}(\log n)^{\nf16},&d=2,\\r_n^{\nf{d}{(d+1)}}(\log n)^{\nf{1}{(d+1)}},&d\geq3\end{cases}\, .
\end{equation}
\end{enumerate}
\end{proposition}
Definitions the statement relies on (verbatim): $r_n$ (lines 323--325), $D_n,\Rin,\Rout$ (lines 122--127).
\begin{equation}\label{eq:radius-norm}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift|B_\gauge|}\right)^{\nf{1}{(d+1)}}\, ,
\end{equation}
Replace each site~$x\in A_n$ by the unit cell~$C_x\coloneqq x+[-\nf12,\nf12)^d$. Let $D_n\coloneqq\bigcup_{x\in A_n}C_x$. The \defn{inner radius} and the \defn{outer radius} are
\begin{equation}\label{eq:radii}
\Rin(n)\coloneqq\inf_{y\notin D_n}|y|
\qquad\text{and}\qquad
\Rout(n)\coloneqq\max_{0\leq j\leq n}|X_j|\, .
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.norm_shape_rates {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (|CERW.normInnerRadius Ψ (X · ω) n - r n|
                    ≤ C * (if d = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
                      else (r n * Real.log n) ^ ((1 : ℝ) / 2)) ∧
                  CERW.normMaxRadius Ψ (X · ω) n - r n
                    ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
                      else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) ∧
                  ∀ x : Site d,
                    |(CERW.localTime (X · ω) n x : ℝ)
                        - 2 * d * ε * max (r n - Ψ (CERW.toSpace x)) 0|
                      ≤ C * (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
                        else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact (CERW.Support.Norm.norm_shape_rates_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.layer_potential @CERW.Support.Norm.moreau_cap CERW.Support.Norm.outer_crossing_holds @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential)
