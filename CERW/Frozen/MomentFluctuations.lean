import CERW.External.MartingaleCLT
import CERW.External.StoutLIL
import CERW.Support.Stout
import CERW.Model
import CERW.Support.Inner.InnerRadius
import CERW.Support.Limit.MomentFluctuations
import CERW.Support.Lower.ExpDeviation
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
# thm:moment-fluctuations

`thm:moment-fluctuations` of the revised paper (`limit-shapes.tex:1353-1374`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `thm:moment-fluctuations`:

```latex
\begin{theorem}[Sum of the distances from the origin]\label{thm:moment-fluctuations}
Let $\gauge$ be the Euclidean norm, let $0<\drift<\nf1d$, and let $\Rmom(n)$ be as in~\eqref{eq:radial-moment-def}. Then the following hold.
\begin{enumerate}[label=\textup{(\roman*)}]
\item \underline{\emph{Central limit theorem}}: as $n\to\infty$,
\begin{equation*}
\frac{\sum_{x\in A_n}|x|-n/(2\drift)}{r_n^{\nf{(d+3)}{2}}}
\xrightarrow{\mathrm d}\mathcal N\Bigl(0,\frac{2d\omega_d}{\drift(d+2)(d+3)}\Bigr)
\end{equation*}
and
\begin{equation*}
\frac{\Rmom(n)-r_n}{r_n^{\nf{(3-d)}{2}}}
\xrightarrow{\mathrm d}\mathcal N\Bigl(0,\frac{2}{\drift d\omega_d(d+2)(d+3)}\Bigr)\, .
\end{equation*}
\item \underline{\emph{Law of the iterated logarithm}}: for each choice of sign, almost surely,
\begin{align}
\limsup_{n\to\infty}\frac{\pm\bigl(\sum_{x\in A_n}|x|-n/(2\drift)\bigr)}{r_n^{\nf{(d+3)}{2}}\sqrt{2\log\log n}}
&=\Bigl(\frac{2d\omega_d}{\drift(d+2)(d+3)}\Bigr)^{\nf12}\, ,\notag\\
\limsup_{n\to\infty}\frac{\pm(\Rmom(n)-r_n)}{r_n^{\nf{(3-d)}{2}}\sqrt{2\log\log n}}
&=\Bigl(\frac{2}{\drift d\omega_d(d+2)(d+3)}\Bigr)^{\nf12}\, .\label{eq:moment-radius-lil}
\end{align}
\end{enumerate}
\end{theorem}
Definitions the statement relies on (verbatim):
\textit{the radius $r_n$ (eq:radius, lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\nf{1}{(d+1)}}\, ,
\end{equation}
\textit{$\mathcal Q_n$ and $\Rmom$ (eq:moment-martingale, eq:radial-moment-def, lines 1344--1351)}
For the Euclidean norm, \eqref{eq:quadratic} reads
\begin{equation}\label{eq:moment-martingale}
\mathcal Q_n=2\drift\sum_{x\in A_n}|x|-n+|X_n|^2\, .
\end{equation}
Let $\Rmom(n)$ be the radius of the centered ball on which the integral of~$|v|$ equals $\sum_{x\in A_n}|x|$, that is,
\begin{equation}\label{eq:radial-moment-def}
\Rmom(n)\coloneqq\left(\frac{d+1}{d\omega_d}\sum_{x\in A_n}|x|\right)^{\nf{1}{(d+1)}}\, .
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.moment_fluctuations {d : ℕ} (hd : 2 ≤ d)
    (hCLT : CERW.External.MartingaleCLT.{u}) (hLIL : CERW.External.StoutLIL.{u}) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let v₁ : ℝ := 2 * d * ωd / (ε * (d + 2) * (d + 3))
    let v₂ : ℝ := 2 / (ε * d * ωd * (d + 2) * (d + 3))
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      let S : ℕ → Ω → ℝ := fun n ω =>
        (∑ x ∈ CERW.departureRange (X · ω) n, euclidNorm x - n / (2 * ε)) /
          r n ^ (((d : ℝ) + 3) / 2)
      let R : ℕ → Ω → ℝ := fun n ω =>
        (CERW.momentRadius (X · ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2)
      TendstoInDistribution S atTop id (fun _ => μ) (gaussianReal 0 v₁.toNNReal) ∧
      TendstoInDistribution R atTop id (fun _ => μ) (gaussianReal 0 v₂.toNNReal) ∧
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
        (∀ᶠ n : ℕ in atTop, σ * S n ω ≤ (Real.sqrt v₁ + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
        (∃ᶠ n : ℕ in atTop, (Real.sqrt v₁ - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * S n ω) ∧
        (∀ᶠ n : ℕ in atTop, σ * R n ω ≤ (Real.sqrt v₂ + δ) * Real.sqrt (2 * Real.log (Real.log n))) ∧
        (∃ᶠ n : ℕ in atTop, (Real.sqrt v₂ - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * R n ω)
-- FROZEN-STATEMENT-END
:= by
  replace hLIL : CERW.Support.Statements.StoutLIL.{u} := CERW.Support.stoutLIL_full hLIL
  revert hLIL hCLT hd d
  exact (CERW.Support.Limit.moment_fluctuations_of @CERW.Support.Main.limit_shape (CERW.Support.Outer.fluctuation_rates_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) (CERW.Support.Outer.outer_radius_of (CERW.Support.Inner.inner_radius_of (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential) @CERW.Support.Norm.norm_ball_potential @CERW.Support.Norm.norm_potential_geometry) CERW.Support.Outer.near_far_holds CERW.Support.Norm.outer_crossing_holds) CERW.Support.Outer.near_far_holds))
