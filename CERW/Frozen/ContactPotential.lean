import CERW.Model
import CERW.Support.Norm.BallLayer
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.Coarse
import CERW.Support.Norm.ContactPotential
import CERW.Support.Norm.Crossing
import CERW.Support.Norm.Geometry
import CERW.Support.Norm.LocalTime
import CERW.Support.Norm.Radial

/-!
# lem:contact

`lem:contact` of the revised paper (`limit-shapes.tex:892-897`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:contact`:

```latex
\begin{lemma}\label{lem:contact}
On the event of Section~\ref{sec:norm-event}, for large~$n$,
\begin{equation*}
H\leq Cr_nq_n=C\begin{cases}\sqrt{r_n\log n},&d=2,\\\log n,&d\geq3\end{cases}\, .
\end{equation*}
\end{lemma}
Definitions the statement relies on (verbatim): $q_n$ (eq:qn, lines 763--766), the event of Section~\ref{sec:norm-event}
(line 841), and the inner radius $b$, the set $E$, the contact point $y_0$ and $H$ (lines 852--860).
Throughout the rest of the paper let
\begin{equation}\label{eq:qn}
q_n\coloneqq\begin{dcases}\sqrt{\frac{\log n}{r_n}},&d=2,\\\frac{\log n}{r_n},&d\geq3\end{dcases}\, .
\end{equation}
\begin{quote}
Intersect the events of Proposition~\ref{prop:coarse} and Lemma~\ref{lem:local} with the events on which~\eqref{eq:vector}, \eqref{eq:localmart}, \eqref{eq:quadratic-coarse} and~\eqref{eq:linear-mart} hold; the complement has probability at most $Cn^{-p}$, and everything below is deterministic on this event. Let $K$ be a constant with $\Rout(n)\leq(K-1)r_n$ on the event of Proposition~\ref{prop:coarse}; then $D_n\subset B(0,Kr_n)$ for large~$n$, and~\eqref{eq:quadratic-coarse} gives
\end{quote}
Let
\begin{equation*}
b\coloneqq\inf\{\gauge(y):y\in\R^d\setminus D_n\}\qquad\text{and}\qquad
E\coloneqq D_n\setminus\{\gauge<b\}\, ,
\end{equation*}
so that $\{\gauge<b\}\subset D_n$. Choose a point~$y_0$ with $\gauge(y_0)=b$ that is the limit of a sequence of points outside~$D_n$. Since the sequence is bounded, some cell~$C_z$ disjoint from~$D_n$ contains infinitely many of its points. Then $\ell_n(z)=0$, the closure of~$C_z$ contains~$y_0$, and $\gauge(z)\geq b$ because $z\in C_z$. Let
\begin{equation*}
H\coloneqq U_{D_n}(y_0)\qquad\text{and}\qquad \mathcal I\coloneqq\int_E(\gauge(v)-b)\dd v\, .
\end{equation*}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.contact_potential {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    let q : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∀ y₀ : EuclideanSpace ℝ (Fin d),
            Ψ y₀ = CERW.normInnerRadius Ψ (X · ω) n →
            y₀ ∈ closure (CERW.cellSet (X · ω) n)ᶜ →
            CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y₀ ≤ C * r n * q n}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact (CERW.Support.Norm.contact_potential_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) (CERW.Support.Norm.norm_coarse_bounds_of (CERW.Support.Norm.norm_local_time_potential_of CERW.Support.Norm.cell_gradient_holds) CERW.Support.Norm.norm_radial_test_holds @CERW.Support.Norm.drift_crossing) @CERW.Support.Norm.norm_potential_geometry @CERW.Support.Norm.norm_ball_potential)
