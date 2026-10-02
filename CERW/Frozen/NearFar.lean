import CERW.Model
import CERW.Support.Outer.NearFar

/-!
# lem:near-far

`lem:near-far` of the revised paper (`limit-shapes.tex:1203-1208`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:near-far`:

```latex
\begin{lemma}\label{lem:near-far}
There exists $C(d,\drift)<\infty$ with the following property. Let $1\leq w\leq b$ and $\lambda\geq1$. Let $D$ be a measurable subset of $\{v\in\R^d:b\leq|v|\leq b+w\}$ such that $|D\cap B((b+w)u,t)|\leq\lambda t^{d-1}$ for every unit vector~$u$ and every $t\geq w$, and $\int_D|v-y|^{2-d}\dd v\leq\lambda b$ for all $y\in\R^d$. Then every $y\in\R^d$ with $b\leq|y|\leq b+w$ satisfies
\begin{equation*}
U_D^+(y)\leq C\bigl(\lambda w^{d-1}\bigr)^{\nf1d}+C\lambda\, .
\end{equation*}
\end{lemma}
Definitions the statement relies on (verbatim):
\textit{$U_D^+$ (lines 1122--1125)}
For a bounded measurable set~$D\subset\R^d$ and $y\in\R^d$, the potential of~$D$ with its negative contributions discarded is
\begin{equation*}
U_D^+(y)\coloneqq\frac{2\drift}{\omega_d}\int_D\left[u_v\cdot\frac{v-y}{|v-y|^d}\right]_+\dd v\, .
\end{equation*}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.near_far {d : ℕ} (hd : 2 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∃ C : ℝ, 0 < C ∧
      ∀ w b lam : ℝ, 1 ≤ w → w ≤ b → 1 ≤ lam →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
        D ⊆ {v | b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w} →
        (∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
          volume (D ∩ Metric.ball ((b + w) • u) t) ≤ ENNReal.ofReal (lam * t ^ (d - 1))) →
        (∀ y : EuclideanSpace ℝ (Fin d), ∫ v in D, ‖v - y‖ ^ (2 - (d : ℝ)) ≤ lam * b) →
        ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
          CERW.positivePotential d ε D y
            ≤ C * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + C * lam
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact CERW.Support.Outer.near_far_holds
