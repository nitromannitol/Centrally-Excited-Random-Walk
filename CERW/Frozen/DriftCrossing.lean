import CERW.Model
import CERW.Support.Norm.Crossing

/-!
# lem:crossing

`lem:crossing` of the revised paper (`limit-shapes.tex:662-667`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:crossing`:

```latex
\begin{lemma}\label{lem:crossing}
Let $\drift\geq0$, let $\xi\colon\Z^d\to\R^d$ be a function, let $X_0,X_1,\ldots$ be a sequence of sites of~$\Z^d$, let $C$ be a real number, and let $n\geq2$ be an integer. Assume that $Z$, defined by~\eqref{eq:vector-def} with $A_j$ and $I_j=\ind_{\{X_j\notin A_j\}}$ formed from this sequence, satisfies~\eqref{eq:vector}. Let $u$ be a unit vector. Let $0\leq s<t\leq n$ be integers such that $u\cdot\xi(X_j)\geq0$ for all $s\leq j<t$ with $I_j=1$. Then
\begin{equation*}
u\cdot(X_t-X_s)\leq C\sqrt{(t-s)\log n}\, .
\end{equation*}
\end{lemma}
The martingale $Z$ and the event of the lemma (verbatim, lines 652--660):
A crossing against the drift requires a large increment of the martingale
\begin{equation}\label{eq:vector-def}
Z_t\coloneqq X_t+\drift\sum_{j<t}I_j\xi(X_j)\, ,
\end{equation}
which takes values in~$\R^d$ and has bounded increments. By Azuma's inequality in each coordinate and a union bound over the pairs $s<t$, we have, for all $p>0$, with probability at least $1-Cn^{-p}$,
\begin{equation}\label{eq:vector}
|Z_t-Z_s|\leq C\sqrt{(t-s)\log n}
\qquad\text{for } 0\leq s<t\leq n\, .
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.drift_crossing {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ) (C : ℝ) :
    let Z : ℕ → EuclideanSpace ℝ (Fin d) := fun t => CERW.toSpace (x t) + ε •
      ∑ j ∈ Finset.range t, if x j ∉ CERW.departureRange x j then ξ (x j) else 0
    (∀ s t : ℕ, s < t → t ≤ n → ‖Z t - Z s‖ ≤ C * Real.sqrt ((t - s : ℝ) * Real.log n)) →
    ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ s t : ℕ, s < t → t ≤ n →
      (∀ j : ℕ, s ≤ j → j < t → x j ∉ CERW.departureRange x j → 0 ≤ inner ℝ u (ξ (x j))) →
      inner ℝ u (CERW.toSpace (x t) - CERW.toSpace (x s))
        ≤ C * Real.sqrt ((t - s : ℝ) * Real.log n)
-- FROZEN-STATEMENT-END
:= by
  revert C n x ξ hε ε d
  exact @CERW.Support.Norm.drift_crossing
