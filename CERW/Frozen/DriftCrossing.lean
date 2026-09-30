import CERW.Model
import CERW.Support.Norm.Crossing

/-!
# lem:crossing

`lem:crossing` of the revised paper (`limit-shapes.tex:661-666`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:crossing`:

```latex
\begin{lemma}\label{lem:crossing}
On the event in~\eqref{eq:vector}, the following holds for every unit vector~$u$ and all integers $0\leq s<t\leq n$. If $u\cdot\xi(X_j)\geq0$ at every first departure time~$j$ with $s\leq j<t$, then
\begin{equation*}
u\cdot(X_t-X_s)\leq C\sqrt{(t-s)\log n}\, .
\end{equation*}
\end{lemma}
The martingale $Z$ and the event of the lemma (verbatim, lines 651--659):
A crossing against the drift requires a large increment of the martingale
\begin{equation}\label{eq:vector-def}
Z_t\coloneqq X_t+\drift\sum_{j<t}I_j\xi(X_j)\, ,
\end{equation}
which takes values in~$\R^d$ and has bounded increments. Azuma's inequality in each coordinate and a union bound over the pairs $s<t$ give, for every $p>0$, with probability at least $1-Cn^{-p}$,
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
