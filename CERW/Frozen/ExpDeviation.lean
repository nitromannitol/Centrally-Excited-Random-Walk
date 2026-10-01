import CERW.Model
import CERW.Support.Lower.ExpDeviation

/-!
# lem:exp-deviation

`lem:exp-deviation` of the revised paper (`limit-shapes.tex:1537-1551`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:exp-deviation`:

```latex
\begin{lemma}\label{lem:exp-deviation}
Let $0<c_0\leq C_0$. There exist $c(c_0,C_0)>0$ and $C(c_0,C_0)<\infty$ with the following property. Let $m$ and~$n$ be positive integers, let $b>0$, $\delta\geq0$ and $0\leq\alpha\leq1$, and let $S^1,\ldots,S^m$ be real martingales with respect to a common filtration, with $S^i_0=0$ and $|S^i_{t+1}-S^i_t|\leq b$ for $0\leq t<n$. Let $\Omega$ be an event with $\P(\Omega)\geq1-\alpha$ on which $c_0\leq\langle S^i\rangle_n\leq C_0$ for $1\leq i\leq m$. Then, for every real $\beta\geq C$ with $\beta b\leq c$, the following hold.
\begin{enumerate}[label=\textup{(\roman*)}]
\item For $1\leq i\leq m$,
\begin{equation*}
\P(S^i_n\geq c\beta)\geq\frac14e^{-C\beta^2}-\alpha
\qquad\text{and}\qquad
\P(S^i_n\leq-c\beta)\geq\frac14e^{-C\beta^2}-\alpha\, .
\end{equation*}
\item If $|\langle S^i,S^j\rangle_n|\leq\delta$ on~$\Omega$ for all $i\neq j$, and $\beta^2\delta+\beta^3b\leq1$, then
\begin{equation*}
\P\Bigl(\max_{1\leq i\leq m}S^i_n<c\beta\Bigr)\leq C\bigl(m^{-1}e^{C\beta^2}+\beta^2\delta+\beta^3b+e^{C\beta^2}\sqrt\alpha\bigr)\, .
\end{equation*}
\end{enumerate}
\end{lemma}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.exp_deviation :
    ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ C₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (m n : ℕ), 0 < m → 0 < n →
      ∀ b δ α : ℝ, 0 < b → 0 ≤ δ → 0 ≤ α → α ≤ 1 →
      ∀ S : Fin m → ℕ → Ω → ℝ, (∀ i, Martingale (S i) ℱ μ) → (∀ i ω, S i 0 ω = 0) →
        (∀ i, ∀ t < n, ∀ ω, |S i (t + 1) ω - S i t ω| ≤ b) →
      ∀ E : Set Ω, MeasurableSet E → 1 - α ≤ (μ E).toReal →
        (∀ i, ∀ᵐ ω ∂μ, ω ∈ E →
          c₀ ≤ CERW.predBracket μ ℱ (S i) (S i) n ω ∧
            CERW.predBracket μ ℱ (S i) (S i) n ω ≤ C₀) →
      ∀ β : ℝ, C ≤ β → β * b ≤ c →
        (∀ i, Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | c * β ≤ S i n ω}).toReal ∧
          Real.exp (-(C * β ^ 2)) / 4 - α ≤ (μ {ω | S i n ω ≤ -(c * β)}).toReal) ∧
        ((∀ i j, i ≠ j → ∀ᵐ ω ∂μ, ω ∈ E → |CERW.predBracket μ ℱ (S i) (S j) n ω| ≤ δ) →
          β ^ 2 * δ + β ^ 3 * b ≤ 1 →
          (μ {ω | ∀ i, S i n ω < c * β}).toReal
            ≤ C * ((m : ℝ)⁻¹ * Real.exp (C * β ^ 2) + β ^ 2 * δ + β ^ 3 * b
              + Real.exp (C * β ^ 2) * Real.sqrt α))
-- FROZEN-STATEMENT-END
:= by
  exact @CERW.Support.Lower.exp_deviation
