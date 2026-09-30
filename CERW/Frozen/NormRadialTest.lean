import CERW.Model
import CERW.Support.Norm.Radial

/-!
# lem:radial

`lem:radial` of the revised paper (`limit-shapes.tex:566-575`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `lem:radial`:

```latex
\begin{lemma}\label{lem:radial}
Let $p>0$. There exist $\rho_0(d,\gauge)>8d$ and $C(d,\drift,\gauge,p)<\infty$ such that, for every integer~$n\geq2$, with probability at least $1-Cn^{-p}$, the following holds simultaneously for all integers~$\rho_0\leq\rho\leq n$:
\begin{equation}\label{eq:radial}
\begin{split}
F(\rho+4d)\leq{}&C\Bigl(\max_{||x|-\rho|\leq3}\ell_n(x)\Bigr)
[F(\rho-4d)-F(\rho+4d)]\\
&+C\Bigl(\max_{|x|\geq\rho-4d}\ell_n(x)\cdot\rho^{1-d}F(\rho-4d)\log n\Bigr)^{\nf12}+C\rho^{1-d}\log n\, .
\end{split}
\end{equation}
\end{lemma}
Definitions the statement relies on (verbatim): the weighted exterior volume $F$ (eq:Fdef, lines 503--506) and the
constants convention (line 295).
\begin{equation}\label{eq:Fdef}
F(s)\coloneqq\frac1{d\omega_d}\int_{D\cap\{|v|>s\}}|v|^{1-d}\dd v
\leq\frac{|D|}{d\omega_ds^{d-1}}\, .
\end{equation}
\begin{itemize}
\item The letters $c>0$ and $C>0$ denote constants depending only on $d$, $\drift$ and the exponent~$p$ of the failure probability under discussion, and in Sections~\ref{sec:norm-setup}--\ref{sec:norms} also on the norm~$\gauge$, but not on the choice of the subgradients~$\xi(x)$; they may change from line to line. Every further dependence is stated, and a subscript on~$O$, as in~$O_y$, means that the implied constant also depends on~$y$. We write $a_n\asymp b_n$ if $c\leq a_n/b_n\leq C$, and $O_{\P}(a_n)$ for random variables~$Y_n$ such that $Y_n/a_n$ is tight.
\end{itemize}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.norm_radial_test {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∃ ρ₀ : ℝ, 8 * d < ρ₀ ∧
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ ρ : ℕ, ρ₀ ≤ ρ → ρ ≤ n →
            CERW.tail d (CERW.cellSet (X · ω) n) ((ρ : ℝ) + 4 * d)
              ≤ C * (CERW.shellMax (X · ω) n ρ : ℝ)
                  * (CERW.tail d (CERW.cellSet (X · ω) n) ((ρ : ℝ) - 4 * d)
                    - CERW.tail d (CERW.cellSet (X · ω) n) ((ρ : ℝ) + 4 * d))
                + C * Real.sqrt
                    (((((CERW.departureRange (X · ω) n).filter
                        (fun x => (ρ : ℝ) - 4 * d ≤ euclidNorm x)).sup
                        (CERW.localTime (X · ω) n) : ℕ) : ℝ)
                      * (ρ : ℝ) ^ (1 - (d : ℝ))
                      * CERW.tail d (CERW.cellSet (X · ω) n) ((ρ : ℝ) - 4 * d) * Real.log n)
                + C * (ρ : ℝ) ^ (1 - (d : ℝ)) * Real.log n}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  revert hd d
  exact CERW.Support.Norm.norm_radial_test_holds
