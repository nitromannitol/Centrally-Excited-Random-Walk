import CERW.Model

/-!
# prop:bulk-profile

`prop:bulk-profile` of the revised paper (`limit-shapes.tex:1658-1665`). The bytes between the markers are the
frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

/-- `prop:bulk-profile`:

```latex
\begin{proposition}\label{prop:bulk-profile}
Let $\gauge$ be the Euclidean norm, let $0<\drift<\nf1d$, and let $0<\theta<1$ and $p>0$. There exists $C(d,\drift,\theta,p)<\infty$ such that, for every integer~$n\geq2$, with probability at least $1-Cn^{-p}$,
\begin{equation}\label{eq:bulk-profile}
\max_{\substack{y\in\Z^d\\|y|\leq\theta r_n}}\bigl|\ell_n(y)-2d\drift(r_n-|y|)\bigr|
\leq C\begin{cases}\sqrt{r_n}\log n,&d=2,\\\sqrt{r_n\log n},&d\geq3\end{cases}\, .
\end{equation}
The same bound holds for all sufficiently large~$n$ almost surely.
\end{proposition}
Definitions the statement relies on (verbatim):
\textit{the radius $r_n$ (eq:radius, lines 98--100)}
\begin{equation}\label{eq:radius}
r_n\coloneqq\left(\frac{(d+1)n}{2d\drift\omega_d}\right)^{\nf{1}{d+1}}\, ,
\end{equation}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.bulk_profile {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      let Good : (ℕ → Site d) → ℕ → Prop := fun Y n =>
        ∀ y : Site d, euclidNorm y ≤ θ * r n →
          |(CERW.localTime Y n y : ℝ) - 2 * d * ε * (r n - euclidNorm y)|
            ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n)
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good (X · ω) n)
-- FROZEN-STATEMENT-END
:= by
  sorry
