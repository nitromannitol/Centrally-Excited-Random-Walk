import CERW.Support.LocalTime.KernelAsymptotics
import CERW.Support.LocalTime.LocalAssembly

/-!
# The local-time potential

`lem:local` of the paper (`limit-shapes.tex:385-401`, Euclidean case). The bytes between
the markers are the frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

/-- `lem:local` (`limit-shapes.tex:385-401`, Euclidean case):

```latex
\begin{lemma}\label{lem:local}
Let $d\geq2$ be an integer, let $0<\eps<1/d$, and let $(X_j)_{j\geq0}$ be
centrally excited random walk started at the origin, with first-departure mean $-\eps u_x$
and probabilities $q_x(\pm e_i)=1/(2d)\mp\eps u_x^i/2$,
with simple symmetric steps on later departures and at the origin.
For every $p>0$ there is $C=C(d,\eps,p)$ such that, for every integer
$n\geq2$, with probability at least $1-Cn^{-p}$, the following estimates
hold simultaneously:
\begin{align}
M_n&\leq C_d\eps R_n^{1/d}+C\lambda_n\, ,\label{eq:M}\\
M_{s,t}&\leq C_d\eps k_{s,t}^{1/d}+C\lambda_n
\qquad(0\leq s<t\leq n)\, ,\label{eq:interval}\\
|\widetilde\ell_n(y)-U_{D_n}(y)|&\leq C e_n(M_n)
\qquad(y\in\R^d,\ |y|\leq2n)\, .\label{eq:approx}
\end{align}
Here $U_D(y)=(2\eps/\omega_d)\int_D u_v\cdot(v-y)|v-y|^{-d}\dd v$,
$L=\log(n+2)$, and $\lambda_n,e_n$ have the values displayed above.
\end{lemma}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.local_time_potential {d : ℕ} (hd : 2 ≤ d) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p →
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let L : ℝ := Real.log (n + 2)
        let lam : ℝ := if d = 2 then L ^ 2 else L
        let e : ℝ → ℝ := fun m =>
          if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L
        μ {ω | ¬ ((CERW.maxLocalTime (X · ω) n : ℝ)
                    ≤ Cd * ε * ((CERW.departureRange (X · ω) n).card : ℝ) ^ ((1 : ℝ) / d)
                      + C * lam ∧
                  (∀ s t : ℕ, s < t → t ≤ n →
                    (CERW.intervalMax (X · ω) s t : ℝ)
                      ≤ Cd * ε * (CERW.freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / d) + C * lam) ∧
                  ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
                    |CERW.cellLocalTime (X · ω) n y
                        - CERW.potential d ε (CERW.cellSet (X · ω) n) y|
                      ≤ C * e (CERW.maxLocalTime (X · ω) n))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨b, h, hF⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  exact CERW.Support.LocalTime.local_time_potential_of_kernelFacts hd hF
