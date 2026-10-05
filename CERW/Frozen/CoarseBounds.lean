import CERW.Support.Norm.EuclideanCoarse

/-!
# The occupation and radius bounds

`prop:coarse` of the paper (`limit-shapes.tex:547-554`, Euclidean case). The bytes between
the markers are the frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

/-- `prop:coarse` (`limit-shapes.tex:547-554`, Euclidean case):

```latex
\begin{proposition}\label{prop:coarse}
Let $d\geq2$ be an integer, let $0<\eps<1/d$, and let $(X_j)_{j\geq0}$ be centrally
excited random walk on $\Z^d$, started at the origin, with first-departure probabilities
$q_x(\pm e_i)=1/(2d)\mp\eps u_x^i/2$ and simple random walk steps
on subsequent departures and at the origin. For every $p>0$, there are constants
$c,C>0$, depending only on $d,\eps,p$, such that for every integer
$n\geq2$, with probability at least $1-Cn^{-p}$,
\begin{equation}\label{eq:coarse}
cN^d\leq R_n\leq CN^d ,\qquad
cN\leq M_n\leq CN ,\qquad cN\leq H_n\leq CN\, ,
\end{equation}
where $N=n^{1/(d+1)}$, $R_n$ counts distinct departure sites,
$M_n$ is the maximum departure local time, and
$H_n=\max_{j\leq n}|X_j|$.
\end{proposition}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.coarse_bounds {d : ℕ} (hd : 2 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        μ {ω | ¬ (c * N ^ d ≤ ((CERW.departureRange (X · ω) n).card : ℝ) ∧
                  ((CERW.departureRange (X · ω) n).card : ℝ) ≤ C * N ^ d ∧
                  c * N ≤ (CERW.maxLocalTime (X · ω) n : ℝ) ∧
                  (CERW.maxLocalTime (X · ω) n : ℝ) ≤ C * N ∧
                  c * N ≤ CERW.maxRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ C * N)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  exact CERW.Support.Norm.EuclideanCoarse.coarse_bounds_euclid hd
