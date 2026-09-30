import CERW.External.LatticePotentialKernel
import CERW.Support.LocalTime.KernelExternal
import CERW.Support.Main.KernelAnchors

/-!
# The fluctuation bounds

`thm:fluctuations` of the paper (`paper/cerw-flat.tex:186-213`). The bytes between
the markers are the frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

/-- `thm:fluctuations` (`cerw-flat.tex:186-213`):

```latex
\begin{theorem}[Fluctuation bounds]\label{thm:fluctuations}
Let $d\geq2$ be an integer, let $0<\eps<1/d$, and let $(X_n)_{n\geq0}$
be centrally excited random walk on $\Z^d$, started at the origin,
with first-departure probabilities
$q_x(\pm e_i)=1/(2d)\mp\eps x_i/(2|x|)$ for $x\ne0$ and simple
random walk steps on every other departure. Let
$a=((d+1)/(2d\eps\omega_d))^{1/(d+1)}$, let $N=n^{1/(d+1)}$, and let
$Q=(\log(n+2)/N)^{1/2}$ for $d=2$ and
$Q=(\log(n+2)/N)^{d/(2d-1)}$ for $d\geq3$.
For every $p>0$, there are constants $C,n_0>0$, depending only on
$d,\eps,p$, such that for every integer $n\geq n_0$, with probability
at least $1-Cn^{-p}$,
\begin{equation}\label{eq:sandwich}
B(0,(a-CQ)N)\cap\Z^d\subseteq A_n\subseteq V_n
\subseteq B(0,(a+CQ^{1/d}L)N)\cap\Z^d\, ,
\end{equation}
where $L=\log(n+2)$. On the same event,
\begin{align}
|(D_n/N)\mathbin{\triangle}B(0,a)|
+\left|\frac{|A_n|}{N^d}-\omega_da^d\right|&\leq CQ\, ,
\label{eq:volume}\\
\sup_{x\in\Z^d}\left|
\frac{\ell_n(x)}N-2d\eps(a-|x|/N)_+\right|&\leq CQ^{1/d}\, .
\label{eq:profile-rate}
\end{align}
All these bounds hold eventually almost surely, with deterministic
constants and a finite random starting time.
\end{theorem}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.fluctuation_bounds {d : ℕ} (hd : 2 ≤ d)
    (hK : CERW.External.LatticePotentialKernel d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    let L : ℕ → ℝ := fun n => Real.log (n + 2)
    let Q : ℕ → ℝ := fun n =>
      if d = 2 then (L n / N n) ^ ((1 : ℝ) / 2) else (L n / N n) ^ ((d : ℝ) / (2 * d - 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      {x : Site d | euclidNorm x < (a - C * Q n) * N n} ⊆ ↑(CERW.departureRange Y n) ∧
      (↑(CERW.departureRange Y n) : Set (Site d)) ⊆ ↑(CERW.visitedRange Y n) ∧
      (↑(CERW.visitedRange Y n) : Set (Site d)) ⊆
        {x | euclidNorm x < (a + C * Q n ^ ((1 : ℝ) / d) * L n) * N n} ∧
      volume (((N n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a)
          + ENNReal.ofReal |((CERW.departureRange Y n).card : ℝ) / N n ^ d - ωd * a ^ d|
        ≤ ENNReal.ofReal (C * Q n) ∧
      ∀ x : Site d,
        |(CERW.localTime Y n x : ℝ) / N n - 2 * d * ε * max (a - euclidNorm x / N n) 0|
          ≤ C * Q n ^ ((1 : ℝ) / d)
    (∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Good C (X · ω) n)
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨b, h, hF⟩ := CERW.Support.LocalTime.exists_kernelFacts hd hK
  exact CERW.Support.Main.fluctuation_bounds_of_kernelFacts hd hF
