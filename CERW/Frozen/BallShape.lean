import CERW.Support.LocalTime.KernelAsymptotics
import CERW.Support.Main.KernelAnchors

/-!
# The ball shape theorem

`thm:shape` of the paper (`paper/cerw-flat.tex:135-160`). The bytes between
the markers are the frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

/-- `thm:shape` (`cerw-flat.tex:135-160`):

```latex
\begin{theorem}[Ball shape]\label{thm:shape}
Let $d\geq2$ be an integer, let $0<\eps<1/d$, and let $(X_n)_{n\geq0}$
be centrally excited random walk on $\Z^d$, started at the origin,
with first-departure probabilities
$q_x(\pm e_i)=1/(2d)\mp\eps x_i/(2|x|)$ for $x\ne0$ and simple
random walk steps on every other departure. Let
$a=((d+1)/(2d\eps\omega_d))^{1/(d+1)}$ and $N=n^{1/(d+1)}$.
Then the following statements hold almost surely.
\begin{enumerate}[label=\textup{(\roman*)}]
\item For every $0<\eta<a$, for all sufficiently large integers $n$,
\begin{equation}\label{eq:shape}
B(0,(a-\eta)N)\cap\Z^d\subseteq A_n\subseteq V_n
\subseteq B(0,(a+\eta)N)\cap\Z^d\, .
\end{equation}
\item The departure local times satisfy
\begin{equation}\label{eq:profile-limit}
\sup_{x\in\Z^d}\left|
\frac{\ell_n(x)}N-2d\eps\left(a-\frac{|x|}N\right)_+
\right|\longrightarrow0\, .
\end{equation}
\item The range satisfies $|V_n|/N^d\longrightarrow\omega_da^d$.
For every fixed $x\in\Z^d$, the local time satisfies
$\ell_n(x)/N\longrightarrow2d\eps a$; in particular, every vertex
is visited infinitely often.
\end{enumerate}
\end{theorem}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.ball_shape {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < a → ∀ᶠ n in atTop,
        {x : Site d | euclidNorm x < (a - η) * N n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆ ↑(CERW.visitedRange (X · ω) n) ∧
        (↑(CERW.visitedRange (X · ω) n) : Set (Site d)) ⊆
          {x | euclidNorm x < (a + η) * N n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) / N n - 2 * d * ε * max (a - euclidNorm x / N n) 0|
          ≤ η) ∧
      Tendsto (fun n => ((CERW.visitedRange (X · ω) n).card : ℝ) / N n ^ d) atTop
        (𝓝 (ωd * a ^ d)) ∧
      (∀ x : Site d,
        Tendsto (fun n => (CERW.localTime (X · ω) n x : ℝ) / N n) atTop (𝓝 (2 * d * ε * a))) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x)
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨b, h, hF⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  exact CERW.Support.Main.ball_shape_of_kernelFacts hd hF hε hεd μ X hX
