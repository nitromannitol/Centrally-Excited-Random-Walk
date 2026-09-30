import CERW.Support.LocalTime.KernelAsymptotics
import CERW.Support.Coarse.RadialAssembly

/-!
# The radial test

`lem:radial` of the paper (`paper/cerw-flat.tex:581-601`). The bytes between
the markers are the frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

/-- `lem:radial` (`cerw-flat.tex:581-601`):

```latex
\begin{lemma}\label{lem:radial}
Let $d\geq2$ be an integer, let $0<\eps<1/d$, and let $(X_j)_{j\geq0}$ be centrally
excited random walk started at the origin, with first-departure probabilities
$q_x(\pm e_i)=1/(2d)\mp\eps u_x^i/2$, with simple symmetric
steps on later departures and at the origin.
Let $b_d=\lceil\sqrt d/2\rceil+6$, and let
$F(s)=\sigma_d^{-1}\int_{D_n\cap\{|v|>s\}}|v|^{1-d}\dd v$.
For every $p>0$, there are $r_0=r_0(d)>2b_d$ and $C=C(d,\eps,p)>0$
such that, for every integer $n\geq2$, with probability at least
$1-Cn^{-p}$, simultaneously for
all integers $r_0\leq r\leq n$,
\begin{equation}\label{eq:radial}
\begin{split}
F(r+b_d)\leq{}&CM_{\rm sh}(r)
 [F(r-b_d)-F(r+b_d)]\\
&+C\left[\sqrt{M_nr^{1-d}F(r-b_d)L}+r^{1-d}L\right]\, .
\end{split}
\end{equation}
Here $L=\log(n+2)$ and
$M_{\rm sh}(r)=\max_{x:\,||x|-r|\leq3}\ell_n(x)$.
\end{lemma}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.radial_test {d : ℕ} (hd : 2 ≤ d) :
    let bd : ℕ := ⌈Real.sqrt d / 2⌉₊ + 6
    ∃ r₀ : ℕ, 2 * bd < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p →
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let L : ℝ := Real.log (n + 2)
        μ {ω | ¬ ∀ r : ℕ, r₀ ≤ r → r ≤ n →
            CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) + bd)
              ≤ C * CERW.shellMax (X · ω) n r
                  * (CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) - bd)
                    - CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) + bd))
                + C * (Real.sqrt ((CERW.maxLocalTime (X · ω) n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ))
                        * CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) - bd) * L)
                    + (r : ℝ) ^ (1 - (d : ℝ)) * L)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨b, h, hF⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  exact CERW.Support.Coarse.radial_test_of_kernelFacts hd hF
