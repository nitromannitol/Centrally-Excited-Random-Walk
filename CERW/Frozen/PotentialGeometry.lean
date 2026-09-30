import CERW.Model
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import CERW.Support.Geometry.Assembly

/-!
# The geometry of the potential

`lem:geometry` of the paper (`paper/cerw-flat.tex:497-514`). The bytes between
the markers are the frozen contract recorded in `ledger/manifest.yaml`.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

/-- `lem:geometry` (`cerw-flat.tex:497-514`):

```latex
\begin{lemma}\label{lem:geometry}
Let $d\geq2$ be an integer, let $\eps>0$, and let $D\subset\R^d$
be a bounded measurable set of volume $R$. Let
$U_D(y)=(2\eps/\omega_d)\int_Du_v\cdot(v-y)|v-y|^{-d}\dd v$,
and let $F(s)=\sigma_d^{-1}\int_{D\cap\{|v|>s\}}|v|^{1-d}\dd v$.
Then there is a constant $C_d>0$, depending only on $d$, such that
for every $y,z\in\R^d$ and every $s>0$,
\begin{align}
\|U_D\|_\infty&\leq C_d\eps R^{1/d}\, ,\label{eq:potential-bound}\\
|U_D(y)-U_D(z)|&\leq C_d\eps R^{1/(2d)}|y-z|^{1/2}\, ,\label{eq:holder}\\
\frac1{\sigma_d}\int_{S^{d-1}}U_D(s\theta)\dd S(\theta)
&=2d\eps F(s)\, .\label{eq:newton}
\end{align}
For every $b>0$, the ball potential is
\begin{equation}\label{eq:ballpotential}
U_{B(0,b)}(y)=2d\eps(b-|y|)_+\, .
\end{equation}
\end{lemma}
```
-/
-- FROZEN-STATEMENT-BEGIN
theorem CERW.Frozen.potential_geometry {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ ε : ℝ, 0 < ε →
      (∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
        let R : ℝ := (volume D).toReal
        (∀ y, |CERW.potential d ε D y| ≤ Cd * ε * R ^ ((1 : ℝ) / d)) ∧
        (∀ y z, |CERW.potential d ε D y - CERW.potential d ε D z|
            ≤ Cd * ε * R ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
        (∀ s : ℝ, 0 < s →
          (d * ωd)⁻¹ * ∫ θ, CERW.potential d ε D (s • (θ : EuclideanSpace ℝ (Fin d)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
            = 2 * d * ε * CERW.tail d D s)) ∧
      ∀ b : ℝ, 0 < b → ∀ y : EuclideanSpace ℝ (Fin d),
        CERW.potential d ε (Metric.ball 0 b) y = 2 * d * ε * max (b - ‖y‖) 0
-- FROZEN-STATEMENT-END
:=
  CERW.Support.Geometry.potential_geometry hd
