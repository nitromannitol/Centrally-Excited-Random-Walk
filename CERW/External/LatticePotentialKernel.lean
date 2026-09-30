import CERW.Model
import LatticeProb.Walk.SimpleTransfer
import LatticeProb.Walk.SRW

/-!
# The lattice potential kernel asymptotics

The cited estimate `eq:kernel-asymptotics` of the paper (`paper/cerw-flat.tex:345-359`). The bytes
between the markers are the frozen contract recorded in `ledger/manifest.yaml`.

Cited from Lawler--Limic, Theorem 4.3.1, Corollary 4.3.3 and Theorem 4.4.4, and carried as an
explicit hypothesis, never as an axiom.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

/-- The cited estimate `eq:kernel-asymptotics` (`cerw-flat.tex:345-359`):

```latex
Let $P$ be the simple random walk transition operator on $\Z^d$.
For $d=2$, let $b$ be the potential kernel normalized by $b(0)=0$.
For $d\geq3$, let $b=-G$, where
$G(x)=\sum_{j\geq0}P^j(0,x)$ is the Green function.
In both cases $(P-I)b=\ind_{\{0\}}$.
The lattice potential estimates of
\citet[Theorem~4.3.1, Corollary~4.3.3, and Theorem~4.4.4]{LawlerLimic2010}
give, as $|x|\to\infty$,
\begin{equation}\label{eq:kernel-asymptotics}
b(x)=\begin{cases}
\dfrac2\pi\log|x|+\kappa+O(|x|^{-2}),&d=2,\\[3pt]
-\dfrac{2}{(d-2)\omega_d}|x|^{2-d}+O_d(|x|^{-d}),&d\geq3
\end{cases}\, ,
\end{equation}
where $\kappa$ is the planar potential-kernel constant.
```
-/
-- FROZEN-STATEMENT-BEGIN
def CERW.External.LatticePotentialKernel (d : ℕ) : Prop :=
  (d = 2 →
    ∃ b : Site 2 → ℝ,
      (∀ x, Tendsto (fun M : ℕ => LatticeProb.srwGreen 2 M 0 - LatticeProb.srwGreen 2 M x)
        atTop (𝓝 (b x))) ∧
      ∃ κ C R : ℝ, 1 ≤ R ∧ ∀ x : Site 2, R ≤ euclidNorm x →
        |b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤ C * euclidNorm x ^ (-2 : ℝ)) ∧
  (3 ≤ d →
    ∃ C R : ℝ, 1 ≤ R ∧ ∀ x : Site d, R ≤ euclidNorm x →
      |LatticeProb.srwGreenInf d x
          - 2 / (((d : ℝ) - 2) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
            * euclidNorm x ^ (2 - (d : ℝ))|
        ≤ C * euclidNorm x ^ (-(d : ℝ)))
-- FROZEN-STATEMENT-END
