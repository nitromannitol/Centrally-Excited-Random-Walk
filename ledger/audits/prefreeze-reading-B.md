Below is my adversarial comparison. I read the paper loci, the eight declarations, the model files, and the library definitions they rely on (`srwGreen`/`srwGreenInf`, `ballFinset`, `Measure.toSphere`, `hausdorffEDist`, `volume`).

For each declaration I state the result and any discrepancy I can actually substantiate.

## 1. `LatticePotentialKernel` (eq:kernel-asymptotics)
**No discrepancy found.**
- d=2: `b` is the limit of the partial sums `G_M(0)-G_M(x)` (paper: potential kernel, b(0)=0); the displayed bound is exactly `|b x − (2/π log|x| + κ)| ≤ C|x|^{-2}`, matching `2/π log|x|+κ+O(|x|^{-2})` (paper line 14). `κ` being existential is harmless since the paper only uses existence.
- d≥3: paper sets `b=-G` and `b(x)= -2/((d-2)ω_d)|x|^{2-d}+O(|x|^{-d})`; Lean states the equivalent positive-coefficient asymptotic for `srwGreenInf = G = -b`. Sign and exponent `2-d` are correct. `ω_d` is the actual unit-ball volume.

## 2. `ball_shape` (thm:shape)
**No discrepancy found.**
- (i) `{x | |x|<(a−η)N} ⊆ A_n ⊆ V_n ⊆ {x | |x|<(a+η)N}` with strict `<` (open ball) and `A_n=departureRange`, `V_n=visitedRange` (paper lines 143–146, 120–123). η restricted to `0<η<a`.
- (ii) `sup_x|…|→0` rendered correctly as `∀η>0, ∀ᶠn, ∀x, |…|≤η`; the profile is `2dε max(a−|x|/N) 0` (paper line 150).
- (iii) `|V_n|/N^d→ω_da^d`, `ℓ_n(x)/N→2dεa`, and recurrence `∀x, ∃ᶠj, X_j=x` (paper lines 153–155). a, N inline exactly as eq:scale.

## 3. `fluctuation_bounds` (thm:fluctuations)
**No discrepancy found.**
- `Q` is `(L/N)^{1/2}` for d=2, `(L/N)^{d/(2d−1)}` for d≥3 (paper eq:rates); `L=log(n+2)`.
- Sandwich radii `a−CQ` and `a+CQ^{1/d}L`; volume uses `(N⁻¹)·cellSet = D_n/N`, `Metric.ball 0 a` open, `|A_n|/N^d` via `departureRange.card`; profile `CQ^{1/d}` (paper eq:sandwich, eq:volume, eq:profile-rate).
- Probability bound written as `μ{¬Good}≤C n^{−p}` with its own constant before `μ`, plus the separate a.s. eventual conjunct. Both parts of Theorem 1.2 present.

## 4. `hausdorff_bound` (eq:hausdorff + planar remark)
**No discrepancy found.**
- Sets are `N⁻¹·toSpace '' V_n` and `Metric.closedBall 0 a` (paper: `N^{-1}V_n`, `\overline B(0,a)`).
- d=2 error `n^{-1/12}L^{5/4}`; d≥3 `n^{-1/((d+1)(2d−1))}L^{2d/(2d−1)}`. Both match eq:hausdorff.
- Inner-radius conjunct only for d=2: `{|x|<aN−C n^{1/6}√L} ⊆ A_n`, matching the remark "in the plane … C n^{1/6}√log(n+2) in lattice units" (note `QN = n^{1/6}√L`). `hausdorffEDist` is the standard sup-inf ENNReal distance, which agrees on these bounded nonempty sets.

## 5. `local_time_potential` (lem:local)
**No discrepancy found.**
- `M_n ≤ C_d ε R_n^{1/d}+Cλ_n` with `M_n=maxLocalTime`, `R_n=departureRange.card`, `λ_n=L²` (d=2) / `L` (d≥3).
- Interval bound `M_{s,t} ≤ C_d ε k_{s,t}^{1/d}+Cλ_n` for `s<t≤n`, with `k_{s,t}=freshCount` (`X_j∉{X_0,…,X_{j−1}}`, including j=0 as in the paper).
- Approximation `|ℓ̃_n(y)−U_{D_n}(y)| ≤ C e_n(M_n)` for `|y|≤2n`, with `e_n` exactly `√m L+L` (d=2) / `√(mL)+L` (d≥3). `cellLocalTime` uses `cellCenter` so it is `ℓ_n` on each half-open cell. `C_d` is bound before ε, as required.

## 6. `potential_geometry` (lem:geometry)
**No discrepancy found.**
- `D` bounded measurable, `R=(volume D).toReal`; `‖U_D‖_∞ ≤ C_d ε R^{1/d}`, `|U_D(y)−U_D(z)| ≤ C_d ε R^{1/(2d)}|y−z|^{1/2}`.
- Spherical average: `(d·ω_d)⁻¹∫ U_D(s•θ) d(volume.toSphere) = 2dε·tail_D(s)`. Since `volume.toSphere` has total mass `d·ω_d = σ_d` and `tail_D(s)=(dω_d)^{-1}∫_{D∩{s<|v|}}|v|^{1−d}`, this is exactly `(1/σ_d)∫_{S^{d−1}}U_D = 2dε F(s)`.
- Ball potential `U_{B(0,b)}(y)=2dε(b−|y|)_+` with `Metric.ball 0 b` (open, per notation; boundary is measure zero). Integrands are integrable on bounded measurable `D` (near-`y` singularity order `d−1`; `|v|^{1−d}` is integrable at 0 in `d` dimensions).

## 7. `radial_test` (lem:radial)
**No discrepancy found.**
- `b_d=⌈√d/2⌉+6`, `r₀>2b_d` bound before ε and p.
- Inequality is exactly `F(r+b_d) ≤ C M_sh(r)[F(r−b_d)−F(r+b_d)] + C[√(M_n r^{1−d}F(r−b_d)L)+r^{1−d}L]`, with `M_sh=shellMax`, `M_n=maxLocalTime`, `F=tail_{D_n}`; quantified over integers `r₀≤r≤n`, `n≥2`.
- `shellMax` filters `|euclidNorm x − r|≤3` inside `ballFinset d (r+3)`; the ball restriction is redundant because `|norm−r|≤3 ⇒ norm≤r+3`, so no site is lost.

## 8. `coarse_bounds` (prop:coarse)
**No discrepancy found.**
- `cN^d ≤ R_n ≤ CN^d`, `cN ≤ M_n ≤ CN`, `cN ≤ H_n ≤ CN` with `R_n=departureRange.card`, `M_n=maxLocalTime`, `H_n=maxRadius = max_{0≤j≤n}|X_j|`, `N=n^{1/(d+1)}`.
- Same `c,C` used for all six inequalities and for the probability bound `1−Cn^{−p}`; `c,C` bound before `μ,X`; `n≥2`.

## Cross-cutting checks
- **Junk values:** no natural-number subtraction underflow (`2*d−1`, `d−2` occur only under `d≥2` or with real coercions); no division/log/sqrt of zero in the statements (`N n>0`, `n+2≥2`, `r≥r₀>0`, `Q n≥0`); no `toReal` of an infinite volume (bounded `D`, unit ball); no integral of a non-integrable function on the carriers used (bounded cell sets).
- **Carriers:** `A_n=departureRange` (times `<n`), `V_n=visitedRange` (times `≤n`); lattice-only sets are `Set (Site d)` with `euclidNorm`; `ℝ^d` objects use `EuclideanSpace ℝ (Fin d)`; scaling `N⁻¹ •` and `Metric.ball`/`Metric.closedBall` are used in the correct open/closed places.
- **IsCERW:** `stepProb` uses `firstStep` iff `x n ≠ 0` and `x n ∉ {x 0,…,x_{n−1}}`; every other departure and every departure from the origin use `srwStep`. `firstStep` matches `1/(2d)∓(ε/2)x_i/|x|` with the correct sign per `±e_i`. The cylinder factorization fixes the conditional law given the full past, so the model is encoded faithfully.

Conclusion: I could not substantiate a discrepancy in any of the eight declarations.
