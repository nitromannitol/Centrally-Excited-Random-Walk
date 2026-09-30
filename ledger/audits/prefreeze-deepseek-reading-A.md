I attempted to refute each declaration by checking, against the paper, (a) quantifier order, (b) which constant is chosen before which variable, (c) placement of the a.s./probability statements, (d) the hypotheses on `d` and `ε`, (e) the index/range conditions, and (f) the formulas and their dependence on the definitions in `CERW/Model`. Here is the result.

## 1. `LatticePotentialKernel` (eq:kernel-asymptotics, local-times.tex 5–19)
**No discrepancy found.**
- `d = 2` case: the limit `srwGreen 2 M 0 − srwGreen 2 M x → b x` is exactly the potential kernel `b` (normalized `b(0)=0`); the bound `|b x − (2/π log|x| + κ)| ≤ C|x|^{-2}` matches the paper's `2/π log|x| + κ + O(|x|^{-2})`.
- `3 ≤ d` case: `srwGreenInf` is the Green function `G`, and `|G(x) − 2/((d−2)ω_d)|x|^{2−d}| ≤ C|x|^{−d}` has the same absolute error as the paper's `b = −G` expansion (sign irrelevant under the absolute value).
- `R ≥ 1` correctly encodes "as `|x| → ∞`"; the constant `C` may depend on `d` (paper's `O_d`).

## 2. `ball_shape` (thm:shape, cerw.tex 135–160)
**No discrepancy found.**
- The a.s. quantifier is outermost over the *whole* conjunction: `∀ᵐ ω, (i) ∧ (ii) ∧ (iii)`, matching "the following statements hold almost surely".
- (i) is `∀ η, 0<η → η<a → ∀ᶠ n, B_{a−η} ⊆ A_n ⊆ V_n ⊆ B_{a+η}`, matching the paper's "for every `0<η<a`, for all sufficiently large `n`" with the null set independent of `η`.
- (ii) is `∀ η>0, ∀ᶠ n, ∀x, |ℓ_n(x)/N − 2dε(a−|x|/N)_+| ≤ η`, the correct formalization of the uniform `sup_x → 0`.
- (iii) has `|V_n|/N^d → ω_d a^d`, `∀x, ℓ_n(x)/N → 2dε a`, and `∀x, ∃ᶠ j, X_j = x`, all inside the same `∀ᵐ`.
- `a = ((d+1)/(2d ε ω_d))^{1/(d+1)}`, `N=n^{1/(d+1)}`, `2≤d`, `0<ε<1/d`: all match.

## 3. `fluctuation_bounds` (thm:fluctuations, cerw.tex 186–213)
**No discrepancy found.**
- First conjunct: `∀p>0, ∃C,n₀` are chosen before the probability space, `n₀ ≤ n`, and `μ{¬Good} ≤ C n^{−p}`; matches "for every `n ≥ n_0`, with probability at least `1−Cn^{−p}`".
- Second conjunct: `∃C, ∀ᵐ ω, ∀ᶠ n, Good C` is exactly "eventually almost surely, with deterministic constants and a finite random starting time".
- `Good` matches the three displays: `B(0,(a−CQ)N) ⊆ A_n ⊆ V_n ⊆ B(0,(a+CQ^{1/d}L)N)`; `|(D_n/N) Δ B(0,a)| + ||A_n|/N^d − ω_d a^d| ≤ CQ`; `∀x, |ℓ_n(x)/N − 2dε(a−|x|/N)_+| ≤ CQ^{1/d}`.
- `Q=(L/N)^{1/2}` for `d=2`, `Q=(L/N)^{d/(2d−1)}` otherwise, `L=log(n+2)`, and `C` is the same constant in `Good` and in the failure probability (legitimate, can be enlarged).

## 4. `hausdorff_bound` (eq:hausdorff + planar remark, cerw.tex 215–225)
**No discrepancy found.**
- The distance is `Metric.hausdorffEDist (N⁻¹ • V_n) (closedBall 0 a)`, i.e. `d_H(N^{-1}V_n, \overline B(0,a))` with `\overline B` the closed ball and the image taken under `x ↦ N⁻¹ • toSpace x`.
- Exponents match exactly: `n^{−1/12}L^{5/4}` for `d=2`, `n^{−1/((d+1)(2d−1))}L^{2d/(2d−1)}` for `d≥3`.
- The planar inner-radius condition is guarded by `d = 2 →` and is `{|x| < aN − Cn^{1/6}√L} ⊆ A_n`, matching `Cn^{1/6}√log(n+2)` "in lattice units". Using `A_n` (departure range) is faithful, since the paper's inradius is that of `D_n`/`A_n` (fluctuations.tex, eq:inradius and the following sentence).
- Turning the "on the event" statement into its own probability bound with its own constant is one of the approved decisions.

## 5. `local_time_potential` (lem:local, local-times.tex 40–74)
**No discrepancy found.**
- `Cd` (the paper's `C_d`) is bound before `ε` and `p`, and `C` after `ε,p`: matches `C_d` depending only on `d` and `C = C(d,ε,p)`.
- Index range: `∀ s t : ℕ, s < t → t ≤ n` is exactly `0 ≤ s < t ≤ n` (naturals make `0 ≤ s` automatic).
- Target range: `∀ y, ‖y‖ ≤ 2*n` matches the paper's `|y| ≤ 2n`.
- `e` and `λ`: `√m L + L` / `√(mL)+L` and `L²` / `L` for `d=2` / `d≥3`; the first two bounds use `R_n = |A_n|` and `k_{s,t}` (`departureRange.card`, `freshCount`) with `C_d ε (·)^{1/d}+Cλ`, matching eq:M and eq:interval.

## 6. `potential_geometry` (lem:geometry, local-times.tex 142–174)
**No discrepancy found.**
- `Cd` is bound before `ε`, matching `C_d` depending only on `d`; `ε` is only required positive, as in the paper.
- `D` ranges over measurable bounded sets, `R = volume D`, and the three bounds match: `|U_D(y)| ≤ Cd ε R^{1/d}`, `|U_D(y)−U_D(z)| ≤ Cd ε R^{1/(2d)}‖y−z‖^{1/2}`, and `(1/σ_d)∫_{S^{d−1}} U_D(sθ) = 2dε F(s)` with `(d ω_d)^{-1}` for `1/σ_d` and `tail d D s = F(s)`.
- The ball identity `U_{B(0,b)}(y) = 2dε(b−|y|)_+` holds for every `b>0` and every `y`, matching the paper.

## 7. `radial_test` (lem:radial, coarse-radius.tex 20–58)
**No discrepancy found.**
- `r₀` is bound before `ε` and `p`, matching `r_0 = r_0(d)`; the condition `2*bd < r₀` matches `r_0 > 2b_d`; `C` is after `ε,p`.
- `bd = ⌈√d/2⌉ + 6` matches `b_d = ⌈√d/2⌉ + 6`.
- The range `∀ r : ℕ, r₀ ≤ r → r ≤ n` is exactly the integers `r_0 ≤ r ≤ n`; the inequality is
  `F(r+b_d) ≤ C M_sh(r)(F(r−b_d)−F(r+b_d)) + C(√(M_n r^{1−d}F(r−b_d)L) + r^{1−d}L)`,
  with `M_sh` (`shellMax`), `M_n` (`maxLocalTime`) and `F` (`tail` on `cellSet`) as in the paper.

## 8. `coarse_bounds` (prop:coarse, coarse-radius.tex 4–18)
**No discrepancy found.**
- `c,C` are chosen after `ε,p` and before the probability space, matching constants depending only on `d,ε,p`.
- The six inequalities are exactly `cN^d ≤ R_n ≤ CN^d`, `cN ≤ M_n ≤ CN`, `cN ≤ H_n ≤ CN`, with `R_n = departureRange.card`, `M_n = maxLocalTime`, `H_n = maxRadius = max_{0≤j≤n}|X_j|`, and `N=n^{1/(d+1)}`.
- `n ≥ 2` and the failure probability `≤ C n^{−p}` match the proposition.

---

**Overall:** after this adversarial pass I could not refute any of the eight declarations. Quantifier order, constant-before-variable placement, a.s. placement, `d`/`ε` hypotheses, and the ranges `0 ≤ s < t ≤ n`, `r₀ ≤ r ≤ n`, `‖y‖ ≤ 2n` all line up with the paper (allowing for the explicitly approved design decisions).
