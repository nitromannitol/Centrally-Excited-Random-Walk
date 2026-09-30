# Draft audit 4 (refute-first): ten draft statements under `scratch/Frozen/`

Paper: `paper/limit-shapes.tex`, Sections 6-9 (`\drift` = kappa, written `ε` in Lean; `\gauge` = Psi = the
Euclidean norm throughout). Conventions: `CORRESPONDENCE.md` ("Transcription conventions"), the
author rulings quoted in the task (Lemma 9.3 as a probabilistic closure; Theorems 8.1 and 8.3 carry
`MartingaleCLT` and `StoutLIL` as hypotheses; Proposition 9.2's almost-sure sentence read with the
same `C`). No Lean file under the repository was edited. Machine evidence was produced from copies
in the session scratchpad (`.../scratchpad/p/*.lean`, `P1.lean`), compiled with
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` against the built `CERW.Model`;
every copy elaborates with only `declaration uses sorry`.

## Summary

| node | draft | verdict |
|---|---|---|
| prop-inner | `InnerRadius.lean` | **DEFECT** (precedence: the volume clause scales the symmetric difference; the statement is false) |
| prop-stronger-outer | `OuterRadius.lean` | PASS |
| lem-near-far | `NearFar.lean` | PASS |
| thm-moment-fluctuations | `MomentFluctuations.lean` | PASS |
| lem-fixed-site-centering | `FixedSiteCentering.lean` | PASS |
| thm-site-fluctuations | `SiteFluctuations.lean` | PASS |
| lem-exp-deviation | `ExpDeviation.lean` | **CONCERN** (low: `S_0 = 0` and the increment bound are hypotheses for every `ω`, the paper's are almost sure) |
| prop-bulk-profile | `BulkProfile.lean` | PASS |
| lem-separated-brackets | `SeparatedBrackets.lean` | PASS (under the author's closure ruling) |
| prop-log-lower | `LogLowerBounds.lean` | PASS |

## Method and machine evidence

1. **Elaborated statements.** For each draft I printed the elaborated type with
   `set_option pp.parens true`, `pp.coercions.types true`, `pp.letVarTypes true` (externals inlined the
   way `scratch/Frozen/check.sh` does it). I read every parse, cast and binder order off the printed
   term rather than off the source text. All ten compile clean (modulo `sorry`).
2. **Casts.** In every node `r n = (((↑d + 1) * ↑n) / (2 * ↑d * ε * ωd)) ^ (1 / (↑d + 1))` with the
   casts at the leaves (no `ℕ`-division, no cast of a sum). `q n ^ (1 / ↑d)`, `(3 - ↑d) / 2`,
   `(↑d + 3) / 2` are real. The only natural-number exponents are `t ^ (d - 1)` (NearFar, LogLowerBounds),
   where `d ≥ 2` so there is no truncated subtraction, and `r n ^ d`, `log n ^ 3`, `h ^ 2`, `‖·‖ ^ d`.
3. **Big-operator parse.** `(∑ x ∈ A, euclidNorm x - n / (2 * ε))` is `(∑ x ∈ A, euclidNorm x) - n / (2 * ε)`
   (body is `term:67`); confirmed in the printed term of `MomentFluctuations`, and likewise for the
   body of `CERW.quadraticMart` (`2 * ε * ∑ … - n + …`).
4. **The one real bug** (InnerRadius) was found by the printed term and reproduced in
   `P1.lean`: `volume (r⁻¹ • A ∆ B)` prints as `volume (r⁻¹ • (A ∆ B))`.
5. **Model definitions read against the paper** (all mean what the paper means):
   * `quadraticMart ε X n = 2ε Σ_{x∈A_n}|x| − n + |X_n|²` = eq:moment-martingale (line 1347); `A_n = departureRange`
     is `{X_0..X_{n-1}}`. Checked the algebra `|X_n|² = n + Q_n − 2εΣ_{x∈A_n}|x|` from
     `Q_t = Σ_{j<t} 2X_j·(X_{j+1}−X_j+ε I_j u_{X_j})`.
   * `momentRadius = (((d+1)/(dω_d)) Σ_{x∈A_n}|x|)^{1/(d+1)}` = eq:radial-moment-def (line 1352).
   * `dynkinBracket p f g X t = Σ_{j<t}(Σ_{e∈unitSteps} p X j e · Δ_e f Δ_e g − stepMean f · stepMean g)`:
     the conditional covariance of `f(X_{j+1})−f(X_j)`, `g(X_{j+1})−g(X_j)` given `ℱ_j`; since the compensator
     of `M^f` is `ℱ_j`-measurable this is the bracket `⟨M^f, M^g⟩_t`. `stepProb d ε X j` is the conditional
     law of the step given the whole past (`IsCERW.step`), first-departure kernel at a fresh nonzero site,
     simple random walk step otherwise.
   * `latticeKernel d x`: `d = 2`: `lim_M Σ_{j<M}[P^j(0,0) − P^j(0,x)]` (potential kernel, `g(0)=0`);
     `d ≥ 3`: `−srwGreenInf d x` with `srwGreenInf d x = Σ_{j≥0} P^j(0,x)` (the `j = 0` term is included, `srwHeat d 0 = δ_0`),
     so `G(0) ≥ 1` and `Δg = 1_{0}` in both cases, as at line 406.
   * `positivePotential d ε D y = (2ε/ω_d) ∫_D max(u_v·(v−y)/|v−y|^d, 0)` = `U_D^+` (line 1125), integrand `0` at `v = y`.
   * `predBracket μ ℱ S T n = Σ_{t<n} μ[ΔS_t ΔT_t | ℱ t]`, the predictable covariation, a.e. defined, used only under `∀ᵐ`.
   * `innerRadius`, `maxRadius`, `cellSet`, `cellLocalTime`, `localTime`, `potential`: as in `Radii.lean`,
     `Occupation.lean`, `Potential.lean`; `innerRadius` is `sInf` over a nonempty bounded-below set.
6. **Non-vacuity.** `CERW.Support.Law.exists_isCERW` shows `IsCERW μ ε X` is satisfiable, so the `∀ (Ω μ X)` blocks are not vacuous.

---

## prop-inner — `InnerRadius.lean` — DEFECT

Paper: Proposition 6.1 (1078-1094), `q_n` eq:qn (763-766).

### The defect

Lines 20-21 of the draft read

```lean
                  volume ((r n)⁻¹ • CERW.cellSet (X · ω) n ∆
                      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
```

`∆` (`symmDiff`) is `scoped[symmDiff] infixl:100` and `•` is `infixr:73`, so `a • b ∆ c` parses as
`a • (b ∆ c)`. The elaborated term printed by `pp.parens` is

```
((ℙ : Set (EuclideanSpace ℝ (Fin d)) → ENNReal) ((r n)⁻¹ • ((CERW.cellSet (fun x => X x ω) n) ∆ (Metric.ball 0 1)))) ≤ ENNReal.ofReal (C * q n)
```

So item (ii) asserts `r_n^{-d} · |D_n ∆ B(0,1)| ≤ C q_n` instead of `|r_n^{-1} D_n ∆ B(0,1)| ≤ C q_n`.

### Why this makes the statement false

Cells are disjoint of volume one, so `|D_n| = |A_n|`, and `|D_n ∆ B(0,1)| ≥ |D_n| − ω_d`. By the proved
`CERW.Frozen.ball_shape` (`|V_n|/N^d → ω_d a^d`, with `aN = r_n`, and `|A_n| ≥ |V_n| − 1`), almost surely
`r_n^{-d} |D_n ∆ B(0,1)| → ω_d` (indeed `≥ ω_d/2` eventually), while `C q_n → 0`. Hence the probability of
the exceptional event tends to `1`, not `≤ C n^{-p} → 0`, for every `C`, every `p > 0`, in every
`(Ω, μ, X)` (and such triples exist). The clause cannot be proved.

The same pattern occurs in `scratch/Frozen/FluctuationRates.lean` line 21 (not in this batch); `draft-audit-1.md`
reports it independently.

### Exact replacement (lines 20-21)

```lean
                  volume (((r n)⁻¹ • CERW.cellSet (X · ω) n) ∆
                      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
```

Checked: the patched copy (`p/InnerRadiusFixed.lean`) elaborates with no error or warning other than `sorry`, and
prints `(((r n)⁻¹ • (CERW.cellSet (fun x => X x ω) n)) ∆ (Metric.ball 0 1))`.

### Everything else in this node checked and correct

* Quantifiers: `∀ ε ∈ (0,1/d)`, `∀ p > 0`, `∃ C > 0`, then `∀ Ω μ X`, `∀ n ≥ 2`. `C = C(d,ε,p)` precedes the probability space.
  One `C` for the three items and the probability, as in the paper. For `n` below some `n₀(d,ε,p)` the right side
  is `≥ 1` once `C ≥ n₀^p`, so `n ≥ 2` for all `n` with a single `C` is not stronger than the paper.
* `q n = if d = 2 then √(log n / r n) else log n / r n`: eq:qn exactly; `n ≥ 2` gives `log n > 0`, `r n > 0`,
  so the real power `q n ^ (1/d)` is the true power; no junk.
* (i) `|innerRadius − r n| ≤ C r_n q_n`, (iii) `∀ y, |ℓ̃_n(y) − 2dε (r_n − |y|)_+| ≤ C r_n q_n^{1/d}` with
  `max (r n − ‖y‖) 0` and `cellLocalTime`: correct. The three items sit inside one `¬ (… ∧ … ∧ …)`.
* Bound is an upper bound on the outer measure of the exceptional set (convention).

---

## prop-stronger-outer — `OuterRadius.lean` — PASS

Paper: Proposition 7.1 (1174-1179).

* Quantifiers as in prop-inner; `C = C(d,ε,p)` before `Ω μ X`; `n ≥ 2`.
* `maxRadius ≤ r n + C * (if d = 2 then √(r n) * (log n) ^ (5/2) else (log n) ^ ((d:ℝ) + 1))`: the two cases,
  exponents `5/2` and `d+1`, and the factor `√r_n` for `d = 2` are the paper's. Printed term:
  `(if d = 2 then √(r n) * (Real.log ↑n) ^ (5 / 2) else (Real.log ↑n) ^ (↑d + 1))`.
* `maxRadius` is `sup'_{0≤j≤n} |X_j|` = `R_out(n)` (eq:radii). Bases are positive, so the real powers are the true powers.

---

## lem-near-far — `NearFar.lean` — PASS

Paper: Lemma 7.2 (1205-1210); `U_D^+` at 1123-1126.

* `∃ C > 0` after `ε`, before `w b lam D`: `C(d,ε)`.
* Hypotheses `1 ≤ w`, `w ≤ b`, `1 ≤ lam`, `MeasurableSet D`, `D ⊆ {b ≤ ‖v‖ ≤ b + w}`: exact.
* (1) `∀ u, ‖u‖ = 1 → ∀ t, w ≤ t → volume (D ∩ ball ((b + w) • u) t) ≤ ofReal (lam * t ^ (d-1))`: open balls, `t ^ (d-1)`
  natural power with `d ≥ 2` (no truncation), `t ≥ w ≥ 1 > 0`. (2) `∀ y, ∫ v in D, ‖v − y‖ ^ (2 − (d:ℝ)) ≤ lam * b`: all `y ∈ ℝ^d`.
* Bochner-integral junk: `D` is bounded measurable and the kernels `|v − y|^{2−d}` and `[…]_+ ≤ |v − y|^{1−d}` are locally integrable
  for `d ≥ 2`, so no integral is the junk value `0`.
* Conclusion `positivePotential d ε D y ≤ C * (lam * w ^ (d-1)) ^ (1/(d:ℝ)) + C * lam` for `b ≤ ‖y‖ ≤ b + w`: exact;
  the base is `≥ 1`.
* Truth check (from the paper's proof, re-derived): `B(y,t) ⊂ B((b+w)u_y, 2t)` for `t ≥ w`;
  `2(|v|²−v·y) = |v−y|² + |v|² − |y|²` with `|v|²−|y|² ≤ 3bw`; bathtub bound near `y`; integration by parts far from `y`. True.

---

## thm-moment-fluctuations — `MomentFluctuations.lean` — PASS

Paper: Theorem 8.1 (1355-1376); `Q_n` (1347), `R_mom` (1352).

* Hypotheses `hCLT`, `hLIL` (both Externals, universe `u` = that of `Ω`) as ruled.
* Constants: `v₁ = 2 d ωd / (ε (d+2)(d+3))`, `v₂ = 2 / (ε d ωd (d+2)(d+3))`; the printed terms are
  `((2 * ↑d) * ωd) / ((ε * (↑d + 2)) * (↑d + 3))` and `2 / ((((ε * ↑d) * ωd) * (↑d + 2)) * (↑d + 3))`: exactly the paper's. Re-derived from
  Step 1 (`⟨Q⟩_n/r_n^{d+3} → 8dεω_d/((d+2)(d+3))`, divided by `4ε²`; then divided by `d²ω_d²` by Step 4): both match.
  Both are positive, so `.toNNReal` is not a junk truncation.
* Normalizations: `S = (Σ|x| − n/(2ε)) / r_n^{(d+3)/2}`, `R = (R_mom − r_n) / r_n^{(3−d)/2}`: exactly the paper's; no `log log` in the
  CLT normalization.
* (i) `TendstoInDistribution S atTop id (fun _ => μ) (gaussianReal 0 v₁.toNNReal)` and the same for `R`: the two convergences are separate, as in the paper.
* (ii) junk-free limsup: `∀ᵐ ω, ∀ δ > 0, ∀ σ = ±1, (∀ᶠ n, σ S ≤ (√v + δ) √(2 log log n)) ∧ (∃ᶠ n, (√v − δ) √(2 log log n) ≤ σ S)`,
  for both `S` (with `v₁`) and `R` (with `v₂`). Multiplying the paper's ratio by `√(2 log log n) > 0` (`n ≥ 3`) is an equivalence; for
  `δ ≥ √v` the frequent clause is implied by `limsup ≥ 0`, which is consistent. The `∀ᵐ` is outside `∀ δ` (right reading).
* No `Real.sqrt` of a negative quantity matters: `log log n ≤ 0` only for `n ≤ 2`.

---

## lem-fixed-site-centering — `FixedSiteCentering.lean` — PASS

Paper: Lemma 8.2 (1432-1438); `Q_n` (1347).

* `∀ y : Site d, ∃ C > 0, ∀ Ω μ X`: `C = C(d,ε,y)` deterministic, before the probability space. `∀ᵐ ω, ∀ᶠ n`: random threshold, as the paper ("almost surely, for all sufficiently large `n`").
* `potential d ε (cellSet (X · ω) n) (toSpace y)` = `U_{D_n}(y)` at the lattice site `y`; `2 * d * ε * (r n − euclidNorm y)` (no positive part, as in the paper);
  `quadraticMart ε (X · ω) n / (ωd * r n ^ d)` = `Q_n / (ω_d r_n^d)`; bound `C * (if d = 2 then log n ^ 3 else 1)`. Printed term matches the paper.
* `quadraticMart` is the paper's eq:moment-martingale for the Euclidean norm (see the Model check above).
* No junk: `D_n` bounded measurable (finite union of boxes), kernel integrable.

---

## thm-site-fluctuations — `SiteFluctuations.lean` — PASS

Paper: Theorem 8.3 (1462-1487); `G` = Green function (line 406).

* `G = LatticeProb.srwGreenInf d`: `Σ_{j≥0} P^j(0,x)`, includes `j = 0` (so `G(0) ≥ 1`); used only in the `d ≥ 3` branch, where the series converges;
  in `d = 2` the `let` is bound but never used (there the tsum would be junk).
* Constants: `σ_n = √(r_n log r_n)` (`d = 2`), `√r_n` (`d ≥ 3`); `lil_n = √(2 r_n log r_n · log log n)` (`d = 2`), `√(2 r_n log log n)` (`d ≥ 3`);
  `v = 16ε/π` (`d = 2`), `2dε(2G(0) − 1)` (`d ≥ 3`); `cov y z = 16ε/π` or `2dε(2G(y−z) − 1_{y=z})`: exactly eq:site-clt, the LIL display and eq:site-covariance.
  The indicator is on the sites `y, z`, as in the paper (so equal sites at different indices give `2G(0) − 1`).
* `v > 0` in both cases (`G(0) ≥ 1`), so `v.toNNReal` is not a truncation.
* (i) `∀ y`, CLT with `gaussianReal 0 v.toNNReal`; (ii) `∀ y, ∀ᵐ ω, ∀ δ > 0, ∀ s = ±1`, junk-free limsup with `lil n`; (iii) `∀ k y : Fin k → Site d`, vector
  `WithLp.toLp 2 (fun i => dev (y i) n ω / σ n)` in `EuclideanSpace ℝ (Fin k)`, limit `multivariateGaussian 0 (Matrix.of fun i j => cov (y i) (y j))`.
* `multivariateGaussian` is `dirac` for a non-PSD matrix; here the matrix is the limit of Gram matrices of conditional covariances
  (`Γ(f,f)(x) = Var ≥ 0`), and for `d = 2` the rank-one matrix `(16ε/π)·𝟙𝟙ᵀ`; so it is PSD and the clause is not a junk one. Re-derived the `d ≥ 3` entries from
  summation by parts: `Σ_x (1/2d)Σ_e Δ_e g_y Δ_e g_z = −2g(y−z) = 2G(y−z)`, minus `Σ Δg_yΔg_z = 1_{y=z}`, times `ℓ_n/r_n → 2dε`.
* `dev y n ω = ℓ_n(y) − 2dε(r_n − |y|)` (the cast of `localTime`, no positive part). Both Externals are hypotheses, as ruled.

---

## lem-exp-deviation — `ExpDeviation.lean` — CONCERN (low)

Paper: Lemma 9.1 (1539-1553).

### What is correct

* `∀ c₀ C₀, 0 < c₀ → c₀ ≤ C₀ → ∃ c C > 0`, before `Ω μ ℱ m n b δ α S E β`: `c, C` depend on `c₀, C₀` only.
* `0 < m`, `0 < n`, `0 < b`, `0 ≤ δ`, `0 ≤ α ≤ 1`, martingales `S : Fin m → ℕ → Ω → ℝ` over one filtration (`Martingale` already implies integrability),
  event `E` measurable with `1 − α ≤ (μ E).toReal`, bracket hypotheses `∀ i, ∀ᵐ ω, ω ∈ E → c₀ ≤ ⟨S^i⟩_n ∧ ⟨S^i⟩_n ≤ C₀` (brackets are a.e. defined).
* `β ≥ C`, `β * b ≤ c`: exact. Conclusions (i) `exp(−Cβ²)/4 − α ≤ P(S^i_n ≥ cβ)`, same for `≤ −cβ`; (ii) under the cross-bracket hypothesis
  (`∀ i ≠ j`, a.e. on `E`) and `β²δ + β³b ≤ 1`: `P(∀ i, S^i_n < cβ) ≤ C(m⁻¹ e^{Cβ²} + β²δ + β³b + e^{Cβ²} √α)`: exact, with the same `c, C`.
* The lower-bound sets `{cβ ≤ S i n ω}`, `{S i n ω ≤ −cβ}` are measurable because a martingale is adapted and `ℱ n ≤ m0`; so the "lower bounds include measurability" convention is met without an explicit conjunct.
  `{max_i S^i_n < cβ} = {∀ i, S i n ω < cβ}` since `m ≥ 1`.
* Re-checked the paper's proof route (stopping at the first predictable `⟨S^i⟩_{t+1} > 2C_0`, exponential martingale, Paley-Zygmund, second moment): it yields the stated constants' dependence.

### The concern

Lines 15-16 of the draft:

```lean
      ∀ S : Fin m → ℕ → Ω → ℝ, (∀ i, Martingale (S i) ℱ μ) → (∀ i ω, S i 0 ω = 0) →
        (∀ i, ∀ t < n, ∀ ω, |S i (t + 1) ω - S i t ω| ≤ b) →
```

assert `S^i_0 = 0` and `|S^i_{t+1} − S^i_t| ≤ b` for every `ω`, whereas the paper states them for real martingales in the usual probabilistic (almost sure) sense, and
the lemma's other hypotheses (brackets) are already almost sure. As a hypothesis a pointwise condition is stronger, so the lemma is weaker than the paper's.
The consumers build `S` from `IsCERW μ ε X`, which only gives `X_0 = 0` and unit steps almost surely (e.g. `𝒬̂_0 = |X_0|²` and the `𝒬`-increments are unbounded on
the null set of non-nearest-neighbour paths); they would have to modify `S` on a null set first. The two forms are equivalent (given a.e. hypotheses
set `S'^i_t := Σ_{s<t} (S^i_{s+1} − S^i_s) · 1_{|S^i_{s+1} − S^i_s| ≤ b}`, which is adapted, `S'^i_0 = 0`, increments `≤ b` everywhere, and `μ`-a.e. equal to `S^i`, hence
with the same martingale property, brackets, and `S^i_n` almost surely), so the a.s. form is true and is the honest transcription.
(`StoutLIL` already uses an almost-sure increment bound.)

### Exact replacement (lines 15-16)

```lean
      ∀ S : Fin m → ℕ → Ω → ℝ, (∀ i, Martingale (S i) ℱ μ) →
        (∀ i, ∀ᵐ ω ∂μ, S i 0 ω = 0) →
        (∀ i, ∀ t < n, ∀ᵐ ω ∂μ, |S i (t + 1) ω - S i t ω| ≤ b) →
```

Checked: the patched copy (`p/ExpDeviationFixed.lean`) elaborates clean. If the author prefers the pointwise form, the verdict is PASS for the statement as a
(slightly weaker) lemma and the burden moves to the two consumers.

---

## prop-bulk-profile — `BulkProfile.lean` — PASS

Paper: Proposition 9.2 (1658-1665).

* `∀ θ ∈ (0,1)`, `∀ p > 0`, `∃ C > 0` (`C(d,ε,θ,p)`), then two conjuncts over all `(Ω, μ, X)`: (a) `∀ n ≥ 2`, `μ {¬ Good} ≤ ofReal (C n^{-p})`; (b) `∀ᵐ ω, ∀ᶠ n, Good`.
  The same `C` in both, as ruled; this is also without loss (`Good` is monotone in `C`, take the larger constant).
* `Good Y n := ∀ y : Site d, euclidNorm y ≤ θ * r n → |localTime Y n y − 2dε(r_n − |y|)| ≤ C * (if d = 2 then √r_n log n else √(r_n log n))`: the `max` over `y ∈ ℤ^d`,
  `|y| ≤ θ r_n`, with the paper's two cases (`√r_n log n` for `d = 2`, `√(r_n log n)` for `d ≥ 3`). No positive part is needed (`|y| ≤ θ r_n < r_n`).
  The `let Good` parses as intended: the next line starts a new conjunct (printed term confirms).
* `n ≥ 2` gives `log n > 0`, `r n > 0`: no junk.

---

## lem-separated-brackets — `SeparatedBrackets.lean` — PASS (under the ruling)

Paper: Lemma 9.3 (1692-1699); definitions 1683-1690; `Ω_n` line 1534; `g` line 406.

### Closure reading

`∃ c₀ C₀ C, 0 < c₀ ∧ c₀ ≤ C₀ ∧ 0 < C ∧ ∃ n₀, ∀ Ω μ X, IsCERW → ∀ n ≥ n₀, μ {¬ ∀ i j, …} ≤ ofReal (C n^{-10})`: constants and `n₀` depend on `(d,ε)` only and precede the
probability space; `∃ n₀` is existential, so no junk at small `n` (`σ_n = 0`, `m_n = 0`) can make the statement easier. The bad event is the failure of some bound for some
`1 ≤ i, j ≤ m n`, as in "for `1 ≤ i ≤ m` and `1 ≤ j ≤ m`". This is what the paper's "on `Ω_n`, `P(Ω_n^c) = O(n^{-10})`" gives, with one `C`.

### Definitions (checked against 1683-1690, line by line)

* `e₁ = LatticeProb.unit ⟨0, _⟩ = Pi.single 0 1 : Site d`: the first coordinate vector of `ℤ^d`, correct dimension `d ≥ 2` (the `by omega` uses `hd`).
* `σ n = if d = 2 then √(r n * log (r n)) else √(r n)`; `k n = m n = ⌊r n ^ (1/8)⌋₊` (natural floor, `k` only used for `d = 2`).
* `y n i = ((i * ⌈r n ^ (1/4)⌉₊ : ℕ) : ℤ) • e₁ = i ⌈r_n^{1/4}⌉ e₁` (natural ceiling, then cast to `ℤ`).
* `f n i z = if d = 2 then g (z − (y n i + (k n : ℤ) • e₁)) − g (z − y n i) else g (z − y n i)`: `f_i = g_{y_i + k e₁} − g_{y_i}` for `d = 2` and `g_{y_i}` for `d ≥ 3`, `g_y = g(· − y)`.
* `g = CERW.latticeKernel d`: potential kernel (`d = 2`) and `−G` (`d ≥ 3`), as line 406.
* `B = dynkinBracket (stepProb d ε) (f n i) (f n j) (X · ω) n / σ n ^ 2` = `⟨M^{f_i}, M^{f_j}⟩_n / σ_n²` = `⟨S^i, S^j⟩_n` (the sign of `S^i = −M^{f_i}/σ_n` squares away).
* Conclusion `i = j → c₀ ≤ B ∧ B ≤ C₀` and `i ≠ j → |B| ≤ C * r n ^ (-(1:ℝ)/4)` (`-(1:ℝ)/4` parses as `(−1)/4`, printed `(-1) / 4`): exact.

### Truth check of the closure

The paper's Steps 1-3 give, on `Ω_n` for large `n`, `|⟨S^i,S^j⟩_n − Σ_ij| ≤ Cλ_n ≤ C r_n^{-1/4}`, `Σ_ii ∈ [c, C]` (`4ε/π` when `d = 2`, `2dε(2G(0) − 1)` when `d ≥ 3`) and
`|Σ_ij| ≤ C r_n^{-1/4}` for `i ≠ j`, with `Σ_ij` computed in the paper (`4ε(4g(ke₁) − 2)/log r_n`, cross terms `O(k²/|y_i − y_j|²)`). I re-derived `Σ_ii → 4ε/π`
(`4 g(k e₁) ≈ (8/π) log k = (1/π) log r_n`). `Ω_n` depends only on `X_0..X_n` and is measurable; `P(Ω_n^c) = O(n^{-10})`. So the closure is true if the paper's lemma is.

---

## prop-log-lower — `LogLowerBounds.lean` — PASS

Paper: Proposition 9.4 (1762-1776).

* `∃ c C h₀ > 0, ∃ n₀, ∀ Ω μ X, IsCERW → (i) ∧ (ii)`: constants and `n₀` depend on `(d,ε)` only; same `c` in (i) and (ii), which the paper justifies in the last sentence of Step 4.
* (i) for `n ≥ n₀` and all real `h` with `h₀ ≤ h ≤ r n / 8`: `μ {r n − h ≤ innerRadius ∧ maxRadius ≤ r n + h} ≤ ofReal (exp (−(c r_n^{d−1} e^{−Ch})))` and
  `μ {maxRadius ≤ r n + h} ≤ ofReal (exp (−(c r_n^{d−1} e^{−Ch})) + exp (−(c r_n^{d−3} h²)))`. `r n ^ (d-1)` natural power (`d ≥ 2`), `r n ^ ((d:ℝ) − 3)` real power (`r_n^{-1}`
  for `d = 2`, as in the paper), `h ^ 2` natural power. The second bound carries both exponentials, and the `∧` has no extra clause.
* (ii) `∀ᵐ ω, ∀ᶠ n, c log n < max (r_n − R_in) (R_out − r_n) ∧ (3 ≤ d → c log n < R_out − r_n)`: strict inequalities, the `d ≥ 3` clause, exactly as in (eq:log-lower-as).
* No junk: `n → ∞` statements, `log n > 0` for `n ≥ 2`, `r n > 0`.

---

## Adjacent observations (not verdicts on these nodes)

1. `scratch/Frozen/FluctuationRates.lean:21` has the same `•`/`∆` precedence error as InnerRadius line 20 (another batch; `draft-audit-1.md` also reports it).
2. The Externals `MartingaleCLT` and `StoutLIL` were read only for consumption by nodes 4 and 6 (Hall-Heyde Corollary 3.1 with constant limit variance needs no nested-σ-field
   condition; Stout's predictable bound `B_n` and the `loglog(⟨S⟩ ∨ e^e)` condition match Step 3 of Theorem 8.1). They state `S 0 = 0` pointwise; a consumer that builds the
   martingale from increments (as `dynkinMart` does) meets this without a null-set modification, so I record no concern here.
