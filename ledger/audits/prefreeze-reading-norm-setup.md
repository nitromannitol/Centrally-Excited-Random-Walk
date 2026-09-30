# Draft audit 2 (refute-first): six norm-section drafts under `scratch/Frozen/`

Paper: `paper/limit-shapes.tex` (`\drift` = κ, written `ε` in Lean; `\gauge` = Ψ; `\nf{a}{b}` = a/b).
Conventions: `CORRESPONDENCE.md`, "Transcription conventions"; `ledger/readings.yaml` for the gate readings.
No Lean file in the repository was edited. All machine evidence comes from probe files compiled in the
session scratchpad (`.../scratchpad/au2_nodes2/*.lean`, reproduced in the appendix) with
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dlinter.unusedVariables=true` against the built
`CERW.Model`, `CERW.Support.Drift.Existence`, `CERW.Support.Statements`, `CERW.Generic.Kernel.Integrable` and
`CERW.Frozen.PotentialGeometry`. This is the independent refute-first key; the three earlier readings are separate.

## Audited bytes

| draft | md5 at audit time |
|---|---|
| `NormShape.lean` | `837d2a05dfa8a5eb8f2d89b2681310b1` |
| `NormBallPotential.lean` | `b7bd6f5be936b223fbe9de6e49bd286f` |
| `NormLocalTime.lean` | `1fa8e5a16b94b3bb78a88390a5e90923` |
| `FreedmanBound.lean` | `2efaf8dedf3597173de19d4c7c34d860` |
| `CellGradient.lean` | `8dc5ef680b72c5fedd228af54013baa8` |
| `NormPotentialGeometry.lean` | `de292bff476486a6a74542b5c569128d` |

`NormPotentialGeometry.lean` was re-wrapped at 14:24 (the `let A` line was 104 characters; it is now three
lines) while the audit was running. I audited the earlier bytes and re-checked the re-wrapped file: the elaborated
statement (`pp.numericTypes`) is identical (empty diff), and the consumption probe E5 was re-run against the current text. The six `Prop`s of `CERW/Support/Statements.lean` agree
definitionally with the six drafts (probe E5). All six drafts elaborate with no errors; the only warnings are the six
`declaration uses sorry`. No line exceeds 100 characters.

## Summary

| node | draft | verdict |
|---|---|---|
| thm-norm-shape | `NormShape.lean` (`CERW.Frozen.norm_shape`) | PASS |
| lem-ballpotential | `NormBallPotential.lean` (`CERW.Frozen.norm_ball_potential`) | PASS (true generalisation in `ε`, machine-checked; note N1) |
| lem-local | `NormLocalTime.lean` (`CERW.Frozen.norm_local_time_potential`) | PASS |
| lem-freedman | `FreedmanBound.lean` (`CERW.Frozen.freedman_bound`) | PASS |
| lem-cell | `CellGradient.lean` (`CERW.Frozen.cell_gradient`) | PASS (requirement R1: the existence of `μ` must be proved; it is a non-vacuity obligation, not a statement error) |
| lem-geometry | `NormPotentialGeometry.lean` (`CERW.Frozen.norm_potential_geometry`) | PASS (true generalisation in `ε`; notes N2, N3) |

No DEFECT and no CONCERN that requires replacement Lean text. The items under "Requirements and notes" concern
gates (existence witness, hazard and exponent declarations), not the meaning of any statement.

## Machine evidence

All probe sources are in the appendix. Every probe compiles with empty output (the consumption file prints only the
six `sorry` warnings of the statement copies).

* **E0. Elaboration.** `#check` with `pp.numericTypes true` for all six drafts. Every cast is in `ℝ`; there is no
  natural-number division or subtraction. Examples: `(↑d + 1) * ↑n / (2 * ↑d * ε * CERW.normBallVolume Ψ)` with
  exponent `1 / (↑d + 1)`; `Real.log ↑n ^ (2 : ℕ)`; `‖y‖ ≤ (2 : ℝ) * ↑n`; `R ^ ((1 : ℝ) / ((2 : ℝ) * ↑d))`.
  Precedence is as intended everywhere that could go wrong: `¬ a ≤ b` is `¬ (a ≤ b)`; `⊆` binds tighter than `∧`;
  `C * if d = 2 then .. else ..`; `(↑d * ωd)⁻¹ * ∫ θ, .. ∂ℙ.toSphere`;
  `2 * ε / ωd * ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d`; the `let A`/`let B` chain.
* **E1. The hypothesis package is inhabited** (`Hyp.lean`). From `IsNorm`, `IsSubgradient` at every nonzero site, `ξ 0 = 0`
  and the ellipticity inequality, the probabilities are nonnegative (`subgradient_abs_coord_le`: `|ξ_i| ≤ Ψ(e_i)`, by
  Euler's relation), and `CERW.Support.Drift.exists_isDriftCERW` gives a probability space and a process with
  `IsDriftCERW μ ε ξ X` (`hyp_package_realisable`). The whole package, including `IsNorm` and the subgradients, is
  witnessed at the Euclidean norm with `ξ(x) = x/|x|` for every `0 < ε < 1/d` (`euclid_package_inhabited`).
* **E2. Junk values** (`Junk.lean`). `IsNorm Ψ` implies `LipschitzWith K Ψ` with `K = Σ_i Ψ(e_i)` (`lipschitz`); hence
  `∀ᵐ v, DifferentiableAt ℝ Ψ v` (`ae_differentiable`, Rademacher), so the Mathlib convention `gradient Ψ v = 0` at
  non-differentiable points is seen only on a Lebesgue-null set. `gradient Ψ` is Borel measurable for every `Ψ`
  (`measurable_gradient`), `‖gradient Ψ v‖ ≤ K` at every point (`norm_gradient_le`), and the integrand of `normPotential`
  is integrable on every bounded measurable set (`integrableOn_normPotential_integrand`, through the existing
  `CERW.Generic.Kernel.integrableOn_and_setIntegral_le`): the Bochner integral of eq:potential-norm is never the junk `0`.
  `(∞ : WithTop ℕ∞) = ((⊤ : ℕ∞) : WithTop ℕ∞)` by `rfl`: the test functions of `IsDistribLaplacian` are smooth, not analytic.
* **E3. Euclidean consistency** (`Eucl.lean`). `gradient (‖·‖) v = unitDir v` at every `v` (including `0`), hence
  `normPotential d ε (‖·‖) D y = potential d ε D y`; and `norm_ball_potential` at `Ψ = ‖·‖`, `ε > 0` is the ball clause of the
  already-PROVED `CERW.Frozen.potential_geometry`. So `normPotential` means what `potential` means, and the norm
  statements specialise to the audited Euclidean ones.
* **E4. Linearity in `ε`** (`Lin.lean`). `normPotential d ε Ψ D y = ε * normPotential d 1 Ψ D y`; `ball_all_eps` derives the ball
  identity for every real `ε` from `ε = 1`; `sup_bound_all_eps` derives the sup bound for every `ε > 0` from `ε = 1` with the same `C`.
* **E5. Consumption** (`Cons.lean`). Each draft is applied to its intended first consumer with the binder order usable as
  written: `norm_shape` and `norm_local_time_potential` at the Euclidean package (and `norm_shape`'s recurrence clause
  extracted), `freedman_bound` at the constant martingale, `cell_gradient` at `Ψ = ‖·‖` with a measure hypothesis,
  `norm_potential_geometry` at `D = ball 0 1`, `norm_ball_potential`. In `cell_gradient` the constant is obtained by
  `Classical.choose` before `Ψ` and `ξ` are given, which exhibits `C(d)` independent of the norm. Also
  `example : Statements.X := @CERW.Frozen.X` for all six `X`: the Support-side `Prop`s are the drafts.
* **E6. Existing bridge.** `CERW.Support.Drift.isCERW_iff_isDriftCERW`: `IsCERW μ ε X ↔ IsDriftCERW μ ε (x ↦ u_x) X`;
  `driftFirstStep_unit`/`driftFirstStep_neg_unit`: the first-departure probabilities are `1/(2d) ∓ (ε/2) w_i` at `±e_i`.
* **E7. Numerical check of the norm potential** (Python, `d = 2`, `Ψ = ‖·‖_∞`, `D = [-1,1]²`, `ε = 1`, grid `4001²`).
  `U_D(0,0) = 3.9988` against `2dε(1-0) = 4`; `U_D(0.3,0.2) = 2.798` against `2.8`. For `s = 1/2`: the sphere average
  `A = 2.19937`, the right side of eq:newton `B = 2.19934`, `F(s) = 0.62219`, `2dε c_Ψ F = 1.7598 ≤ B ≤ 2dε Λ_Ψ F = 2.4888`
  with `c_Ψ = 2^{-1/2}`, `Λ_Ψ = 1`. So the normalisations `2ε/ω_d`, `1/(d ω_d)`, and the roles of `c_Ψ`, `Λ_Ψ` as transcribed are right.
* **E8. Simulation of the walk** (Python, `d = 2`, `ε = 0.4`, subgradients `ξ(x) = (sgn x_1, 0)` if `|x_1| ≥ |x_2|` else
  `(0, sgn x_2)` for `‖·‖_∞`, and `ξ(x) = (sgn x_1, sgn x_2)` for `‖·‖_1`; the drift points to the origin). `|A_n| / (|B_Ψ| r_n^d)`
  with `r_n` as transcribed (`|B_{∞}| = 4`, `|B_1| = 2`): `0.956` (`‖·‖_∞`, `n = 10^6`), `0.987` (`‖·‖_∞`, `n = 8·10^6`), `0.956`
  (`‖·‖_1`, `n = 10^6`), increasing toward `1`. With the sign of the drift flipped (outward), `|A_n| = 626206` against the predicted `24137` (ratio `25.9`). This corroborates the sign of the kernel and the constant in `r_n`.
* **E9. Gate pre-reads** (static, with the vendored `leanform_tools` regexes, no manifest edit): hazard tokens per block
  (`CellGradient`: `bochner`; `NormPotentialGeometry`: `toReal`, `inv`, `bochner`; the other four: none); exponent comparison
  (see R3).

## The Model definitions used (check 6)

Read in `CERW/Model/*.lean`; each means what the paper means.

* `IsNorm Ψ`: subadditive, `Ψ(t x) = |t| Ψ(x)`, `Ψ x = 0 → x = 0`: a norm. Nonnegativity, evenness, Lipschitz: E2.
* `IsSubgradient Ψ x ξ := ∀ y, Ψ x + ⟪ξ, y - x⟫ ≤ Ψ y`: paper line 196 verbatim. Euler's relation and `|ξ_i| ≤ Ψ(e_i)` follow (E1).
* `coordVec i = EuclideanSpace.single i 1` = `e_i`. `toSpace x` has coordinates `(x i : ℝ)`, so `Ψ (toSpace x) = Ψ(x)`.
* `normBallVolume Ψ = (volume {y | Ψ y < 1}).toReal` = `|B_Ψ|`. The set is open and bounded (Ψ is continuous and `≥ c_Ψ ‖·‖`), so the volume is finite and positive and `toReal` is honest; `volume` on `EuclideanSpace` is Lebesgue measure. `normMax`, `normMin` are `sSup`, `sInf` of `Ψ` on the compact nonempty Euclidean sphere, hence the true maximum and minimum.
* `driftFirstStep d ε w e`: `1/(2d) - (ε/2) w_i` at `e = +e_i`, `1/(2d) + (ε/2) w_i` at `-e_i`, `0` otherwise (E6). `driftStepProb d ε ξ x n e` is that with `w = ξ (x n)` when `x n ≠ 0 ∧ x n ∉ (range n).image x`, else the simple random walk step `srwStep` (`1/(2d)`, real division). This is eq:kernel and the sentence "first departure from each site `x ≠ 0`". `IsDriftCERW`: measurability, `X 0 = 0` a.s., and the cylinder factorisation through `ofReal (driftStepProb ..)`; it fixes the law of the path. It is `IsCERW` when `ξ = u` (E6), and it is realisable (E1).
* `localTime X n x = #{j < n : X j = x}` = `ℓ_n(x)`; `departureRange X n = (range n).image X` = `A_n`; `maxLocalTime` = `Finset.sup` of `localTime` over `A_n` = `max_x ℓ_n(x)`.
* `freshCount X s t = #{j ∈ [s,t) : X j ∉ departureRange X j}` = `k_{s,t}` (`A_j = {X_0..X_{j-1}}`, `I_j = 1{X_j ∉ A_j}`, so `I_0 = 1`).
* `intervalMax X s t = sup_{x ∈ image X [s,t)} #{j ∈ [s,t) : X j = x}` = `M_{s,t}` (sites not visited in `[s,t)` contribute `0`).
* `cell x = x + [-1/2,1/2)^d`; `cellCenter v i = ⌊v i + 1/2⌋`; `cellSet X n = ⋃_{x ∈ A_n} cell x` = `D_n`; `cellLocalTime X n v = ℓ_n(cellCenter v)` = `ℓ̃_n(v)` (equal to `ℓ_n(x)` on `C_x`, `0` off `D_n`).
* `normPotential d ε Ψ D y = 2 * ε / ω_d * ∫ v in D, ⟪gradient Ψ v, v - y⟫ / ‖v - y‖ ^ d`: eq:potential-norm, with `‖v - y‖ ^ d` the natural-number power. E2, E3.
* `tail d D s = (d ω_d)⁻¹ * ∫ v in D ∩ {s < ‖v‖}, ‖v‖ ^ (1 - d)` = `F(s)` of eq:Fdef (used and proved in the Euclidean frozen lemma).
* `predBracket μ ℱ S T n = Σ_{t<n} μ[(S_{t+1} - S_t)(T_{t+1} - T_t) | ℱ_t]`: the predictable covariation through time `n`; `predBracket μ ℱ Z Z n ≤ n` for increments `≤ 1`, which the paper's proof of Lemma 3.2 uses.
* `IsDistribLaplacian Ψ m := ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∫ φ ∂m = ∫ Ψ * Laplacian.laplacian φ`: Mathlib's Laplacian is `Σ_i ∂_i²` in an orthonormal basis; both sides are genuine integrals of continuous compactly supported functions against locally finite measures.

---

## 1. thm-norm-shape (`CERW.Frozen.norm_shape`, paper 329-342): PASS

1. **Quantifiers.** No constants. `d ≥ 2`, `Ψ` and `ξ`, `ε`, the probability space and `X` all precede the a.s. clause. The only quantifiers
   inside `∀ᵐ` are `∀ η` (parts i, ii) and `∀ x`. The statement holds for every admissible `ξ`, as the paper says "chosen".
2. **Exponents, case splits, normalisation.** `r_n = ((d+1) n / (2 d ε |B_Ψ|))^{1/(d+1)}` exactly as eq:radius-norm (E0 shows all casts are real; E8 corroborates the constant).
   (i) is `{Ψ < (1-η) r_n} ⊆ A_n ⊆ {Ψ < (1+η) r_n}` for `0 < η < 1`, eventually. (ii): `(1/r_n) max_x |ℓ_n(x) - 2dε (r_n - Ψ(x))_+| → 0` is
   `∀ η > 0, ∀ᶠ n, ∀ x, |ℓ_n(x) - 2dε max(r_n - Ψ x, 0)| ≤ η r_n`, equivalent because `r_n > 0` for `n ≥ 1` and the maximum is over finitely many sites
   (off `A_n` and off `{Ψ < r_n}` both terms vanish). (iii) is `∀ x, ∃ᶠ j, X j ω = x`.
3. **Junk.** `r_0 = 0` and `n = 0` are irrelevant under `∀ᶠ n`. `0 ^ (1/(d+1)) = 0` is the true value. The denominator `2dε|B_Ψ|` is positive. No `log`, no `sInf`, no Bochner integral, no `toReal` of an infinite volume.
4. **Weakening or strengthening.** None. All three parts are present with the paper's strength. The extra hypothesis `ξ 0 = 0` is the paper's own notation item (line 294); the law never reads `ξ 0`, so it does not change the conclusion for this node (note N4).
5. **Hypotheses.** `d ≥ 2`, `ε > 0`, eq:ellipticity as `∀ i, ε Ψ(e_i) < 1/d` (`max_i` is `∀ i`), `Ψ` a norm, `ξ(x) ∈ ∂Ψ(x)` at `x ≠ 0`: exactly the paper's. Binder classes: `hd` STANDING; `Ψ hΨ ξ hξ ε hε hεΨ Ω μ X hX` SOURCE/TYPING; `hξ0` STANDING (idle here); no EXCESS. Non-vacuity: E1.
6. **Model.** `IsDriftCERW`/`driftStepProb` vs eq:kernel; `departureRange`, `localTime`; `normBallVolume`: see above.

Refutation attempts that failed: the sign of the drift (E8: with the transcribed kernel the range has size `≈ |B_Ψ| r_n^d`; with the opposite sign it is 26 times larger); a wrong `|B_Ψ|` versus `ω_d` (E8, ratios `→ 1` for `ℓ¹` and `ℓ^∞`); quantifier slip between `ξ` and `∀ᵐ` (none); `η` range (`η < 1` keeps `(1-η) r_n > 0`).

## 2. lem-ballpotential (`CERW.Frozen.norm_ball_potential`, paper 360-365): PASS

1. **Quantifiers.** `hd`, `Ψ`, `ε`, `ρ > 0`, `y`: all universally quantified, no constants.
2. **Exponents, normalisation.** `U_{Ψ<ρ}(y) = 2dε (ρ - Ψ y)_+` as `2 * d * ε * max (ρ - Ψ y) 0`; `U_D` is `normPotential` (eq:potential-norm exactly; E3 ties it to `potential`). E7: `U(0,0) = 3.9988 ≈ 4`, `U(0.3,0.2) = 2.798 ≈ 2.8`.
3. **Junk.** Gradient at non-differentiable points is `0` on a null set (E2). The integrand is integrable, `‖v - y‖ ^ d = 0` only at `v = y` (a point). `max · 0` is the positive part. No other.
4. **The question about every real `ε`.** The draft binds `(ε : ℝ)` with no hypothesis; the paper's `ε` satisfies eq:ellipticity. The identity is true for every real `ε`: `normPotential d ε Ψ D y = ε * normPotential d 1 Ψ D y` and the right side of the lemma is `ε` times an `ε`-free term (E4, `ball_all_eps`). This is a strengthening, true, machine-checked; it is recorded in the NL twin. For `ρ ≤ 0` the identity would also hold (empty ball, both sides `0`), but the paper assumes `ρ > 0` and the draft keeps it.
5. **Hypotheses.** `d ≥ 2` STANDING; `Ψ` norm, `ρ > 0`, `y`: SOURCE. No EXCESS. The dropped hypotheses (`0 < ε`, ellipticity) are only weakenings of the assumptions (a stronger lemma).
6. **Model.** `normPotential`: E2, E3.

Refutation attempts that failed: negative and zero `ε` (linear, E4); `y` outside the ball (the lemma gives `0`, consistent with `f(y) = (ρ - Ψ y)_+ = 0` in eq:gradient-identity, and with E7 at interior points where the value is `4(1 - Ψ y)`); unit-ball-volume normalisation (E3 against the proved Euclidean statement; E7 in `ℓ^∞`).

## 3. lem-local (`CERW.Frozen.norm_local_time_potential`, paper 384-400): PASS

1. **Quantifiers.** `∀ Ψ, IsNorm Ψ → ∀ ε, 0 < ε → ellipticity → ∀ p > 0, ∃ C > 0, ∀ ξ (admissible) → ∀ (Ω μ X), IsDriftCERW → ∀ n ≥ 2`. So `C = C(d, ε, Ψ, p)` precedes the choice of `ξ`, the probability space and `n` (paper line 295: constants depend on `d, ε, p, Ψ` and not on `ξ`). E5 applies the statement in exactly this order.
2. **Exponents, case split, normalisation.** (i) `max ℓ_n ≤ C |A_n|^{1/d} + C (log n)^2` with `(1:ℝ)/d` and `Real.log n ^ 2` for every `d ≥ 2` (the paper has no case split here). (ii) `M_{s,t} ≤ C k_{s,t}^{1/d} + C (log n)^2` for `0 ≤ s < t ≤ n` (`∀ s t, s < t → t ≤ n`). (iii) for `|y| ≤ 2n`: `|ℓ̃_n(y) - U_{D_n}(y)| ≤ C log n + C · (if d = 2 then √M · log n else √(M log n))` with `M = max ℓ_n`, i.e. `(max ℓ)^{1/2} log n` and `(max ℓ · log n)^{1/2}`. The simultaneous probability bound is `μ {ω | ¬ (i ∧ ii ∧ iii)} ≤ ofReal (C n^{-p})`. All as displayed (E0).
3. **Junk.** `log n` at `n ≥ 2`; `Real.sqrt` of `maxLocalTime ≥ 0` and `maxLocalTime * log n ≥ 0`; `card ^ (1/d)` with a base `≥ 0`; `n ^ (-p)` with `n ≥ 2`; `Finset.sup` over a possibly empty set equals `0`, the true value (`intervalMax` is over a nonempty image when `s < t`); the integrand of `normPotential` over the bounded cell set is integrable (E2). `ofReal` arguments are `≥ 0`.
4. **One `C`.** The paper's `C` changes from line to line; a single `C > 0` is enough (enlarging `C` only weakens every clause and the probability bound). No weakening, no strengthening.
5. **Hypotheses.** The standing assumptions of Sections 2-3: norm, `ε > 0` with eq:ellipticity, chosen subgradients, `d ≥ 2`, `n ≥ 2`. Binder classes: `hd` STANDING; `Ψ hΨ ε hε hεΨ p hp` SOURCE; `ξ hξ` SOURCE; `hξ0` STANDING (idle in the statement, needed in the paper's Dynkin sum); `Ω μ X hX n hn` SOURCE/TYPING. No EXCESS. Non-vacuity: E1.
6. **Model.** `intervalMax`, `freshCount`, `maxLocalTime`, `cellLocalTime`, `cellSet`, `normPotential`: see above. `IsDriftCERW`: E6.

Refutation attempts that failed: dependence of `C` on `ξ` (none: `ξ` is bound after `C`); the paper's `ℓ̃_n` versus `cellLocalTime` off `D_n` (both `0`); `k_{s,t}` when `s = 0` (`I_0 = 1`, so `k_{0,n} = |A_n|`, which the paper uses to recover (i)); `d = 2` versus `d ≥ 3` branch placement (the `if` governs only the square-root term); small `n` (for `n` with `C n^{-p} ≥ 1` the clause is trivial).

## 4. lem-freedman (`CERW.Frozen.freedman_bound`, paper 436-441): PASS

1. **Quantifiers.** `∀ p > 0, ∃ C > 0, ∀ n ≥ 2, ∀ (Ω μ ℱ Z), Martingale Z ℱ μ → (increments ≤ 1 a.s.) → μ {..} ≤ ofReal (C n^{-p})`. `C = C(p)` precedes `n`, the space, the filtration and `Z` (paper: "There exists `C(p)`").
2. **Exponents, normalisation.** `|Z_n - Z_0| ≤ C (√(⟨Z⟩_n log n) + log n)`; `⟨Z⟩_n = predBracket μ ℱ Z Z n = Σ_{t<n} E((ΔZ_t)² | ℱ_t)` (the paper's convention, for which `⟨Z⟩_n ≤ n` in its proof). One `C` for the constant and the probability, as in the paper.
3. **Junk.** `log n` at `n ≥ 2`. `Real.sqrt` of `⟨Z⟩_n · log n`, nonnegative almost surely (conditional expectation of a nonnegative function), so `sqrt` is the true root off a null set. The bracket is a conditional expectation defined up to a null set; the event is measured by `μ`, so the choice of version is immaterial. Integrability of `Z` is implied by `Martingale` with bounded increments (a non-integrable `Z_i` would have `μ[Z_i | ℱ_i] = 0`, forcing `Z_i = 0` a.e.).
4. **Filtration and increments.** The filtration is arbitrary (Freedman's inequality holds for every filtration to which `Z` is a martingale, and this is how the lemma is used: the natural filtration of the walk). "Increments have absolute value at most 1" is written almost surely and for all times `t`, which is the paper's hypothesis (a martingale is defined up to null sets, so a.s. is the natural reading); only `t < n` matters for the conclusion, so the hypothesis is not excessive in any way the paper does not already accept.
5. **Hypotheses.** No dimension, no norm. Binders: `p hp n hn Ω μ ℱ Z` SOURCE/TYPING; no EXCESS. Non-vacuity: E5 (constant martingale).
6. **Model.** `predBracket` is the predictable quadratic variation.

Refutation attempts that failed: pointwise versus a.e. increments (a.e. is more general and true: modify `Z` on a null set); `⟨Z⟩_n` using `ℱ_t` versus a larger filtration (true for each); `Z_0` not constant (the lemma centres at `Z_0`; the bracket ignores `Z_0`); `n ≥ 2` against `log n > 0`.

## 5. lem-cell (`CERW.Frozen.cell_gradient`, paper 454-459): PASS (requirement R1)

1. **Quantifiers.** `∃ C > 0, ∀ Ψ, IsNorm Ψ → ∀ ξ, (admissible) → ξ 0 = 0 → ∀ m, IsLocallyFiniteMeasure m → IsDistribLaplacian Ψ m → ∀ x, ..`. `C = C(d)` is chosen before the norm, the subgradients, the measure and the site: it does not depend on `Ψ` (the paper states `C(d)`; its proof gives a dimensional constant: the inequality is homogeneous in `Ψ`, `h(x) = 0` removes the only `Ψ`-dependent term, and the mollification bound is dimensional; E5 exhibits the order). `ξ` is quantified after `C`.
2. **Exponents, normalisation.** `∫_{C_x} |∇Ψ(v) - ξ(x)| dv ≤ C μ(B(x, 6√d))` with `C_x = cell x`, the open ball of radius `6 * Real.sqrt d` about `toSpace x`. I re-derived the radius: `A = 2√d` bounds the `2d` neighbouring cells, the mollified averaging gives `μ(B(x, 2A + r))` with `r < A`, hence `μ(B(x, 3A)) = μ(B(x, 6√d))`; the open ball suffices. The inequality is in `ℝ≥0∞` with `ofReal` on the nonnegative integral; `m` is finite on balls (locally finite).
3. **Junk.** `gradient Ψ = 0` on the null non-differentiability set only; the integrand `‖gradient Ψ v - ξ x‖` is measurable and bounded by `K + ‖ξ x‖` on the bounded cell (E2), so the integral is genuine. `IsDistribLaplacian`: both sides genuine integrals, `ContDiff ℝ ∞` smooth (E2), `Laplacian.laplacian` is `Σ ∂_i²`.
4. **Weakening or strengthening.** The draft quantifies over every locally finite measure with the defining identity. Two such measures coincide (Radon measures are determined by integrals against `C_c^∞`), so this is the paper's `μ`, **provided** one exists. The paper proves existence (mollification gives nonnegative Laplacians, hence a positive Radon measure). If no such `m` existed for some norm the statement would be vacuous there; the paper's argument shows this does not occur, but the existence is not machine-witnessed (R1). `ξ 0 = 0` is needed for `x = 0` (for `x = 0` it is a subgradient because `Ψ ≥ 0`), and `x` ranges over all of `Z^d`, as the paper says.
5. **Hypotheses.** `hd` STANDING; `Ψ hΨ ξ hξ hξ0` SOURCE; `m`, `IsLocallyFiniteMeasure m` (positive Radon measure), `IsDistribLaplacian Ψ m` (the definition of `μ`, line 449) SOURCE; `x` SOURCE. No EXCESS.
6. **Model.** `cell`, `toSpace`, `IsDistribLaplacian`: above.

Refutation attempts that failed (analytic; no machine artifact beyond E2 and E5): scaling `Ψ → λΨ` (both sides scale by `λ`, so `C` cannot depend on `Ψ`); `ℓ^1` at `x = 0` and next to a coordinate hyperplane (the cell gradient equals `ξ(x)` or differs by `O(1)` on a set that the singular measure `μ` charges); `ℓ^∞` at the diagonal corner `x = (N, N)` (the left side is a positive constant and `μ` has a ridge through the ball); `x = 0` with `ξ(0) = 0`; the Euclidean norm at distance `N` (both sides of order `1/N`).

## 6. lem-geometry (`CERW.Frozen.norm_potential_geometry`, paper 509-527): PASS

1. **Quantifiers.** `∀ Ψ, IsNorm Ψ → ∃ C > 0, ∀ ε > 0, ∀ D, MeasurableSet D → IsBounded D → (i) ∧ (ii) ∧ ∀ s > 0, (iii)`. `C = C(d, Ψ)`: chosen after `Ψ` and before `ε` and `D` (the paper writes "Let `D` be bounded measurable. There exists `C(d, Ψ)`"; the notation says `C` does not depend on `D`, and the lemma is used uniformly over `D_n`). Since `U_D` is linear in `ε` and `C ε R^{1/d}`-type bounds carry an explicit `ε`, placing `∃ C` before `∀ ε` loses nothing (E4).
2. **Exponents, normalisation.** (i) `|U_D(y)| ≤ C ε R^{1/d}`; (ii) `|U_D(y) - U_D(z)| ≤ C ε R^{1/(2d)} ‖y - z‖^{1/2}`; (iii) for `s > 0`, `A = B` with `A = (d ω_d)⁻¹ ∫_{S} U_D(sθ) d(toSphere)` and `B = (2ε/ω_d) ∫_{D ∩ {|v| > s}} Ψ(v)/|v|^d`. `toSphere` has total mass `d ω_d` (`Measure.toSphere_apply_univ`) and is the polar-coordinates measure, so `A` is the mean of `U_D` over the sphere of radius `s`; this is the normalisation of the already-frozen Euclidean lemma. `2dε c_Ψ F(s) ≤ B ≤ 2dε Λ_Ψ F(s)` and, for `Ψ = ‖·‖`, `B = 2dε F(s)`. E7 checks `A = B`, both bounds, and the constants numerically for `ℓ^∞`.
3. **Junk.** `R = (volume D).toReal` finite because `D` is bounded; `(d ω_d)⁻¹` with `d ≥ 2`, `ω_d > 0`; `Ψ v / ‖v‖ ^ d` only where `‖v‖ > s > 0`; `R = 0` gives `U_D = 0` and `0 ^ (1/d) = 0` (both sides `0`); `normMin`, `normMax` are the true min and max; `normPotential` integrand integrable (E2); the sphere integrand is continuous by (ii); the integrand of `B` is bounded by `Λ_Ψ s^{1-d}` on a bounded set, so integrable.
4. **Reading of the Euclidean clause.** "It equals `2dκF(s)` for the Euclidean norm" is `(∀ v, Ψ v = ‖v‖) → B = 2dε F(s)`, a clause about `B` inside the universally quantified `Ψ`. This is the natural reading (the Euclidean case of the lemma); for `Ψ = ‖·‖` it is non-trivial. Not a weakening.
5. **`ε`.** The draft allows every `ε > 0`; the paper's `ε` also satisfies eq:ellipticity, which this lemma does not use. All clauses are `ε`-homogeneous and the orientation of the inequalities in (iii) needs `ε > 0`, so this is a true generalisation.
6. **Model.** `normPotential`, `tail`, `normMax`, `normMin`, `toSphere`: above.

Refutation attempts that failed: normalisation of the sphere average (E7 numeric `A = B` with `ω_2 = π`); the roles of `c_Ψ` and `Λ_Ψ` (E7: `c_Ψ = 2^{-1/2}`, `Λ_Ψ = 1` for `ℓ^∞`; the bounds hold and are not vacuous); `D` null or tiny (both sides `0`); order of `∃ C` and `∀ ε` (equivalent, E4); `s` so large that `D ∩ {|v| > s} = ∅` (`B = tail = 0`).

---

## Junk-value ledger (check 3), all six drafts

| item | where | status |
|---|---|---|
| `gradient Ψ = 0` at non-differentiable points | `normPotential`, `cell_gradient` | harmless: null set (E2), only under integrals |
| Bochner integrals | `normPotential`, `cell_gradient`, `A`, `B`, `tail`, `IsDistribLaplacian` | all integrable (E2 and the bounds above) |
| division `/ (d:ℝ)`, `/ ωd`, `(d ωd)⁻¹`, `/ (2dε|B_Ψ|)` | several | denominators `> 0` (`d ≥ 2`, `ωd > 0`, `ε > 0`, `|B_Ψ| > 0`) |
| `‖v - y‖ ^ d` at `v = y` | `normPotential` | `0/0 = 0` at one point, null |
| `Real.log n` | `lem-local`, `lem-freedman` | `n ≥ 2`, so `> 0` |
| `rpow` | `r n`, `card ^ (1/d)`, `R ^ (1/d)`, `n ^ (-p)` | bases `≥ 0` (`0 ^ positive = 0` is the true value) |
| `toReal` | `ωd`, `normBallVolume`, `R` | finite volumes of bounded sets |
| `sSup`/`sInf` | `normMax`, `normMin` | compact nonempty sphere, continuous `Ψ`: true max/min |
| `Finset.sup` | `maxLocalTime`, `intervalMax` | empty value `0` is the true maximum of counts |
| `Real.sqrt` | `lem-local`, `lem-freedman` | arguments `≥ 0` (a.s. for `predBracket`) |
| `ENNReal.ofReal` | all `μ`-bounds, `cell_gradient` | arguments `≥ 0` |

## Requirements and notes (none changes a verdict)

* **R1 (lem-cell, non-vacuity witness, gate B.5).** `IsDistribLaplacian Ψ m` is the only hypothesis family without a machine
  witness: a grep over `CERW/`, `wip/` and `ledger/` finds no existence lemma (`Laplacian.lean` promises one). The statement is
  equivalent to the paper's only if a locally finite `m` with the identity exists for every norm `Ψ` (true: mollification
  and Riesz). Add `exists_isDistribLaplacian (hd : 1 ≤ d) (hΨ : IsNorm Ψ) : ∃ m, IsLocallyFiniteMeasure m ∧ IsDistribLaplacian Ψ m`
  to the frontier; `lem-local`'s proof needs it anyway (for eq:hessian-growth). No change to the frozen text is needed.
* **R2 (hazards).** `check_hazards` will report `bochner` for `CellGradient` and `toReal`, `inv`, `bochner` for
  `NormPotentialGeometry`. Proposed `ledger/readings.yaml` entries:
  `lem-cell: bochner: "the integrand |∇Ψ - ξ(x)| is measurable and bounded by K + |ξ(x)| on the bounded cell, hence integrable; gradient Ψ = 0 only on the Lebesgue-null set where the Lipschitz function Ψ is not differentiable"`;
  `lem-geometry: toReal: "ω_d is finite and positive; R = (volume D).toReal is finite because D is bounded", inv: "(d·ω_d)⁻¹ with d ≥ 2 and ω_d > 0", bochner: "normPotential's integrand is integrable for bounded measurable D (|∇Ψ| ≤ K, |v-y|^{1-d} integrable); the sphere integral is of a continuous function (clause ii); the integral defining B has a bounded integrand on a bounded set"`.
* **R3 (exponent gate).** The vendored `check_exponents.canon` understands `\frac` but not the paper's `\nf{a}{b}` (`\nicefrac`), so it reports `\nf{1}{d}`, `\nf12`, `\nf{1}{2d}`, `\nf{1}{2}` as absent from the Lean text on `lem-local` and `lem-geometry`
  (they are present as `(1:ℝ)/d`, `sqrt`, `(1:ℝ)/(2*d)`, `(1:ℝ)/2`). Either teach `canon` the `\nf{a}{b}` macro and the two-token form `\nf12`, or record waivers. The remaining genuine difference is `d-1` in `lem-geometry` (`s^{d-1}` of the sphere normalisation), which Lean carries as the unit-sphere average `(d ω_d)⁻¹ ∫ ... d(toSphere)`:
  `lem-geometry: - detail: "d-1: definition: the paper's 1/(d ω_d s^{d-1}) ∫_{|v|=s} dS is the average over the unit sphere, written (d * ωd)⁻¹ * ∫ θ, .. (s • θ) ∂volume.toSphere", kind: definition`. And `lem-local` for `\nf12`: `kind: notation` ("the paper's (·)^{1/2} is Real.sqrt").
* **N1 (lem-ballpotential).** Dropping `0 < ε` and ellipticity is a true strengthening (E4). If the author prefers a literal transcription, add `(hε : 0 < ε)` after `ε`; I recommend keeping the draft: it is weaker in hypotheses, and any consumer at an admissible `ε` instantiates it.
* **N2 (lem-geometry).** `C` before `ε` is equivalent to the paper's reading (E4). No change.
* **N3 (lem-geometry).** The Euclidean clause is an implication in `Ψ`; an equivalent and possibly clearer spelling is to omit it (it is the `Ψ = ‖·‖` instance of the `A = B` clause and of the equality of the two bounds because `c_Ψ = Λ_Ψ = 1`). Keeping it is harmless and mirrors the paper's sentence.
* **N4 (`hξ0`).** In `norm_shape` and `norm_local_time_potential` the hypothesis `ξ 0 = 0` does not affect the conclusion (the law reads `ξ` only at nonzero sites). It is the paper's convention (line 294), it is essential in `cell_gradient`, and it keeps the three norm statements uniform; removing it from the two probability statements would be a harmless strengthening if ever wanted.
* **N5 (`check_clauses` readings).** Proposed one-line readings: `thm-norm-shape`: "one ∀ᵐ over (i),(ii),(iii); (ii) is ∀η ∀ᶠ n ∀x with η r_n; r_n by eq:radius-norm with |B_Ψ| = normBallVolume"; `lem-ballpotential`: "every real ε: the identity is linear in ε"; `lem-local`: "C after (Ψ, ε, p), before ξ, (Ω, μ, X) and n; one C; log n at n ≥ 2; √M log n for d = 2, √(M log n) for d ≥ 3"; `lem-freedman`: "C(p) before n and the space; any filtration; a.s. increments ≤ 1; predBracket is ⟨Z⟩_n"; `lem-cell`: "C(d) before Ψ, ξ, m, x; m is any locally finite measure with the defining identity (R1)"; `lem-geometry`: "C(d, Ψ) before ε and D; sphere average is (dω_d)⁻¹ ∫ d(toSphere); (iii) is four conjuncts".


---

## Appendix: probe sources (all compiled with empty output unless stated)

Compile command for every Lean probe (from the repository root, `PATH` containing `~/.elan/bin`):
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dlinter.unusedVariables=true <file>`.

### E1 `Hyp.lean`: the hypothesis package is realisable and inhabited

```lean
import CERW.Model
import CERW.Support.Drift.Existence

open MeasureTheory LatticeProb CERW

namespace Probe
variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

lemma norm_apply_zero (hΨ : IsNorm Ψ) : Ψ 0 = 0 := by
  simpa using hΨ.smul 0 (0 : EuclideanSpace ℝ (Fin d))

lemma norm_apply_neg (hΨ : IsNorm Ψ) (x : EuclideanSpace ℝ (Fin d)) : Ψ (-x) = Ψ x := by
  simpa using hΨ.smul (-1) x

lemma inner_coordVec (ξ : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    inner ℝ ξ (coordVec i) = ξ i := by
  simp [coordVec, EuclideanSpace.inner_single_right]

lemma subgradient_euler (hΨ : IsNorm Ψ) {x ξ : EuclideanSpace ℝ (Fin d)}
    (h : IsSubgradient Ψ x ξ) : inner ℝ ξ x = Ψ x ∧ ∀ y, inner ℝ ξ y ≤ Ψ y := by
  have key : ∀ y, Ψ x + inner ℝ ξ y - inner ℝ ξ x ≤ Ψ y := by
    intro y
    have hh := h y
    rw [inner_sub_right] at hh
    linarith
  have hlow : Ψ x ≤ inner ℝ ξ x := by
    have h0 := key 0
    rw [inner_zero_right, norm_apply_zero hΨ] at h0
    linarith
  have hhigh : inner ℝ ξ x ≤ Ψ x := by
    have h2 := key ((2 : ℝ) • x)
    rw [real_inner_smul_right, hΨ.smul 2 x] at h2
    norm_num at h2
    linarith
  have heuler : inner ℝ ξ x = Ψ x := le_antisymm hhigh hlow
  refine ⟨heuler, fun y => ?_⟩
  have hy := key y
  rw [heuler] at hy
  linarith

lemma subgradient_abs_coord_le (hΨ : IsNorm Ψ) {x ξ : EuclideanSpace ℝ (Fin d)}
    (h : IsSubgradient Ψ x ξ) (i : Fin d) : |ξ i| ≤ Ψ (coordVec i) := by
  have hb := (subgradient_euler hΨ h).2
  have hpos := hb (coordVec i)
  have hneg := hb (-coordVec i)
  rw [inner_coordVec] at hpos
  rw [inner_neg_right, inner_coordVec, norm_apply_neg hΨ] at hneg
  rw [abs_le]
  constructor <;> linarith

/-- The hypothesis package of `norm_shape` / `norm_local_time_potential` is realisable. -/
theorem hyp_package_realisable (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    (ξ : Site d → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) (hξ0 : ξ 0 = 0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site d), IsDriftCERW μ ε ξ X := by
  refine CERW.Support.Drift.exists_isDriftCERW hd hε.le (fun z i => ?_)
  by_cases hz : z = 0
  · subst hz
    simp [hξ0]
  · have h1 := subgradient_abs_coord_le hΨ (hξ z hz) i
    have h2 := hell i
    calc ε * |ξ z i| ≤ ε * Ψ (coordVec i) := mul_le_mul_of_nonneg_left h1 hε.le
      _ ≤ 1 / (d : ℝ) := h2.le


/-- The Euclidean norm satisfies `IsNorm`. -/
theorem euclid_isNorm : IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) :=
  ⟨fun x y => norm_add_le x y, fun t x => by simp [norm_smul], fun x h => norm_eq_zero.mp h⟩

/-- `x/|x|` (and `0` at the origin) is a subgradient of the Euclidean norm at `x`. -/
theorem euclid_subgradient (x : EuclideanSpace ℝ (Fin d)) :
    IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) x (‖x‖⁻¹ • x) := by
  intro y
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
    have h2 : inner ℝ x (y - x) = inner ℝ x y - ‖x‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    simp only [real_inner_smul_left, h2]
    have h3 : ‖x‖⁻¹ * inner ℝ x y ≤ ‖y‖ := by
      calc ‖x‖⁻¹ * inner ℝ x y ≤ ‖x‖⁻¹ * (‖x‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hn.le)
        _ = ‖y‖ := by field_simp
    have h4 : ‖x‖ + ‖x‖⁻¹ * (inner ℝ x y - ‖x‖ ^ 2) = ‖x‖⁻¹ * inner ℝ x y := by
      field_simp
      ring
    linarith

lemma toSpace_zero : toSpace (0 : Site d) = 0 := by
  ext i
  simp [toSpace]

/-- The whole hypothesis package is inhabited for the Euclidean norm with `xi(x) = x/|x|`. -/
theorem euclid_package_inhabited (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site d),
      IsDriftCERW μ ε (fun x : Site d => ‖toSpace x‖⁻¹ • toSpace x) X := by
  refine hyp_package_realisable (Ψ := fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) hd
    euclid_isNorm hε (fun i => ?_) _ (fun x _ => euclid_subgradient (toSpace x))
    (by simp [toSpace_zero])
  have : ‖coordVec (d := d) i‖ = 1 := by simp [coordVec]
  simpa [this] using hεd

end Probe
```

### E2 `Junk.lean`: junk values (Lipschitz, a.e. differentiability, measurability, integrability)

```lean
import CERW.Model
import CERW.Generic.Kernel.Integrable
import Mathlib.Analysis.Calculus.Rademacher

open MeasureTheory LatticeProb CERW
open scoped ContDiff

namespace ProbeJunk
variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

lemma norm_apply_zero (hΨ : IsNorm Ψ) : Ψ 0 = 0 := by
  simpa using hΨ.smul 0 (0 : EuclideanSpace ℝ (Fin d))

lemma norm_apply_neg (hΨ : IsNorm Ψ) (x : EuclideanSpace ℝ (Fin d)) : Ψ (-x) = Ψ x := by
  simpa using hΨ.smul (-1) x

/-- `Ψ v ≤ (Σ_i Ψ e_i) ‖v‖` : a function with the three norm axioms is bounded by a multiple of
the Euclidean norm. -/
lemma le_mul_norm (hΨ : IsNorm Ψ) (v : EuclideanSpace ℝ (Fin d)) :
    Ψ v ≤ (∑ i : Fin d, Ψ (coordVec i)) * ‖v‖ := by
  have hb := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  have hsum : Ψ v ≤ ∑ i : Fin d, Ψ (((EuclideanSpace.basisFun (Fin d) ℝ).repr v i) •
      (EuclideanSpace.basisFun (Fin d) ℝ) i) := by
    conv_lhs => rw [← hb]
    exact Finset.le_sum_of_subadditive Ψ (norm_apply_zero hΨ).le hΨ.add_le _ _
  refine hsum.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hΨ.smul]
  have hc : |(EuclideanSpace.basisFun (Fin d) ℝ).repr v i| ≤ ‖v‖ := by
    simpa [EuclideanSpace.basisFun_repr] using PiLp.norm_apply_le v i
  have hcoord : (EuclideanSpace.basisFun (Fin d) ℝ) i = coordVec i := by
    simp [coordVec]
  rw [hcoord]
  have : 0 ≤ Ψ (coordVec i) := by
    have h := hΨ.add_le (coordVec i) (-coordVec i)
    rw [add_neg_cancel, norm_apply_zero hΨ, norm_apply_neg hΨ] at h
    linarith
  nlinarith

/-- A function with the three norm axioms is Lipschitz. -/
lemma lipschitz (hΨ : IsNorm Ψ) :
    ∃ K : NNReal, LipschitzWith K Ψ := by
  refine ⟨Real.toNNReal (∑ i : Fin d, Ψ (coordVec i)), ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal']
  have hM : ∀ w, Ψ w ≤ max (∑ i : Fin d, Ψ (coordVec i)) 0 * ‖w‖ := fun w =>
    (le_mul_norm hΨ w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h1 : Ψ x ≤ Ψ y + Ψ (x - y) := by
    have := hΨ.add_le y (x - y)
    simpa using this
  have h2 : Ψ y ≤ Ψ x + Ψ (y - x) := by
    have := hΨ.add_le x (y - x)
    simpa using this
  have h3 : Ψ (y - x) = Ψ (x - y) := by
    rw [← norm_apply_neg hΨ (x - y)]; simp
  rw [abs_le]
  have := hM (x - y)
  constructor <;> linarith

/-- The exceptional set of non-differentiability of a norm is Lebesgue-null, so the value
`gradient Ψ v = 0` there never enters an integral. -/
theorem ae_differentiable (hΨ : IsNorm Ψ) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), DifferentiableAt ℝ Ψ v := by
  obtain ⟨K, hK⟩ := lipschitz hΨ
  exact hK.ae_differentiableAt

/-- `gradient Ψ` is Borel measurable for every function `Ψ`. -/
theorem measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Measurable (gradient Ψ) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ _).symm.continuous.measurable.comp (measurable_fderiv ℝ Ψ)

/-- Where a norm is differentiable the Mathlib gradient is the true gradient, and away from
those points it is `0`. -/
example (hΨ : IsNorm Ψ) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), HasGradientAt Ψ (gradient Ψ v) v := by
  filter_upwards [ae_differentiable hΨ] with v hv using hv.hasGradientAt

/-- The smooth-function scalar `∞` of `IsDistribLaplacian` is smooth, not analytic. -/
example : ((∞ : WithTop ℕ∞)) = ((⊤ : ℕ∞) : WithTop ℕ∞) := rfl

/-- The gradient of a norm is bounded by the Lipschitz constant, at every point. -/
theorem norm_gradient_le (hΨ : IsNorm Ψ) :
    ∃ K : ℝ, ∀ v, ‖gradient Ψ v‖ ≤ K := by
  obtain ⟨K, hK⟩ := lipschitz hΨ
  refine ⟨K, fun v => ?_⟩
  have h := norm_fderiv_le_of_lipschitz ℝ hK (x₀ := v)
  simpa [gradient] using h

/-- The integrand of `normPotential` is integrable on every bounded measurable set: the
Bochner integral in `eq:potential-norm` is a genuine integral, never the junk value `0`. -/
theorem integrableOn_normPotential_integrand (hd : 1 ≤ d) (hΨ : IsNorm Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d) D := by
  obtain ⟨K, hK⟩ := norm_gradient_le hΨ
  have hfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  obtain ⟨hint, -⟩ := CERW.Generic.Kernel.integrableOn_and_setIntegral_le hd hD hfin y
  have hmeas : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d) := by
    have h1 : Measurable (fun v : EuclideanSpace ℝ (Fin d) => inner ℝ (gradient Ψ v) (v - y)) :=
      (measurable_gradient Ψ).inner (measurable_id.sub_const y)
    exact h1.div (by fun_prop)
  refine (hint.const_mul (max K 0)).mono' hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun v => ?_
  rcases eq_or_ne v y with rfl | hv
  · simp
    positivity
  · have hn : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
    have h1 : |inner ℝ (gradient Ψ v) (v - y)| ≤ max K 0 * ‖v - y‖ := by
      calc |inner ℝ (gradient Ψ v) (v - y)| ≤ ‖gradient Ψ v‖ * ‖v - y‖ := abs_real_inner_le_norm _ _
        _ ≤ max K 0 * ‖v - y‖ :=
          mul_le_mul_of_nonneg_right ((hK v).trans (le_max_left _ _)) (norm_nonneg _)
    have h2 : ‖v - y‖ ^ (1 - (d : ℝ)) = ‖v - y‖ / ‖v - y‖ ^ d := by
      rw [Real.rpow_sub hn, Real.rpow_one, Real.rpow_natCast]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hn d), h2, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right h1 (pow_pos hn d).le

end ProbeJunk
```

### E3 `Eucl.lean`: Euclidean consistency of `normPotential`

```lean
import CERW.Model
import CERW.Frozen.PotentialGeometry
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory LatticeProb CERW

namespace ProbeEucl
variable {d : ℕ}

lemma hasGradientAt_norm (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) :
    HasGradientAt (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) (‖v‖⁻¹ • v) v := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖ ^ 2)
      (2 • innerSL ℝ v) v := (hasStrictFDerivAt_norm_sq v).hasFDerivAt
  have h2 := h1.sqrt (by positivity)
  have h3 : (fun w : EuclideanSpace ℝ (Fin d) => √(‖w‖ ^ 2)) = fun w => ‖w‖ := by
    funext w; exact Real.sqrt_sq (norm_nonneg w)
  rw [h3] at h2
  rw [hasGradientAt_iff_hasFDerivAt]
  have h4 : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (‖v‖⁻¹ • v) =
      (1 / (2 * √(‖v‖ ^ 2))) • 2 • innerSL ℝ v := by
    ext w
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, innerSL_apply_apply, Real.sqrt_sq hn.le, smul_eq_mul]
    simp only [nsmul_eq_mul]
    field_simp
    norm_num
  rw [h4]
  exact h2

/-- For the Euclidean norm the Mathlib gradient is the paper's direction `u_v = v/|v|`, with the
value `0` at the origin, at every point. -/
theorem gradient_norm_eq_unitDir (v : EuclideanSpace ℝ (Fin d)) (hd : 1 ≤ d) :
    gradient (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) v = unitDir v := by
  rcases eq_or_ne v 0 with rfl | hv
  · haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
      haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      infer_instance
    rw [gradient_eq_zero_of_not_differentiableAt (not_differentiableAt_norm_zero _)]
    simp
  · rw [(hasGradientAt_norm v hv).gradient]
    rfl

/-- The norm potential of the Euclidean norm is the Euclidean potential. -/
theorem normPotential_euclid (hd : 1 ≤ d) (ε : ℝ) (D : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε (fun w => ‖w‖) D y = potential d ε D y := by
  unfold normPotential potential
  simp only [gradient_norm_eq_unitDir _ hd]

/-- Consistency with the already-frozen Euclidean ball identity: `norm_ball_potential` at
`Ψ = |·|` and `ε > 0` is the ball clause of `potential_geometry`. -/
example (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {ρ : ℝ} (hρ : 0 < ρ)
    (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε (fun w => ‖w‖) {v | ‖v‖ < ρ} y = 2 * d * ε * max (ρ - ‖y‖) 0 := by
  rw [normPotential_euclid (by omega)]
  obtain ⟨Cd, -, h⟩ := CERW.Frozen.potential_geometry hd
  have := (h ε hε).2 ρ hρ y
  have hset : {v : EuclideanSpace ℝ (Fin d) | ‖v‖ < ρ} = Metric.ball 0 ρ := by
    ext v; simp
  rw [hset]
  exact this

end ProbeEucl
```

### E4 `Lin.lean`: linearity in `ε`

```lean
import CERW.Model

open CERW

namespace ProbeLin
variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The potential is linear in `ε`. -/
theorem normPotential_eps (ε : ℝ) (D : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ D y = ε * normPotential d 1 Ψ D y := by
  unfold normPotential
  ring

/-- `norm_ball_potential` for every real `ε` follows from its value at `ε = 1`: the draft's
dropping of `0 < ε` and of the ellipticity hypothesis is a true generalisation. -/
theorem ball_all_eps {ρ : ℝ}
    (h1 : ∀ y, normPotential d 1 Ψ {v | Ψ v < ρ} y = 2 * d * 1 * max (ρ - Ψ y) 0)
    (ε : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ {v | Ψ v < ρ} y = 2 * d * ε * max (ρ - Ψ y) 0 := by
  rw [normPotential_eps, h1 y]
  ring

/-- The sup bound of `norm_potential_geometry` at `ε = 1` gives it for every `ε > 0` with the
same constant: putting `∃ C` before `∀ ε` loses nothing. -/
theorem sup_bound_all_eps (D : Set (EuclideanSpace ℝ (Fin d))) (C R : ℝ)
    (h1 : ∀ y, |normPotential d 1 Ψ D y| ≤ C * 1 * R) {ε : ℝ} (hε : 0 < ε)
    (y : EuclideanSpace ℝ (Fin d)) : |normPotential d ε Ψ D y| ≤ C * ε * R := by
  rw [normPotential_eps, abs_mul, abs_of_pos hε]
  calc ε * |normPotential d 1 Ψ D y| ≤ ε * (C * 1 * R) := mul_le_mul_of_nonneg_left (h1 y) hε.le
    _ = C * ε * R := by ring

end ProbeLin
```

### E5 `Cons.lean`: consumption prototypes

The file begins with the six frozen blocks of the drafts (extracted between `FROZEN-STATEMENT-BEGIN` and `-END`, each closed by `:= by sorry`, which produces the six `declaration uses sorry` warnings and nothing else), then:

```lean
namespace ConsProbe
open CERW
variable {d : ℕ}

theorem euclid_isNorm : IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) :=
  ⟨fun x y => norm_add_le x y, fun t x => by simp [norm_smul], fun x h => norm_eq_zero.mp h⟩

theorem euclid_subgradient (x : EuclideanSpace ℝ (Fin d)) :
    IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) x (‖x‖⁻¹ • x) := by
  intro y
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
    have h2 : inner ℝ x (y - x) = inner ℝ x y - ‖x‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    simp only [real_inner_smul_left, h2]
    have h3 : ‖x‖⁻¹ * inner ℝ x y ≤ ‖y‖ := by
      calc ‖x‖⁻¹ * inner ℝ x y ≤ ‖x‖⁻¹ * (‖x‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hn.le)
        _ = ‖y‖ := by field_simp
    have h4 : ‖x‖ + ‖x‖⁻¹ * (inner ℝ x y - ‖x‖ ^ 2) = ‖x‖⁻¹ * inner ℝ x y := by
      field_simp
      ring
    linarith

lemma toSpace_zero : toSpace (0 : Site d) = 0 := by
  ext i
  simp [toSpace]

lemma ell_euclid {ε : ℝ} (hεd : ε < 1 / (d : ℝ)) (i : Fin d) :
    ε * (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (coordVec i) < 1 / (d : ℝ) := by
  have : ‖coordVec (d := d) i‖ = 1 := by simp [coordVec]
  simpa [this] using hεd

/-- first consumer of `norm_shape`: recurrence, at the Euclidean data. -/
example (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d)
    (hX : IsDriftCERW μ ε (fun x : Site d => ‖toSpace x‖⁻¹ • toSpace x) X) :
    ∀ᵐ ω ∂μ, ∀ x : Site d, ∃ᶠ j in atTop, X j ω = x := by
  have h := CERW.Frozen.norm_shape hd (Ψ := fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
    euclid_isNorm (ξ := fun x : Site d => ‖toSpace x‖⁻¹ • toSpace x)
    (fun x _ => euclid_subgradient (toSpace x)) (by simp [toSpace_zero]) hε
    (ell_euclid hεd) μ X hX
  filter_upwards [h] with ω hω using hω.2.2

/-- first consumer of `norm_local_time_potential`. -/
example (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d)
    (hX : IsDriftCERW μ ε (fun x : Site d => ‖toSpace x‖⁻¹ • toSpace x) X) : True := by
  obtain ⟨C, hC, h⟩ := CERW.Frozen.norm_local_time_potential hd (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖)
    euclid_isNorm ε hε (ell_euclid hεd) p hp
  have := h (fun x : Site d => ‖toSpace x‖⁻¹ • toSpace x) (fun x _ => euclid_subgradient (toSpace x))
    (by simp [toSpace_zero]) μ X hX 2 le_rfl
  trivial

/-- first consumer of `freedman_bound`: the constant martingale. -/
example {Ω : Type} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {p : ℝ} (hp : 0 < p) : True := by
  obtain ⟨C, hC, h⟩ := CERW.Frozen.freedman_bound p hp
  have := h 2 le_rfl μ ℱ (fun _ _ => (0 : ℝ)) (martingale_const ℱ μ 0)
    (Filter.Eventually.of_forall fun ω t => by simp)
  trivial

/-- first consumer of `cell_gradient`. -/
example (hd : 2 ≤ d) (m : Measure (EuclideanSpace ℝ (Fin d))) [IsLocallyFiniteMeasure m]
    (hm : IsDistribLaplacian (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) m) (x : Site d) :
    ENNReal.ofReal (∫ v in cell x,
        ‖gradient (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) v - ‖toSpace x‖⁻¹ • toSpace x‖)
      ≤ ENNReal.ofReal (Classical.choose (CERW.Frozen.cell_gradient hd)) *
        m (Metric.ball (toSpace x) (6 * Real.sqrt d)) := by
  obtain ⟨hC, h⟩ := Classical.choose_spec (CERW.Frozen.cell_gradient hd)
  exact h _ euclid_isNorm (fun x : Site d => ‖toSpace x‖⁻¹ • toSpace x)
    (fun x _ => euclid_subgradient (toSpace x)) (by simp [toSpace_zero]) m inferInstance hm x

/-- first consumer of `norm_potential_geometry`. -/
example (hd : 2 ≤ d) : True := by
  have h := CERW.Frozen.norm_potential_geometry hd
  obtain ⟨C, hC, h⟩ := h (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) euclid_isNorm
  have := h 1 one_pos (Metric.ball 0 1) measurableSet_ball Metric.isBounded_ball
  trivial

/-- first consumer of `norm_ball_potential`. -/
example (hd : 2 ≤ d) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d 1 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) {v | ‖v‖ < 1} y =
      2 * d * 1 * max (1 - ‖y‖) 0 :=
  CERW.Frozen.norm_ball_potential hd euclid_isNorm 1 one_pos y

end ConsProbe

/-! The Support-side `Prop`s agree definitionally with the drafts. -/
example : CERW.Support.Statements.norm_ball_potential := @CERW.Frozen.norm_ball_potential
example : CERW.Support.Statements.norm_shape := @CERW.Frozen.norm_shape
example : CERW.Support.Statements.norm_local_time_potential :=
  @CERW.Frozen.norm_local_time_potential
example : CERW.Support.Statements.freedman_bound := @CERW.Frozen.freedman_bound
example : CERW.Support.Statements.cell_gradient := @CERW.Frozen.cell_gradient
example : CERW.Support.Statements.norm_potential_geometry := @CERW.Frozen.norm_potential_geometry
```

### E7 numerical check of the norm potential (`numpy`)

```python
import numpy as np
# d=2, Psi = l_inf, D = [-1,1]^2 (= {Psi<1}), eps=1
N=4001
xs=(np.arange(N)+0.5)/N*2-1
X,Y=np.meshgrid(xs,xs); dv=(2/N)**2
r=np.hypot(X,Y); Psi=np.maximum(abs(X),abs(Y))
s=0.5
mask=r>s
B=(2/np.pi)*np.sum(Psi[mask]/r[mask]**2)*dv
F=(1/(2*np.pi))*np.sum(1/r[mask])*dv
print("B",B,"F",F,"2dcF",4*(1/np.sqrt(2))*F,"2dLamF",4*1*F)
th=np.linspace(0,2*np.pi,200001)
A=np.mean(4*(1-s*np.maximum(abs(np.cos(th)),abs(np.sin(th)))))   # U_D(y)=4(1-Psi(y)) inside D
print("A",A)
def U(y):
    dx=X-y[0]; dy=Y-y[1]; rr2=dx**2+dy**2+1e-300
    gx=np.where(abs(X)>=abs(Y),np.sign(X),0.0); gy=np.where(abs(X)<abs(Y),np.sign(Y),0.0)
    return (2/np.pi)*np.sum((gx*dx+gy*dy)/rr2)*dv
print("U(0.3,0.2)",U((0.3,0.2)),"expected",4*(1-0.3)); print("U(0,0)",U((1e-9,1e-9)),"expected 4")
```

Output: `B 2.19934  F 0.62219  2dcF 1.75983  2dLamF 2.48877`, `A 2.19937`, `U(0.3,0.2) 2.79822`, `U(0,0) 3.99884`.

### E8 simulation (`sim.py`)

```python
import random, math, sys
random.seed(1)
eps=0.4; d=2
n=int(sys.argv[1]) if len(sys.argv)>1 else 1000000
kind=sys.argv[2] if len(sys.argv)>2 else "inf"
def xi(x,y):
    if kind=="inf":
        if abs(x)>=abs(y): return (1 if x>0 else -1,0)
        return (0,1 if y>0 else -1)
    if kind=="one":   # l1 norm: subgradient (sgn x, sgn y) (sgn 0 -> 0 allowed)
        sx=(x>0)-(x<0); sy=(y>0)-(y<0); return (sx,sy)
visited=set(); x=y=0
ell={}
first=set()
pos=(0,0)
for t in range(n):
    p=(x,y)
    ell[p]=ell.get(p,0)+1
    if p not in first:
        first.add(p)
        if p!=(0,0):
            a,b=xi(x,y)
            # +e1: 1/4-eps a/2 ; -e1: 1/4+eps a/2 ; +e2: 1/4-eps b/2 ; -e2: 1/4+eps b/2
            pr=[0.25-eps*a/2,0.25+eps*a/2,0.25-eps*b/2,0.25+eps*b/2]
        else: pr=[.25]*4
    else: pr=[.25]*4
    u=random.random()*sum(pr)
    if u<pr[0]: x+=1
    elif u<pr[0]+pr[1]: x-=1
    elif u<pr[0]+pr[1]+pr[2]: y+=1
    else: y-=1
A=len(ell)
volB={"inf":4.0,"one":2.0}[kind]
r=((d+1)*n/(2*d*eps*volB))**(1/(d+1))
Psi=(lambda a,b:max(abs(a),abs(b))) if kind=="inf" else (lambda a,b:abs(a)+abs(b))
print("n",n,"|A_n|",A,"|B|*r^d",volB*r**d,"ratio",A/(volB*r**d))
mx=max(abs(ell.get((a,b),0)-2*d*eps*max(r-Psi(a,b),0)) for a in range(-int(2*r),int(2*r)+1) for b in range(-int(2*r),int(2*r)+1))
print("r_n",r,"max |l_n - cone|/r_n",mx/r)
# inclusion check
inner=sum(1 for a in range(-int(2*r),int(2*r)+1) for b in range(-int(2*r),int(2*r)+1) if Psi(a,b)<0.9*r and (a,b) not in ell)
outer=sum(1 for (a,b) in ell if Psi(a,b)>=1.1*r)
print("sites with Psi<0.9 r_n not visited:",inner," visited with Psi>=1.1 r_n:",outer)
```

Run as `python3 sim.py 1000000 inf`, `python3 sim.py 8000000 inf`, `python3 sim.py 1000000 one`; the flipped-sign run replaces the list `pr` by `[0.25+eps*a/2, 0.25-eps*a/2, 0.25+eps*b/2, 0.25-eps*b/2]`.
