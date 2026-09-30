# Draft audit 3 (refute-first): Sections 4-5 of limit-shapes.tex, eight draft statements

Auditor: independent reader; wrote none of the drafts. Nothing under `scratch/Frozen/`, `CERW/`, `ledger/`, `paper/`
was edited. Outputs: this report and `scratch/nl/{prop-coarse,lem-radial,lem-crossing,prop-norm-shape,lem-layer,lem-cap,lem-contact,lem-outer-crossing}.tex`.
Paper: `paper/limit-shapes.tex` (pinned in the working tree). Line numbers below are the file's own; the constants
convention is at line 295 (the brief says 293) and `xi(0)=0` at 294.

## Verdicts

| node | draft | paper | verdict |
|---|---|---|---|
| prop-coarse | `NormCoarseBounds.lean` | Prop 4.1, 546-553 | PASS |
| lem-radial | `NormRadialTest.lean` | Lem 4.2, 566-575 | PASS |
| lem-crossing | `DriftCrossing.lean` | Lem 4.3, 661-666 | PASS |
| prop-norm-shape | `NormShapeRates.lean` | Prop 5.1, 745-761 | PASS |
| lem-layer | `LayerPotential.lean` | Lem 5.2, 779-784 | PASS |
| lem-cap | `MoreauCap.lean` | Lem 5.3, 809-814 | PASS |
| lem-contact | `ContactPotential.lean` | Lem 5.4, 891-896 | PASS |
| lem-outer-crossing | `OuterCrossing.lean` | Lem 5.5, 988-993 | PASS |

No CONCERN or DEFECT, so no replacement text is proposed. Reading choices that the author may wish to confirm are listed
under "Notes for the author" at the end; none changes a verdict.

## Evidence (all commands run from the repository root with `PATH=$HOME/.elan/bin:$PATH`)

1. Elaboration and coercions. For each draft a copy was placed in the scratchpad
   (`.../scratchpad/probe/<Name>.lean`) with
   `set_option pp.numericTypes true; pp.funBinderTypes true; pp.coercions true` and `#print CERW.Frozen.<name>` appended, then
   `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false <copy>`. All eight elaborate; the only message is
   `declaration uses sorry`. The printed telescopes were read line by line against the paper. All casts are to `ℝ`
   (for example `r n = ((↑d + 1) * ↑n / (2 * ↑d * ε * normBallVolume Ψ)) ^ (1 / (↑d + 1))`, `(t - s : ℝ)` is `↑t - ↑s`, `ρ₀ ≤ ↑ρ`,
   `↑ρ - 4 * ↑d`), exponents are `Real.rpow` with the literal values `3/4, 5/6, 7/6, 1/4, 1/6, 1/2, d/(d+1), (d+2)/(d+1), 1/(d+1)`,
   and `r n ^ d` is a natural power.
2. `Prec.lean`: `example : (y ∈ closure (A)ᶜ) = (y ∈ closure (Aᶜ)) := rfl` compiles, so `closure (cellSet …)ᶜ` in `ContactPotential.lean`
   is the closure of the complement.
3. `Ev.lean`: `x j ∉ CERW.departureRange x j ↔ x j ∉ (Finset.range j).image x` is `Iff.rfl` (the first-departure test in the
   statements is the test inside `driftStepProb`), and `departureRange X n = (Finset.range n).image X` is `rfl`. The existing Support
   theorems `CERW.Support.Drift.sum_driftFirstStep_mul`, `sum_driftStepProb_mul`, `sum_driftStepProb`, `stepMean_driftStepProb`,
   `dynkinMart_driftStepProb_eq_driftDynkin` and `condExp_next_drift` exist at the pin (`#check` in `Ev.lean`, `Ev2.lean`); together they say that `stepMean (driftStepProb d ε ξ) f x j` is
   `walkOp f (x j) - f (x j) - (first-departure indicator) * ε * ⟪ξ (x j), centralDiff f (x j)⟫`, i.e.
   `Δf - ε I_j ξ·∇̄f` of line 425, and that the next-step mean equals the conditional expectation on the walk.

## Model definitions, read against the paper

| Lean | paper | reading |
|---|---|---|
| `IsNorm` | norm (symmetric, homogeneous, triangle) | correct; nonnegativity and continuity follow |
| `IsSubgradient Ψ x ξ` | `ξ ∈ ∂Ψ(x)` | `Ψ x + ⟪ξ, y - x⟫ ≤ Ψ y` for all `y`; correct |
| `normMax`, `normMin` | `Λ_Ψ`, `c_Ψ` (line 327) | `sSup`/`sInf` of `Ψ` on the Euclidean unit sphere; attained, so equal to the max/min (sphere nonempty for `d ≥ 2`) |
| `normBallVolume Ψ` | `|B_Ψ|` | `(volume {Ψ < 1}).toReal`, Lebesgue measure; the ball is bounded with positive volume, so no junk |
| `driftFirstStep`, `driftStepProb`, `IsDriftCERW` | eq:kernel and the sentence after it | `e = x+e_i` gets `1/(2d) - (ε/2) ξ_i`, `x-e_i` gets `1/(2d) + (ε/2) ξ_i`; drift only when `x_n ≠ 0` and `x_n ∉ {x_0..x_{n-1}}`; else simple random walk; cylinder factorization plus `X_0 = 0` a.s. |
| `departureRange X n` | `A_n = {ℓ_n > 0} = {X_0..X_{n-1}}` (95) | correct (`mem_departureRange_iff`) |
| `x j ∉ departureRange x j` | `I_j = 1{X_j ∉ A_j}` (line 297 notation) | correct, `j = 0` gives the empty range (`ξ(0)=0` makes that term vanish) |
| `localTime`, `maxLocalTime` | `ℓ_n(x)`, `max_x ℓ_n(x)` | correct; `ℓ_n = 0` off `A_n`, so the `sup` over `A_n` is the max over `ℤ^d` |
| `maxRadius` | `R_out(n) = max_{0≤j≤n} |X_j|` (126) | Euclidean, `j ∈ range (n+1)`; correct |
| `normMaxRadius Ψ` | `max_{0≤j≤n} Ψ(X_j)` | correct |
| `cell`, `cellSet` | `C_x = x + [-1/2,1/2)^d`, `D_n = ∪_{x∈A_n} C_x` | correct |
| `normInnerRadius Ψ X n` | `inf_{y ∉ D_n} Ψ(y)` | `sInf (Ψ '' (cellSet X n)ᶜ)`; the set is nonempty (`D_n` bounded) and bounded below by `0`, so no junk |
| `tail d D s` | `F(s) = (dω_d)^{-1} ∫_{D∩{|v|>s}} |v|^{1-d} dv` (503) | correct, strict inequality `s < ‖v‖`; integrable for `D` bounded, `s > 0` |
| `shellMax X n ρ` | `max_{||x|-ρ|≤3} ℓ_n(x)` | correct (`ballFinset d (ρ+3)` contains the shell) |
| `normPotential d ε Ψ D y` | eq:potential-norm (349-351) | `(2ε/ω_d) ∫_D ⟪gradient Ψ v, v-y⟫ / ‖v-y‖^d`; Mathlib `gradient` is `0` off the differentiability set, a null set (Rademacher); integrand at `v = y` reads `0` (null) |
| `moreauEnvelope Ψ τ x` | `F_τ(x) = min_z {Ψ(z) + |x-z|²/(2τ)}` (794-798) | real `⨅`, family bounded below by `0`, infimum attained (paper); `gradient` of it is `p_x` since `F_τ` is `C¹` |
| `stepMean`, `dynkinMart p f X t` | `M^f_t = f(X_t) - f(X_0) - Σ_{j<t} E(f(X_{j+1})-f(X_j) | F_j)` (421-425) | the conditional expectation is written pathwise as `Σ_{e ∈ unitSteps} p_j(e) (f(X_j+e) - f(X_j))` with `p_j = driftStepProb d ε ξ X j`, the conditional step law; equal to `Δf - ε I_j ξ·∇̄f` (Evidence 3); correct for the path-level transcription the author ruled |

## Per-node reports

### prop-coarse (`norm_coarse_bounds`) - PASS

- Quantifier order: `hd; Ψ; ε (0 < ε, ellipticity); let r; p; ∃ c C > 0; ∀ ξ (subgradients, ξ 0 = 0); ∀ Ω μ X (IsDriftCERW); ∀ n ≥ 2`.
  Constants `c, C` depend on `d, ε, Ψ, p` only (line 295), and precede `ξ` and the probability space. One letter `C` in both the
  upper bounds and the failure probability is the usual maximum.
- Normalizations: `r` is eq:radius-norm; casts checked. `|A_n|`, `max ℓ_n`, `R_out` as in the table. The six inequalities are
  exactly the three two-sided bounds; `R_out` is Euclidean (`maxRadius`), not `Ψ`, as eq:radii and line 544 say.
- Probability: `μ{¬(…)} ≤ ofReal (C * n ^ (-p))`, every `n ≥ 2`.
- Junk: none (`r n > 0`; `normBallVolume` is finite and positive).
- Hypotheses: `hd` (standing), `IsNorm`, `0 < ε` (standing: needed for `r_n`), ellipticity (source, `max_i` as `∀ i`), subgradients
  (source), `ξ 0 = 0` (line 294), `IsDriftCERW` (source). No excess.

### lem-radial (`norm_radial_test`) - PASS

- Quantifier order matches "`ρ₀(d,Ψ) > 8d`, `C(d,ε,Ψ,p)`": `∀ Ψ, IsNorm Ψ → ∃ ρ₀ : ℝ, 8d < ρ₀ ∧ ∀ ε (elliptic) p, ∃ C > 0, ∀ ξ …`. `ρ₀` is before `ε`,
  `p`, `ξ`; this is as strong as the paper (the proof of (radial-drift) uses only `g`, `c_Ψ`, `Λ_Ψ`).
- Terms: `F(ρ+4d) ≤ C·M_sh(ρ)·[F(ρ-4d) - F(ρ+4d)] + C·√(M_{≥ρ-4d} · ρ^{1-d} · F(ρ-4d) · log n) + C·ρ^{1-d}·log n`. The middle maximum is the `sup` of
  `localTime` over `departureRange` filtered by `ρ - 4d ≤ euclidNorm` (paper: `max_{|x| ≥ ρ-4d}`); `ρ` ranges over naturals with `ρ₀ ≤ ρ ≤ n`.
  `ρ - 4d > 4d > 0`, so `tail` is over a set bounded away from `0` (integrable, no junk). `log n = Real.log n` (not `log(n+2)` as in the old
  Euclidean frozen statement, correctly, since the paper now says `log n`).
- The single `C` in the three coefficients and in the probability is the maximum of the line-by-line constants (all three factors are nonnegative).
- Hypotheses: as prop-coarse.

### lem-crossing (`drift_crossing`) - PASS

- Deterministic reading as ruled: event = hypothesis `∀ s < t ≤ n, ‖Z t - Z s‖ ≤ C √((t-s) log n)`, with the same `C` in the conclusion.
  `Z t = toSpace (x t) + ε • Σ_{j<t} (if x j ∉ departureRange x j then ξ (x j) else 0)` is eq:vector-def with `I_j` as in the table.
- Conclusion: for every unit `u` and `s < t ≤ n`, if `0 ≤ ⟪u, ξ (x j)⟫` for every first-departure time `j ∈ [s,t)`, then
  `⟪u, toSpace (x t) - toSpace (x s)⟫ ≤ C √((t-s) log n)`. Paper's proof: `u·(X_t-X_s) = u·(Z_t-Z_s) - ε Σ I_j u·ξ(X_j) ≤ |Z_t - Z_s|`; it uses `ε ≥ 0`,
  the sign hypothesis and Cauchy-Schwarz, all available.
- Strengthening, justified: the declaration assumes `0 ≤ ε` (paper: `ε > 0` with ellipticity), no condition on `ξ` and none on the
  path `x` (paper: subgradients, nearest-neighbour path from `0`), and `n` arbitrary. The proof is the same, so this is the paper's lemma with
  unused hypotheses dropped. Consumers (Step 3 of prop:coarse, Step 4 of lem:outer-crossing) instantiate it on the walk's path.
- Junk: `Real.log n ≥ 0`; for `n ≤ 1` the statement is still true (no pairs, or the right side is `0` and then the hypothesis gives `Z t = Z s`).

### prop-norm-shape (`norm_shape_rates`) - PASS

- One `C(d,ε,Ψ,p)`, after `p`, before `ξ`. Three conjuncts inside one event, all for every `n ≥ 2`.
- Exponents checked against eq:norm-shape, eq:norm-outer, eq:norm-local: `d = 2`: `r^{3/4}(log n)^{1/4}`, `r^{5/6}(log n)^{7/6}`, `r^{5/6}(log n)^{1/6}`;
  `d ≥ 3`: `(r log n)^{1/2}`, `r^{d/(d+1)}(log n)^{(d+2)/(d+1)}`, `r^{d/(d+1)}(log n)^{1/(d+1)}`. Case split `if d = 2` with `2 ≤ d`.
- (i) two-sided for the inner radius (`normInnerRadius`), one-sided for the outer radius (`normMaxRadius - r ≤ …`), as in the paper (outer bound is an upper
  bound only). (ii) `∀ x : Site d, |ℓ_n(x) - 2dε · max (r - Ψ(x)) 0| ≤ …`; the max over `x ∈ ℤ^d` is the universal quantifier.
- Junk: `Real.log n ^ (·)` with `n ≥ 2` positive; no empty sets.

### lem-layer (`layer_potential`) - PASS

- `b ≥ 0`, `a > 0`, `D` measurable `⊆ {b ≤ Ψ ≤ b+a}`, conclusion `∀ y, |U_D(y)| ≤ 2 d ε a` (equivalent to `sup_y`). No constants or probability.
- Strengthening, justified: ellipticity is omitted (the proof does not use it); `0 < ε` is kept (needed for the sign of the bound). The shell is bounded, so no
  boundedness hypothesis is needed. Sharpness is unaffected: for `Ψ` Euclidean and `D = {b ≤ |v| < b+a}`, `U_D(0) = 2dεa`.
- `MeasurableSet D` is Borel; the paper's "measurable" may mean Lebesgue. The Lebesgue case follows (replace `D` by a Borel subset of full measure, which stays
  inside the shell and has the same potential), and the repository uses `MeasurableSet` for this word in `potential_geometry`. No change needed.
- Junk: `gradient` off the differentiability set is a null set; the integral is over a bounded set of a function dominated by `Λ_Ψ ‖v-y‖^{1-d}`, integrable.

### lem-cap (`moreau_cap`) - PASS

- `η = c_Ψ⁴/(8Λ_Ψ²)` is `normMin Ψ ^ 4 / (8 * normMax Ψ ^ 2)`. `q = gradient (moreauEnvelope Ψ τ) x` (`∇F_τ(x) = p_x`; `F_τ` is `C¹`, so this is not a junk value).
  Hypotheses: `F_τ(y) ≤ F_τ(x)`; `inner q x - η * τ < inner q y` (paper `q·y > q·x - ητ`); `τ * normMax Ψ < ‖y‖` (paper `|y| > τΛ_Ψ`); `IsSubgradient Ψ y ξ`.
  Conclusion `normMin Ψ ^ 2 / 2 ≤ inner q ξ`.
- I re-derived the paper's proof against these exact hypotheses: `z_y ≠ 0` from `|y| > τΛ`; `|p_y| ≥ c`; monotonicity gives `ξ·p_y ≥ |p_y|² ≥ c²`; `φ = F_τ - q·` is minimized at
  `x`, `φ(y) - φ(x) < ητ`, the Taylor upper bound with `h = -τ(p_y - q)` gives `|p_y - q|² < 2η`, `Λ(2η)^{1/2} = c²/2`, so `q·ξ ≥ c² - c²/2`. All steps use only the listed hypotheses.
- Junk: none (`normMax`, `normMin` attained on the nonempty sphere; `moreauEnvelope` family bounded below).

### lem-contact (`contact_potential`) - PASS

- Author ruling followed: `∀ p, ∃ C > 0, ∃ n₀, ∀ ξ …, ∀ n ≥ n₀, μ{¬ ∀ y₀, (Ψ y₀ = normInnerRadius …) → (y₀ ∈ closure (cellSet …)ᶜ) → U_{D_n}(y₀) ≤ C r_n q_n} ≤ ofReal (C n^{-p})`.
  Contact point = `Ψ(y₀) = b` and limit of points outside `D_n` (closure of the complement, Evidence 2). The proof (lines 857 onward) uses only these two properties, so the claim
  is for every contact point.
- `q_n` is eq:qn: `if d = 2 then √(log n / r n) else log n / r n`, so `C r_n q_n = C√(r_n log n)` (`d = 2`) or `C log n` (`d ≥ 3`); checked.
- `C` and `n₀` precede `ξ`: the "for large `n`" steps (`D_n ⊂ B(0,Kr_n)`, `|z| ≤ C r_n < 3n`, `|y₀| + R ≤ 2n`) come from the constants of prop:coarse and lem:local, which do not depend on `ξ`,
  and the final absorption `H ≤ H/2 + C log n` has no threshold. A `ξ`-uniform `n₀` is also what prop:norm-shape needs to absorb `n < n₀` into `C`.
- `H = U_{D_n}(y₀) = normPotential d ε Ψ (cellSet …) y₀`; the bound is one-sided.
- The Lean statement is implied by the paper's (the event of sec:norm-event has probability `≥ 1 - C'n^{-p}`; take the larger constant) and is the form a union bound needs.
  The event's content (prop:coarse, lem:local, eq:vector, eq:localmart, eq:quadratic-coarse, eq:linear-mart) is not named, which matches the ruling.
- Cosmetic: `closure (CERW.cellSet (X · ω) n)ᶜ` parses as the closure of the complement (verified) but a reader may misparse it; `closure ((CERW.cellSet (X · ω) n)ᶜ)` is identical and clearer.
  Optional, not required.

### lem-outer-crossing (`outer_crossing`) - PASS

Hypotheses against the lemma (every line checked against the printed telescope):

| paper | Lean |
|---|---|
| `α > 0`; `C(d,ε,Ψ,α,p)` | `∀ α > 0, ∀ C₁ > 0, ∃ C > 0` before `ξ`, `n`, `q`, path, `j₀`, `h`, `b`; `C₁` is the event constant for the fixed `p` (ruling) |
| `q ∈ ℝ^d`, `|q| ≤ Λ_Ψ` | `‖q‖ ≤ normMax Ψ` |
| "a path of the walk" | `x 0 = 0`, `∀ j, x (j+1) - x j ∈ unitSteps d` (every such path has positive probability under ellipticity; only `x_0..x_n` enter) |
| eq:vector (line 656) | `∀ s < t ≤ n, ‖Z t - Z s‖ ≤ C₁ √((t-s) log n)`, `Z` as eq:vector-def |
| eq:linear-mart for `q` and every `a ∈ Λ_Ψ ℤ ∩ [0, Λ_Ψ n]` | `∀ k ≤ n`, `|dynkinMart (driftStepProb d ε ξ) (fun z => max (⟪q, z⟫ - kΛ) 0) x n| ≤ C₁ (√(log n Σ_{z ∈ A_n, kΛ-Λ < ⟪q,z⟫} ℓ_n z) + log n)` (`a = kΛ`, `Λ > 0`) |
| `x_*` one of `X_0..X_n` with `q·X_j ≤ T := q·x_*` | `j₀ ≤ n`, `∀ j ≤ n, ⟪q, x j⟫ ≤ ⟪q, x j₀⟫`, `T = ⟪q, x j₀⟫` |
| `h > 0`, `q·ξ(X_j) ≥ α` for `0 ≤ j ≤ n` with `q·X_j > T - h` | `0 < h`, `∀ j ≤ n, T - h < ⟪q, x j⟫ → α ≤ ⟪q, ξ (x j)⟫` |
| `L_b = 1 + max{ℓ_n(x) : q·x ≥ b}` | `1 + ↑(sup over A_n filter (b ≤ ⟪q,z⟫) of localTime x n)` |
| `T ≤ max{T-h, b} + C L_b log n` for every `b ≥ 0` | `∀ b ≥ 0, T ≤ max (T - h) b + C * (1 + …) * log n` |

- `dynkinMart` is the paper's `M^{q,a}_n` with the conditional expectation written on the path (table above and Evidence 3): the step law `p_j(e) = driftStepProb d ε ξ x j e` is the
  conditional probability that `IsDriftCERW` prescribes, and `Σ_e p_j(e) (f(x_j+e) - f(x_j)) = Δf - ε I_j ξ·∇̄f`. Sum in the bracket bound: over `q·x > a - Λ`, i.e. `z ∈ A_n` with
  `kΛ - Λ < ⟪q,z⟫` (`ℓ_n = 0` elsewhere).
- Edge: for `q = 0`, `b > 0` the paper's maximum is over an empty set and Lean reads `0`; the statement is vacuous there (`T = 0`, `T - h < 0 = ⟪q, x 0⟫` forces `α ≤ ⟪0, ξ 0⟫ = 0`). In general `j = 0` forces `T ≥ h`
  in both the paper and the declaration.
- Is the lemma true as transcribed, and does it need the walk's law? I re-ran Steps 1-4 of the paper's proof with exactly the Lean hypotheses:
  Step 1 (a),(b) use the `α`-hypothesis and `a ≥ a₀ ≥ max{T-h, b+Λ}`; Step 2 is the Dynkin identity `φ(x_n) = Σ_{j<n}[Δφ - ε I_j ξ·∇̄φ](x_j) + M^{q,a}_n` (definition of `dynkinMart`, `φ(x_0) = 0` since `x_0 = 0`, `a > 0`),
  `φ` linear where `q·x ≥ a + Λ` because `‖q‖ ≤ Λ`, first departures from such sites give `≤ -εα` each (`|A_n|` sites, each with a first departure before `n`), the band `|q·x - a| < Λ` costs `≤ C L_b` per site (`ℓ_n < L_b` by (a)),
  the martingale term is bounded by the `k`-hypothesis at `a = a₀ + 2mΛ ≤ Λn` (levels above `Λn` are empty because `T = q·x_{j₀} ≤ ‖q‖ |x_{j₀}| ≤ Λ n` for a unit-step path from `0`);
  Step 3 is arithmetic (`u₀ ≤ |A_n| ≤ n`, true for any path); Step 4 uses the first hitting time `σ ≤ j₀ ≤ n`, `q·x_s ≤ ā + Λ` (steps change `q·x` by at most `‖q‖`), the `α`-hypothesis for `q·x_j > ā ≥ a₀ ≥ T-h`,
  and `drift_crossing` with the eq:vector hypothesis and `u = q/|q|`, `t = σ ≤ n`. The only inputs are pathwise: the kernel inside `driftStepProb`, `|ξ(x)| ≤ Λ_Ψ` for subgradients, unit steps from `0`. Nothing about the law
  of the walk beyond the kernel is used, so the deterministic transcription is exactly the lemma, and it is true with `C = C(d,ε,Ψ,α,C₁)` independent of `ξ`, `n`, `q`, the path, `h`, `b`.
- Using one constant `C₁` in both hypotheses is the maximum of the paper's two event constants (hypotheses weaken as `C₁` grows, so the lemma for the maximum is the lemma for each).
- Consumption: for prop:norm-shape (Step "outer radius") one instantiates `q = ∇F_τ(x_*)`, `α = c_Ψ²/2`, `h = ητ`, `b = r_n` with `C₁` the event constant; for the Euclidean case `q = u_{x_*}`, `Λ = 1`, `α = 1/2`, `h = R_out/2`. Both fit.

## Notes for the author (none changes a verdict)

1. lem-contact: `n₀` is placed before `ξ`. This is the reading consistent with the ruling ("there are `C` and `n₀`"), with line 295, and with the use in prop:norm-shape; I checked that every threshold in the proof is `ξ`-uniform.
2. lem-crossing and lem-layer are slightly more general than the paper (fewer hypotheses, same proofs): `0 ≤ ε` instead of ellipticity, no subgradient/path structure (crossing); no ellipticity (layer).
3. lem-layer uses Borel `MeasurableSet`; `NullMeasurableSet D volume` would be the literal Lebesgue reading and implies nothing more. Repository convention kept.
4. lem-outer-crossing: the paper's `C(d,ε,Ψ,α,p)` becomes `C(d,ε,Ψ,α,C₁)`; `p` enters only through `C₁`. A consumer must pass the same constant to eq:vector and eq:linear-mart.
5. `closure (…)ᶜ` in `ContactPotential.lean` could be parenthesized for readability (identical term).
