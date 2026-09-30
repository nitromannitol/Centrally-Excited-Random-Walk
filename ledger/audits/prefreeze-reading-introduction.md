# Draft audit 1 (refute-first): eight draft statements under `scratch/Frozen/`

Paper: `paper/limit-shapes.tex` (`\drift` = kappa, written `ε` in Lean). Conventions: `CORRESPONDENCE.md`
("Transcription conventions"). No Lean file was edited. All machine evidence was produced from copies in the
session scratchpad (`.../scratchpad/chk/*.lean`, `.../scratchpad/Probe1.lean`, `Probe2.lean`), compiled with
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` against the built `CERW.Model`.

## Summary

| node | draft | verdict |
|---|---|---|
| thm-shape | `LimitShape.lean` | PASS |
| thm-fluctuations | `FluctuationRates.lean` | **DEFECT** (precedence: the volume clause scales the symmetric difference, making the statement false) |
| thm-sharp-radii | `SharpRadii.lean` | PASS |
| thm-sharp-radii-lil | `SharpRadiiLil.lean` | PASS |
| thm-sharp-bulk | `SharpBulk.lean` | PASS |
| thm-sharp-width | `SharpWidth.lean` | PASS |
| ext-martingale-clt | `MartingaleCLT.lean` | PASS (two optional convenience notes) |
| ext-stout-lil | `StoutLIL.lean` | PASS (one point about the cited theorem's exact hypothesis I cannot confirm from memory, stated below) |

All eight drafts elaborate with no errors (only `declaration uses sorry` for the six theorems; the two
externals are silent). No line exceeds 100 characters.

## The Model definitions used (check 6)

Read in `CERW/Model/*.lean`; each means what the paper means.

* `CERW.localTime X n x = #{j < n : X j = x}` = `ℓ_n(x) = Σ_{j=0}^{n-1} 1{X_j = x}` (paper line 90-95).
* `CERW.departureRange X n = (range n).image X` = `{X_0,…,X_{n-1}}`; `mem_departureRange_iff` proves it equals `{x : ℓ_n(x) > 0}`.
  The paper's "visited by time n" set is `A_{n+1}`; the drafts use `A_n` throughout, as the paper does.
* `CERW.cellSet X n = ⋃_{x ∈ A_n} cell x`, `cell x = {v | ∀ i, x_i - 1/2 ≤ v_i < x_i + 1/2}` = `C_x = x + [-1/2,1/2)^d`; `D_n` is built from `A_n`, not `V_n`. Correct.
* `CERW.innerRadius X n = sInf ((‖·‖) '' (cellSet X n)ᶜ)` = `inf_{y ∉ D_n} |y|`. `D_n` is a finite union of bounded cells, so the complement is
  nonempty and the image is nonempty and bounded below by 0: the `sInf` is the honest infimum, no junk value. `‖·‖` on `EuclideanSpace` is the Euclidean norm.
* `CERW.maxRadius X n = sup'_{j ∈ range (n+1)} euclidNorm (X j)` = `max_{0 ≤ j ≤ n} |X_j|` (includes `j = n`, as `eq:radii`).
* `CERW.IsCERW μ ε X`: `X_j` measurable, `X_0 = 0` a.s., and every cylinder factors through `stepProb`. `stepProb` uses `firstStep` exactly when
  `x n ≠ 0` and `x n ∉ {x_0..x_{n-1}}` (first departure from a nonzero site) and `srwStep` otherwise. `firstStep` gives `x + e_i` probability
  `1/(2d) - (ε/2) x_i/|x|` and `x - e_i` probability `1/(2d) + (ε/2) x_i/|x|`, mean step `-ε x/|x|`: the paper's kernel (lines 82-84). The law of
  every finite prefix of the path is determined, so any probability of a path event is realization-independent (used below to justify constants and `n₀`
  being bound before the probability space). `CERW.Support.Law.exists_isCERW` proves the hypothesis satisfiable for `0 < ε < 1/d`.
* `ω_d := (volume (Metric.ball 0 1)).toReal` is the Lebesgue volume of the Euclidean unit ball (`CERW.unitBallVolume`).
* Elaboration check (`pp.numericTypes`, `pp.coercions`): `r n = ((↑d + 1) * ↑n / (2 * ↑d * ε * ωd)) ^ (1 / (↑d + 1))` with every cast in `ℝ`; no natural-number
  division anywhere in the eight statements.

---

## 1. thm-shape (`CERW.Frozen.limit_shape`, paper 103-116): PASS

1. No constants. Hypotheses `2 ≤ d`, `0 < ε < 1/d` precede `Ω, μ, X`. Correct.
2. One `∀ᵐ ω ∂μ` over the conjunction (i) and (ii) and (iii); the quantifier over `η` is inside it ("almost surely, for every η"). Correct, and the law is `IsCERW`.
3. `r_n` is `eq:radius` exactly. (i): `{|x| < (1-η) r_n} ⊆ A_n ⊆ {|x| < (1+η) r_n}` for `0<η<1`, eventually in `n`. (ii): "`(1/r_n) max_x |ℓ_n(x) - 2dκ(r_n - |x|)_+| → 0`"
   is `∀ η > 0, ∀ᶠ n, ∀ x, |ℓ_n(x) - 2dε max(r_n - |x|,0)| ≤ η r_n`: equivalent, because the maximum is over finitely many `x` (outside `B(0,r_n)∪A_n` both terms vanish) and
   `r_n > 0` for `n ≥ 1`. (iii): `∀ x, ∃ᶠ j, X j ω = x`. All match.
4. Junk: `r_0 = 0` and `n = 0` are irrelevant under `∀ᶠ n`. `max · 0` is the positive part. No `sInf`, no `Real.log`. None.
5. Not weakened (all three parts, same strength), not strengthened.
6. Models used: `localTime`, `departureRange` (above).

## 2. thm-fluctuations (`CERW.Frozen.fluctuation_rates`, paper 130-152): DEFECT

### The defect

The volume clause is written

```lean
      volume ((r n)⁻¹ • CERW.cellSet Y n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
```

In Mathlib `∆` is `infixl:100` (scoped `symmDiff`) and `•` is `infixr:73`, so `∆` binds tighter and this parses as
`volume ((r n)⁻¹ • (CERW.cellSet Y n ∆ Metric.ball 0 1))`, the scaled symmetric difference, not `(r_n^{-1} D_n) △ B(0,1)` as in the paper
("`|r_n^{-1} D_n △ B(0,1)|`"). Machine evidence (compiles with no output; the second `example` is the statement that the draft's term equals
the wrongly-scaled term, proved by `rfl`; the attempted `rfl` for the paper's grouping fails with a type mismatch, checked separately):

```lean
import CERW.Model
open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

-- the draft's clause parses with the scaling applied to the symmetric difference
example {d : ℕ} (Y : ℕ → Site d) (n : ℕ) (r : ℕ → ℝ) :
  ((r n)⁻¹ • CERW.cellSet Y n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) =
    (r n)⁻¹ • (CERW.cellSet Y n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := rfl

-- hence its volume is r^{-d} |D ∆ B(0,1)|
example {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) {r : ℝ} (hr : 0 < r) :
  volume (r⁻¹ • (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) =
    ENNReal.ofReal ((r ^ d)⁻¹) * volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  rw [Measure.addHaar_smul]
  simp [finrank_euclideanSpace, abs_of_pos hr]

-- and |D ∆ B(0,1)| ≥ |D| - ω_d
example {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) :
  volume D ≤ volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) +
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  refine le_trans (measure_mono (t := (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∪
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ?_) (measure_union_le _ _)
  intro x hx
  by_cases h : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1
  · exact Or.inr h
  · exact Or.inl (Or.inl ⟨hx, h⟩)
```

Consequence: the drafted clause says `r_n^{-d} |D_n △ B(0,1)| ≤ C·(√(log n / r_n) or log n / r_n)`. But `|D_n| = |A_n|` and, by Theorem 1.1(i)
(a.s. `|A_n|/r_n^d → ω_d`) and the third example, `r_n^{-d}|D_n △ B(0,1)| ≥ r_n^{-d}(|A_n| - ω_d) → ω_d > 0`, while the right side tends to 0
(`r_n → ∞`). So `Good C (X · ω) n` fails for all large `n` almost surely, for every `C`, and the drafted theorem is **false** (not merely unprovable): the
canonical realization (`exists_isCERW`) refutes both the probability clause and the almost-sure clause. The registered predecessor
`CERW.Frozen.fluctuation_bounds` (`CERW/Frozen/FluctuationBounds.lean:64`) and every `Support` use write
`(((N n)⁻¹ • CERW.cellSet Y n) ∆ ...)` with the parentheses.

### Proposed replacement (only the volume clause changes)

```lean
      volume (((r n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          ≤ ENNReal.ofReal
            (C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) ∧
```

The whole corrected file elaborates with no error (only `sorry`): `.../scratchpad/chk/FRfixed.lean`. With that one edit the parse is
`volume ((scaled D_n) ∆ ball)`, as in the registered predecessor.

### The rest of the statement (checked, all correct once the above is fixed)

1. Binder order `hd, ε (0<ε<1/d), p, ∃ C > 0, ∀ Ω μ X`: `C(d,κ,p)` precedes the probability space and follows `d, κ, p`. Correct. `0 < C` loses nothing (enlarging `C` weakens both clauses).
2. The probability clause is `μ {ω | ¬ Good C (X · ω) n} ≤ ofReal (C n^{-p})` for every `n ≥ 2` (outer-measure convention); the a.s. clause is
   `∀ᵐ ω, ∀ᶠ n, Good C (X · ω) n` with the same `C` (author ruling; consistent: for small `p` take the maximum of `C(p)` and `C(2)`).
3. Exponents: `d=2`: `|R_in - r| ≤ C√(r log n)`, `R_out - r ≤ C√r (log n)^{5/2}`; `d≥3`: `≤ C log n`, `≤ C (log n)^{d+1}`; volume `C√(log n/r)` / `C log n/r`;
   local times `C√r (log n)^{3/2}` / `C√(r log n)`, for all `x` with `max(r - |x|, 0)`. Precedences in `C * √(r n) * Real.log n ^ (5/2)` and in `C * if … else …` confirmed by the
   elaborated term (`pp`): the `if`/`else` in the last conjunct ends at the end of `Good`, and `∀ x` covers only the local-time bound.
4. Junk: `n ≥ 2` gives `log n > 0`, `r n > 0`; `innerRadius` is a genuine infimum; `volume` is in `ℝ≥0∞` and compared with `ofReal` of a positive number. None.
5. Strength: after the fix it is the paper's claim (simultaneous bounds, same `C`, eventually a.s.).
6. Models: `innerRadius`, `maxRadius`, `cellSet`, `localTime` as above.

### Cross-node note (outside my nine nodes)

`scratch/Frozen/InnerRadius.lean` lines 20-21 contain the same pattern `volume ((r n)⁻¹ • CERW.cellSet (X · ω) n ∆ Metric.ball ... 1)` and therefore the same misparse. I did not audit that node
otherwise.

## 3. thm-sharp-radii (`CERW.Frozen.sharp_radii`, Theorem 1.3(i), paper 159-164): PASS

1. `c(κ,p)`: `∀ p > 0, ∃ c > 0, ∃ n₀, ∀ Ω μ X, IsCERW → ∀ n ≥ n₀`. `c` and `n₀` follow `ε, p` and precede the probability space. Binding `n₀` before the space is legitimate and is
   what the paper says, because both events are functions of `(X_0,…,X_n)` and the law of the prefix is fixed by `IsCERW`.
2. Two-sided statements are probability lower bounds, written `MeasurableSet E ∧ ofReal(n^{-p}) ≤ μ E` for both events (convention). Measurability is true (finite-valued functions of measurable `X_j`). No a.s. clause in the paper.
3. `d = 2` via `hd : d = 2`; events `c√(r n log n) ≤ r n - innerRadius` and `c√(r n log n) ≤ maxRadius - r n`. Match `eq:planar-polynomial-lower`.
4. Junk: `n₀` is existentially chosen, so `Real.log n = 0` at `n ∈ {0,1}` cannot trivialize the claim; for `n ≥ n₀ ≥ 2` everything is real.
5. Not weakened (probability lower bound `n^{-p}` for both radii, for every `p`), not stronger than the paper's.
6. Models: `innerRadius`, `maxRadius`.

## 4. thm-sharp-radii-lil (`CERW.Frozen.sharp_radii_lil`, Theorem 1.3(ii), paper 165-170): PASS

1. No constants. `hLIL : CERW.External.StoutLIL.{u}` with the same universe `u` as `Ω` (author ruling; the proof reaches Stout through Theorem 8.1 / line 1412).
2. `∀ᵐ ω, ∀ δ > 0, (∃ᶠ n, …) ∧ (∃ᶠ n, …)`: the `limsup ≥ L` convention (only the "frequently" half), both displays as conjuncts under one `∀ᵐ`.
3. `L = 1/√(10πκ)` is `1 / Real.sqrt (10 * Real.pi * ε)`; normalizer `√(r_n log log n)`; first display `r_n - R_in`, second `R_out - r_n`. Consistency check against the proof: `eq:moment-radius-lil` at `d=2`
   gives `√2/√(20πκ) = 1/√(10πκ)`. Match.
4. Junk: `log log n ≤ 0` for `n ≤ 2` (and `sqrt` of a negative number is 0) affects finitely many `n`, irrelevant to `∃ᶠ`; for `n ≥ 3` the normalizer is positive so `(L-δ)√(…) ≤ a_n` is the ratio statement.
   For `δ ≥ L` the claim is implied by the claim for small `δ`, so the quantification over all `δ > 0` is harmless.
5. Exactly the paper's claim (limsup `≥`, not `=`).
6. Models: `innerRadius`, `maxRadius`.

## 5. thm-sharp-bulk (`CERW.Frozen.sharp_bulk`, Theorem 1.3(iii), paper 171-175): PASS

1. `c(d,κ)`: `∃ c > 0, ∃ n₀, ∀ Ω μ X, IsCERW → ∀ n ≥ n₀`; the same `c` is the multiplier and the exponent, as in the paper (shrinking `c` weakens both, so it is consistent). `2 ≤ d` for `d ≥ 2`.
2. "With probability at least `1 - n^{-c}`": `μ {ω | ¬ ∃ x, …} ≤ ofReal (n^{-c})` (outer-measure convention). The maximum over the finite set `{|x| ≤ r_n^{1/2}}` (contains 0, so nonempty) being `≥ c φ_n` is exactly `∃ x, |x| ≤ √(r n) ∧ c φ_n ≤ |…|`.
3. `φ_n = √r log n` for `d=2`, `√(r log n)` for `d≥3` via `if d = 2 then … else …` (else = `d ≥ 3`). `|ℓ_n(x) - 2dε (r n - |x|)|` without positive part, as in the paper.
4. Junk: none for `n ≥ n₀ ≥ 2`.
5. Same strength as the paper.
6. Model: `localTime`.

## 6. thm-sharp-width (`CERW.Frozen.sharp_width`, Theorem 1.3(iv)(a),(b), paper 176-187): PASS

1. (a): `∀ p, ∃ c > 0, ∃ n₀, ∀ Ω μ X, … ∀ n ≥ n₀` with `MeasurableSet E ∧ ofReal(n^{-p}) ≤ μ E`, `E = {c√(r log n) ≤ maxRadius - innerRadius}`. Matches `eq:planar-width-polynomial`. (b): `∀ Ω μ X, IsCERW → ∀ᵐ ω, ∀ δ > 0, ∃ᶠ n, (√(π/(3ε)) - δ)√(r log log n) ≤ maxRadius - innerRadius`; matches `eq:planar-width-lil`
   (`limsup ≥`). The constant `√(π/(3κ))` is `Real.sqrt (Real.pi / (3 * ε))`; the proof's Step 3 ends at `(π/(3κ))^{1/2}`.
2. The two parts are one conjunction under a single `∀ ε` (author ruling); `hLIL` is carried, used by (b) only (line 1647).
3. Junk as in node 4. `d = 2`.
4. The parenthesization of the `let E … ; MeasurableSet E ∧ …` inside the `∀ p` conjunct is correct (elaborates; conjunction `(∀ p …) ∧ (∀ Ω … ∀ᵐ …)`).
5. Not weakened.
6. Models: `innerRadius`, `maxRadius`.

## 7. ext-martingale-clt (`CERW.External.MartingaleCLT`; cited at lines 1401, 1521): PASS

What I believe Hall and Heyde (1980), Corollary 3.1 says: for a zero-mean square-integrable martingale array `(S_{ni}, F_{ni}; 1 ≤ i ≤ k_n)` with differences `X_{ni}` and an a.s. finite random variable `η²`,
if for every `δ>0` the conditional Lindeberg sum `Σ_i E[X_{ni}² 1{|X_{ni}|>δ} | F_{n,i-1}] → 0` in probability, and `V²_{nk_n} = Σ_i E[X_{ni}² | F_{n,i-1}] → η²` in probability, and
the σ-fields are nested (`F_{n,i} ⊆ F_{n+1,i}`), then `S_{nk_n} → Z` in distribution, `Z` with characteristic function `E exp(-η² t²/2)`. I am fairly but not fully sure that nesting is dropped when `η²` is constant; it is
irrelevant here because `F_{n,i} = F_i` is nested.

The Lean Prop is the case `k_n = n`, `F_{n,i} = F_i`, `S_{ni} = S_i / s_n` for one martingale `S`, deterministic `s_n > 0`, and constant `η² = v ≥ 0`.
* Lindeberg: `Σ_{i<n} E[((S_{i+1}-S_i)/s_n)² 1{δ < |S_{i+1}-S_i|/s_n} | ℱ_i] → 0` in measure: exact (strict `>`, `i` indexes `F_{n,i-1}`).
* Variance: `predBracket μ ℱ S S n / s n ^ 2 → v` in measure: exact (`^` binds tighter than `/`).
* Conclusion `TendstoInDistribution (S n / s n) atTop id (fun _ => μ) (gaussianReal 0 v)`: checked against `ConvergenceInDistribution.lean` (`Z := id` on `(ℝ, gaussianReal 0 v)`;
  `aemeasurable` side conditions are automatic). `gaussianReal 0 0` is the Dirac mass at `0` (Mathlib `gaussianReal`), which is HH's `η² = 0` case that line 1521 asks for.
* Integrability: `Martingale S ℱ μ`, `MemLp (S n) 2 μ`, `S 0 = 0`; conditional expectations are a.e.-defined and `TendstoInMeasure` is insensitive to that.
Implied by the cited theorem, with the special case faithful. No junk (`s n > 0`, `v : ℝ≥0`).

Strength for the uses: line 1401 (`Q_n / r_n^{(d+3)/2} → N(0, 8dκω_d/((d+2)(d+3)))`): the paper proves a.s. that the conditional Lindeberg sum vanishes for large `n` (increment bounded by `C|X_j|`, an `F_j`-measurable bound) and
`⟨Q⟩_n / r_n^{d+3} → const` a.s.; both imply the two convergence-in-measure hypotheses. Line 1521 (`-M^y`, deterministic normalizers `√(r_n log r_n)` or `√r_n`, bounded increments, brackets converge a.s., Cramér-Wold
linear combinations are again one scalar martingale, variance may be 0): covered.

Optional convenience notes (not defects; both strengthen the External while it stays a consequence of the cited theorem):
* `(∀ ω, S 0 ω = 0)` is the literal special case (HH arrays start from `S_{n0} = 0`). The paper's `Q_n = 2κΣ|x| - n + |X_n|²` has `Q_0 = |X_0|² = 0` only almost surely, so a consumer applies the Prop to `Q - Q_0`
  (same filtration, same increments, same bracket). Replacing the hypothesis by `∀ᵐ ω ∂μ, S 0 ω = 0` would spare this step; it is still a consequence of the everywhere form applied to `S - S 0`.
  (Dynkin martingales `M^f` have `M^f_0 = 0` surely.)
* `(∀ n, 0 < s n)`: the natural normalizers (`r_n^{(d+3)/2}`, `√(r_n log r_n)`) vanish or are junk at `n = 0, 1`; a consumer replaces finitely many `s n` (neither hypotheses nor conclusion are sensitive to that at `atTop`).
  `∀ᶠ n in atTop, 0 < s n` would be more convenient.

## 8. ext-stout-lil (`CERW.External.StoutLIL`; cited at lines 1412, 1521, 1647): PASS, with one unverified point

What I believe Stout (1970), "A martingale analogue of Kolmogorov's law of the iterated logarithm", Z. Wahrsch. verw. Gebiete 15, 279-290, Theorem 1 says (also Hall and Heyde 1980, Theorem 4.8, number recalled from memory):
let `S_n = Σ_{i≤n} X_i` be a zero-mean square-integrable martingale, `s_n² = Σ_{i≤n} E[X_i² | F_{i-1}]`. If `s_n² → ∞` a.s. and `|X_n| ≤ K_n` with `K_n` `F_{n-1}`-measurable and
`K_n = o(s_n / (log log s_n²)^{1/2})` a.s., then `limsup S_n / (2 s_n² log log s_n²)^{1/2} = 1` a.s.
**Unverified:** I am not certain of the exact wording of the bound hypothesis in the original paper (predictable `K_n` as above, which is what the paper asserts at line 1406 "is predictable", versus a constant or a
weaker/stronger form), and I did not have the paper to hand. The Lean Prop requires the predictable form, so if Stout's theorem only needs `K_n` to be `F_n`-measurable it is implied; if it needs something
beyond the paper's verification (for example monotone `K_n`) it would be too strong. Please check against the PDF before accepting.

Match with the Lean Prop (all confirmed by reading):
* `S` martingale, `MemLp 2`, `S 0 = 0`; `B (n+1)` is `ℱ n`-strongly measurable and bounds `|S (n+1) - S n|` a.s.: the bound of the increment at time `n+1` is determined at time `n`, i.e. `K_{n+1}` is `F_n`-measurable. Correct indexing.
* `predBracket μ ℱ S S n = Σ_{t<n} E[(S_{t+1}-S_t)² | ℱ_t] = s_n²`, which is `F_{n-1}`-measurable; `B n` (bound on `S_n - S_{n-1}`) is paired with `⟨S⟩_n`, as `K_n` with `s_n`.
* `⟨S⟩_n → ∞` a.s.; growth condition `B_n √(log log(⟨S⟩_n ∨ e^e)) / √⟨S⟩_n → 0` a.s.: exactly the expression the paper verifies at lines 1406-1412 (note `√(log log(· ∨ e^e)) ≥ 1`, so it implies `B_n/√⟨S⟩_n → 0`; it is equivalent to Stout's `K_n = o(s_n (log log s_n²)^{-1/2})` once `⟨S⟩_n > e^e`).
* Conclusion: `∀ᵐ ω, ∀ δ > 0, (∀ᶠ n, S n ≤ (1+δ)√(2⟨S⟩ log log ⟨S⟩)) ∧ (∃ᶠ n, (1-δ)√(2⟨S⟩ log log ⟨S⟩) ≤ S n)`: the junk-free form of `limsup = 1`; `log log ⟨S⟩` has no `max`, but `⟨S⟩ → ∞` a.s. makes it real for all large `n`, and both clauses are tail statements.
Junk check: `B n * … / √⟨S⟩` divides by zero only at finitely many `n`; nothing is vacuous (the hypotheses are satisfiable, e.g. simple random walk, `B = 1`).

Strength for the uses: line 1412 (`Q` and `-Q`, predictable `B_n = C|X_{n-1}|`, `⟨Q⟩_n ~ r_n^{d+3}`, ratio `O(√(log log n / n))`), line 1521 (`±M^y`, constant bound, `⟨M^y⟩_n ~ r_n log r_n` or `~ r_n`), line 1647
(`Y`, constant bound 2, `⟨Y⟩_n / n → 1/2`): all supply exactly the Prop's hypotheses; the two-sided sign is obtained by applying the Prop to `-S`. Both halves of the conclusion are used (upper bound for the `=` statements of
Theorem 8.1; "frequently ≥" for Theorem 1.3(ii) and (iv)). The only adaptations on the consumer side: `S 0 = 0` everywhere (`Q_0 = |X_0|²` is 0 only a.s.; use `Q - Q_0`).

---

## Checks performed that found nothing (for the record)

* Elaborated `LimitShape` and `FluctuationRates` with `pp.numericTypes`/`pp.coercions`: all casts as intended.
* `if d = 2 then … else …` versus `d ≥ 3`: under `hd : 2 ≤ d` (respectively `d = 2`, where the else branch never occurs) the split is the paper's.
* Every probability lower bound carries `MeasurableSet`; every "with probability at least 1-…" is an outer-measure upper bound on the complement; every limsup is junk-free.
* No draft uses `sInf`/`sSup`/`tsum`/`ncard`/division by a possibly zero term other than the `Real.log`/`Real.sqrt`/`1/√` junk discussed above (each only at finitely many `n`).
