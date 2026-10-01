# Can `CERW.External.StoutLIL` be proved? Feasibility study

Target: `CERW.External.StoutLIL` (CERW/External/StoutLIL.lean:18, twin `CERW.Support.Statements.StoutLIL` at
CERW/Support/Statements.lean:38). HEAD 9217e0b; the statement and `CERW.predBracket` (CERW/Model/Bracket.lean:16)
are unchanged. Every external name below is `#check`ed in `scratch/externals/LilProbe.lean` (exit status 0,
87 `#check`s plus one `example`). Private declarations are cited by line range only, never by name.
Notation: `P_n = predBracket μ ℱ S S n`, `L(x) = log log x`, `f(x) = x / L(max x e^e)`, `x_k = θ^k`.

Read first. `predBracket μ ℱ S S n` is *literally* `LatticeProb.condQvar μ ℱ S n` up to `sq` (the `example` at the
end of the probe proves this). So Freedman's inequality (LatticeProb/Prob/Freedman.lean) speaks about `P_n` directly.

## 0. Summary

| half | route | packets | new lines | verdict |
|---|---|---|---|---|
| (U) `∀ᶠ n, S n ≤ (1+δ)√(2⟨S⟩ log log ⟨S⟩)` | geometric bracket blocks + maximal Freedman + Borel-Cantelli, with predictable truncation of `B` | 9 | about 1060 (800 to 1300) | FEASIBLE |
| (L) `∃ᶠ n, (1-δ)√(…) ≤ S n` | Stout's Theorem 2: pad, bracket stopping times, sharp conditional lower tail, Lévy conditional BC, plus (U) for `-S` | 12 (after the 9 of (U)) | about 3600 (3000 to 4500) | NOT FEASIBLE NOW |

A proved (U) lets the External be reduced to a pure `∃ᶠ` proposition (`StoutLower`), and
`StoutLIL ⇐ StoutUpper ∧ StoutLower` is about 20 lines (`ae_all_iff`, `Filter.Eventually.and`).

## 1. Route (U), the upper half

Source. Stout (1970), Theorem 1 (p. 286); the textbook proof is the geometric-block argument of the LIL with the
exponential bound (Stout, Almost Sure Convergence 1974, 5.4; I could not read it, see stout-source.md section 3).
Below is my adaptation to the exact Lean statement; the Lean-specific devices are mine.

Fix `δ ∈ (0,1]` (rational `1/(m+1)` suffices: the conclusion for a smaller `δ` implies it for a larger one, and a
countable `ae_all_iff` finishes). Choose `θ > 1`, `ε > 0`, `η > 0` with
`(1+δ)² / (θ + ε(1+δ)√(2θ)/3) ≥ 1+η`. For `k` large put `L_k = log log x_k = log(k log θ)` and
`v_k = x_{k+1}`, `b_k = ε√(θ x_k / L_k)`, `r_k = (1+δ)√(2 x_k L_k)`.

1. Bracket version. `V k = Σ_{t<k} max(μ[(ΔS_{t+1})² | ℱ t], 0)` is sure-nondecreasing, `V 0 = 0`, `V (k+1)` is
   `ℱ k`-measurable, dominates the conditional variances, and equals `P_k` for all `k` a.s.
   (same device as the private lemma at CERW/Support/Norm/Freedman.lean:28).
2. Predictable truncation of the unbounded `B`. `T^{(k)}_n = Σ_{j<n} 1{B_{j+1} ≤ b_k} ΔS_{j+1}` is
   `predictableStop S B b_k n` (the existing gate `1{V(k+1) ≤ v}` with `V := B`). It is a square-integrable
   martingale since `B (j+1)` is `ℱ j`-measurable. Its increments are a.s. at most `b_k`, so `exists_martingale_clamp`
   gives an a.s.-equal martingale with surely bounded increments (needed by `freedman_upper`). Its conditional
   variances are at most those of `S`. No padding is needed: only upper tails are used, and truncation only lowers
   the bracket.
3. Bracket stopping. Stop `T^{(k)}` predictably once `V` would exceed `v_k` (`predictableStop … V v_k`, existing).
   The stopped conditional variance is at most `v_k` by `condQvar_predictableStop_le`
   (this is the predictable analogue of the stopping times `τ_k = inf{n : P_{n+1} ≥ θ^k}`; it avoids
   `IsStoppingTime` and `ℱ_τ` altogether).
4. Maximal Freedman. For a martingale `M` with `M 0 = 0`, surely `|ΔM| ≤ b`, `condQvar_n ≤ v`:
   `μ{∃ i ≤ n, r < M i} ≤ exp(-r²/(2(v + b r/3)))`. Route A (primary): stop `M` predictably at the first time its
   running max exceeds `r` (a third `predictableStop`, with `V' (k+1) = max_{i ≤ k} M i`), the stopped martingale
   is `> r` at time `n` on the event, then `freedman_upper` at time `n`. Route B (fallback, about +60 lines):
   `exp(λ M)` is a submartingale by `ConvexOn.map_condExp_le_univ`, apply `maximal_ineq`, then the mgf bound that
   is internal to `freedman_upper_of_pos`'s proof (re-derive from `integral_exp_sub_condQvar_le_one`).
5. Exponent. `v + b r/3 = x_k(θ + ε(1+δ)√(2θ)/3)`, so `r²/(2(v+br/3)) ≥ (1+η) L_k`, and the bound is
   `exp(-(1+η)L_k) = (k log θ)^{-(1+η)}`, summable. Monotone union over the horizon `N` gives
   `μ(E_k) ≤ (k log θ)^{-(1+η)}` for `E_k = {∃ n, V n ≤ v_k ∧ r_k < T^{(k)}_n}`.
6. Borel-Cantelli (`ae_eventually_notMem`): a.s. `ω ∉ E_k` for all large `k`.
7. Pathwise. Fix a good `ω`. Hypothesis `B_n√L/√P_n → 0` gives `N` with `B_m ≤ ε√f(P_m)` for `m ≥ N`.
   `f` is nondecreasing on `[0,∞)` (elementary: for `e^e ≤ x ≤ y`, `L(y) ≤ L(x) + (y/x - 1)` by
   `log_le_sub_one_of_pos`, then `x L(y) ≤ y L(x)` because `L(x) ≥ 1`), so for `m ≥ N` with `P_m < x_{k+1}`:
   `B_m ≤ ε√f(x_{k+1}) ≤ b_k` (`L(θ x_k) ≥ L_k`). The finitely many `m < N` satisfy `B_m ≤ b_k` once `k ≥ k_0(ω)`
   (`b_k → ∞`). Hence `T^{(k)}_n = S n` whenever `P_n < x_{k+1}`, `k ≥ k_0`. Pick `k` with
   `x_k ≤ P_n < x_{k+1}` (`exists_nat_pow_near`; `k → ∞` as `P_n → ∞`). If `S n > (1+δ)√(2 P_n L(P_n)) ≥ r_k`
   (monotonicity of `y L(y)` on `[e,∞)`) then `ω ∈ E_k`. Contradiction for large `n`.

The hypothesis `B_n √L(P_n ∨ e^e)/√P_n → 0` (random, a.s.) is exactly what step 7 consumes; it is used only
through the *eventual* bound with a random `N`, so no localization is needed in (U).

## 2. Packet table (U). Proposed new files under `CERW/Generic/Martingale/Lil/` (none exists yet)

| # | File: lemmas (signature sketch) | Existing names used (file:line) | New lines | Risk |
|---|---|---|---|---|
| U1 | `LilBracket`: `exists_regBracket (hS : Martingale S ℱ μ) (hL2 : ∀ n, MemLp (S n) 2 μ) : ∃ V, (∀ k, StronglyMeasurable[ℱ k] (V (k+1))) ∧ (∀ ω, V 0 ω = 0) ∧ (∀ k ω, V k ω ≤ V (k+1) ω) ∧ (∀ k, μ[(ΔS)^2 \| ℱ k] ≤ᵐ V (k+1) - V k) ∧ ∀ᵐ ω, ∀ k, V k ω = predBracket μ ℱ S S k ω` ; `predBracket_eq_condQvar` (compiles, see probe) | `CERW.predBracket` Model/Bracket.lean:16; `LatticeProb.condQvar` Freedman.lean:114; `condExp_nonneg` Mathlib …/ConditionalExpectation/Basic.lean:495; `stronglyMeasurable_condExp` Basic.lean:187; `MemLp.integrable_sq` L2Space.lean:42 | 70 | low |
| U2 | `GatedVariance`: `condExp_sq_predictableStop_le` (`μ[(Δ predictableStop M V v)^2 \| ℱ j] ≤ᵐ μ[(ΔM)^2 \| ℱ j]` under `MemLp 2`, no sure bound); `abs_predictableStop_succ_sub_ae_le` | `predictableStop` FreedmanEvent.lean:30; `predictableStop_succ_sub` :77; `bracketIndicator_nonneg` :34, `_le_one` :40, `_mul_self` :46; `condExp_stronglyMeasurable_mul_of_bound` PullOut.lean:260; `condExp_mono` Basic.lean:486 | 70 | low |
| U3 | `FirstPassage`: `runMax`; `firstPassage M r := predictableStop M (fun k => runMax M (k-1)) r`; `lt_firstPassage_of_exists_gt` (`∃ i ≤ n, r < M i ω → r < firstPassage M r n ω`); `condQvar_firstPassage_le` | `bracketIndicator_of_le` :52, `_of_lt` :58; `stronglyMeasurable_bracketIndicator` :64; `martingale_predictableStop` :173; `abs_predictableStop_succ_sub_le` :196; U2 | 110 | med |
| U4 | `MaximalFreedman`: `measure_exists_gt_le` : `μ{ω \| ∃ i ≤ n, V i ω ≤ v ∧ r < M i ω} ≤ ofReal (exp (-(r^2/(2*(v+b*r/3)))))` for a martingale with sure increments `≤ b`, `V` as in U1 | `LatticeProb.freedman_upper` Freedman.lean:360; `condQvar_predictableStop_le` FreedmanEvent.lean:207; `predictableStop_eq_of_le` :83; `sum_bracketIndicator_mul_le` :100; U3 | 100 | med |
| U5 | `TruncatedBlock`: `measure_exists_truncated_le` : `μ{ω \| ∃ n, V n ω ≤ v ∧ r < predictableStop S B b n ω} ≤ ofReal (exp (…))` (layer 1 truncation, clamp, U4, monotone union over horizon, a.e. transfer) | `exists_martingale_clamp` Clamp.lean:85; `martingale_predictableStop` :173; `integrable_predictableStop` :134; `Monotone.measure_iUnion` MeasureSpace.lean:520; `condExp_congr_ae` Basic.lean:201; U1, U2, U4 | 160 | med-high |
| U6 | `LilArith`: `exists_lil_params (δ) : ∃ θ ε η, …` ; `exponent_ge` (`r²/(2(v+br/3)) ≥ (1+η) L`) ; `mono_div_loglog` (`MonotoneOn f (Ici (exp (exp 1)))`) ; `mono_mul_loglog` | `Real.log_le_sub_one_of_pos` Log/Basic.lean:306; `Real.add_one_le_exp` Complex/Exponential.lean:631; reference for the arithmetic style: `CERW.Generic.Martingale.le_freedman_exponent` Arith.lean:18 | 130 | med (nlinarith; use explicit `mul_le_mul`) |
| U7 | `LilBorelCantelli`: `summable_blocks` (`Summable fun k => ((k:ℝ) * log θ)^(-(1+η))` and the `ENNReal` form `∑' k, μ (E k) ≠ ∞`) ; `ae_eventually_not_block` | `Real.summable_nat_rpow_inv` PSeries.lean:280; `Real.log_pow` Log/Basic.lean:287; `MeasureTheory.ae_eventually_notMem` OuterMeasure/BorelCantelli.lean:86; `measure_limsup_atTop_eq_zero` :62; U5, U6 | 110 | low-med |
| U8 | `LilPathwise` (deterministic): `predictableStop_eq_self_of_le` (`(∀ j < n, B (j+1) ω ≤ b) → predictableStop S B b n ω = S n ω`; note `predictableStop_eq_of_le` needs `V` monotone, `B` is not) ; `eventually_le_of_not_block` (all pathwise hypotheses ⇒ `∀ᶠ n, S n ≤ (1+δ)√(2 P_n log log P_n)`) | `exists_nat_pow_near` Archimedean/Basic.lean:197; `bracketIndicator_of_le` FreedmanEvent.lean:52; `predictableStop_succ_sub` :77; `Filter.eventually_all_finset` Order/Filter/Finite.lean:258; U6 | 220 | med-high |
| U9 | `StoutUpper`: `def StoutUpper : Prop` (the `∀ᶠ` conjunct only), `stout_upper : StoutUpper`, `stoutLIL_of_upper_lower` | `ae_all_iff` OuterMeasure/AE.lean:95; U1 to U8; `CERW.External.StoutLIL` External/StoutLIL.lean:18 | 90 | low-med |

Dependencies: U1 → U2 → U3 → U4 → U5 → U7 → U8 → U9; U6 is independent and feeds U7 and U8.
Total: 9 packets, about 1060 lines. Critical path U1-U2-U3-U4-U5-U7-U8-U9, about 980 lines, each file one or two lemmas.
Existing code that already does 60 percent of the infrastructure: CERW/Generic/Martingale/FreedmanEvent.lean (295 lines) and Clamp.lean (102).

### Missing pieces for (U), stated precisely
(a) a maximal form of Freedman (U3, U4): LatticeProb's `freedman_upper` is fixed-time; Mathlib's `maximal_ineq`
needs a submartingale. (b) A gate-with-`MemLp 2` variance comparison (U2): `condQvar_predictableStop_le` assumes a
sure increment bound on the *inner* martingale, which the truncation `predictableStop S B b` only has a.s.
(c) the monotonicity of `x / log log x` (U6), absent from Mathlib. (d) the deterministic block bookkeeping (U8).

### Verdict (U): FEASIBLE
9 packets, about 1060 lines (800 to 1300). Critical path as above. Riskiest step: U8, the pathwise assembly
(random `N` and `k_0`, block index `k(n)`, `P_n` versus `V n` null sets, four monotonicity facts), which is a long
chain of real-analysis inequalities in the style that previously hit `nlinarith` whnf timeouts (bisect with `sorry`,
use explicit `mul_le_mul`). Second riskiest: U5 (a.e.-equal martingale juggling: clamp, gate, nested `predictableStop`).

## 3. Route (L), the lower half

Source. Stout (1970), Theorem 2 (p. 287), proof pp. 287-288, as recorded in stout-source.md section 1:
truncate on `C_n^M = {K_j ≤ M ∀ j ≤ n}`, pad with independent symmetric ±1 variables `R_n`, conclude
`X_{t_k} > (1-δ')s_{t_k}u_{t_k}` i.o. on `∩_n C_n^M`, hence on `∪_M ∩_n C_n^M = Ω`. Stout (1974) 5.4.1 is not
open access. Everything below beyond that summary is my reconstruction (marked [R]).

Adapted to the Lean statement (`K_n ≍ B_n√(2L(P_n))/√P_n`, `ℱ n`-predictable):

0. [U for `-S`] `-S` is a martingale with the same bracket (`predBracket (-S) (-S) = predBracket S S`, a three-line
   algebra fact, private in ExpDeviation.lean:1391), so (U) gives `S_n ≥ -(1+δ')√(2P_nL)` eventually. This is the
   only place (U) is used, and it is why (U) is a prerequisite of (L).
1. Localise and pad. Work on `Ω̃ = Ω × (ℕ → Bool)` with `μ ⊗ infinitePi (uniform)`, filtration
   `ℱ̃_n = ℱ_n∘fst ∨ σ(ξ_1..ξ_n)`. Gate out increments with `K_{j+1} > M` (predictable indicator) and replace them by
   `a_j ξ_{j+1}` with predictable `a_j`. The padded `S̃` is a martingale, `P̃_n → ∞` surely, `K̃ ≤ M`, and
   `S̃ = S` on `C^M`. [R] Padding cannot be skipped: truncation alone makes the block bracket deficient on an event
   `D_k` whose conditional probabilities are summable (Lévy converse) but without a rate, while the sharp lower
   tail loses a factor `e^{s²v} = k^{O(1)}` on `D_k` (Cauchy-Schwarz on `E[Z 1_D]`); this kills summability.
   This agrees with ledger/audits/stout-uses.md ("Does a standard localization recover (D)?": padding is the
   only thing that works).
2. Blocks. `τ_k = inf{n : P̃_{n+1} ≥ θ^k}` (stopping times), `G_k = ℱ̃_{τ_k}`; surely `P̃_{τ_k} ∈ [x_k(1-s), x_k)`.
3. Sharp conditional lower tail [R]. For `F ∈ G_{k-1}`: `P(F ∩ {S̃_{τ_k} - S̃_{τ_{k-1}} ≥ a_k}) ≥ q_k P(F)`,
   `a_k = (1-δ/2)√(2 x_k L_k)`, `q_k = (k log θ)^{-(1-η)}`. Proof: exponential martingale `Z = exp(sN - K(s))`
   with the cumulant estimate `|K(s) - s²V/2| ≤ 2|s|³bV` (exists privately, ExpDeviation.lean:205-330), tilted
   measure `Q = Z·P`, Chebyshev under `Q`, `P(N∈[a,a']) ≥ e^{-sa'+K_min} Q(N∈[a,a'])`.
4. Lévy's conditional BC along `G_k` (`ae_mem_limsup_atTop_iff`): `Σ q_k = ∞` ⇒ `A_k` i.o.
5. Combine with 0 and `θ → ∞` (`θ^{-1/2}(1+δ')` small): `S̃_{τ_k} ≥ (1-δ)√(2P̃L)` i.o.; `τ_k → ∞` gives `∃ᶠ n`;
   transfer along `fst`, union over `M`.

Why nothing already in the repo shortcuts this. `CERW.Support.Lower.exp_deviation` (ExpDeviation.lean:1408) is
existential and not sharp (its proof uses `c ≤ 1/8` and the bound `exp(-12 C₀β²)/4`; the Paley-Zygmund route loses
a factor 8 in the exponent, `e^{-4a²/v}` against the needed `e^{-a²/(2v)}`). `CERW.Frozen.freedman_bound` and
`LatticeProb.freedman*` are upper tails. LatticeProb has no LIL and no Brownian LIL; Skorokhod embedding is absent.

## 4. Packet table (L), in dependency order (after all of (U))

| # | File: lemma | Existing names used (file:line) | New lines | Risk |
|---|---|---|---|---|
| L1 | `PadSpace`: `Ω̃`, `ℱ̃`, `fst`-lift of a martingale is a martingale for `ℱ̃` | `MeasureTheory.Measure.prod` Measure/Prod.lean:171, `Measure.infinitePi` ProductMeasure.lean:356; `iIndepFun_infinitePi` Independence/InfinitePi.lean:127; `condExp_indep_eq` Probability/ConditionalExpectation.lean:42 | 250 | med |
| L2 | `PadCondExp`: `μ̃[X∘fst \| ℱ̃_n] = (μ[X \| ℱ_n])∘fst` (join of `ℱ_n∘fst` with an independent σ-algebra; π-λ on rectangles; `condExp_indep_eq` covers only a purely independent σ-algebra) | `condExp_indep_eq` ConditionalExpectation.lean:42; `condExp_congr_ae` Basic.lean:201 | 400 | high |
| L3 | `PaddedMart`: gated-and-padded `S̃` is a square-integrable martingale, `P̃` formula, `P̃ → ∞` surely, `K̃ ≤ M` | `martingale_predictableStop` FreedmanEvent.lean:173; `condExp_stronglyMeasurable_mul_of_bound` PullOut.lean:260; U1, U2 | 400 | med |
| L4 | `BracketTimes`: `τ_k : Ω → WithTop ℕ`, `IsStoppingTime`, window `P̃_{τ_k} ∈ [x_k(1-s), x_k)`, `τ_k < ∞`, `τ_k → ∞` | `IsStoppingTime` Stopping.lean:75; `stoppedValue` :788; `hittingBtwn` HittingTime.lean:56; `Adapted.isStoppingTime_hittingBtwn` :401 | 300 | med |
| L5 | `BlockMart`: block increment `N` as a martingale from the *random* time `τ_{k-1}` for `(ℱ̃_{τ_{k-1}+j})` (deterministic version: `martingale_shift`) | `IsStoppingTime.measurableSpace` Stopping.lean:444; `measurableSpace_mono` :468; `measurable_stoppedValue` :1035; `martingale_shift` Shift.lean:26; `shiftFiltration` :20 | 350 | high |
| L6 | `SharpCumulant`: make public or copy the private `expMart`/cumulant development (ExpDeviation.lean:60-680): `E Z = 1`, `|K(s) - s²V/2| ≤ 2|s|³bV`, horizon limit `τ_k ∧ N → τ_k` (uniform integrability from `E Z² ≤ e^{6 s² v}`) | `LatticeProb.exp_le_one_add_add_sq_div` Bernstein.lean:43; `condExp_exp_le` Freedman.lean:61 | 250 | med |
| L7 | `TiltedChebyshev`: under `Q = Z·P` (`withDensity`), mean `≈ sV` and variance `≲ V` of `N` | `condExp_mul_of_stronglyMeasurable_left` PullOut.lean:245; L6 | 500 | high |
| L8 | `SharpLowerTail`: `P(F ∩ {N ≥ a_k}) ≥ q_k P(F)` for `F ∈ ℱ̃_{τ_{k-1}}` | L5, L6, L7; `measure_ge_le_exp_mul_mgf` Moments/Basic.lean:429 (only as the matching upper bound) | 350 | high |
| L9 | `ConditionalBC`: Lévy's lemma along `G_k = ℱ̃_{τ_k}` | `ae_mem_limsup_atTop_iff` Martingale/BorelCantelli.lean:331 | 200 | med |
| L10 | `LowerArith`: parameter choice `θ(δ), η`; `Σ (k log θ)^{-(1-η)} = ∞` | `Real.summable_nat_rpow_inv` PSeries.lean:280 | 150 | med |
| L11 | `PaddedLower`: assemble `S̃_{τ_k} ≥ (1-δ)√(2P̃L)` i.o., using U on `-S̃` | `Martingale.neg` Martingale/Basic.lean:117; U9 | 250 | med |
| L12 | `StoutLower`: transfer along `fst`, union over `M`, `K → 0` reduction, final `StoutLIL` | `ae_all_iff` AE.lean:95 | 250 | med |

Total 12 packets, about 3600 lines (3000 to 4500). Critical path L1-L2-L3-L4-L5-L8-L9-L11-L12 (about 2400 lines),
with L6, L7, L10 feeding L8 and L11.

### Missing pieces for (L), stated precisely
1. A *sharp* lower tail for martingale block increments, conditional on `ℱ_{τ_{k-1}}`: `P(N ≥ (1-δ)√(2vL) | G) ≥
   (log v)^{-(1-η)}`. Not in Mathlib, LatticeProb or CERW (`exp_deviation` is existential, constant `c ≤ 1/8`).
2. The padding wrapper: `condExp` on a product filtration `ℱ_n∘fst ∨ σ(ξ_{≤n})` (Mathlib's `condExp_indep_eq` needs
   the conditioning σ-algebra independent of the integrand). Same gap as stout-uses.md reports.
3. Strong-Markov-type conditioning: the block martingale from a random time and probabilities given `ℱ_{τ}`.
4. A re-indexed Lévy BC along `ℱ_{τ_k}` (Mathlib has it only for a `Filtration ℕ`; `τ_k` gives one, but
   monotonicity `ℱ_{τ_k} ≤ ℱ_{τ_{k+1}}` and measurability of `A_k` must be built).

### Verdict (L): NOT FEASIBLE NOW
Reason: items 1 and 2 are each larger than the whole of (U); nothing exists to start from; total about 3600 lines
and 12 packets, 4 of them high risk, on top of the 1060 of (U). It is provable in principle from Mathlib and
LatticeProb. Riskiest step: L2 (the padded conditional expectation), then L7/L8 (tilted Chebyshev and the
conditional sharp lower tail). If the owner wants (L) anyway, the order is: (U) first (independently valuable),
then L6 (cheap, unlocks the cumulant estimates), then L2 as an isolated probe.

## 5. What a proved (U) buys (from ledger/audits/stout-uses.md)
`ae_sum_ratio`, `ae_tendsto_radiusFactor`, the two `∀ᶠ` conjuncts of moment-fluctuations, the `∀ᶠ` half of the site
LIL and the CLT/joint-limit items use only the upper conjunct. The pure-`∃ᶠ` consumers (`width_lil`,
`moment_radius_lil`) and the `∃ᶠ` halves still need (L).

## 6. Probe
`scratch/externals/LilProbe.lean`; run from the repo root:
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false scratch/externals/LilProbe.lean`.
Exit status 0 (87 `#check`s, no errors or warnings, plus the `predBracket = condQvar` example).
