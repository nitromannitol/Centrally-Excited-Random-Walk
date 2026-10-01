# How the development uses the martingale law of the iterated logarithm

*Closed: the predictable form is Stout (1970), Theorems 1 and 2 (see `external-sources.md`,
"Resolution"). This analysis is kept as a record and is not needed.*

Notation. `P_n` is `predBracket μ ℱ S S n` (the `s_n²` of the hypothesis) and `L(x) = log log max(x, e^e)`.
"Surely" means: outside one null set, for all `n` at once.
* (U): only the eventual upper bound, with predictable random `B`, is available.
* (D): `B` is a function of `n` alone and `B_n √L(P_n)/√P_n ≤ a_n` surely, for a deterministic `a_n → 0`.
* (D*): the form recorded in `ledger/audits/external-sources.md`, `|ΔS_n| ≤ a_n √P_n/√L(P_n)` with
  deterministic `a_n → 0`. The bound is random and predictable but the ratio is deterministic.
  (D) is a special case of (D*), which is a special case of the current hypothesis.

Two facts about the target hypothesis. `x ↦ L(x)/x` is decreasing on `(0, ∞)`, so a sure lower bound on
`P_n` gives a deterministic bound on `B_n √L(P_n)/√P_n`. A bound that holds only eventually, with a random
threshold, gives nothing of this kind.

## Table

| site | conjunct used | frozen node | bound supplied; what is known about `P_n` | survives (D)? | survives (U)? |
|---|---|---|---|---|---|
| `lil_normalized` (MomentCommon:803) | both: `hS δ hδ` is split into `hup, hlow` and both go to `lil_rescale` | feeds the next two rows | any random predictable `B` with `B_n²/s_n → 0` a.s.; only `P_n/s_n² → V` a.s. with deterministic `s_n` (N1) | no for strict (D); yes for (D*) after N1 | upper yes, lower lost |
| `dynkin_sq_lil` (MomentLil:43), then SharpRadii:1677 (`moment_radius_lil`, forwarded by `sharp_radii_lil_of_moment_lil`:1770) | lower only at the end (`(h δ hδ σ hσ).2` in `moment_radius_lil_of_stout`, both signs); the upper conjunct enters earlier through `ae_sum_ratio` | thm-sharp-radii-lil | `B_{n+1} = 4\|X_n\|+2`, random, unbounded; a.s. asymptotics only (N1) | strict (D) no; (D*) yes (N1) | no: the node is a pure `∃ᶠ` |
| `dynkin_sq_laws` (MomentFluctuations:229) | both; the result feeds `sum_lil` and `radius_lil` | thm-moment-fluctuations (LIL conjuncts for `S` and `R`; the CLT conjuncts do not use it) | same martingale and bound as the previous row | as above | `∀ᶠ` halves yes, `∃ᶠ` halves lost |
| `lil_of_bracket` (SiteFluctuations:2166), called once, at `lil_site` (3428, call at 3453) | both: `(hω δ' hδ').1` and `.2` go to `lil_of_bracket_convert` | thm-site-fluctuations, second item | `B ≡ 2C` constant, increments a.s. (`dynkin_martingale_facts`); only `P_n/σ_n² → c > 0` a.s. (N2) | `B` deterministic, domination fails even for (D*); needs padding | `∀ᶠ` half yes, `∃ᶠ` half lost |
| `ae_potential_term_le` (3122), `ae_potential_term_tendsto` (3347), `clt_combo` (3368), `clt_site` (3516) | pass `hLIL` to `hmom` only; used are `.2.2` and then `.1` at `δ = 1`, `σ = ±1`: the upper bound for `S` | thm-site-fluctuations, CLT and joint-limit items (negligible potential term) | as the Dynkin row (the `S` upper bound is the moment-fluctuations output) | as the Dynkin row, upper conjunct only | yes |
| `width_lil` (SharpWidth:1525) | lower only: `(hSω s hs0).2` | thm-sharp-width (b) | `B ≡ 2` surely; surely `P_n ≥ (1/2 - ε²) n` (N3) | yes, directly | no: the node is a pure `∃ᶠ` |

## Notes

**N1. The Dynkin martingale of `|x|²` (rows 1 to 3).** The bound is `B_{n+1} = 4|X_n| + 2`, predictable by
`stronglyMeasurable_comp_pastPath` and valid by `ae_abs_dynkin_sq_succ_sub_le`. The hypotheses of
`lil_normalized` are `P_n/s_n² → V` a.s. (from `ae_predBracket_dynkin_sq`, `tendsto_bracket_quotient` and the
limit shape), `s_n = norming d r n` deterministic with `log s_n² / log n → (d+3)/(d+1)`, and `B_n²/s_n → 0`
a.s. The last one comes from `maxRadius ≤ 2 r_n` eventually, the output of `fluctuation_rates`, with a random
index. The only sure bound on `B` is `|X_n| ≤ n` (`ae_euclidNorm_le`), and `n²/s_n` does not tend to 0.
So strict (D) is out of reach as the code stands. (D*) holds with no probabilistic localization.
By `ae_predBracket_dynkin_sq`, `P_n ≥ c₀ Σ_{t<n} |X_t|²` with `c₀ = 4/d - 4ε² > 0`. Steps are unit steps
(`ae_sub_mem_unitSteps`) from `0`, so `|X_t| ≥ 1` at odd `t`, and `|X|` changes by at most 1 per step, so it
passes every level `k ≤ M := |X_n|`; hence `Σ_{t≤n} |X_t|² ≥ ⌊M⌋³/3`. Therefore
`P_{n+1} ≥ c₀ max(⌊n/2⌋, ⌊M⌋³/3)` and `B_{n+1}² L(P_{n+1}) / P_{n+1} ≤ C (M+1)² log log n / max(n, M³)
≤ C n^{-1/3} log log n`. Cost: about 300 lines of elementary arithmetic (level-crossing lemma, decrease of
`L(x)/x`, replacement of the `hBs` and `tendsto_stout_condition` step inside `lil_normalized`). The two
copies, `dynkin_sq_lil` and `dynkin_sq_laws`, both go through `lil_normalized`, so one change serves both.

**N2. The kernel martingale (row 4).** `B ≡ 2C` is constant, so the only issue is the bracket. The proof
knows `W_n/σ_n² → c` a.s. (`ae_bracket_tendsto`, `σ_n = sigmaN`), a random threshold. No sure growth bound
exists. Every unit step has probability at least `1/(2d) - ε/2 > 0` (`firstStep`, `srwStep`, `IsCERW.step`),
so every nearest-neighbour path has positive probability. Along the ray `t e₁` the increments of the kernel
are at most `C(1+t)^{1-d}`, so the conditional variances are at most `C²(1+t)^{2-2d}`, which is summable for
`d ≥ 2`. Hence `P(W_n ≤ C') > 0` for every `n`, with `C'` independent of `n`. A deterministic lower bound
tending to infinity is impossible, so (D*) fails as well as (D).

**N3. The coordinate martingale (width row).** `exists_coord_martingale` gives increments at most 2 for all
`i, ω` (through `exists_martingale_clamp`) and, a.s. for all `n`, a bracket at least
`n/2 - ε²|A_n| ≥ (1/2 - ε²) n` (`card_departureRange_le`). With `c = 1/2 - ε²` and `φ(x) = L(x)/x`, (D) holds
with `a_n = 2√φ(c n)`. The proof only has to replace the use of `tendsto_bracket_ratio` (SharpWidth:1500)
at `hratio` by this bound and prove that `φ` decreases. Cost: about 80 lines.

**N4. Bundled lemmas.** `ae_sum_ratio` and `ae_tendsto_radiusFactor` read only `.1` (upper, `δ = 1`, both
signs). `lil_rescale`, `lil_add_small`, `lil_mul_seq`, `sum_lil` and `radius_lil` state the pair as one
hypothesis, but each half of the output uses the matching half of the input. Splitting them is mechanical.

## Does a standard localization recover (D)?

Two different defects must be repaired, and only the second is serious.
1. Random `B` (the `|x|²` site). Predictable truncation `Y_n 1{B_n ≤ b_n}` works: the indicator is
   `ℱ_{n-1}`-measurable, so the product is again a martingale difference with no recentring. With
   `b_n = 8 r_n + 2` we get `b_n²/s_n → 0` (`tendsto_scale_sq_div`) and the truncated martingale agrees
   with the original up to a random finite constant, with `P'_n = P_n - O_ω(1)`. Stopping at the first
   exit does the same. Cost: about 400 lines (`condExp` of a bounded predictable factor times a difference,
   bracket comparison, transfer back). This gives deterministic `B` but not the sure bracket bound.
2. A sure lower bound on the bracket. Stopping alone fails: `P_{n∧τ}` freezes, so the bracket does not
   tend to infinity on `{τ < ∞}`. Truncation fails: on an escaping ray the truncated bracket stays bounded.
   Predictable rescaling `λ_n Y_n` fails: on the ray the conditional variances are summable, and (D) forces
   each bracket increment to be a vanishing fraction of the bracket. A time change by the bracket,
   `T_k = inf{n : P_{n+1} ≥ k}`, gives bracket about `k`, but the increments of `M_{T_k}` are sums over a
   random number of steps and are not bounded by a deterministic `b_k`, so (D) is again not met; the
   formal cost (optional sampling at `T_k`, the filtration `ℱ_{T_k}`, finiteness of `T_k`) is also highest.
   What does work is independent padding (my analysis, not checked in the formalization):
   * Take `Ω' = Ω × (ℕ → Bool)` with `μ ⊗ infinitePi` of the uniform measure, independent signs `ξ_i`, and
     deterministic `η_i ∈ (0, 1]` with `Σ_{i≤n} η_i² = g_n`, where `g_n → ∞` and `g_n = o(σ_n²)`
     (for example `g_n = σ_n`).
   * `M' = M∘fst + Σ η_i ξ_i` is a martingale for `ℱ_n∘fst ∨ σ(ξ_1..ξ_n)`; the cross term of the bracket
     vanishes by independence, so `P'_n = P_n∘fst + g_n ≥ g_n` surely and `|ΔM'| ≤ K + 1`.
     (D) applies, with `a_n² ≍ log log g_n / g_n`.
   * `P'_n ~ P_n`, so the conclusion for `M'` has the right constants. Apply the same hypothesis to `±W`,
     where `W` is the padding (deterministic bracket `g_n`): `|W_n| = O(√(g_n log log g_n)) =
     o(σ_n √(log log n))`. Transfer the a.s. statements along `fst`.
   Cost: one generic wrapper, about 1000 to 1500 lines by estimate. Mathlib has `Measure.infinitePi`,
   `iIndepFun_infinitePi` and `condExp_indep_eq`, but the last covers a purely independent σ-algebra; the
   join with `ℱ_n∘fst` needs a π-λ argument on rectangles. It serves every constant-`B` site once.

## Verdict

* thm-sharp-width (b). Under (D): safe, about 80 lines (N3). Under (U): lost entirely, since the node is
  a pure `∃ᶠ` and no other proof route exists in the repository.
* thm-sharp-radii-lil. Under (D*): safe by N1, about 300 lines, no new probability. Under strict (D): needs
  truncation plus padding, about 1500 or more lines. Under (U): lost entirely (pure `∃ᶠ`, both signs).
* thm-moment-fluctuations. The CLT conjuncts do not use the hypothesis. The LIL conjuncts: as for
  sharp-radii-lil under (D*) and (D). Under (U) the two `∀ᶠ` conjuncts (for `S` and for `R`) survive (after N4), the two `∃ᶠ`
  conjuncts are lost.
* thm-site-fluctuations. The CLT and joint-limit items use the hypothesis only through the `S` upper bound
  of the previous node, so they survive under (U) and under (D*) at the `|x|²` site. The LIL item needs the
  padding wrapper under (D*) and (D) (N2). Under (U) its `∀ᶠ` half survives and its `∃ᶠ` half is lost.

Cheapest repair per scenario:
* The lower half is published for (D*) (the literature form): N3, N1 and the padding wrapper; roughly
  1400 to 1900 lines in total, of which the padding wrapper is the bulk, and only the site LIL needs it.
* Only strict (D): add truncation (about 400 lines) at the `|x|²` site; the `|x|²` bracket then also
  needs padding.
* Only (U): two nodes (sharp-radii-lil, sharp-width (b)) cannot be saved, and the other two lose their
  `∃ᶠ` halves. The only repair is to prove the lower half directly (an exponential lower tail for
  martingales, then conditional Borel-Cantelli, for which Mathlib has `ae_mem_limsup_atTop_iff`).

Housekeeping. Any weakening edits the frozen `CERW.External.StoutLIL` and its twin
`CERW.Support.Statements.StoutLIL` (Statements:38). The frozen theorem texts mention it only by name.
