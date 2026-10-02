# The route to the lower half of Stout's law, and its state

This is a working record, not a ruling. It extends `stout-lil-feasibility.md`, section 3, with the
design decisions taken while the pieces were written, and lists which pieces are proved. The
target is `CERW.External.StoutLIL`, the conclusion `∃ᶠ n, (1 − δ) √(2 P_n log log P_n) ≤ S_n`.
Nothing here is assumed: every item marked proved is a theorem with axioms
`propext, Classical.choice, Quot.sound`.

## The route

0. Upper half for `−S̃`. `CERW.Generic.Martingale.Lil.stout_upper` gives `S̃_n ≥ −(1+δ')√(2 P̃_n L)`
   eventually, for the padded martingale `S̃` below.
1. Gate. A cumulative predictable gate `G_j`, open before a start time `N`, that closes for good at
   the first time `i ≥ N` at which `K_i = B_{i+1} √(log log (P_{i+1} ∨ e^e)) / √P_{i+1}` exceeds a
   small level `ε` (`levelGate`). The level must be small, because the sharp lower tail needs
   `a b ≤ ε₀ v` with a tiny `ε₀`, so a fixed large level cannot work. The sets `C_{N,ε} =
   {K_i ≤ ε for all i ≥ N}` increase to a set of full measure as `N → ∞`. The gate is open before
   `N`, so that no padding enters before `N` and `P̃ = P` exactly on `C_{N,ε}`; padding before `N`
   would give `P̃_n = N + P_n − P_N` and no deterministic bound on the block increments.
2. Padding. `S̃` has the increment `G_j ΔS_{j+1} + (1 − G_j) ε_{j+1}` with `ε` independent fair
   signs, on `Ω × (ℕ → Bool)` with the filtration that joins `ℱ` with the coin filtration. The
   padded bracket `P̃_n = ∑_{j<n} (G_j c_j + 1 − G_j)` depends on `ω` only and is predictable and
   pathwise nondecreasing. It equals `P_n` while the gate has been open, and `P̃_n → ∞` almost
   surely.
3. Blocks. `τ_k` is the first passage of `P̃` over `x_k = θ^k`, a stopping time. The bracket
   between `τ_k` and `τ_{k+1}` lies in a window `[v(1−ρ), v]` once the one-step jump of `P̃` is small
   against `x_k`. Inside block `k` the increments of `S̃` are surely bounded by
   `b_k = max(1, M √(x_{k+1} / log log x_k))`.
4. Conditional sharp lower tail. For an event `F` before `τ_k` and inside `{τ_k ≥ N}`, so that no
   increment before `N` enters the block, the conditioned measure `μ[|F]` and
   the increments of `S̃` between `τ_k` and `τ_{k+1}` kept on `F` satisfy the hypotheses of the sharp
   lower tail with a stopping-time horizon, so `μ(F ∩ A_{k+1}) ≥ q_{k+1} μ(F)`, where
   `A_{k+1}` says that the block increment is at least `(1 − δ/2)√(2 x_{k+1} L_{k+1})`.
5. Lévy. The conditional probabilities of the `A_k` given the events before `τ_{k−1}` have an
   infinite sum, so `A_k` occurs infinitely often almost surely.
6. Combine with step 0 and let `θ → ∞`: `S̃_{τ_k} ≥ (1 − δ)√(2 P̃_{τ_k} L)` infinitely often.
7. Transfer. On `C_{N,ε}` the gate never closes, so `S̃ = S ∘ fst` there. Take the union over `N`,
   which has full measure because `K_n → 0` almost surely. Pass from almost everywhere on the
   product to almost everywhere on `Ω` along the first projection.

## State

| piece | file | state |
|---|---|---|
| exponential martingale and cumulant, public | `Generic/Martingale/ExpMart.lean` | proved |
| sharp lower tail, stopping-time horizon (limit form) | `Generic/Martingale/Tilt/` | proved |
| join with an independent factor, martingale lift | `LilLower/ProdCondExp.lean` | proved |
| optional stopping for a martingale bounded in `L²` | `LilLower/StoppedValueL2.lean` | proved |
| Lévy's lemma along stopping times | `LilLower/StoppedLevy.lean` | proved |
| first passage of a predictable process, window | `LilLower/BracketTimes.lean` | proved |
| adapted signs, coin space | `LilLower/SignSequence.lean`, `CoinSpace.lean` | proved |
| padded martingale, conditional second moment | `LilLower/Padding.lean` | proved |
| block increments under the conditioned measure | `LilLower/ConditionedBlock.lean` | proved |
| level gate, open before the start time | `LilLower/Gate.lean` | proved |
| bracket of the padded process | `LilLower/PaddedBracket.lean` | proved |
| block parameters, arithmetic, conditional bound, combination, transfer, final theorem | `Generic/Martingale/LilAssembly/` | in progress |

## Open points

- The arithmetic that combines the block increment with the step-0 bound: the choice of `θ`, `δ'`
  and the exponent `η` of the sharp lower tail against the sum of `q_k`.
- The measurability of the events `A_k` in the stopping σ-algebra of `τ_k`.
- That `P̃` grows by at most `max(b², 1)` per step, which fixes the window width.
- The final theorem `CERW.External.StoutLIL`, which would retire the last assumption of the
  development in the way ruling D6 retired the martingale central limit theorem.
