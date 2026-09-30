# Post-seal audit

This audit was done by a fresh instance that wrote none of the code. It read the sources only and
changed nothing. Its question was whether the sealed results could be empty or misleading.
**Verdict: PASS on all five points.** It raised one process concern, handled below.

1. **The External is true as stated: PASS.**
   * d = 2: the limit of `srwGreen 2 M 0 − srwGreen 2 M x` is the potential kernel `a(x) ≥ 0`.
     It satisfies `|a(x) − (2/π) log|x| − κ| ≤ C|x|^{-2}`.
     * The constant `2/π` was checked against the exact value `a(3,0) = 17 − 48/π`.
     * The partial sums reproduce `a(1,0) ≈ 1` and `a(3,0) ≈ 1.716`.
     * The limit exists by dominated convergence of the Fourier representation.
   * d ≥ 3: the constant `2/((d−2)ω_d)` equals Lawler–Limic's `dΓ(d/2)/((d−2)π^{d/2})`. This
     was checked numerically:
     * for d = 3, `G(x)|x| ≈ 0.4775 = 3/(2π)` at `|x| = 10, 20`;
     * for d = 4, `G(10,0,0,0) ≈ 0.00205` against `(2/π²)|x|^{-2} ≈ 0.00203`.
   * The definitions used by the External:
     * `srwGreen d m x` is `Σ_{j<m} P^j(0,x)`.
     * `srwGreenInf d x` is the full sum, and its summability for `d ≥ 3` is a theorem of the
       lattice-probability library, so it is not a junk value.
     * `euclidNorm` is the Euclidean norm.
     * `(volume (ball 0 1)).toReal` is `ω_d`.
   * One point was left unsettled: which Lawler–Limic theorem number covers which clause. The
     mathematical content is correct either way.
2. **The bridge: PASS.** `exists_kernelFacts` only unpacks the External's two clauses. Every field
   of `KernelFacts` is proved in `KernelBridge.lean`: the Poisson equation, the level sets, the
   gradient asymptotics, the one-step gradient bound and the logarithmic growth. For d ≥ 3 the
   positivity of `G` is derived from summability, not assumed.
3. **Non-vacuity of the other hypotheses: PASS.** `IsCERW` has a model: `exists_isCERW` builds it
   from the Ionescu–Tulcea trajectory measure, and `Guards.exists_cerw_realization` gives one at
   `ε = 1/(2d)`. The remaining hypotheses (`2 ≤ d`, `0 < ε < 1/d`, a probability measure) are
   jointly satisfiable.
4. **Each seal: PASS.**
   * Six frozen proofs are exactly the bridge plus one Support theorem. `potential_geometry` is
     direct, with no External.
   * The frozen and External files contain no `set_option`, `attribute`, `notation` or
     `instance`, and there is no `sorry` or `axiom` under `CERW/`.
   * All eight block hashes and the paper pin were recomputed and match the manifest.
   * The seven theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
5. **Junk values: PASS.** No empty-range, `n = 0` or division edge case makes a frozen statement
   trivially true. The quantifiers keep every edge case out of reach (`n ≥ 2`, `0 < n₀`,
   `∀ᶠ n`, `s < t`, `r ≥ r₀ > 2 b_d`), and the integrands of the potential and the tail are
   proved integrable.

**Concern, and how it is handled.** While the audit ran, the heartbeat-margin work
(`ledger/HARDENING.md`) was editing Support files. The axiom closure it saw is therefore a
snapshot. `check_axioms` is re-run after every hardening landing and once more when that work
ends.
