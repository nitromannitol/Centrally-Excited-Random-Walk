# Proved-gate audit: third independent refute-first audit of the frozen surface

**Commit audited:** 6d83920, a fresh `git archive` checkout. The 30 nodes are those of `ledger/manifest.yaml` whose `source` starts with `limit-shapes.tex:`. The two cited Externals were audited as well.

**Auditors:** three independent auditors (groups A, B, C), coordinated from a separate working copy. None of them wrote any proof in this repository. Each formed its verdicts before reading the earlier audits.

## Summary

| | count |
|---|---|
| PASS (incl. PASS with note) | 29 nodes, plus External MartingaleCLT |
| CONCERN | 1 node (thm-sharp-width), plus External StoutLIL (low) |
| DEFECT | **0** |

- **thm-sharp-width — CONCERN.** `hLIL : StoutLIL` is a hypothesis of the whole (a)∧(b). Only (b) uses the LIL, so (a) is formally conditional where the paper's (a) is not. Splitting (a) from (b) would make (a) unconditional. Nothing changes mathematically, since StoutLIL is a true cited result. Documented in PROOF.md §4 item 15.
- **External StoutLIL — CONCERN (low).** The Lean form allows a random predictable bound. This is believed true and matches the restatements cited in `external-sources.md`, but the primary text of Stout (1970) / Hall–Heyde Thm 4.8 was not retrieved. **The author should confirm the original wording.**
- **Notes (no action needed):**
  - lem-exp-deviation assumes per-ω where the paper means a.s. (PROOF.md item 19).
  - lem-separated-brackets uses the closure form (PROOF.md item 14).
  - thm-site-fluctuations (iii) relies on the covariance being PSD, which it is.
  - lem-geometry and lem-layer use Borel `MeasurableSet` for the paper's Lebesgue measurability.
  - The clause strings in `ledger/readings.yaml` are cut at about 1000 characters.

## Axiom closure (step 2)
- Probe: `import CERW` plus `#print axioms` for all 39 manifest exports, run with `lake env lean` against the director's built oleans. The tree was clean at 6d83920.
- Every export depends on exactly `[propext, Classical.choice, Quot.sound]`.
- In the frozen blocks, `CERW.External.MartingaleCLT` / `StoutLIL` occur only in:
  - thm-sharp-radii-lil: StoutLIL;
  - thm-sharp-width: StoutLIL;
  - thm-moment-fluctuations: MartingaleCLT, StoutLIL;
  - thm-site-fluctuations: MartingaleCLT, StoutLIL;
  - and their own ext-* nodes.
- Each auditor confirmed from the elaborated types that the Externals enter only as explicit hypotheses, never in a conclusion or a definition.
- Caveat: a later re-run of `import CERW` in the shared checkout failed mid-rebuild (`CERW/Support/Norm/ShapeRates.olean` missing), so the auditors also probed per-node modules. The audited sources match 6d83920 byte for byte.

## Disagreements with earlier audits
- Earlier DEFECTs for the `•`/`∆` precedence, in thm-fluctuations and prop-inner, applied to the drafts. The frozen text at 6d83920 is parenthesised and elaborates correctly, so neither DEFECT stands.
- thm-sharp-width is graded CONCERN here, PASS (note N2) earlier. The finding is the same; only the grade differs.
- lem-exp-deviation is graded PASS with a note here, CONCERN (low) earlier. The substance is the same.
- `postseal-revised-audit.md` predates the seals of thm-fluctuations, thm-sharp-radii, thm-sharp-radii-lil, thm-sharp-bulk and thm-norm-shape, so its proof-side checks do not cover them. This audit's statement-side verdicts agree with the earlier `prefreeze-reading-*.md` readings.

## Group A (10 nodes): thm-shape, thm-fluctuations, thm-sharp-radii, thm-sharp-radii-lil, thm-sharp-bulk, thm-sharp-width, thm-norm-shape, lem-ballpotential, lem-local, lem-freedman

All verdicts were fixed before reading `ledger/audits/*.md`.

**Method.** Each frozen block was read against `paper/limit-shapes.tex` and the `CERW/Model/` definitions it uses. Elaborated types were checked with `pp.numericTypes` through probes that restate the frozen text with `sorry` and import only `CERW.Model` and `CERW.External.StoutLIL`. (A full `import CERW` was mid-rebuild at the time.)

**Common findings.**
- All casts to ℝ are at leaves; there is no ℕ division or subtraction.
- The first-departure rule is `x n ≠ 0 ∧ x n ∉ image x (range n)`. The mean step is `-ε ξ(x)`, with SRW at the origin and at later departures; this matches eq:kernel (line 313).
- `IsCERW` and `IsDriftCERW` fix the law of every cylinder, so constants and `n₀` bound before `(Ω, μ, X)` are equivalent to the paper's.
- Realizations exist (`exists_isCERW`, `exists_norm_realization`), so no hypothesis bundle is vacuous.
- "With probability at least 1 − Cn^{-p}" is the outer-measure bound `μ {¬good} ≤ ofReal (C n^{-p})`, which is at least as strong as the paper's.

### thm-shape — PASS (paper 90–119; theorem 103–116; eq:radius 98)
- A single outer `∀ᵐ ω` covers (i), (ii) and (iii), with the `η` quantifiers inside, as in "almost surely, for every 0<η<1".
- (i) has both inclusions, strict, eventually in n.
- (ii) is `∀ η>0, ∀ᶠ n, ∀ x, |ℓ_n x − 2dε·max(r n − |x|) 0| ≤ η r n`. This is equivalent to `(1/r_n) max → 0`, since the max is over finitely many nonzero terms and `r n > 0` for `n ≥ 1`.
- (iii) is `∀ x, ∃ᶠ j, X j ω = x`.
- Junk: `r 0 = 0` is irrelevant under `∀ᶠ`; there is no log and no sInf.

### thm-fluctuations — PASS (paper 90–101, 117–152; eq:radii 123)
- Binder order: `ε ∈ (0,1/d), p, ∃ C > 0`, then `∀ Ω μ X`.
- One `C` serves both the n ≥ 2 probability bound and the a.s. clause `∀ᵐ ω, ∀ᶠ n`. `∀ᵐ` is outside `∀ᶠ`, as in the paper.
- Exponents match the paper:

  | | d = 2 | d ≥ 3 |
  |---|---|---|
  | radii | `C√(r log n)`, `C√r (log n)^{5/2}` | `C log n`, `C (log n)^{d+1}` (real exponent) |
  | volume | `C√(log n/r)` | `C log n/r` |
  | local times, over all x with `max (r−|x|) 0` | `C√r (log n)^{3/2}` | `C√(r log n)` |

- R_in is two-sided and R_out one-sided, as in the paper. `if d = 2 … else` is d ≥ 3 under `hd`.
- The volume clause elaborates as `symmDiff ((r n)⁻¹ • cellSet Y n) (ball 0 1)`, so only D_n is scaled. The earlier `•`/`∆` precedence defect is fixed.
- Junk: `log n > 0` for n ≥ 2. `innerRadius` is a genuine infimum, since D_n is bounded and its complement nonempty.

### thm-sharp-radii — PASS (paper 153–164, 189–197)
- `hd : d = 2`, then `∀ p>0, ∃ c>0, ∃ n₀, ∀ Ω μ X, ∀ n ≥ n₀`. So c depends on (ε, p), and `n₀` is the paper's "sufficiently large".
- Both displays are conjuncts, each with `MeasurableSet` (an extra conclusion) and `ofReal(n^{-p}) ≤ μ E`.
- Small-n junk cannot help, because `n₀` is chosen by the prover.

### thm-sharp-radii-lil — PASS (paper 165–170, 189–197)
- `hLIL : StoutLIL.{u}` is a plain hypothesis; it is not in the conclusion or in any definition (checked in the elaborated type).
- Conclusion: `∀ᵐ ω, ∀ δ>0, (∃ᶠ n, (1/√(10πε) − δ)·√(r n·log log n) ≤ r n − R_in) ∧ (∃ᶠ n, … ≤ R_out − r n)`. This is the junk-free form of `limsup ≥ L`; `≤` vs `<` and `δ ≥ L` are harmless.
- `log log n ≤ 0` (so √ of a negative is 0) occurs only for n ≤ 2, which is irrelevant under `∃ᶠ`. The constant matches `1/√(10πκ)`.

### thm-sharp-bulk — PASS (paper 171–175, 189–197)
- `2 ≤ d`, then `∃ c>0, ∃ n₀` after (d, ε) and before the space. The same c is the multiplier and the exponent of `n^{-c}`, as in the paper's single c.
- "The max over {|x| ≤ √r_n} is ≥ cφ_n" is written `∃ x, |x| ≤ √(r n) ∧ cφ_n ≤ |ℓ_n x − 2dε (r n − |x|)|`. The set is finite and contains 0, so it is nonempty. The failure event is bounded by `ofReal (n^{-c})`.
- φ_n is `√r log n` for d = 2 and `√(r log n)` for d ≥ 3. There is no positive part, as in the paper (`|x| ≤ √r_n < r_n`).

### thm-sharp-width — CONCERN (paper 176–187, 189–197)
- (a): `∀ p>0, ∃ c>0, ∃ n₀, …` with `E = {c√(r n log n) ≤ maxRadius − innerRadius}`, `MeasurableSet E` and `ofReal(n^{-p}) ≤ μ E`.
- (b): `∀ᵐ ω, ∀ δ>0, ∃ᶠ n, (√(π/(3ε)) − δ)·√(r n·log log n) ≤ maxRadius − innerRadius`.
- Constants, exponents and junk handling match the paper, and thm-sharp-radii-lil. `hLIL` enters only as a hypothesis.
- **The concern:** `hLIL : StoutLIL` is a hypothesis of the whole (a)∧(b). The paper's (iv)(a) does not use the LIL (line 1647 belongs to part (b)), so (a) is formally conditional where the paper's (a) is not.
- `StoutLIL` is a true cited theorem, so nothing changes mathematically; the point is documented in `PROOF.md` §4 item 15. Splitting (a) from (b) would make (a) unconditional.

### thm-norm-shape — PASS (paper 289–342; eq:kernel 313, eq:ellipticity 318, eq:radius-norm 322, theorem 329–342; notation 290–306)
- Hypotheses:
  - `2 ≤ d` and `IsNorm Ψ`;
  - `ξ x` is a subgradient at every `x ≠ 0`;
  - `ξ 0 = 0`, the paper's convention (the law never reads `ξ 0`);
  - `0 < ε`, and `∀ i, ε Ψ(e_i) < 1/d`, which is the paper's max-over-i condition;
  - `IsDriftCERW μ ε ξ X`.
- `r n` uses `normBallVolume Ψ`, which is finite and positive.
- The conclusion is thm-shape with `Ψ (toSpace x)` in place of `|x|`, under one `∀ᵐ`. ξ is fixed before the a.s. event, and no uniformity in ξ is claimed.

### lem-ballpotential — PASS (paper 343–366; eq:potential-norm 349, eq:ballpotential 362)
- `normPotential` is `2ε/ω_d · ∫_D ⟪gradient Ψ v, v−y⟫ / ‖v−y‖^d`, with d a natural-number power. Its value is 0 at v = y, and Mathlib's `gradient` is 0 only on a null set. This is the paper's U_D.
- The statement is for `D = {Ψ < ρ}`, with right side `2dε·max (ρ − Ψ y) 0`.
- ε is an arbitrary real; this is a documented strengthening, since both sides are linear in ε. `hd : 2 ≤ d` is standing.
- Bochner junk is excluded: the integrand is bounded by `|v−y|^{1−d}` times a constant on a bounded set.

### lem-local — PASS (paper 373–400; M_{s,t} and k_{s,t} at 379–382)
- Binder order: `Ψ, ε (with ellipticity), p, ∃ C>0`, then `∀ ξ`, then `∀ Ω μ X`, then `n ≥ 2`. So C depends on (d, ε, Ψ, p) and not on ξ, as the paper's notation says.
- One C serves (i)–(iii) and the bound on the complement of their conjunction.
- (i): `maxLocalTime ≤ C|A_n|^{1/d} + C(log n)²`.
- (ii): `∀ s<t≤n, intervalMax ≤ C·freshCount^{1/d} + C(log n)²`, where `freshCount` counts `s ≤ j < t` with `X j ∉ A_j`.
- (iii): `∀ y, ‖y‖ ≤ 2n → |cellLocalTime − normPotential (cellSet)| ≤ C log n + C·{√M log n for d = 2; √(M log n) for d ≥ 3}`.
- Junk: `log n > 0` for n ≥ 2, and `0^{1/d} = 0` is the true value at k = 0. `maxLocalTime` is a `Finset.sup` of counts, so it is a true maximum.

### lem-freedman — PASS (paper 427–441; lemma 436–441; proof 443–450)
- `∀ p>0, ∃ C>0`, then `∀ n ≥ 2`, then any `(Ω, μ, ℱ, Z)` with `Martingale Z ℱ μ` and `∀ᵐ ω, ∀ t, |Z(t+1) − Z t| ≤ 1`. The a.s. increment bound makes it slightly stronger than an "everywhere" bound would.
- Conclusion: `μ{¬ |Z n − Z 0| ≤ C(√(⟨Z⟩_n log n) + log n)} ≤ ofReal (C n^{-p})`.
- `predBracket` is `Σ_{t<n} E[(ΔZ)² | ℱ t]`. It is a genuine definition, since the increments are bounded, and the event does not depend on the representative.
- `log n > 0` for n ≥ 2, and the sqrt argument is nonnegative a.s.

### External usage in group A
- `StoutLIL` occurs only as `hLIL`, in thm-sharp-radii-lil and thm-sharp-width.
- `MartingaleCLT` occurs in none of these ten nodes.
- `StoutLIL`'s form lines up with Stout's `K_n` and `s_n²`: predictable `B (n+1)` that is `ℱ n`-measurable, and a bracket `⟨S⟩_n` that includes the n-th increment. Its truth is audited under group C.

### Disagreements with earlier audits (group A)
- `prefreeze-reading-introduction.md` reported a DEFECT: the thm-fluctuations volume clause misparsed as `(r n)⁻¹ • (cellSet ∆ ball)`. The frozen text at 6d83920 has the parentheses and elaborates correctly, so there is no standing disagreement.
- `prefreeze-reading-introduction.md` and `postseal-revised-audit.md` grade thm-sharp-width PASS (their note N2). This audit grades it CONCERN for the same fact; only the grading differs.
- `postseal-revised-audit.md` predates the sealing of thm-fluctuations, thm-sharp-radii, thm-sharp-radii-lil, thm-sharp-bulk and thm-norm-shape, so its proof-side checks do not cover those five. The statement-side readings in `prefreeze-reading-*.md` agree with this audit for all five.

## Group B (10 nodes): lem-cell, lem-geometry, prop-coarse, lem-radial, lem-crossing, prop-norm-shape, lem-layer, lem-cap, lem-contact, lem-outer-crossing

All ten PASS. There is no CONCERN and no DEFECT.

**Method.**
- Paper lines read: those in the manifest (454-459, 509-527, 546-553, 566-575, 661-666, 745-761, 779-784, 809-814, 891-896, 988-993), the cited definitions (122, 294-295, 327, 348-352, 503-507), and `CERW/Model/`.
- The SHA-256 of the marker bytes matches `frozen_sha256` for all ten.
- Statements were printed with `pp.numericTypes` and `pp.coercions`. Every cast to ℝ is at a leaf, `(t-s:ℝ)` is `↑t-↑s`, and exponents are real powers with the paper's fractions. There is no `⌊⌋`, `⌈⌉`, `toNNReal` or ℕ subtraction.
- `import CERW` failed in the shared checkout, because `CERW/Support/Norm/ShapeRates.olean` was missing mid-rebuild. The per-node `CERW.Frozen.*` modules were imported instead. The ten frozen statements and all of `CERW/Model/*.lean` there are byte-identical to the audited commit (diffed).
- Probes that mattered:
  - `ContDiff ℝ ∞` in `IsDistribLaplacian` is C^∞, not analytic.
  - `closure (A)ᶜ` in ContactPotential.lean is the closure of the complement (`rfl`).
  - `toSphere_apply_univ` shows `volume.toSphere` has total mass d·ω_d, which gives the surface-average normalisation of lem-geometry (iii).
  - `exists_isDistribLaplacian` and `exists_isDriftCERW` show the hypothesis packages are inhabited.

### lem-cell — PASS
- `∃ C>0` sits right after `hd`, before Ψ, ξ and the measure m (the paper's C(d)).
- m is any locally finite measure satisfying the distributional-Laplacian identity; such a measure is unique and exists.
- The integral over the half-open `cell x` is genuine (bounded, measurable, on a bounded set), so the Bochner junk value 0 cannot trivialise it.
- The ball is open, `Metric.ball (toSpace x) (6√d)`, and x = 0 is covered via ξ 0 = 0.

### lem-geometry — PASS
- C(d,Ψ) precedes ε and D. ε is any positive real, a true generalisation.
- The exponents 1/d, 1/(2d) and 1/2 match, and `R = (volume D).toReal` is finite.
- Part (iii): `(d ωd)⁻¹ ∫ U_D(s•θ) ∂volume.toSphere` equals the paper's `1/(dω_d s^{d-1}) ∫_{|v|=s} U_D dS`.
- `B` and `tail` use the strict `s < ‖v‖`. The normMin/normMax sandwich and the Euclidean clause are present.

### prop-coarse — PASS
- Order: Ψ, ε (ellipticity), p, then `∃ c C>0`, then ξ, Ω, μ, X, n≥2. The constants depend only on (d, ε, Ψ, p).
- The six inequalities are exactly the three two-sided bounds. R_out is the Euclidean `maxRadius`, as in eq:radii.

### lem-radial — PASS
- ρ₀ precedes ε, p and ξ, and C comes after p.
- F is `tail` of `cellSet`. The shell max is over the closed shell, and the middle max has no upper cut-off.
- Every factor under √ is nonnegative (ρ−4d > 4d > 0), so there is no √ junk.
- The failure event is `¬∀ρ`, which gives "simultaneously".

### lem-crossing — PASS
- The event of eq:vector becomes a hypothesis on the path, with the same C in the conclusion (author ruling).
- Z and I_j are as in the paper, and the sign condition holds exactly "at every first-departure time".
- It needs fewer hypotheses than the paper (`0 ≤ ε`, no ellipticity, no subgradient or path structure), so it is a true generalisation.

### prop-norm-shape — PASS
- One C, after p and before ξ, and the three bounds sit in one conjunction.
- All six exponents match the case split: d=2 gives 3/4·1/4, 5/6·7/6, 5/6·1/6; d≥3 gives 1/2, d/(d+1)·(d+2)/(d+1), d/(d+1)·1/(d+1).
- The inner-radius bound is two-sided and the outer-radius bound one-sided, as in the paper. The local-time bound is `∀ x` with `max (r−Ψ x) 0`.

### lem-layer — PASS
- The shell is closed, `b ≤ Ψ ≤ b+a`, and the conclusion is `∀ y, |U_D(y)| ≤ 2dεa`.
- `normPotential` matches eq:potential-norm, and its integrand is integrable on the bounded shell.
- ε is any positive real, a generalisation.

### lem-cap — PASS
- `η = normMin⁴/(8 normMax²)`, and each inequality is strict or non-strict exactly as in the paper.
- `q = gradient (moreauEnvelope Ψ τ) x` is the honest gradient, since F_τ is C¹.
- The Moreau envelope is a real `iInf` of a family bounded below by 0.

### lem-contact — PASS
- "On the event, for large n" becomes `∃C ∃n₀ ∀n≥n₀, μ{¬∀y₀ …} ≤ ofReal(C n^{-p})` (author ruling). n₀ is deterministic and uniform in ξ, and n<n₀ is absorbed into C.
- A contact point is `Ψ y₀ = normInnerRadius` with `y₀ ∈ closure(D_nᶜ)`, quantified over every such point. The set is nonempty, so the statement is not vacuous.
- `r·q` is √(r log n) for d=2 and log n for d≥3, far below the trivial `C r_n`.

### lem-outer-crossing — PASS
- The events eq:vector and eq:linear-mart become hypotheses with an explicit constant C₁ (author ruling).
- C depends on (d, ε, Ψ, α, C₁) only, and is chosen before ξ, n, q, the path, j₀, h and b.
- `a ∈ ΛZ∩[0,Λn]` is written `a = kΛ` with `k ≤ n`.
- `dynkinMart` is the path-level conditional-expectation form of M^{q,a}. The bracket sum is over `A_n ∩ {kΛ−Λ < q·z}`.
- `L_b` is 1 + sup over A_n filtered by `b ≤ q·z`. An empty set gives 0, which equals the maximum over ℤ^d.
- "Path of the walk" is `x 0 = 0` plus unit steps, which is all the proof uses.

### Notes (no action needed)
1. In lem-geometry and lem-layer, `MeasurableSet D` is Borel, while the paper's "measurable" is Lebesgue. A Lebesgue-measurable D differs from a Borel set by a null set, so nothing changes; the repository uses this reading throughout.
2. The shared checkout's build lagged the audited commit during this audit, so `#print axioms` re-runs there must import per-node modules or build elsewhere.

### Disagreements with earlier audits (group B)
There is no disagreement on any verdict with `prefreeze-reading-norm-setup.md`, `prefreeze-reading-norm-shape.md` or `postseal-revised-audit.md`. The Borel-versus-Lebesgue note was recorded earlier only for lem-layer; this audit applies it to lem-geometry as well.

## Group C (10 nodes and both Externals): prop-inner, prop-stronger-outer, lem-near-far, thm-moment-fluctuations, lem-fixed-site-centering, thm-site-fluctuations, lem-exp-deviation, prop-bulk-profile, lem-separated-brackets, prop-log-lower; `CERW.External.MartingaleCLT`, `CERW.External.StoutLIL`

All verdicts were formed before reading `ledger/audits/*.md`. Probe files are `auditC/p1.lean` through `p4.lean`.

| node | verdict |
|---|---|
| prop-inner | PASS |
| prop-stronger-outer | PASS |
| lem-near-far | PASS |
| thm-moment-fluctuations | PASS |
| lem-fixed-site-centering | PASS |
| thm-site-fluctuations | PASS (see note on (iii)) |
| lem-exp-deviation | PASS with a low note |
| prop-bulk-profile | PASS |
| lem-separated-brackets | PASS under the documented closure reading |
| prop-log-lower | PASS |
| External MartingaleCLT | PASS |
| External StoutLIL | CONCERN (low) |

### Notes and concerns
- **lem-exp-deviation.** `S i 0 = 0` and the increment bound `|ΔS| ≤ b` are assumed for every ω, where the paper means almost surely. Formally this assumes more than the paper, but it is equivalent after a null-set modification and is documented (PROOF.md item 19).
- **lem-separated-brackets.** The paper's "on Ω_n" is closed as "failure probability ≤ C n^{-10}". This follows from the paper's form, and downstream uses need only an event of that probability. It is a documented author ruling (PROOF.md item 14).
- **thm-site-fluctuations (iii).** Mathlib's `multivariateGaussian` silently degenerates to a Dirac mass for a non-PSD matrix. The covariance here is PSD:
  - for d = 2 it has rank one;
  - for d ≥ 3, 2G − 1_{x=0} has Fourier transform (1+φ)/(1−φ) ≥ 0.

  So no junk value arises, but the statement relies on this fact.
- **StoutLIL (CONCERN, low).** The primary text of Stout (1970) / Hall–Heyde Thm 4.8 could not be retrieved.
  - The Lean form allows a random predictable bound `B`. A secondary restatement (Zeng 2015) writes a "positive sequence αₙ → 0" without saying whether it is deterministic.
  - The random predictable form is believed true: predictable truncation `X'ₙ = Xₙ·1{αₙ ≤ ε}` is again a martingale difference, and the paper itself uses a random bound at lines 1406–1412.
  - `external-sources.md` cites restatements in the predictable form.
  - **The author should confirm against the original wording.**
- **Ledger hygiene.** The clause strings in `ledger/readings.yaml` are cut at about 1000 characters; e.g. the lem-separated-brackets entry ends mid-sentence. The full text is in `ledger/nl/*.tex`.

### What was checked
- Every frozen type was printed from the built oleans, and the `Model/`, `Frozen/` and `External/` sources were matched to the checkout. Casts sit at leaves.
- The `∑ … - n/(2ε)` and `quadraticMart` parses were confirmed by `rfl`, and the `∆`/`•` parenthesisation in prop-inner is correct.
- `r n ^ (d-1)` is a natural-number power with no truncation for d ≥ 2.
- `G = srwGreenInf` includes the j = 0 term, so G(0) ≥ 1 and `toNNReal` never truncates.
- v₁ and v₂ were recomputed from the paper's bracket and match.
- `exists_isCERW` has clean axioms, so the statements are non-vacuous.
- `MartingaleCLT` carries all three Hall–Heyde conditions: square integrability, conditional Lindeberg, and bracket convergence in measure. Nesting is automatic and v = 0 is allowed.
- In thm-moment-fluctuations and thm-site-fluctuations both Externals enter only as the explicit hypotheses `hCLT` and `hLIL`, at the same universe `u` as `Ω`.

### Disagreements with earlier audits (group C)
- The earlier limit-laws audit gave prop-inner a DEFECT for the `•`/`∆` precedence of the draft. The frozen text is now parenthesised and elaborates correctly, so that DEFECT no longer applies.
- The earlier audit graded lem-exp-deviation CONCERN (low). Here it is PASS with a note; the substance is the same.
- This audit agrees with every other earlier verdict, including IMPLIED-WITH-REMARK for both Externals.
