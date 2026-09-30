# Independent audit of the CERW Lean formalization — auditor 1

* Worktree: `/home/bourabbe/lean/CERW-audit1` at `6e1c58b320f6a7334b8d819867a39121a7d8d90e` (`git status --short` → only the pre-existing untracked `.lake` symlink; nothing edited).
* Paper pin: `sha256sum paper/cerw-flat.tex` → `53d8c0a7…943a`, equal to `ledger/manifest.yaml:21`. `python3 tools/flatten_paper.py --check` → `paper/cerw-flat.tex is current (1150 lines)`. Section offsets verified by `diff`: `sections/local-times.tex` = flat 341–543, `coarse-radius.tex` = 544–844, `fluctuations.tex` = 845–1146, all identical (manifest header offsets 340/543/844 are correct).
* Protocol followed: all verdicts below were formed from the sources, the paper and my own probes before `ledger/audits/*` was opened; the comparison is in §6.
* Probe artifacts (scratch, outside the repo): `axioms.lean`, `telescope.lean`, `sameStatement2.lean`, `nonvacuity2.lean`, `numeric2.py`, `verify.out` under `/tmp/claude-1001/-home-bourabbe-lean-CERW-audit1/52136f44-74a2-4384-9083-67f7166e324d/scratchpad/`.

## 1. Verdict table

| # | check | verdict | evidence (one line) |
|---|---|---|---|
| 1 | Source fidelity | **PASS** | All 8 `frozen_sha256` recomputed with the tool's convention (bytes strictly between markers, one leading newline dropped, `lean_source.py:86-89`) → 8/8 match. Every frozen-file docstring `latex` block is byte-identical to its cited paper range (script, 8/8 `True`). Clause-by-clause reading in §2/§7 finds no quantifier, constant-scope, a.s.-form, or junk-value deviation. |
| 2 | Statement integrity | **PASS** | One `BEGIN`/`END` pair per file (8/8); declaration scan shows exactly one declaration per file and each name equals the manifest `export`; `grep -nE "set_option\|attribute\|notation\|instance" CERW/Frozen/*.lean CERW/External/*.lean` → none. |
| 3 | Hypothesis smuggling | **PASS** | Meta probe `telescope.lean` walked every elaborated ∀/let/∃ binder (implicit and instance binders expanded). Every binder is SOURCE, STANDING, TYPING or the single EXTERNAL `hK : CERW.External.LatticePotentialKernel d`. EXCESS = 0 on all 7 anchors (table §2). |
| 4 | Seal and consumption | **PASS** | `#print` of each anchor: body is `Exists.casesOn (exists_kernelFacts hd hK) fun b h => Exists.casesOn h fun h hF => <provider> hd hF …` (six anchors) or `CERW.Support.Geometry.potential_geometry hd` (one). Meta probe: after `{d} (hd) (hK)` vs `{d} (hd) {b} {h} (hK')`, the remaining statements are structurally equal `Expr`s (`==` → `true`, 6/6); `potential_geometry` full type `==` → `true`. `exists_kernelFacts` (`KernelExternal.lean:17-24`) uses only `hK.1 rfl` and `hK.2 h3`. |
| 5 | Axioms and hygiene | **PASS** (build), **see §3-C1** (gates) | `#print axioms` on all 8 exports → exactly `[propext, Classical.choice, Quot.sound]`. Comment-masked token scan with the tool's own `token_hits` for `sorry admit axiom native_decide sorryAx maxHeartbeats` → 0 of 173 files. `flock … lake build --no-build` → `All targets up-to-date (8894 jobs)`; `flock … lake build` replay → 0 lines matching `warning\|error`. `verify.py --keep-going` → 14 gates OK, `sync_docs` VACUOUS (README/CORRESPONDENCE absent), exit 2. |
| 6 | Non-vacuity | **PASS** | `exists_cerw_realization` (clean axioms) instantiated into `ball_shape` (d=2) and `coarse_bounds` (d=3, p=1, n=2) in a compiled probe; kernel sign probe `firstStep 2 ε e₀ e₀ = 1/4 − ε/2`; External clauses cross-checked numerically (d=2 residual·|x|² ∈ [−0.063, −0.017] for |x|=4..16; d=3 `|G − c/|x||·|x|³ ≤ 0.14` for |x|=5..30) and by the constant identity `2/((d−2)ω_d) = dΓ(d/2)/((d−2)π^{d/2})` (≤ 6e-17, d=3..8). No frozen statement is reachable through a junk value (§7). |
| 7 | Record and gates | **CONCERN** | `ASSUMPTIONS.md`, `CERTIFICATE.md` agree with manifest and code (hashes, toolchain `v4.32.0`, Mathlib `81a5d257`, 8894 jobs, verbatim External). `check_clauses/constants/exponents/hazards/paper_anchors/paper_citations` all OK. `PROOF.md`, `CORRESPONDENCE.md`, `README.md` **do not exist** (`ls *.md` → only two files; `git log --all -- PROOF.md CORRESPONDENCE.md README.md` → empty). README/CORRESPONDENCE are the known pending author decision; `PROOF.md` is not covered by that note. |
| 8 | Independent re-derivation | **PASS** | `prop:coarse` and `lem:local` reconstructed from the paper alone (§5); the frozen statements are the paper's statements. Trust points listed. |

## 2. Per-anchor table

Binder bins from the elaborated telescope (`telescope.out`). "inner" = binders under `let`/`∃`/`→` in the statement body; all are SOURCE (paper hypotheses) or TYPING/STANDING.

| anchor | export | hash recomputed = manifest | binders (outer; inner) | EXCESS | `#print axioms` | fidelity |
|---|---|---|---|---|---|---|
| `ext-lattice-kernel` | `CERW.External.LatticePotentialKernel` | ✔ `0e20a9f8…85dda` | `(d : ℕ) : Prop` | 0 | classical only | PASS (true as stated, §4) |
| `thm-shape` | `CERW.Frozen.ball_shape` | ✔ `e3cff69c…8718d` | `{d}` T, `hd` S, `hK` EXT, `{ε}` T, `hε hεd` S, `{Ω}` T, `[MeasurableSpace Ω]` T, `μ` T, `[IsProbabilityMeasure μ]` STANDING, `X` T, `hX : IsCERW` S | 0 | classical only | PASS |
| `thm-fluctuations` | `CERW.Frozen.fluctuation_bounds` | ✔ `c76a39db…2aa2d` | `{d} hd hK`; inner `ε, 0<ε, ε<1/d, p, 0<p, Ω/inst/μ/inst/X, IsCERW, n, n₀≤n` | 0 | classical only | PASS |
| `eq-hausdorff` | `CERW.Frozen.hausdorff_bound` | ✔ `5c06b6e9…10887` | as above with `n₀ ≤ n` | 0 | classical only | PASS (form note §3-C2) |
| `lem-local` | `CERW.Frozen.local_time_potential` | ✔ `381f9ba4…b2959` | as above with `2 ≤ n` | 0 | classical only | PASS |
| `lem-geometry` | `CERW.Frozen.potential_geometry` | ✔ `3cd2d500…51121` | `{d} hd`; inner `ε, 0<ε, D, MeasurableSet D, IsBounded D, y, z, s, 0<s, b, 0<b` | 0 | classical only | PASS |
| `lem-radial` | `CERW.Frozen.radial_test` | ✔ `b07ab5ed…6bb09` | as `lem-local`; inner also `r, r₀≤r, r≤n` | 0 | classical only | PASS |
| `prop-coarse` | `CERW.Frozen.coarse_bounds` | ✔ `8e67c961…197d9f` | as `lem-local` | 0 | classical only | PASS |

Commands: hash recomputation — Python over `CERW/Frozen/*.lean`, `CERW/External/*.lean` (8 × `match`); axioms — `lake env lean axioms.lean` (11 lines, all `[propext, Classical.choice, Quot.sound]`, including `exists_kernelFacts`, `Guards.exists_cerw_realization`, `Law.exists_isCERW`).

## 3. Defects and concerns

No DEFECT was found. Concerns, in decreasing weight:

**C1 — Record incomplete; `verify.py` does not exit 0.** `PROOF.md`, `CORRESPONDENCE.md`, `README.md` are absent from the worktree and from all git history.
```
$ ls *.md
ASSUMPTIONS.md  CERTIFICATE.md
$ python3 tools/verify.py --keep-going        (tail)
=== sync_docs
      FAIL  README.md does not exist
      FAIL  CORRESPONDENCE.md does not exist
    sync_docs: META-CHECK FAILED — processed 0 items of 8 available. …
   sync_docs          VACUOUS
verify: VACUOUS — a gate inspected nothing. Treat as a failure.
exit=2
```
README/CORRESPONDENCE are the known pending arXiv-id decision, so their absence is not reported as a defect. `PROOF.md` is not covered by that note; `sync_docs.py:335` treats it as optional (`required=False`), so no gate fails on it, but the record described in the claim names it and it does not exist. Correction: either add `PROOF.md` or drop it from the stated record.

**C2 — `eq:hausdorff` is transcribed as a stand-alone probability bound, not "on the event in Theorem thm:fluctuations".** Paper `cerw-flat.tex:215-218`: "On the event in Theorem~\ref{thm:fluctuations}, the Euclidean Hausdorff distance satisfies …". Frozen `HausdorffBound.lean:44-59`: `∀ p>0, ∃ C n₀, … μ {ω | ¬(d_H … ≤ … ∧ (d=2 → …))} ≤ ofReal (C n^{-p})`. The Lean statement has the same probabilistic strength (the paper's event has probability ≥ 1 − Cn^{-p}), but the coupling "same event as `Good C`" is not stated, and `C` is a fresh constant. `ledger/readings.yaml` records this choice ("(R-7) The statement is a probability bound with its own constant"). Form only; not a weakening a reader would be misled by.

**C3 — Manifest citation over-inclusive, not a fidelity issue.** `manifest.yaml:27` cites Lawler–Limic "Thm 4.3.1, Cor 4.3.3, Thm 4.4.4" for the External. Cor 4.3.3 (gradient estimates) is *not* assumed: `eq:gradient` is derived in `KernelBridge.lean:81-87,149-156` from the two asymptotic clauses. The External assumes exactly Thm 4.3.1 (d ≥ 3 clause) and Thm 4.4.4 together with the partial-sum definition of the planar kernel (d = 2 clause). Harmless; could be tightened.

**C4 — Frozen planar remark is the two-sided reading.** `HausdorffBound.lean:55-58` asserts both the inner inclusion and an unvisited site within `aN + C n^{1/6}√L`. The paper (`:224-225`) says "inner-radius error … at most"; two-sided is the natural reading of "error" and is strictly stronger, and `n^{1/6}√L = NQ` at d = 2 matches `eq:inradius`. The approval packet (`ledger/approval/PHASE-B.md:23-37`) records this as a delegated ruling. Nothing to fix; noted because a strictly literal reader might expect only the inner inclusion.

## 4. The External: true as stated (my own check)

`CERW/External/LatticePotentialKernel.lean:42-54`.

* **d = 2.** `b x := lim_M Σ_{j<M}[P^j(0,0) − P^j(0,x)]` (`srwGreen 2 M 0 − srwGreen 2 M x`, `SRW.lean:105-106`, `walkOp` = neighbour average `/(2d)`, `Site.lean:47-48`). This is the standard potential kernel `a(x)` with `a(0)=0`; the limit exists for every `x` (for odd `x` only as a limit of partial sums, which is what `Tendsto` states). Asymptotic `a(x) = (2/π) log|x| + κ + O(|x|^{-2})`: for SRW Γ = ½I, `√det Γ = ½`, so LL's `1/(π√det Γ) = 2/π`. Numeric (`numeric2.py`, exact 1D-product computation, M = 6000): `a(1,0)=0.999947` (exact 1), `a(1,1)=1.273240` (4/π), `a(2,0)=1.453521` (4−8/π), `a(3,0)=1.721073` (17−48/π); `(a(r,0) − (2/π)log r − κ)·r²` for r = 4,5,6,8,10,12,16 = −0.063, −0.060, −0.057, −0.055, −0.052, −0.047, −0.017 (bounded, so `O(|x|^{-2})` holds with `C ≈ 0.07`, `R = 1`).
* **d ≥ 3.** `srwGreenInf d x = Σ' j, P^j(0,x)` (`SimpleTransfer.lean:25`), a genuine sum since `summable_srwHeat (3 ≤ d)` is a library theorem (used at `KernelBridge.lean:141`). Constant: `ω_d = π^{d/2}/Γ(d/2+1)` gives `2/((d−2)ω_d) = dΓ(d/2)/((d−2)π^{d/2})`, LL's `C_d` (difference ≤ 5.6e-17 for d = 3..8). Numeric via Poissonization `G(x) = ∫₀^∞ Π_i e^{−t/3} I_{x_i}(t/3) dt`: `G·|x|` = 0.4830, 0.4787, 0.4778, 0.4767, 0.4773, 0.4776 at |x| = 5, 10, 20, 6√3, 12√3, 30 (target `3/(2π) = 0.47746`); `|G − c/|x||·|x|³` = 0.139, 0.123, 0.120, 0.080, 0.080, 0.120 (bounded ⇒ `O(|x|^{-3})`).
* Nothing else is assumed: `(P−I)b = 1_{0}`, the level sets, both gradient estimates and log growth are proved in `KernelBridge.lean` from these two clauses (axioms of `exists_kernelFacts` clean).

## 5. Independent re-derivation (check 8)

**`prop:coarse`** from `cerw-flat.tex:547-561` with the definitions at `:120-132` and `:328-336`. What the paper asserts: for every integer `d ≥ 2`, every `ε ∈ (0, 1/d)`, every `p > 0`, there exist `c, C > 0` depending only on `(d, ε, p)` such that for every integer `n ≥ 2`, for CERW started at the origin, `P(cN^d ≤ R_n ≤ CN^d ∧ cN ≤ M_n ≤ CN ∧ cN ≤ H_n ≤ CN) ≥ 1 − Cn^{-p}`, with `N = n^{1/(d+1)}`, `R_n = |A_n| = |{X_0,…,X_{n−1}}|`, `M_n = max_x ℓ_n(x)`, `H_n = max_{0≤j≤n}|X_j|`. Frozen `CoarseBounds.lean:39-50`: `∀ ε, 0<ε → ε<1/d → ∀ p, 0<p → ∃ c C, 0<c ∧ 0<C ∧ ∀ {Ω} [..] μ [..] X, IsCERW μ ε X → ∀ n, 2 ≤ n → let N := n^{1/(d+1)}; μ{¬(six inequalities)} ≤ ofReal (C n^{-p})`. Quantifier order identical (constants after `d, ε, p`, before the realization and `n`); one `c`, one `C` shared with the probability, as in the paper; `N^d` is the natural power; failure event is the complement of the conjunction. **This is the paper's statement.**

Where a reader must trust the formalization (checked by me, each by reading the definition and its characterization lemma):
* `IsCERW` (`Law.lean:27-36`): measurability, `μ{X 0 ≠ 0} = 0`, and the cylinder factorization `μ{∀ j ≤ n+1, X j = x j} = μ{∀ j ≤ n, X j = x j} · ofReal(stepProb d ε x n (x(n+1) − x n))`. This determines the law of the path; `stepProb` (`Kernel.lean:45-46`) is `firstStep` exactly when `x n ≠ 0 ∧ x n ∉ {x 0,…,x(n−1)}` and `srwStep` otherwise, matching `:108-115`. `firstStep` (`Kernel.lean:30-33`) is `q_x(±e_i) = 1/(2d) ∓ (ε/2)·x_i/|x|`; probe: `firstStep 2 ε e₀ e₀ = 1/4 − ε/2` (inward).
* `departureRange X n = image X (range n)` (`Occupation.lean:26-27`; `mem_departureRange_iff : x ∈ A_n ↔ 0 < ℓ_n(x)` at `:30-32`), so `card = R_n`. `maxLocalTime = sup over A_n of ℓ_n` (`:44-45`); equals `max_x` because `ℓ_n = 0` off `A_n` (`:47-54`). `maxRadius = sup'_{j ≤ n} euclidNorm (X j)` (`:57-59`). `euclidNorm x = √Σ x_i²` (`LatticeProb/Walk/Ball.lean:27`).
* `ENNReal.ofReal (C n^{-p})`: when `C n^{-p} ≥ 1` the bound is trivial, exactly as in the paper.

**`lem:local`** from `:397-414` with `:380-395`, `:333-336`: for every `p>0` there is `C = C(d,ε,p)` such that for every `n ≥ 2`, with probability ≥ `1 − Cn^{-p}`: `M_n ≤ C_d ε R_n^{1/d} + Cλ_n`; `M_{s,t} ≤ C_d ε k_{s,t}^{1/d} + Cλ_n` for `0 ≤ s < t ≤ n`; `|ℓ̃_n(y) − U_{D_n}(y)| ≤ C e_n(M_n)` for `|y| ≤ 2n`; `λ_n = L²` (d=2) / `L` (d≥3), `e_n(m) = √m L + L` / `√(mL) + L`. Frozen `LocalTimePotential.lean:42-62` matches, with `C_d` bound *before* `ε` (the paper's `C_d` depends only on `d`; `:406` writes `C_d` without `(d,ε,p)`), then `∀ε ∀p ∃C`. Trust points: `cellLocalTime X n y = ℓ_n(cellCenter y)` with `cellCenter v = ⌊v_i + ½⌋` and half-open cells (`Space.lean:53-58`, `mem_cell_iff :80-82`); `potential` is the Bochner integral `2ε/ω_d ∫_D ⟨u_v, v−y⟩/‖v−y‖^d` (`Potential.lean:31-33`; integrable for bounded `D`, the only case used); `freshCount = #{s ≤ j < t : X_j ∉ A_j}` (`Occupation.lean:67-68`); `intervalMax` (`:75-76`).

## 6. Comparison with the prior audits (opened only after §1–5 were formed)

* `ledger/audits/postseal-audit.md`: agrees on all five points. Its open item "which Lawler–Limic theorem number covers which clause" is settled here (§4, C3): Thm 4.3.1 ↔ `d ≥ 3` clause; Thm 4.4.4 plus the partial-sum definition ↔ `d = 2` clause; Cor 4.3.3 is not assumed.
* `ledger/audits/prefreeze-refute-first-audit.md`: agrees (PASS, EXCESS 0 everywhere). Its CONCERN (one-sided planar remark) is resolved in the frozen text by variant B (`HausdorffBound.lean:55-58`), which I confirm is what is hashed (`5c06b6e9…`).
* Readings A/B/C: "no discrepancy" — consistent with mine. No disagreement to report. The prior audits did not flag C1 (`PROOF.md`) or the `verify.py` exit code 2; C2 is recorded in `readings.yaml` but not surfaced as a concern.

## 7. Junk-value and quantifier checks I performed (all clean)

* Division by `(d:ℝ)`, `(d+1)`, `2d−1`: `d ≥ 2` throughout. `N n`, `N⁻¹`: only at `n ≥ n₀ ≥ 1`, `n ≥ 2`, or under `∀ᶠ n`. `Real.log (n+2) ≥ log 2 > 0`. All `rpow` bases ≥ 0; `Real.sqrt` arguments ≥ 0 (`tail ≥ 0`, `M_n ≥ 0`, `L ≥ 0`).
* `Finset.sup` on possibly empty sets (`maxLocalTime`, `intervalMax` with `s<t`, `shellMax`): the empty value 0 is the true max; it appears on the harder side of each inequality.
* Bochner integrals (`potential`, `tail`, sphere integral): domains are `cellSet` (finite union of cells), `Metric.ball 0 b`, or `D` with `MeasurableSet D ∧ IsBounded D`; all integrable. `(d·ω_d)⁻¹ ∫ … ∂volume.toSphere` matches `σ_d^{-1}∫_{S^{d-1}}` because `toSphere_apply_univ : μ.toSphere univ = dim E * μ (ball 0 1)` (`Mathlib/…/HaarToSphere.lean:87`).
* `hausdorffEDist` in `ℝ≥0∞`: both sets nonempty (`X 0 ∈ V_n`, `a > 0`); an empty image would give `⊤` and *fail* the event, not satisfy it.
* Almost-sure form of `thm:shape`: single `∀ᵐ ω ∂μ` before `∀ η` and `∀ x` (`BallShape.lean:58-71`), the strong reading of `:142`. `sup_x |…| → 0` rendered as `∀ η>0, ∀ᶠ n, ∀ x, |…| ≤ η` (equivalent).
* `thm:fluctuations`: `C, n₀` after `(d, ε, p)` and before `(Ω, μ, X, n)`; same `C` in `Good` and in `C n^{-p}` (`:195-197`); `Q` cases, radii `a − CQ`, `a + CQ^{1/d}L`, `eq:volume` as an `ℝ≥0∞` sum, `eq:profile-rate` with `CQ^{1/d}`, and the eventual-a.s. clause `∃ C, ∀ᵐ ω, ∀ᶠ n` all present (`FluctuationBounds.lean:52-78`).
* `lem:radial`: `r₀` depends only on `d` (bound before `ε`, `p`), `r₀ > 2b_d`, so `r − b_d > 0`; `b_d = ⌈√d/2⌉₊ + 6`; `M_sh(r)` over `||x| − r| ≤ 3` (`Occupation.lean:92-93`).
* No `sSup`, no `tsum` in any frozen block (the External's `srwGreenInf` is a `tsum`, justified by library summability for `d ≥ 3`); no `ncard`.

## 8. What I could not verify, and why

* The text of Lawler–Limic Thm 4.3.1 / Thm 4.4.4 (no copy in the worktree). I verified the constants analytically and numerically (§4) and that the External's shape is the standard one; I did not verify the theorem numbers against the book.
* Consistency of `README.md`, `CORRESPONDENCE.md`, `PROOF.md` with the manifest — the files do not exist (C1).
* The ~170 Support/Generic proofs individually. I rely on Lean's kernel (`#print axioms` clean, zero build warnings) and on the structural identity of provider and frozen statements; that is the intended trust boundary.
* The Lake oleans were built in the main checkout at the same commit (`6e1c58b`, clean tree) and reached through the `.lake` symlink; `lake build --no-build` and the replayed `lake build` (8894 jobs, 0 warnings) confirm they are current for these sources, but I did not rebuild from scratch (instructed not to).

## 9. Overall verdict

**The claim survives.** Every anchor transcribes its paper statement at the right quantifier order and constant scope; every anchor is fully proved with axiom closure exactly `{propext, Classical.choice, Quot.sound}`; the only assumption is the single External, which is true as stated (both clauses cross-checked); the bridge unpacks only its two clauses; frozen and provider statements are structurally identical; hashes, paper pin and section offsets all recompute.

The one qualification is to the *record*, not to the mathematics: `PROOF.md` (and the known-pending `README.md`/`CORRESPONDENCE.md`) do not exist, so `python3 tools/verify.py --keep-going` exits 2 (`sync_docs VACUOUS`), and the claim's sentence "the record (manifest, ASSUMPTIONS.md, CERTIFICATE.md, PROOF.md, CORRESPONDENCE.md, ledger/) is consistent" cannot be true of files that are absent. Most damaging artifact: the `verify.out` tail quoted in §3-C1. If `PROOF.md` is added (or removed from the stated record) and the arXiv-id decision lands, no other finding stands in the way.
