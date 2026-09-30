# Post-seal audit of the revised-paper nodes

Auditor: independent, read-only on the repository (this file is the only write). Date of run: 2026-09-30, about 19:10 to 19:40 local.
Scope: every node of `ledger/manifest.yaml` with `state: SEALED` whose `source:` starts with `limit-shapes.tex:` (18 nodes; the brief said "about 21", the manifest at
the time of the run has exactly 18 SEALED, 12 DRAFT_SORRY, 7 PROVED first-version nodes and 2 FROZEN externals), plus the two Externals `ext-martingale-clt` and `ext-stout-lil`.
Pinned paper `paper/limit-shapes.tex` has the sha256 recorded in the manifest (`8a17876c...`), checked.

## Overall verdict

**PASS (no DEFECT).** All 18 sealed nodes satisfy checks 1 to 4. Checks 1, 2 and 3 are mechanical (Lean metaprograms and scripts, listed below), not by reading alone.
There are four NOTES, none of which changes a verdict (section "Notes"): N1 (subgradient-selection existence for general norms is not guarded in the repository; a scratch proof
closes it), N2 (thm-sharp-width rests on the explicit `External.StoutLIL` hypothesis, used only at the constant bound `B = 2`), N3 (Frozen and External sources are newer than their oleans, rewritten
with identical content by `seal.sh`; the current sources were recompiled and agree), N4 (another worker started adding `CERW/Support/Lower/SeparatedBrackets.lean` at 19:25, a DRAFT_SORRY node outside
every sealed closure; not audited here).

## Method and evidence (the probe files were kept outside the repository; `<scratchpad>` below names that working directory)

| Check | How | Result |
|---|---|---|
| Manifest hashes | SHA-256 of the bytes strictly between `-- FROZEN-STATEMENT-BEGIN\n` and `-- FROZEN-STATEMENT-END` for each of the 20 nodes | all 20 equal `frozen_sha256`; one marker pair per file; no `sorry` in any sealed or external file |
| Proof shape | Regex on the text after `-- FROZEN-STATEMENT-END`; compare with `scratch/proofs.py` | all 18 are exactly `:= by [revert <own binders>] exact <registered term>`; the term equals the `proofs.py` entry verbatim |
| Statement = Prop | Lean metaprogram (`ps/Stmt.lean`): `isDefEq (type of CERW.Frozen.X) (value of CERW.Support.Statements.X)` with shared universe levels; plus a text comparison of the two bodies | 18/18 sealed, 12/12 draft nodes and both Externals are definitionally equal (kernel defeq); textually the bodies are identical and differ only in the binder header (`(hd : P)` vs `∀ … (_ : P),`). Structural `Expr` equality (after erasing binder names and binder infos) fails; in every case printed, the first difference is a proof term (a Prop-valued instance such as `Module.Finite` or `Nat.AtLeastTwo` in one elaboration, an auxiliary `_proof_n` lemma in the other) or, for `sharp_width`, the constant `External.StoutLIL` against `Statements.StoutLIL`. Defeq is the operative check, and the kernel performs the same conversion when it checks each frozen proof |
| Dependency chain | Lean metaprogram (`ps/Chain.lean`): transitive closure of constants in the value and type of each frozen theorem; every `Statements.*` constant met; every `CERW.External.*` constant met | see section 1; no sealed frozen type mentions a `Statements.*` Prop; `External.StoutLIL` appears only in the type of `thm-sharp-width`; `MartingaleCLT` is in no sealed closure |
| Axioms | `<scratchpad>/Ax.lean` (output `Ax.out`): `import CERW`, `#print axioms` for every revised and first-version frozen theorem and the guards | 18/18 sealed: `[propext, Classical.choice, Quot.sound]`. 12/12 DRAFT_SORRY: `[propext, sorryAx, Classical.choice, Quot.sound]` (fluctuation_rates, sharp_radii, sharp_radii_lil, sharp_bulk, norm_shape, norm_shape_rates, outer_radius, moment_fluctuations, fixed_site_centering, site_fluctuations, bulk_profile, separated_brackets). 7/7 first-version: clean. Guards clean |
| Whole-environment scan | `ps/Scan.lean`: all 4455 `CERW.*` and `_private.CERW*` constants | `sorryAx` occurs directly in exactly the 12 DRAFT_SORRY theorems; no `axiom` declared in `CERW`; no `native_decide`, `opaque`, `unsafe`, `implemented_by`, `macro`, `instance`, `notation` anywhere under `CERW/` (grep) |
| Fresh recompile | Copied the 18 current `CERW/Frozen/*.lean` sources to the scratchpad, appended `#print axioms`, ran `lake env lean` | 18/18 compile, all `[propext, Classical.choice, Quot.sound]` |
| Paper text | For each sealed node, every non-blank line of `limit-shapes.tex` lines `A-B` (the manifest range) occurs in the Frozen docstring | 18/18, 0 missing lines |

## 1. Hypothesis chain (check 1)

`_of` theorems (those taking `Statements.*` Props) met in the closures, and what discharges each hypothesis:

| `_of` / consumer | Props consumed | Discharged by (all proved, no Statement hypotheses of their own) |
|---|---|---|
| `Lower.sharp_width_of` | `limit_shape`, `exp_deviation` | `@Main.limit_shape`, `@Lower.exp_deviation` |
| `Norm.norm_local_time_potential_of` | `cell_gradient` | `Norm.cell_gradient_holds` |
| `Norm.norm_coarse_bounds_of` | `norm_local_time_potential`, `norm_radial_test`, `drift_crossing` | `norm_local_time_potential_of cell_gradient_holds`, `Norm.norm_radial_test_holds`, `@Norm.drift_crossing` |
| `Norm.contact_potential_of` (and internal `ContactConv.convBound`) | `norm_local_time_potential`, `norm_coarse_bounds`, `norm_potential_geometry`, `norm_ball_potential` | the two terms above, `@Norm.norm_potential_geometry`, `@Norm.norm_ball_potential` |
| `Inner.inner_radius_of` | `contact_potential`, `norm_ball_potential`, `norm_potential_geometry` | `contact_potential_of …`, `@Norm.norm_ball_potential`, `@Norm.norm_potential_geometry` |

Base theorems (`Main.limit_shape`, `Norm.freedman_bound`, `Norm.moreau_cap`, `Norm.norm_potential_geometry`, `Norm.drift_crossing`, `Outer.near_far_holds`, `Norm.norm_ball_potential`,
`Norm.layer_potential`, `Norm.norm_radial_test_holds`, `Lower.exp_deviation`, `Norm.outer_crossing_holds`, `Norm.cell_gradient_holds`, `Lower.log_lower_bounds_holds`): the only
`Statements.*` constant in each one's closure is its own conclusion (closure analysis). `limit_shape` and `sharp_width` additionally use the first-version PROVED `CERW.Frozen.ball_shape`
(clean axioms, hypothesis-free statement about `IsCERW`). No sealed closure contains a DRAFT_SORRY node. Since the kernel accepts each term with no `sorryAx`, no Prop is assumed anywhere.

## 2. Statements.lean versus the frozen blocks (check 2)

Defeq and textual identity for all 18 nodes (table above). The Props used by the chain are exactly these 18 plus nothing else: `limit_shape, sharp_width, norm_ball_potential,
norm_local_time_potential, freedman_bound, cell_gradient, norm_potential_geometry, norm_coarse_bounds, norm_radial_test, drift_crossing, layer_potential, moreau_cap, contact_potential,
outer_crossing, inner_radius, near_far, exp_deviation, log_lower_bounds`. The Statements versions of `MartingaleCLT` and `StoutLIL` have the same text as `CERW.External.*`
(identical text, defeq); `sharp_width` in `Statements` carries `StoutLIL`, the frozen one `External.StoutLIL`, defeq. No proof of a Prop can be weaker than the frozen statement: they are the same type.

## 3. Axioms (check 3)

As in the table: sealed nodes clean; only the 12 DRAFT_SORRY nodes show `sorryAx`.

## 4. Vacuity (check 4)

Model definitions read: `IsCERW`/`IsDriftCERW` (cylinder factorisation of `stepProb`/`driftStepProb`, with `X 0 = 0` a.s. and `Measurable (X n)`), `IsNorm`, `IsSubgradient`,
`IsDistribLaplacian`, `normPotential`/`potential`/`positivePotential` (Bochner integrals), `moreauEnvelope`, `innerRadius`/`normInnerRadius`/`maxRadius`, `localTime`/`departureRange`/`cellSet`/`cellLocalTime`,
`predBracket`, `dynkinMart`, `tail`, `normMin`/`normMax`/`normBallVolume`. No instance, notation or macro is declared in `CERW`, so the meaning of the frozen text cannot be altered by the imports.
Junk values (Bochner integral of a non-integrable function, `sSup`/`sInf`, `gradient` off a differentiable point): each one is either excluded by a boundedness hypothesis carried in the statement
(`lem-geometry`: measurable and bounded `D`; `lem-layer`: `D` inside a bounded layer; the cell sets are finite unions of cells) or shown non-junk by a proved theorem
(`lem-ballpotential` gives a nonzero closed form for `normPotential`, so the integral is not collapsing to `0`; `Norm/MoreauCap.lean` proves `HasGradientAt`/`DifferentiableAt` of the Moreau envelope, so
`gradient (moreauEnvelope Ψ τ)` is the honest gradient; `lem-geometry (iii)` forces integrability of the spherical average whenever `F(s) > 0`).

Guards in the repository and what they cover:

* `CERW.Support.Law.exists_isCERW` (`d ≥ 1`, `0 ≤ ε < 1/d`) and `CERW.Support.Guards.exists_cerw_realization` (`d ≥ 2`): a probability space and process with `IsCERW`. Covers `thm-shape`, `thm-sharp-width`, `prop-inner`, `prop-log-lower`.
* `CERW.Support.Main.exists_norm_realization`: for `d ≥ 1`, every norm `Ψ`, every `ξ` with `IsSubgradient Ψ (toSpace x) (ξ x)` for `x ≠ 0` and `ξ 0 = 0`, every `ε > 0` with `ε Ψ(e_i) < 1/d`, a realization with `IsDriftCERW`.
  The hypothesis bundle is literally the bundle of the frozen statements of `lem-local`, `prop-coarse`, `lem-radial`, `lem-contact`. Covers them.
* `CERW.Support.Main.euclidean_norm_hypotheses`: the Euclidean norm with `ξ = x/|x|`, `ξ 0 = 0` and `ε < 1/d` meets the whole bundle, so the bundle is inhabited (and `CERW.Support.Drift.isCERW_iff_isDriftCERW` ties `IsCERW` to `IsDriftCERW` for this `ξ`).
* `CERW.Support.Norm.exists_isDistribLaplacian`: every norm has a locally finite measure with `IsDistribLaplacian`. Covers `lem-cell`.

Gap found and closed in scratch (NOTE N1): the repository has no theorem that a subgradient selection `ξ` exists for a general (non-Euclidean) norm, so inhabitedness of the bundle is guarded only for `‖·‖`.
`ps/Subgrad.lean` proves (Hahn-Banach, `exists_extension_of_le_sublinear`) `exists_subgradient`, `exists_subgradient_selection`, and then
`norm_hyps_inhabited` (every norm, `d ≥ 1`, ellipticity: a selection with `ξ 0 = 0` and a realization of `IsDriftCERW`), `cell_hyps_inhabited` and `euclid_inhabited`; all three `#print axioms` clean.
This is a generality point only: the statements are non-vacuous already at the Euclidean norm.

Nodes with no probabilistic or norm hypothesis bundle, checked by hand (no formal witness in the repository, none needed for soundness):
`lem-freedman` (martingale `Z ≡ 0`, or a simple random walk); `lem-exp-deviation` (for any `c₀ ≤ C₀`, a scaled simple random walk with `n ≈ c₀/b²`, `m = 1`, `E = Ω`, `α = 0`, then `β = max(C, …)`, `βb ≤ c`
for `b` small enough; the constants `c, C` depend only on `c₀, C₀` so `b → 0` is allowed); `lem-near-far` (`D = ∅`, and non-trivially `D` the full shell with `λ = C_d w`);
`lem-cap` (`x = y`, `‖y‖ > τΛ`, `ξ = y/|y|` for the Euclidean norm); `lem-crossing` and `lem-outer-crossing` (deterministic; for `lem-outer-crossing`: `d = 2`, Euclidean norm, `q = e₁`, the straight path `x_j = j e₁`,
`j₀ = n`, small `h`, `α ≤ 1`, `C₁` large, all hypotheses hold and the conclusion is non-trivial); `lem-layer`, `lem-ballpotential`, `lem-geometry` (no hypothesis beyond norm, `ε`, bounded measurable `D`).

Quantifier order was read against the paper for every node (constants before the realization, `n₀` before the realization, `C` independent of `ξ`, `ρ₀` independent of `ε`): no node has a constant chosen after
the object it should not depend on, and no node is weaker than the paper on this axis. `lem-crossing` is stated deterministically with the same `C` in hypothesis and conclusion, which is true
(`u·(x_t − x_s) = u·(Z_t − Z_s) − ε Σ I_j u·ξ(x_j) ≤ |Z_t − Z_s|` when `ε ≥ 0` and `u·ξ ≥ 0` at first departures).

## 5. Deep spot-check of two proofs (check 5)

**`CERW/Support/Norm/ContactPotential.lean` (5976 lines).** The only place `Statements.*` Props are consumed by name is `contact_potential_of` (line 5762: local time, coarse, geometry, ball) and `ContactConv.convBound` (line 2554:
geometry, ball). The local Props `BregmanSumBound`, `ConvBound`, `CellTestBound` are local lemma statements discharged inside the same proof (`ContactBregman.bregmanSumBound_of`, `ContactConv.convBound`,
`ContactCellTest.cellTestBound`, fed by `ContactWeakLap.inner_gradient_integral_nonpos`). The assembly intersects exactly: the `prop-coarse` event, the `lem-local` event, the drift Dynkin local martingale event
(`ContactDynkin.exists_drift_local_mart`), and the a.s. fact `X 0 = 0 ∧ ∀ j, |X_j| ≤ j` (from `IsDriftCERW`). It uses a subset of the events the paper lists for `lem:contact`, so nothing stronger than the paper is assumed.
The two deterministic cores (`contact_bound_two`, `contact_bound_three_le`) take only deterministic inequalities that the events deliver (`maxLocalTime ≤ CM r`, `maxRadius ≤ CR r`, `log(n+2)^4 ≤ r`,
the pointwise Dynkin bound `hfine`, the cell modulus `hmod`, the crude `lem-local (iii)` bound), each supplied on the event in `contact_potential_of`. The kernel facts (`exists_kernelFacts`: Poisson equation, level sets,
gradient asymptotics, growth of the potential kernel) are obtained by an unconditional existence theorem, not assumed. The conclusion is stronger than the paper's (all contact points `y₀`, not one chosen `y₀`). Verdict: PASS.

**`CERW/Support/Inner/InnerRadius.lean` (1160 lines).** `inner_radius_of` consumes `contact_potential`, `norm_ball_potential`, `norm_potential_geometry` and nothing else by name. It instantiates them at `Ψ = ‖·‖`,
`ξ = unitDir ∘ toSpace` via `euclidean_norm_hypotheses`, transfers `IsCERW` to `IsDriftCERW` by `isCERW_iff_isDriftCERW`, rewrites `normPotential` to `potential` by `normPotential_norm_eq`
(gradient of `‖·‖` is `v/|v|` off the origin, proved), and combines with `exists_event_prob` (the first-version fluctuation event, probability `≤ C n^{-p}`) and the deterministic `inner_core`
(contact bound at every contact point, plus ball potential and the sup bound for the potential, give (i) radius, (ii) volume, (iii) local times). The small-`n` case is closed by taking `C` larger than `nbig^p`.
The docstring says "`lem:contact` (assumed …)"; that is the `_of` design and the assumption is discharged by `contact_potential_of` in the frozen proof. Verdict: PASS.

## Notes (none changes a verdict)

* **N1.** Subgradient-selection existence for arbitrary norms is not a theorem of the repository; a scratch proof is in `ps/Subgrad.lean` (axioms clean). Suggest adding it to `CERW/Support/Guards.lean` if a general-norm non-vacuity guard is wanted.
* **N2.** `thm-sharp-width` is conditional on the explicit hypothesis `CERW.External.StoutLIL`. Its only use (`Lower.width_lil`, line 1525 ff.) instantiates it with the constant bound `B = fun _ _ => 2` and the compensated first coordinate
  martingale, the classical bounded-increment case. Truth of the hypothesis as stated (predictable `B`) rests on Stout (1970) and is assessed in `scratch/audits/external-sources.md` (IMPLIED-WITH-REMARK, primary text not reached); the statement was read against Hall-Heyde Thm 4.8 and the index alignment
  (`B (n+1)` is `ℱ n`-measurable, `⟨S⟩_n` includes the increment `n`) is right. `MartingaleCLT` is in no sealed closure.
* **N3.** 31 files (29 of the 37 `CERW/Frozen/*.lean`, including 17 of the 18 sealed ones, all but `InnerRadius.lean`, and both `CERW/External/*.lean`) have an mtime newer than their `.olean` (`seal.sh` runs `write_frozen.py`, which rewrote them at 16:40:59 to 16:41:00; the bytes between the markers still match the manifest hashes, and lake keys on content hashes). The
  other 233 modules are older than their oleans. The 18 current sealed Frozen sources were recompiled against the Support oleans (clean), which covers the stale-mtime possibility. `lake env lean` ignores the lakefile's `autoImplicit := false`, but the
  Frozen types are defeq to the `Statements.lean` Props, which `lake build` elaborated with `autoImplicit := false`, so no auto-bound implicit can sit in a frozen type.
* **N4.** During the audit (19:25) `CERW/Support/Lower.lean` was modified and `CERW/Support/Lower/SeparatedBrackets.lean` appeared, consistent with work on the DRAFT_SORRY node `lem-separated-brackets`. All my runs loaded the pre-existing
  oleans and the closures above do not contain those modules.

## Per-node verdicts

* thm-shape: PASS. Frozen proof is `exact @Support.Main.limit_shape`; Prop defeq; axioms clean; chain uses only PROVED `ball_shape`; realization guard `exists_isCERW`.
* thm-sharp-width: PASS (note N2). `exact Lower.sharp_width_of @Main.limit_shape @Lower.exp_deviation`; `External.StoutLIL` only as the statement's own hypothesis; axioms clean; realization guard.
* lem-ballpotential: PASS. `exact @Norm.norm_ball_potential`; no hypothesis bundle to be vacuous; closed form is non-zero, so the integral is not junk.
* lem-local: PASS. `norm_local_time_potential_of cell_gradient_holds`; `exists_norm_realization` and `euclidean_norm_hypotheses` cover the bundle (note N1 for general norms).
* lem-freedman: PASS. `exact @Norm.freedman_bound`; Prop syntactically identical to the frozen block; hypothesis satisfiable (zero martingale, random walk).
* lem-cell: PASS. `exact Norm.cell_gradient_holds`; `exists_isDistribLaplacian` covers the measure hypothesis (note N1 for the selection).
* lem-geometry: PASS. `exact @Norm.norm_potential_geometry`; bounded measurable `D` hypothesis removes the junk-integral risk.
* prop-coarse: PASS. `norm_coarse_bounds_of (…local…) norm_radial_test_holds @drift_crossing`; bundle covered.
* lem-radial: PASS. `exact Norm.norm_radial_test_holds`; bundle covered; `ρ₀` before `ε` as in the paper.
* lem-crossing: PASS. `exact @Norm.drift_crossing`; deterministic, true with the same `C`; hypotheses satisfiable.
* lem-layer: PASS. `exact @Norm.layer_potential`; `D` in a bounded layer, measurable.
* lem-cap: PASS. `exact @Norm.moreau_cap`; Moreau envelope differentiability is proved, so `gradient` is not junk; hypotheses satisfiable (`x = y`).
* lem-contact: PASS. `contact_potential_of` fed by proved local, coarse, geometry, ball; spot-checked in depth (section 5); bundle covered.
* lem-outer-crossing: PASS. `exact Norm.outer_crossing_holds`; deterministic path statement with the paper's `a ∈ Λℤ ∩ [0, Λn]` as `k ≤ n`; hypotheses satisfiable (straight path).
* prop-inner: PASS. `inner_radius_of (contact_potential_of …) …`; spot-checked in depth (section 5); realization guard.
* lem-near-far: PASS. `exact Outer.near_far_holds`; hypotheses satisfiable (shell with `λ = C_d w`).
* lem-exp-deviation: PASS. `exact @Lower.exp_deviation`; hypotheses satisfiable (scaled random walk); constants depend on `c₀, C₀` only, as in the paper.
* prop-log-lower: PASS. `exact Lower.log_lower_bounds_holds`; realization guard.
* ext-martingale-clt: PASS (FROZEN, not proved, by design). `def … : Prop`, not an axiom; identical to `Statements.MartingaleCLT`; in no sealed closure.
* ext-stout-lil: PASS (FROZEN, not proved, by design). `def … : Prop`, not an axiom; identical to `Statements.StoutLIL`; appears only as `hLIL` of `thm-sharp-width`.
