# Centrally-Excited-Random-Walk

A Lean 4 formalization of
> **Limit shapes of centrally excited random walks**  
> Ahmed Bou-Rabee and Yuval Peres, pinned here at [`paper/limit-shapes.tex`](paper/limit-shapes.tex)

An earlier version of the paper, *The limit shape of centrally excited random walk*, pinned at [`paper/cerw-flat.tex`](paper/cerw-flat.tex), was formalized first. Its seven statements are kept, with their frozen text.

This repository formalizes the whole revised paper: Theorems 1.1, 1.2, 1.3 and 2.1, and every lemma and proposition of Sections 2 to 9. Each statement is registered in `ledger/manifest.yaml` as one node, with Theorem 1.3 split into four nodes, one for each part:
- Theorem 1.1, the limit shape (`thm:shape`), and Theorem 2.1, the limit shape for a norm (`thm:norm-shape`), with the potential of a norm ball (Lemma 2.2);
- Theorem 1.2, the fluctuation bounds (`thm:fluctuations`);
- Theorem 1.3, sharpness (`thm:sharp`): lower bounds for the radii in the plane, with probability bounds and an iterated logarithm, lower bounds for the local times near the origin, and lower bounds for the difference of the radii in the plane;
- Section 3, local times and the potential: Lemmas 3.1 to 3.4;
- Section 4, coarse bounds: Proposition 4.1, Lemmas 4.2 and 4.3;
- Section 5, the limit shape with rates: Proposition 5.1, Lemmas 5.2 to 5.5;
- Section 6, the inner radius: Proposition 6.1; Section 7, the outer radius: Proposition 7.1 and Lemma 7.2;
- Section 8, limit laws: Theorems 8.1 and 8.3 and Lemma 8.2;
- Section 9, lower bounds on the fluctuations: Lemmas 9.1 and 9.3, Propositions 9.2 and 9.4.

The seven statements of the first version are the ball shape theorem, the fluctuation bounds, the Hausdorff estimate with the planar remark, the occupation and radius bounds, the local-time potential lemma, the geometry of the potential, and the radial test. Which statements are proved is recorded in `ledger/manifest.yaml` and summarized under Status below.

The development rests on Mathlib and on the shared library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability) (`LatticeProb`), which supplies lattice sites, the simple random walk and its Green function, the asymptotics of the lattice potential kernel and Green function, Freedman's inequality, the Paley–Zygmund inequality and the Cramér–Wold device. The kernel asymptotics that the paper cites from the literature are proved in Lattice-Probability, not assumed. The only results assumed are the two that the paper cites for its limit laws: Hall and Heyde's martingale central limit theorem (Corollary 3.1) and Stout's martingale law of the iterated logarithm (1970). Each is a proposition in `CERW/External/` and an explicit hypothesis of every theorem whose proof uses it.

## The model

Centrally excited random walk on `ℤ^d`, `d ≥ 2`, starts at the origin. On its first departure from a site `x ≠ 0` it steps `±e_i` with probability `1/(2d) ∓ ε x_i/(2|x|)`, which is a drift of size `ε` toward the origin. On every later departure, and on every departure from the origin, it takes a simple random walk step. The paper writes the drift as `κ`; Lean, and this file, write `ε`.

The walk whose drift is a subgradient of a norm replaces `x/|x|` by a chosen subgradient. Let `Ψ` be a norm on `ℝ^d` and fix a subgradient `ξ(x)` of `Ψ` at each site `x ≠ 0`, that is, a vector with `Ψ(y) ≥ Ψ(x) + ξ(x)·(y − x)` for every `y`. On its first departure from `x ≠ 0` the walk steps `x ± e_i` with probability `1/(2d) ∓ ε ξ_i(x)/2`, so the step has mean `−ε ξ(x)`. The probabilities are positive when `ε Ψ(e_i) < 1/d` for every `i`. For the Euclidean norm, `ξ(x) = x/|x|` gives the walk above.

Let `A_n` be the set of sites departed from before time `n`, `ℓ_n(x)` the number of departures from `x`, and `ω_d` the volume of the unit ball. Set `r_n = ((d+1)n/(2dεω_d))^{1/(d+1)}`, and for a norm `r_n = ((d+1)n/(2dε|B_Ψ|))^{1/(d+1)}` with `B_Ψ` the unit ball of `Ψ`. The first version of the paper uses `N = n^{1/(d+1)}` and `a = ((d+1)/(2dεω_d))^{1/(d+1)}`, so that `r_n = aN`; it also uses `V_n`, the set of visited sites.

The limit shape theorem, `thm:shape`, says that for `0 < ε < 1/d`, almost surely:
- for every `0 < η < 1`, eventually `{|x| < (1 − η) r_n} ⊆ A_n ⊆ {|x| < (1 + η) r_n}`;
- `r_n^{-1} max_x |ℓ_n(x) − 2dε (r_n − |x|)_+| → 0`;
- every site is visited infinitely often.

`thm:norm-shape` is the same statement for the walk with norm `Ψ`, with `Ψ(x)` in place of `|x|`.

The fluctuation bounds, `thm:fluctuations`, quantify this for the Euclidean norm. Let `D_n` be the union of the unit cells of the sites of `A_n`, and let `R_in(n) = inf_{y ∉ D_n} |y|` and `R_out(n) = max_{j ≤ n} |X_j|` be the inner and outer radii. With probability at least `1 − Cn^{-p}`, in the plane `|R_in(n) − r_n| ≤ C√(r_n log n)` and `R_out(n) − r_n ≤ C√r_n (log n)^{5/2}`, and for `d ≥ 3` `|R_in(n) − r_n| ≤ C log n` and `R_out(n) − r_n ≤ C (log n)^{d+1}`. The volume `|r_n^{-1} D_n △ B(0,1)|` and the local times are bounded too. `thm:sharp` shows that the rates in the plane cannot be improved, and `thm:moment-fluctuations` and `thm:site-fluctuations` give central limit theorems and laws of the iterated logarithm for `Σ_{x ∈ A_n} |x|` and for the local times at fixed sites.

The proof compares the local time with a potential `U_D(y) = (2ε/ω_d) ∫_D ∇Ψ(v) · (v − y)|v − y|^{-d} dv` of the occupied cells, whose value on a ball of `Ψ` is the cone `2dε(ρ − Ψ(y))_+`. Dynkin's formula writes each local time as this potential minus a martingale, up to an error; Freedman's inequality bounds the martingales, and convexity bounds the cost of replacing the chosen subgradients by the gradient (`lem:local`, `lem:cell`). Coarse bounds (`prop:coarse`) fix the scale. A contact argument at the inner radius and a crossing argument at the outer radius give the rates (`lem:contact`, `lem:outer-crossing`), and for the Euclidean norm the refinements in Sections 6 and 7. The limit laws come from the martingale central limit theorem and law of the iterated logarithm, and the lower bounds from exponential martingales.

## Where to start reading

| File or directory | Contents |
|---|---|
| `CERW/Frozen/LimitShape.lean` | Theorem 1.1, `CERW.Frozen.limit_shape`, transcribing `thm:shape`. |
| `CERW/Frozen/FluctuationRates.lean` | Theorem 1.2, `CERW.Frozen.fluctuation_rates`, transcribing `thm:fluctuations`. |
| `CERW/Frozen/SharpRadii.lean`, `SharpRadiiLil.lean`, `SharpBulk.lean`, `SharpWidth.lean` | Theorem 1.3, one file for each part. |
| `CERW/Frozen/NormShape.lean` | Theorem 2.1, `CERW.Frozen.norm_shape`, transcribing `thm:norm-shape`. |
| `CERW/Frozen/BallShape.lean`, `FluctuationBounds.lean` | The first-version ball shape theorem, `CERW.Frozen.ball_shape`, and fluctuation bounds, `CERW.Frozen.fluctuation_bounds`, each with its proof. |
| `CERW/Frozen/` | The registered theorem statements, one per file, each followed by the body that proves it (for a node in state `DRAFT_SORRY`, the registered `sorry`). |
| `CERW/External/` | The two cited results that are assumed: `MartingaleCLT.lean` and `StoutLIL.lean`. |
| `CERW/Model/` | Vocabulary shared by the statements: the laws `IsCERW` and `IsDriftCERW`, ranges and local times, lattice cells, norms and subgradients, the potentials and their tail, the radii, the Moreau envelope, the distributional Laplacian, and the pathwise martingales. `CERW.lean` imports the whole development. |
| `CERW/Generic/` | Results independent of the paper: lattice sums and packing, kernel estimates, dyadic halving, Young absorptions, martingale inequalities, Gauss's flux theorem with Newton's spherical averages, and facts about norms. |
| `CERW/Support/` | Lemmas used by the proofs, in directories that follow the paper (table below). |
| `ledger/manifest.yaml` | The registered nodes: file, Lean name, state, SHA-256 of the frozen statement, and paper source. |
| `ledger/readings.yaml`, `ledger/nl/`, `ledger/audits/` | The written reading of each statement against the paper, its natural-language twin, and the independent readings and audits of the statements. |
| `ledger/approval/` | The rulings on the statements: [`REVISED-SURFACE.md`](ledger/approval/REVISED-SURFACE.md) for the revised paper, [`KERNEL-ASYMPTOTICS.md`](ledger/approval/KERNEL-ASYMPTOTICS.md) for the kernel asymptotics, and [`PROVED-PROMOTION.md`](ledger/approval/PROVED-PROMOTION.md). |
| [`ASSUMPTIONS.md`](ASSUMPTIONS.md) | Every result this development assumes, with the verbatim Lean proposition and where the paper cites it. Generated by `python3 -m leanform_tools.assumptions`. |
| [`CORRESPONDENCE.md`](CORRESPONDENCE.md) | Transcription conventions, the table of registered statements with their paper anchors, and the cited results with where each is proved or assumed. |
| [`CERTIFICATE.md`](CERTIFICATE.md) | The environment, the axiom closure of each registered declaration, and the commands that reproduce them. Generated by `python3 -m leanform_tools.certificate`. |
| [`PROOF.md`](PROOF.md) | The mathematics of the proofs, the Lean import layout, and the points where the formalized statements differ from the published text. |
| `paper/` | [`limit-shapes.tex`](paper/limit-shapes.tex), the pinned revised paper, whose SHA-256 is recorded in the manifest as `source_pin`; [`cerw-flat.tex`](paper/cerw-flat.tex), the pinned first version, which is `paper/cerw.tex` with its three section files under `paper/sections/` expanded in place; and `proof-audit-source.md`, a consistency review of the first-version drafts. |

The directories of `CERW/Support/`:

| Directory | Contents |
|---|---|
| `Law/`, `Drift/` | The law of the Euclidean walk and of the walk with a drift field: one-step kernels, conditional step laws, Dynkin's formula, existence of realizations, and the bridge between the two. |
| `Occupation/`, `Geometry/` | Facts about cells, local times and sums over the range; the geometry of the Euclidean potential: sup and Hölder bounds, spherical averages, and the mass identity. |
| `LocalTime/`, `Coarse/`, `Crossing/`, `Contact/` | The Euclidean local-time potential lemma, the radial test, the coarse bounds and the outer bound, the crossing arguments, and the contact argument; the kernel facts derived from the lattice kernel asymptotics. |
| `Main/` | The final assembly of the first-version theorems; the limit shape in the normalization by `r_n`; and the non-vacuity of the statements about the norm walk: realizations, and subgradient selections for every norm. |
| `Norm/` | Sections 2 to 5 for a norm: the potential of a ball and of a layer, Freedman's inequality at a logarithmic threshold, the gradient on a cell, geometry, local times, the coarse bounds, the radial and crossing lemmas, the Moreau envelope and cap lemma, the contact bound and the outer crossing lemma. |
| `Inner/`, `Outer/` | Sections 6 and 7 for the Euclidean norm: the inner radius, and the near-far lemma. |
| `Limit/`, `Lower/` | Section 8, the limit laws; Section 9 and Theorem 1.3, the lower bounds. |
| `Statements.lean`, `Guards.lean` | Each registered statement as a proposition, so that a proof can assume the statements it uses; and checks that the vocabulary takes the values the paper gives by hand. |

## Terms

These words are used throughout with fixed meanings.

| term | meaning |
|---|---|
| **registered statement**, also called a **node** | one Lean declaration transcribing one statement of the paper, or one result the paper cites. Each has an entry in `ledger/manifest.yaml`. |
| **frozen statement** | the declaration's text between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`, pinned by the SHA-256 of those bytes. It cannot change without the change being recorded in the manifest. The proof after the end marker may be rewritten freely. |
| **`SEALED`** | the node is **proved** here: a complete proof, whose axiom closure contains only `propext`, `Classical.choice` and `Quot.sound`. A theorem that carries a cited result as a hypothesis is proved relative to it. |
| **`PROVED`** | the node is `SEALED` and its statement and proof have been independently audited (`ledger/audits/`); the promotion is recorded in `ledger/approval/PROVED-PROMOTION.md`. |
| **`FROZEN`** | the node is **assumed**, not proved: a result the paper quotes from the literature, stated as a proposition in `CERW/External/` and carried as an explicit hypothesis by every theorem whose proof uses it. Each is listed with its statement in [`ASSUMPTIONS.md`](ASSUMPTIONS.md). There are two: `ext-martingale-clt` and `ext-stout-lil`. |
| **`DRAFT_SORRY`** | the statement is pinned but its proof is still open, registered as a `sorry`. |
| **cited input**, **external** | a `FROZEN` node, in the sense above. |
| **statement proposition** | the proposition in `CERW/Support/Statements.lean` that says what a registered statement says. A Support theorem takes the statement propositions it depends on as hypotheses, and a frozen proof applies it to the proofs of those statements. |
| **norm walk** | centrally excited random walk whose drift at a first departure is a chosen subgradient of a norm, `CERW.IsDriftCERW`. The Euclidean walk, `CERW.IsCERW`, is the case `ξ(x) = x/\|x\|`. |
| **axiom closure** | the axioms a proof ultimately rests on, as reported by Lean's `#print axioms`. |
| **`sorryAx`** | the axiom Lean inserts for an unproved `sorry`; its presence in an axiom closure means the result is not proved. |

The word *frozen* carries two senses, so it is worth separating them: every
registered statement is frozen in the sense of being **pinned by hash**, while
the state `FROZEN` marks the subset that is **assumed rather than proved**.

## How a statement is tied to the paper

Each registered statement is a single declaration in its own Lean file, between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`. For each node, `ledger/manifest.yaml` records:
- the SHA-256 of the bytes between the markers, as `frozen_sha256`, with one leading newline dropped and the trailing newline kept;
- a `source:` entry giving the line range in the pinned paper and, for the revised paper, the LaTeX label the declaration transcribes, for example `limit-shapes.tex:103-116 (label thm:shape)`. The four parts of Theorem 1.3 cite the same label with the number of the part. The first-version nodes cite `paper/cerw-flat.tex` by line range.

`python3 -m leanform_tools.check_manifest` recomputes the hashes, so a statement cannot change without the manifest changing. For a theorem, the proof follows the end marker and may be rewritten freely.

## Which Lean theorem proves which result

`CORRESPONDENCE.md` holds the table of registered statements: node id, Lean name, paper line range and label, and state. The table is generated from `ledger/manifest.yaml` by `python3 -m leanform_tools.sync_docs`. `PROOF.md` lists the statements in the order of the paper. The four theorems of the introduction are `CERW.Frozen.limit_shape` (`thm:shape`), `CERW.Frozen.fluctuation_rates` (`thm:fluctuations`), the four declarations `CERW.Frozen.sharp_radii`, `sharp_radii_lil`, `sharp_bulk` and `sharp_width` (`thm:sharp`), and `CERW.Frozen.norm_shape` (`thm:norm-shape`).

## Status

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **39 registered statements — 30 sealed, 7 proved, 2 assumed.**  The 30 sealed and 7 proved node(s) are machine-checked: complete proofs whose axiom closure contains no `sorryAx`.  The 2 assumed (`FROZEN`) node(s) are cited results, stated in `CERW/External/` and carried as explicit hypotheses by the theorems that use them; they are assumed here, not proved.  Run
`python3 -m leanform_tools.check_manifest` to confirm. Counts here
are generated from `ledger/manifest.yaml` by
`python3 -m leanform_tools.sync_docs`; do not edit them by hand — a
hand-edited number inside this block is a failure, not a correction.

<!-- STATUS-END -->

The table of registered statements, with the state of each, is in [`CORRESPONDENCE.md`](CORRESPONDENCE.md).

The theorems that use a cited result carry it as a hypothesis: `sharp_radii_lil` and `sharp_width` carry `hLIL : CERW.External.StoutLIL`, and `moment_fluctuations` and `site_fluctuations` carry both `hCLT : CERW.External.MartingaleCLT` and `hLIL`. No other theorem carries a hypothesis beyond the parameters of the paper's statement. The kernel asymptotics that the proofs use are supplied by `LatticeProb.External.potentialKernelAsymptotics_holds`, a theorem of Lattice-Probability whose axiom closure is the same three standard axioms.

## Building and checking

Lean and Mathlib are pinned by `lean-toolchain` and `lake-manifest.json`. `Lattice-Probability` is a git dependency pinned to a commit in `lakefile.lean` and `lake-manifest.json`.

```sh
elan toolchain install $(cat lean-toolchain)
lake exe cache get      # optional: prebuilt Mathlib
lake build CERW
python3 tools/verify.py
```

`tools/verify.py` runs the gates of `tools/leanform/` in order and stops at the first failure. A single gate runs as `PYTHONPATH=tools/leanform python3 -m leanform_tools.<gate> .`.

| Gate | What it guarantees |
|---|---|
| `check_manifest` | Every manifest file has exactly one frozen block whose SHA-256 and declaration name match the manifest; every file under `CERW/Frozen/` and `CERW/External/` belongs to one node; no `axiom`, `admit`, `native_decide` or `sorryAx` token occurs in the source tree, and `sorry` occurs only in nodes in state `DRAFT_SORRY`. Needs neither Lake nor network. |
| `check_axioms` | Runs `#print axioms` on every registered export. Each closure contains only `propext`, `Classical.choice` and `Quot.sound`; `sorryAx` is tolerated only for a node in state `DRAFT_SORRY`. |
| `check_constants` | In each frozen statement whose conclusion has a real existential constant, no parameter the constant must not depend on is bound before it. |
| `check_warnings` | Runs `lake build CERW` and fails if the build fails or emits any warning other than the `sorry` warnings expected for `DRAFT_SORRY` nodes. |
| `check_progress` | Counts the open `sorry`s against the baseline `ledger/holes.json`: a change may close them and may not open new ones. |
| `check_coverage`, `check_clauses`, `check_exponents`, `check_hazards`, `paper_anchors`, `paper_citations` | Every labelled statement of the paper is registered, every node has a written reading against the paper, the exponents of the paper and of Lean agree, junk values are guarded, and the recorded line ranges and citations still match the paper's labels. |
| `sync_docs`, `assumptions`, `certificate`, `linkcheck` | The generated blocks of this file, of `PROOF.md` and of `CORRESPONDENCE.md`, `ASSUMPTIONS.md` and `CERTIFICATE.md` are current, and no Markdown file has a dangling link. |

The gates need PyYAML. `sync_docs` checks (`--write` regenerates) the status block of this file and of `PROOF.md`, and the registered-statements table of `CORRESPONDENCE.md`. `assumptions` and `certificate` write `ASSUMPTIONS.md` and `CERTIFICATE.md` (`--check` verifies they are current), and `freeze` registers or refreshes a node.

## Scope

Formalized: the statements of the revised paper, namely Theorems 1.1, 1.2, 1.3 and 2.1 and the lemmas and propositions of Sections 2 to 9, for centrally excited random walk as defined in `CERW/Model/`, both the walk with the Euclidean drift `x/|x|` and the walk whose drift is a subgradient of a norm; and the seven statements of the first version. Every labelled theorem-like environment of the pinned paper is claimed by a node. The law of the walk is given by cylinder factorization, and every theorem holds for every process on every probability space with that law.

Assumed: Hall and Heyde's martingale central limit theorem (*Martingale Limit Theory and Its Application*, 1980, Corollary 3.1), in the form the paper uses it for one martingale with deterministic normalization, and Stout's martingale law of the iterated logarithm (*A martingale analogue of Kolmogorov's law of the iterated logarithm*, 1970), in the form the paper verifies. The paper cites them at lines 1401, 1412, 1521 and 1647 of `limit-shapes.tex`. Nothing else is assumed.

Several results the paper cites are proved rather than assumed:
- the asymptotics of the lattice potential kernel and Green function (Lawler–Limic, Theorems 4.3.1 and 4.4.4), in Lattice-Probability;
- the gradient estimates for the kernel (Lawler–Limic, Corollaries 4.3.3 and 4.4.5), derived here from those asymptotics;
- Freedman's inequality, the Paley–Zygmund inequality and the Cramér–Wold device, from Lattice-Probability, in the forms the paper uses;
- the mean-value identity behind Newton's spherical averages, via Gauss's flux theorem;
- Rademacher's theorem for norms, which Mathlib supplies, and the existence of the distributional Laplacian of a norm as a locally finite measure.

Where the formalized statements or proofs differ from the published text, `PROOF.md` gives the reason. In summary:

- "With probability at least `1 − Cn^{-p}`" is formalized as an upper bound on the outer measure of the exceptional event, and a probability lower bound as a measurable event of at least that probability. A supremum tending to zero is formalized as an eventual bound for every `η > 0`, and `limsup ≥ L` as a bound that holds infinitely often for every `δ > 0` with `L − δ`.
- Constants are bound after the parameters the paper lets them depend on and before the probability space; for the norm walk, before the subgradients as well.
- The four statements the paper makes "on the event" of Section 5.2 are read as follows: Lemmas 4.3 and 5.5, about a single path, deterministically with the constants of the event as parameters; Lemmas 5.4 and 9.3 as probability bounds that hold for every large `n`.
- Theorem 1.3 is four statements, one for each part, and the two parts of (iv) form one statement.
- Three hypotheses that the proofs do not use are kept as the paper states them: `b ≥ 0` in Lemma 5.2, `ε < 1/d` in Lemma 7.2, and the maximality of `x_*` in Lemma 5.5.
- Lemmas 2.2, 3.4, 4.3 and 5.2 are stated for a wider range of `ε` than the paper's, because their proofs do not use the ellipticity condition.
- `eq:hausdorff` of the first version, which the paper states on the event of its `thm:fluctuations`, is formalized as a probability bound with its own constant, and the planar remark after it in its two-sided reading.
- The paper stops the quadratic martingale on first exit from a ball. The formalization truncates its increments predictably instead; on the coarse event the two agree.

Not formalized: the introduction's discussion and the proof overview, the related work, the notation section's prose, the figures, and the closing remark of Section 5 on Minkowski functionals of convex bodies that are not symmetric. The paper states no further theorem, proposition or lemma.
