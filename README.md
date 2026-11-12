# Limit shapes for centrally excited walks

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee, Tuan-Minh Nguyen, Yuval Peres and Arvind Singh,
> [*Limit shapes for centrally excited walks*](https://arxiv.org/abs/2610.10162),
> arXiv:2610.10162.

The paper's source, bibliography and figures are included under [`paper/`](paper/), and the
formalized source is pinned in [`ledger/current.yaml`](ledger/current.yaml). Every theorem, lemma
and proposition of the paper is stated as printed and proved by the argument printed in the paper,
with no cited result assumed.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and the
shared library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability)
(`LatticeProb`).

[![CI](https://github.com/nitromannitol/Centrally-Excited-Random-Walk/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Centrally-Excited-Random-Walk/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Centrally-Excited-Random-Walk/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Centrally-Excited-Random-Walk/actions/workflows/comparator.yml)

## What is proved

A centrally excited random walk `X_0 = 0, X_1, X_2, …` on `ℤ^d`, `d ≥ 2`, moves like simple
random walk, except that on its first departure from each site `x ≠ 0` it moves to `x ± e_i`
with probability `1/(2d) ∓ ε x_i/(2|x|)`, where `0 < ε < 1/d`. This step has a drift of size `ε`
toward the origin. The local time `ℓ_n(x)` is the number of departures from `x` before time
`n`, and the range `A_n` is the set of sites departed from before time `n`.

Kozma conjectured that after `n` steps the visited set approximates a ball of radius of order
`n^(1/(d+1))`. The paper proves this in every dimension `d ≥ 2`, with

> `r_n = ((d+1) n / (2 d ε ω_d))^(1/(d+1))`,  `ω_d` the volume of the unit ball,

so that the cone `2 d ε (r_n − |x|)₊` has integral `n`, and shows that the local times converge
to this cone uniformly at the scale `r_n`. It bounds the fluctuations of the radii and of the
local times, shows that the planar bounds are sharp, and extends the limit shape to walks whose
drift is opposite to a subgradient of a norm. The model is stated precisely in
[Standing assumptions and scope](#standing-assumptions-and-scope).

The main results, Theorems 1.1, 1.2 and 1.3 of the introduction and Theorem 2.1, formalized as
stated in the paper, are collected in [`CERW/MainTheorems.lean`](CERW/MainTheorems.lean) as
seven theorems. Each restates the registered statement of the same name in
[`CERW/LimitShapes/Frozen/`](CERW/LimitShapes/Frozen/), where every labelled result of the
paper is registered:

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 (label `thm:shape`) | `CERW.MainTheorems.limit_shape` | Almost surely, the range is eventually between the balls of radii `(1 − η) r_n` and `(1 + η) r_n`, the local times are within `o(r_n)` of the cone, and every site is visited infinitely often. |
| Theorem 1.2 (label `thm:fluctuations`) | `CERW.MainTheorems.fluctuation_rates` | Bounds on the deviations of the inner and outer radii, of the rescaled volume and of the local times, with probability at least `1 − C n^(−p)` and eventually almost surely. |
| Theorem 1.3 (i) (label `thm:sharp`) | `CERW.MainTheorems.sharp_radii` | In the plane, each radius deviates from `r_n` by at least `c √(r_n log n)` with probability at least `n^(−p)`. |
| Theorem 1.3 (ii) (label `thm:sharp`) | `CERW.MainTheorems.sharp_radii_lil` | In the plane, an iterated-logarithm lower bound for the deviations of both radii. |
| Theorem 1.3 (iii) (label `thm:sharp`) | `CERW.MainTheorems.sharp_bulk` | With probability at least `1 − n^(−c)`, some site within `√r_n` of the origin has local-time error at least `c √r_n log n` in the plane and `c √(r_n log n)` for `d ≥ 3`. |
| Theorem 1.3 (iv) (label `thm:sharp`) | `CERW.MainTheorems.sharp_width` | In the plane, polynomial-probability, iterated-logarithm and small-width bounds for the difference of the two radii. |
| Theorem 2.1 (label `thm:norm-shape`) | `CERW.MainTheorems.norm_shape` | When the drift is opposite to a subgradient of a norm, the range approximates the ball of that norm and the local times approximate its cone. |
| Lemma 2.2 (label `lem:ballpotential`) | `CERW.LimitShapes.norm_ball_potential` | The potential of the norm ball `{Ψ < ρ}` is the cone `2 d ε (ρ − Ψ(y))₊`. |
| Lemma 3.1 (label `lem:local`) | `CERW.LimitShapes.norm_local_time_potential` | With probability at least `1 − C n^(−p)`, the smoothed local time differs from the potential of the occupied cells by at most `C log n` plus a term governed by the largest local time. |
| Lemma 3.2 (label `lem:freedman`) | `CERW.LimitShapes.freedman_bound` | A martingale with increments bounded by `1` satisfies `|Z_n − Z_0| ≤ C (√(⟨Z⟩_n log n) + log n)` with probability at least `1 − C n^(−p)`. |
| Lemma 3.3 (label `lem:cell`) | `CERW.LimitShapes.cell_gradient` | On each unit cell `C_x`, the `L¹` distance between the gradient of the norm and the subgradient `ξ(x)` is bounded by a measure of a nearby ball. |
| Lemma 3.4 (label `lem:layer`) | `CERW.LimitShapes.layer_potential` | The potential of a set in the layer `{b ≤ Ψ ≤ b + a}` is bounded by `2 d ε a`. |
| Proposition 4.1 (label `prop:coarse`) | `CERW.LimitShapes.norm_coarse_bounds` | Coarse bounds, with probability at least `1 − C n^(−p)`, including `c r_n^d ≤ |A_n| ≤ C r_n^d`. |
| Proposition 5.1 (label `prop:norm-shape`) | `CERW.LimitShapes.norm_shape_rates` | Rates for Theorem 2.1, with a constant that does not depend on the choice of the subgradients. |
| Lemma 5.2 (label `lem:contact`) | `CERW.LimitShapes.contact_potential` | On the event of Section 5.1, the contact term is at most `√(r_n log n)` in the plane and `log n` for `d ≥ 3`, up to a constant. |
| Proposition 6.1 (label `prop:inner`) | `CERW.LimitShapes.inner_radius` | For the Euclidean norm, bounds on the inner radius, the volume and the local times, with probability at least `1 − C n^(−p)`. |
| Proposition 7.1 (label `prop:stronger-outer`) | `CERW.LimitShapes.outer_radius` | For the Euclidean norm, the outer radius exceeds `r_n` by at most `C √r_n (log n)^(5/2)` in the plane and `C (log n)^(d+1)` for `d ≥ 3`, with probability at least `1 − C n^(−p)`. |
| Lemma 7.2 (label `lem:near-far`) | `CERW.LimitShapes.near_far` | A deterministic bound on the potential of a set in a thin spherical shell, at the points of the shell. |
| Theorem 8.1 (label `thm:moment-fluctuations`) | `CERW.LimitShapes.moment_fluctuations` | A central limit theorem and a law of the iterated logarithm for the sum of the distances from the origin. |
| Lemma 8.2 (label `lem:fixed-site-centering`) | `CERW.LimitShapes.fixed_site_centering` | Almost surely, the potential of the occupied cells at a fixed site is the cone plus an explicit correction, up to `C (log n)^3` in the plane and `C` for `d ≥ 3`. |
| Theorem 8.3 (label `thm:site-fluctuations`) | `CERW.LimitShapes.site_fluctuations` | A central limit theorem, a law of the iterated logarithm and joint limits for the local times at fixed sites. |
| Lemma 9.1 (label `lem:exp-deviation`) | `CERW.LimitShapes.exp_deviation` | Lower bounds for the deviations of martingales with bounded increments and comparable brackets, and for the maximum of nearly orthogonal ones. |
| Proposition 9.2 (label `prop:bulk-profile`) | `CERW.LimitShapes.bulk_profile` | For the Euclidean norm, the local times at the sites with `|y| ≤ θ r_n` are within `C √r_n log n` of the cone in the plane and `C √(r_n log n)` for `d ≥ 3`. |
| Lemma 9.3 (label `lem:separated-brackets`) | `CERW.LimitShapes.separated_brackets` | On the event of Section 5.1, the martingales of Section 9 have comparable brackets and small cross-brackets. |
| Proposition 9.4 (label `prop:log-lower`) | `CERW.LimitShapes.log_lower_bounds` | Tail bounds and almost-sure lower bounds for the deviations of the radii. |

<!-- LIMIT-SHAPES-STATUS-BEGIN -->

**All 22 labeled results are proved in 29 checked declarations.** The literal Section 5.1 event has polynomial exceptional probability, and both contact and separated brackets use its produced uniform constants.

<!-- LIMIT-SHAPES-STATUS-END -->

Four further registered declarations prove intermediate steps that the paper states in its text:
the distance-crossing bound, the common event of Section 5.1 with polynomially small exceptional
probability, and the contact and separated-bracket estimates on that event.
[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps every statement to the paper, and
[`PROOF.md`](PROOF.md) describes each proof.

**Theorem 1.1 (limit shape, `thm:shape`).** Let `d ≥ 2` and `0 < ε < 1/d`. Almost surely, the
centrally excited random walk has the following properties.

1. *Shape.* For every `0 < η < 1` and all sufficiently large `n`,
   `{x ∈ ℤ^d : |x| < (1 − η) r_n} ⊂ A_n ⊂ {x ∈ ℤ^d : |x| < (1 + η) r_n}`.
2. *Local times.* As `n → ∞`, `r_n⁻¹ max_x |ℓ_n(x) − 2 d ε (r_n − |x|)₊| → 0`.
3. *Recurrence.* The walk visits every site of `ℤ^d` infinitely often.

In Lean, `CERW.MainTheorems.limit_shape` holds for every process `X : ℕ → Ω → ℤ^d` on every
probability space whose law is that of the walk (`CERW.IsCERW μ ε X`). The range `A_n` is
`CERW.departureRange`, the local time `ℓ_n` is `CERW.localTime`, and `ω_d` is the Lebesgue
measure of the open unit ball of `EuclideanSpace ℝ (Fin d)`. Part 2 is stated as: for every
`η > 0`, eventually `|ℓ_n(x) − 2 d ε (r_n − |x|)₊| ≤ η r_n` for every `x`.

**Theorem 1.2 (fluctuation bounds, `thm:fluctuations`).** Let `d ≥ 2` and `0 < ε < 1/d`. Let
`D_n` be the union of the unit cells `x + [−½, ½)^d`, `x ∈ A_n`, let the inner radius `R_in(n)`
be the distance from the origin to the complement of `D_n`, and let the outer radius be
`R_out(n) = max_{j ≤ n} |X_j|`. For every `p > 0` there is `C(d, ε, p) < ∞` such that, for
every integer `n ≥ 2`, the following bounds hold simultaneously with probability at least
`1 − C n^(−p)`; in particular they hold for all sufficiently large `n` almost surely.

1. *Radii.* `|R_in(n) − r_n| ≤ C √(r_n log n)` and `R_out(n) − r_n ≤ C √r_n (log n)^(5/2)` if
   `d = 2`; `|R_in(n) − r_n| ≤ C log n` and `R_out(n) − r_n ≤ C (log n)^(d+1)` if `d ≥ 3`.
2. *Volume.* The volume of `r_n⁻¹ D_n △ B(0, 1)` is at most `C √(log n / r_n)` if `d = 2` and
   `C log n / r_n` if `d ≥ 3`.
3. *Local times.* `max_x |ℓ_n(x) − 2 d ε (r_n − |x|)₊|` is at most `C √r_n (log n)^(3/2)` if
   `d = 2` and `C √(r_n log n)` if `d ≥ 3`.

In Lean, `CERW.MainTheorems.fluctuation_rates` chooses `C` before the probability space and the
process, so one constant serves every realization of the walk, and states the almost-sure
conclusion with the same constant. The radii are `CERW.innerRadius` and `CERW.maxRadius`, and
`D_n` is `CERW.cellSet`.

**Theorem 1.3 (sharpness, `thm:sharp`).** Let `d ≥ 2` and `0 < ε < 1/d`.

1. *Radii in the plane.* Let `d = 2`. For every `p > 0` there is `c(ε, p) > 0` such that, for
   all sufficiently large `n`, `P(r_n − R_in(n) ≥ c √(r_n log n)) ≥ n^(−p)` and
   `P(R_out(n) − r_n ≥ c √(r_n log n)) ≥ n^(−p)`.
2. *Iterated logarithm for the radii in the plane.* Let `d = 2`. Almost surely, both
   `limsup (r_n − R_in(n)) / √(r_n log log n)` and `limsup (R_out(n) − r_n) / √(r_n log log n)`
   are at least `1/√(10πε)`.
3. *Local times near the origin.* There is `c(d, ε) > 0` such that, for all sufficiently large
   `n`, with probability at least `1 − n^(−c)`,
   `max_{|x| ≤ √r_n} |ℓ_n(x) − 2 d ε (r_n − |x|)|` is at least `c √r_n log n` if `d = 2` and
   `c √(r_n log n)` if `d ≥ 3`.
4. *Difference of the radii in the plane.* Let `d = 2`. (a) For every `p > 0` there is
   `c(ε, p) > 0` such that `P(R_out(n) − R_in(n) ≥ c √(r_n log n)) ≥ n^(−p)` for all
   sufficiently large `n`. (b) Almost surely,
   `limsup (R_out(n) − R_in(n)) / √(r_n log log n) ≥ √(π/(3ε))`. (c) For every `a ≥ 0`,
   `limsup P(R_out(n) − R_in(n) ≤ a √r_n) ≤ 1 − exp(−3εa²/π)`.

In Lean, the four parts are `CERW.MainTheorems.sharp_radii`, `CERW.MainTheorems.sharp_radii_lil`,
`CERW.MainTheorems.sharp_bulk` and `CERW.MainTheorems.sharp_width`; parts 1, 2 and 4 take
`d = 2` as a hypothesis. The constants and the threshold beyond which "sufficiently large `n`"
holds are chosen before the probability space and the process. Parts 1 and 4(a) also state that
the events are measurable. Each lower bound on a `limsup` is stated as: for every `δ > 0`, the
deviation is at least the constant minus `δ`, times `√(r_n log log n)`, for infinitely many `n`.

**Theorem 2.1 (limit shape for a norm, `thm:norm-shape`).** Let `d ≥ 2`, let `Ψ` be a norm on
`ℝ^d`, let `ξ(x)` be a subgradient of `Ψ` at `x`, chosen at every site `x ≠ 0`, and let `ε > 0`
satisfy `ε max_i Ψ(e_i) < 1/d`. Consider the walk whose first departure from each site `x ≠ 0`
has the probabilities above with `x/|x|` replaced by `ξ(x)`, and let `r_n` be given by the
formula above with the volume of the unit ball of `Ψ` in place of `ω_d`. Almost surely:

1. *Shape.* For every `0 < η < 1` and all sufficiently large `n`,
   `{x ∈ ℤ^d : Ψ(x) < (1 − η) r_n} ⊂ A_n ⊂ {x ∈ ℤ^d : Ψ(x) < (1 + η) r_n}`.
2. *Local times.* As `n → ∞`, `r_n⁻¹ max_x |ℓ_n(x) − 2 d ε (r_n − Ψ(x))₊| → 0`.
3. *Recurrence.* The walk visits every site of `ℤ^d` infinitely often.

In Lean, `CERW.MainTheorems.norm_shape` holds for every process with the law
`CERW.IsDriftCERW μ ε ξ X`, every `Ψ` with `CERW.IsNorm Ψ` and every field `ξ` with
`CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)` at each `x ≠ 0`. The field is extended by
`ξ(0) = 0`, so the walk has no drift at the origin, and the condition on `ε` is `ε Ψ(e_i) < 1/d`
for every `i`. Part 2 is stated as in Theorem 1.1.

## Standing assumptions and scope

1. **Every theorem is about every process.** `CERW.IsCERW μ ε X` says that the process `X` has
   the law of the centrally excited walk with drift `ε`; the theorems hold for every such
   process on every probability space. The local time at a site counts the departures from it,
   and the range is the set of sites departed from by time `n`.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no new `axiom`. The axiom report of every registered declaration consists
   of exactly `propext`, `Classical.choice` and `Quot.sound`. Nothing is assumed: no theorem
   carries a cited result as a hypothesis ([`ASSUMPTIONS.md`](ASSUMPTIONS.md)).
3. **Quantifiers.** Constants depend only on the parameters the paper names (`d`, `ε`, `p`), and
   are chosen before `n`, as printed.
4. **The two-author manuscript.** The repository also formalizes the manuscript
   [*Kozma's centrally excited walk converges to a Euclidean ball*](paper/limit-shapes.tex)
   (Ahmed Bou-Rabee and Yuval Peres), whose results the paper above extends. Its 27 registered
   statements, pinned in [`ledger/manifest.yaml`](ledger/manifest.yaml) and stated in
   [`CERW/Frozen/`](CERW/Frozen/), are proved, and its certificate is
   [`CERTIFICATE.md`](CERTIFICATE.md). Results whose statement and printed proof are the same in
   both sources share their formal proofs.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **27 registered statements — 27 proved.**  The 27 proved statements are machine-checked: complete proofs whose axiom closure contains no `sorryAx`.

<!-- STATUS-END -->

## Guarantees

- **No `sorry`.** The library has none. The four comparator challenges under
  [`CERWAudit/`](CERWAudit/) contain seven intentional statement-level `sorry`s, one per target,
  which the solutions prove.
- **Standard axioms only.** The axiom report of every registered declaration is exactly
  `propext`, `Classical.choice` and `Quot.sound` ([`CERTIFICATE-LIMIT-SHAPES.md`](CERTIFICATE-LIMIT-SHAPES.md));
  `tools/AllAxioms.lean` checks every declaration of the library.
- **Independent check of the statements.** The introduction's theorems are restated in
  [`CERWAudit/`](CERWAudit/) using mathlib alone, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the solutions
  prove them with only the three standard axioms, through the Lean kernel and the independent
  nanoda kernel. See [`CERWAudit/README.md`](CERWAudit/README.md).
- **Pinned toolchain and dependencies.** Lean `v4.32.0`; mathlib at
  `81a5d257c8e410db227a6665ed08f64fea08e997` and Lattice-Probability at
  `424de9b04279b9aa58364ab227b44c8007e0b5ba`, both exact commits recorded in
  [`lake-manifest.json`](lake-manifest.json) (see [Building](#building)).
- **The paper is part of the repository.** The statement map refers to the versions in
  [`paper/`](paper/), pinned by SHA-256 to
  `128646310ef17f4f897b5dfa9305187a85280eef391b70d8c7be009a5da5c87d`
  (`centrally-excited-walks.tex`) and
  `0771c8808b3b1f50a0131433c190ce07f908eadd7d2b3145d8f86589be2f9396` (`limit-shapes.tex`).
- **Kernel replay.** `tools/replay_kernel.sh` replays every declaration of `CERW` and of the
  modules of Lattice-Probability it imports in the Lean kernel, and is tested on a fixture that
  bypasses the kernel.
- **Pinned statements.** The bytes of each registered statement of the paper are pinned by SHA-256
  in [`ledger/current.yaml`](ledger/current.yaml), with the lines of the paper it states (those of
  the two-author manuscript in [`ledger/manifest.yaml`](ledger/manifest.yaml)), and
  `tools/check_frozen_types.py` checks the elaborated types of these statements and of the seven
  theorems of `CERW/MainTheorems.lean`.
- **Warning-free build.** The continuous-integration build rejects any warning.

## Size

The library contains 661 Lean files with 154,869 physical lines (`CERW.lean` and `CERW/`), of
which 127,905 lines remain once comments and blank lines are removed, on top of mathlib and
Lattice-Probability. Both formalized sources are counted. The comparator sources under
`CERWAudit/` are counted separately: 13 Lean files with 1,647 physical lines.

## Building

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned in
[`lean-toolchain`](lean-toolchain). From a clone:

```bash
lake exe cache get
lake build             # the library
lake build CERWAudit   # the comparator challenges and solutions
```

`import CERW` loads the development. The dependencies are fetched at these exact commits from
[`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `424de9b04279b9aa58364ab227b44c8007e0b5ba`.

The checks run by the continuous integration need Python 3.10 or later:

```bash
python3 -m venv .venv
. .venv/bin/activate
python -m pip install ./tools/leanform
python -m leanform_tools.verify .     # the two-author manuscript: manifest, coverage, axioms
python tools/verify_current.py        # the paper: manifest, coverage, axioms, documentation
lake env lean tools/AllAxioms.lean    # the axioms of every declaration
bash tools/replay_kernel.sh           # the kernel replay
lake env lean tools/FrozenTypes.lean
python tools/check_frozen_types.py    # the elaborated types of the frozen statements
```

To build the paper, run `latexmk -pdf centrally-excited-walks.tex` in `paper/`.

## Running the comparators

Each comparator pair has a configuration `CERWAudit/<Pair>/comparator.json` that permits exactly
`propext`, `Classical.choice` and `Quot.sound`. [leanprover/comparator](https://github.com/leanprover/comparator)
checks that the solution proves the challenge statement, compares their dependency closures, and
replays the proof with the Lean kernel and the independent nanoda kernel.

`bash CERWAudit/check_standalone.sh --vocabulary` checks that each challenge elaborates on mathlib
alone and that its vocabulary matches the solution's.
[`CERWAudit/README.md`](CERWAudit/README.md) gives the commands to run the comparator locally.

There are two continuous-integration workflows: **CI**
([`build.yml`](.github/workflows/build.yml)) builds the library and the comparator surface and
runs the checks listed under Building, and **Comparator audit**
([`comparator.yml`](.github/workflows/comparator.yml)) checks all four challenge/solution pairs.
CI runs on pushes to `main` that change Lean sources, `CERWAudit/`, the tools, the ledger, the
paper, `formalization.yaml`, the build configuration or the CI workflow, and the comparator audit
on pushes that change Lean sources, `CERWAudit/`, the build configuration or the comparator
workflow. Both workflows can be started manually from the
[Actions page](https://github.com/nitromannitol/Centrally-Excited-Random-Walk/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
CERW.lean             the root module, importing the development
CERW/
  MainTheorems.lean   the introduction's theorems, stated in full
  LimitShapes/        the paper's statements (Frozen/), the common event of Section 5.1 and the proofs
  Frozen/             the statements of the two-author manuscript
  Model/              the walk, its law, local times and ranges
  Support/            the proofs of the papers' results
  Generic/            general results used in the proofs
  Meta/               axiom reports
CERWAudit/            the mathlib-only comparator challenges and their solutions
.github/workflows/    build and comparator workflows
ledger/               current.yaml and manifest.yaml (statement hashes, paper lines, states) and
                      the paper excerpt beside each Lean statement (nl/)
paper/                centrally-excited-walks.tex, limit-shapes.tex, bibliography and figures
tools/                the checkers listed under Building
CORRESPONDENCE.md     paper ↔ Lean, statement by statement
ASSUMPTIONS.md        what the development assumes (nothing)
CONTRIBUTING.md       build conventions and contribution notes
PROOF.md              the proofs and the formalization conventions
CERTIFICATE-LIMIT-SHAPES.md, CERTIFICATE.md
                      generated records of the toolchain, the build and each statement's axioms
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and, for
auxiliary proof work, DeepSeek, under the direction of the author. Every proof is checked by the
Lean kernel. The models and tooling are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**. To cite it, use [`CITATION.cff`](CITATION.cff).
The paper is by Ahmed Bou-Rabee, Tuan-Minh Nguyen, Yuval Peres and Arvind Singh.

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
The paper sources in [`paper/`](paper/) are included for reference and are not covered by this
licence.
