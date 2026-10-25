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

<!-- LIMIT-SHAPES-STATUS-BEGIN -->

**All 22 labeled results are proved in 29 checked declarations.** The literal Section 5.1 event has polynomial exceptional probability, and both contact and separated brackets use its produced uniform constants.

<!-- LIMIT-SHAPES-STATUS-END -->

[![CI](https://github.com/nitromannitol/Centrally-Excited-Random-Walk/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Centrally-Excited-Random-Walk/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Centrally-Excited-Random-Walk/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Centrally-Excited-Random-Walk/actions/workflows/comparator.yml)

## What is proved

A centrally excited random walk on `ℤ^d` moves like simple random walk, except that its first step
from each site other than the origin has a drift of size `ε` toward the origin. Kozma conjectured
that after `n` steps the visited set approximates a ball of radius of order `n^(1/(d+1))`. The paper
proves this in every dimension `d ≥ 2`, with

> `r_n = ((d+1) n / (2 d ε ω_d))^(1/(d+1))`,  `ω_d` the volume of the unit ball,

and shows that the rescaled local times converge uniformly to the cone `2 d ε (r_n − |x|)₊`.
The introduction's theorems are restated in full in
[`CERW/MainTheorems.lean`](CERW/MainTheorems.lean), for every `d ≥ 2` and `0 < ε < 1/d` and every
process whose law is that of the walk (`CERW.IsCERW`):

- **`CERW.MainTheorems.limit_shape`** (Theorem 1.1): almost surely, for every `0 < η < 1` and all
  large `n`, the set of sites the walk has departed from contains the ball of radius `(1 − η) r_n`
  and is contained in the ball of radius `(1 + η) r_n`; the local times are within `η r_n` of the
  cone, uniformly in the site; and every site is visited infinitely often.
- **`CERW.MainTheorems.fluctuation_rates`** (Theorem 1.2): the inner and outer radii, the volume of
  the symmetric difference with the ball and the local-time errors satisfy explicit
  dimension-dependent bounds (in the plane, `√(r_n log n)` for the inner radius and
  `√r_n (log n)^(5/2)` for the outer radius), with probability at least `1 − C n^(−p)` for every
  `p`, and eventually almost surely.
- **`sharp_radii`, `sharp_radii_lil`, `sharp_bulk`, `sharp_width`** (Theorem 1.3): the planar
  bounds are sharp up to the power of the logarithm, with polynomial-probability and
  iterated-logarithm lower bounds for the radii and their difference and a lower bound for the
  local-time error in the bulk.
- **`CERW.MainTheorems.norm_shape`** (Theorem 2.1): when the drift is opposite to a subgradient of
  a norm, the visited set approximates the ball of that norm.

Every labelled result of the paper is a frozen statement in
[`CERW/LimitShapes/Frozen/`](CERW/LimitShapes/Frozen/):

| Paper | Label | Lean declaration |
| --- | --- | --- |
| Theorem 1.1 (limit shape) | `thm:shape` | `CERW.LimitShapes.limit_shape` |
| Theorem 1.2 (fluctuation bounds) | `thm:fluctuations` | `CERW.LimitShapes.fluctuation_rates` |
| Theorem 1.3 (i) (sharpness: the radii) | `thm:sharp` | `CERW.LimitShapes.sharp_radii` |
| Theorem 1.3 (ii) (sharpness: iterated logarithm) | `thm:sharp` | `CERW.LimitShapes.sharp_radii_lil` |
| Theorem 1.3 (iii) (sharpness: the bulk) | `thm:sharp` | `CERW.LimitShapes.sharp_bulk` |
| Theorem 1.3 (iv) (sharpness: the width) | `thm:sharp` | `CERW.LimitShapes.sharp_width` |
| Theorem 2.1 (limit shape for a norm) | `thm:norm-shape` | `CERW.LimitShapes.norm_shape` |
| Lemma 2.2 (the potential of a norm ball) | `lem:ballpotential` | `CERW.LimitShapes.norm_ball_potential` |
| Lemma 3.1 | `lem:local` | `CERW.LimitShapes.norm_local_time_potential` |
| Lemma 3.2 | `lem:freedman` | `CERW.LimitShapes.freedman_bound` |
| Lemma 3.3 | `lem:cell` | `CERW.LimitShapes.cell_gradient` |
| Lemma 3.4 | `lem:layer` | `CERW.LimitShapes.layer_potential` |
| Proposition 4.1 | `prop:coarse` | `CERW.LimitShapes.norm_coarse_bounds` |
| Proposition 5.1 | `prop:norm-shape` | `CERW.LimitShapes.norm_shape_rates` |
| Lemma 5.2 | `lem:contact` | `CERW.LimitShapes.contact_potential` |
| Proposition 6.1 (inner radius) | `prop:inner` | `CERW.LimitShapes.inner_radius` |
| Proposition 7.1 (outer radius) | `prop:stronger-outer` | `CERW.LimitShapes.outer_radius` |
| Lemma 7.2 | `lem:near-far` | `CERW.LimitShapes.near_far` |
| Theorem 8.1 (sum of the distances from the origin) | `thm:moment-fluctuations` | `CERW.LimitShapes.moment_fluctuations` |
| Lemma 8.2 | `lem:fixed-site-centering` | `CERW.LimitShapes.fixed_site_centering` |
| Theorem 8.3 (local times at fixed sites) | `thm:site-fluctuations` | `CERW.LimitShapes.site_fluctuations` |
| Lemma 9.1 | `lem:exp-deviation` | `CERW.LimitShapes.exp_deviation` |
| Proposition 9.2 | `prop:bulk-profile` | `CERW.LimitShapes.bulk_profile` |
| Lemma 9.3 | `lem:separated-brackets` | `CERW.LimitShapes.separated_brackets` |
| Proposition 9.4 (lower bounds for the radii) | `prop:log-lower` | `CERW.LimitShapes.log_lower_bounds` |

Four further registered declarations prove intermediate steps that the paper states in its text:
the distance-crossing bound, the common event of Section 5.1 with polynomially small exceptional
probability, and the contact and separated-bracket estimates on that event.
[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps every statement to the paper, and
[`PROOF.md`](PROOF.md) describes each proof.

## Standing assumptions and scope

1. **Nothing is assumed.** No theorem carries a cited result as a hypothesis
   ([`ASSUMPTIONS.md`](ASSUMPTIONS.md)).
2. **The model.** `CERW.IsCERW μ ε X` says that the process `X` has the law of the centrally
   excited walk with drift `ε`; the theorems hold for every such process on every probability
   space. The local time at a site counts the departures from it, and the range is the set of
   sites departed from by time `n`.
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
- **Kernel replay.** `tools/replay_kernel.sh` replays every declaration of `CERW` and of the
  modules of Lattice-Probability it imports in the Lean kernel, and is tested on a fixture that
  bypasses the kernel.
- **Pinned statements.** The bytes of every frozen statement are pinned by SHA-256 in
  [`ledger/current.yaml`](ledger/current.yaml), with the lines of the paper it states, and
  `tools/check_frozen_types.py` checks the elaborated types of the frozen statements.
- **Warning-free build.** The continuous-integration build rejects any warning.
- **Independent check of the statements.** The introduction's theorems are restated in
  [`CERWAudit/`](CERWAudit/) using mathlib alone, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the solutions
  prove them with only the three standard axioms, through the Lean kernel and the independent
  nanoda kernel. See [`CERWAudit/README.md`](CERWAudit/README.md).
- **Pinned toolchain.** Lean `v4.35.0-rc2`, mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` and
  Lattice-Probability `6d06eddaede1eb285cbe4327d14f7c310e695f9d`, recorded in
  [`lake-manifest.json`](lake-manifest.json).

## Size

About 155,000 lines of Lean in 661 modules (`CERW.lean` and `CERW/`), of which about 128,000
lines are code once comments and blank lines are removed, on top of mathlib and
Lattice-Probability. Both formalized sources are counted; the comparator surface under
`CERWAudit/` is not.

## Building

Install [elan](https://github.com/leanprover/elan); the toolchain is pinned in
[`lean-toolchain`](lean-toolchain). From a clone:

```bash
lake exe cache get
lake build             # the library
lake build CERWAudit   # the comparator challenges and solutions
```

`import CERW` loads the development. The checks run by the continuous integration need Python 3.10
or later:

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

`bash CERWAudit/check_standalone.sh --vocabulary` checks that each challenge elaborates on mathlib
alone and that its vocabulary matches the solution's. The workflow
[`comparator.yml`](.github/workflows/comparator.yml) runs
[leanprover/comparator](https://github.com/leanprover/comparator) on the four pairs, with nanoda
replay; [`CERWAudit/README.md`](CERWAudit/README.md) gives the commands to run it locally.

## Repository layout

```text
CERW/
  MainTheorems.lean   the introduction's theorems, stated in full
  LimitShapes/        the paper's statements (Frozen/), the common event of Section 5.1 and the proofs
  Frozen/             the statements of the two-author manuscript
  Model/              the walk, its law, local times and ranges
  Support/            the proofs of the papers' results
  Generic/            general results used in the proofs
  Meta/               axiom reports
CERWAudit/            the mathlib-only comparator challenges and their solutions
ledger/               current.yaml and manifest.yaml (statement hashes, paper lines, states) and
                      the paper excerpt beside each Lean statement (nl/)
paper/                centrally-excited-walks.tex, limit-shapes.tex, bibliography and figures
tools/                the checkers listed under Building
CORRESPONDENCE.md     paper ↔ Lean, statement by statement
PROOF.md              the proofs and the formalization conventions
CERTIFICATE-LIMIT-SHAPES.md, CERTIFICATE.md
                      generated records of the toolchain, the build and each statement's axioms
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and, for
auxiliary proof work, DeepSeek, under the direction of the authors. Every proof is checked by the
Lean kernel. The models and tooling are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee** and **Yuval Peres**. The paper is by Ahmed
Bou-Rabee, Tuan-Minh Nguyen, Yuval Peres and Arvind Singh. To cite the formalization, use
[`CITATION.cff`](CITATION.cff).

## License

The Lean code is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The paper sources
in [`paper/`](paper/) are included for reference and are not covered by this licence.

## Palomar preflight

The manually dispatched [Palomar full preflight](.github/workflows/palomar-preflight.yml)
calls Palomar's complete verifier at a pinned revision. Select the repository-relative
Comparator configuration to check. It records the dispatched commit and runs with
`mode: full` and `execution_profile: palomar-standard-v1`. Resolve the current Lean
minimum, source-module, Challenge-closure, licensing and metadata requirements before
dispatch. A passing preflight is advisory; it is separate from submission, editorial
review and a public registry record.

The selected Palomar compatibility revision updates public module interfaces and
uses the exact original Lattice-Probability snapshot with module interfaces and
existing proof API compatibility fixes. Frozen source statements and mathematical
definitions are retained. The full official preflight is scoped to the selected
Challenge/Solution pair at its exact dispatched commit.

Existing product-measurability and ergodicity proof calls use the corresponding
current Mathlib lemmas, retaining their original maps and hypotheses. The selected
preflight scope is its unchanged Challenge; other configurations are separate.
