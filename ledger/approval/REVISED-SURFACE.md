# Freeze of the statements of the revised paper

The registry records the revised paper at the exact source pin below. On 2026-10-06 the
author explicitly approved all five complete successor statements in the linked review packet.
The five replacements preserve the other 22 registered statements and all earlier valid proofs.
They add no node or External. The approval concerns these exact mathematical interfaces; the
verification certificate records the actual installed source and checked declarations.

**The author's rulings.** The work was authorized under gates G1–G8, and batches were to be frozen
under G7's standing approval.
- **G1:** the statements are declared final, and the revised text is pinned as
  `paper/limit-shapes.tex`, with its sha256 in `source_pin`.
- **G2:** the eight first-version nodes are relabelled.
- **G3:** of the four lemmas stated "on the event", `lem:crossing` and `lem:outer-crossing` are
  read deterministically, and `lem:contact` and `lem:separated-brackets` as probability bounds.
- **G4:** Theorem 1.3 is split into four parts.
- **G5:** the two Externals are those of the plan, after the sources were checked.
- **G7:** the batches are frozen under standing approval and presented in HANDOFF.md.

The rulings above are the historical record of the previous revision. The cited inputs have
subsequently been proved and discharged under D6/D7; no final registered root carries an open
cited-result binder.

## Revised registry

- **The pin.** `source_pin` is `paper/limit-shapes.tex`, sha256
  `c39feeaf71f83234fdd4b1e2fd6b4d6c739197b2c419c8ac1bb868ce8768c219`. Every one of its 24 labelled
  theorem-like environments is claimed by a node (`check_coverage`).
- **Theorem nodes.** There are **27**, one file each under `CERW/Frozen/`:
  - one per environment;
  - Theorem 1.3 as four nodes, `thm-sharp-radii`, `thm-sharp-radii-lil`, `thm-sharp-bulk` and
    `thm-sharp-width`, one per part (G4).
- **No open Externals.** The two cited martingale limit theorems — Hall–Heyde's central limit
  theorem and Stout's law of the iterated logarithm — are **proved** here
  (`CERW.Generic.Martingale.CLT.martingaleCLT_proved`, `CERW.Generic.Martingale.Lil.stout_upper`
  and `CERW.Generic.Martingale.LilAssembly.stout_lower`). The conditional assembly lemmas keep them
  as internal proof parameters (`hCLT`, `hLIL`), which the final registered roots supply proved; no
  final statement carries a cited hypothesis (`ASSUMPTIONS.md` is "Nothing"). The retired citation
  ids are recorded in `CORRESPONDENCE.md`; none is registered as an External.
- **Historical relabelling of first-version nodes (G2).** Their frozen text was unchanged; only the ids changed,
  and their `source:` now cites `paper/cerw-flat.tex` by line, with no label:
  - `thm-shape` → `ball-shape`;
  - `thm-fluctuations` → `fluctuation-bounds`;
  - `eq-hausdorff` → `hausdorff-bound`;
  - `lem-local` → `local-time-potential`;
  - `lem-geometry` → `potential-geometry`;
  - `lem-radial` → `radial-test`;
  - `prop-coarse` → `coarse-bounds`.

## Author-approved successors, 2026-10-06

The author approved the exact five statements after independent source, carrier, body and
consumption review. Each replaces its predecessor under the same id and export.

| id | node | version | revised interface |
|---|---|---|---|
| S1 | `thm-sharp-width` | 4 | all (iv)(a), (b), (c), including the numerical small-ball bound for every `a ≥ 0` |
| S2 | `lem-crossing` | 2 | the source vector event, its uniform probability estimate and its crossing implication |
| S3 | `lem-outer-crossing` | 2 | the finite radial-family event and separate arbitrary-vector deterministic implication |
| S4 | `lem-contact` | 2 | nearest-projection existence/uniqueness, the literal seven-estimate event and the contact estimate almost surely on it |
| S5 | `lem-exp-deviation` | 2 | finite-horizon adaptation/integrability and almost-sure start/increment bounds, with both tails and the many-site bound |

For an arbitrary walk law the legal-path conclusions are almost sure. Typed legal paths are
used explicitly for pathwise implications. Legality is not added to the seven-estimate event.
The precise complete contracts and source quotations are `ledger/nl/<id>.tex`.
`lem:separated-brackets` retains its approved probability reading; no sixth approval is needed.

## Preserved support outside the registry

Five Lean modules of the earlier registration are preserved support and are no longer rows of the
table: `CERW/Support/Legacy/{LocalTimePotential,CoarseBounds}.lean` are the Euclidean cases of
`lem:local` and `prop:coarse` (the pinned paper states these two results for a norm, as the rows
`lem-local` and `prop-coarse`), and
`CERW/Support/Legacy/{NormPotentialGeometry,NormRadialTest,MoreauCap}.lean` carry the statements of
`lem:geometry`, `lem:radial` and `lem:cap` of the previous pin of the paper, which the pinned paper
does not state. Their declarations, types and proofs are those of commit `f7696856`.

These exports remain available as proved support. `BulkProfile` and `SharpWidth` consume the
Euclidean legacy exports, and the `NormPotential`/`NormRates` guard modules consume the retired norm
machinery. The registered norm coarse theorem applies
`CoarseVolume.norm_coarse_bounds_closed` directly. The current frozen assemblies and source-event
producers are recorded separately.

The revised source's Newton/radial, asymmetric-gauge and planar real-profile obligations are
supplied by dedicated support modules outside the registry
(`CERW/Support/Norm/GaugeRadialNewtonConvolution.lean`,
`CERW/Support/Norm/GaugeSourceContactConsequences.lean`,
`CERW/Support/Outer/PlanarRealProfileFiltration.lean`); none is a registered node or a frozen
statement.

## Evidence before the freeze

- **Readings.** Four independent refute-first readings covered the registered nodes:
  - `ledger/audits/prefreeze-reading-introduction.md`;
  - `ledger/audits/prefreeze-reading-norm-setup.md`;
  - `ledger/audits/prefreeze-reading-norm-shape.md`;
  - `ledger/audits/prefreeze-reading-limit-laws.md`.

  Two DEFECTs were found and fixed before the freeze. Both were the same parenthesization of the
  scaled cell set in the volume clauses of Theorem 1.2 and Proposition 6.1.
- **The cited results.** The source check is `ledger/audits/external-sources.md`. Both cited
  theorems were checked against the literature and are now proved in this repository.
- **NL twins:** `ledger/nl/<id>.tex`.
- **Non-vacuity:**
  - `CERW.Support.Main.exists_norm_realization`: the walk with norm `Ψ` exists for every norm and
    every choice of subgradients;
  - `CERW.Support.Main.euclidean_norm_hypotheses`: the Euclidean norm meets the norm hypotheses;
  - `CERW.Support.Drift.exists_isDriftCERW`.
- **Consumption.** The registered theorems apply complete proved support. The five revised interfaces use
  `RevisedPaper.sharp_width_extended`, `crossing_on_vector_event`,
  `outer_crossing_on_source_events`, `contact_on_source_carrier` and
  `Lower.exp_deviation_ae_upTo`. Internal conditional assembly parameters are supplied by
  independently proved producers. `SourceEvents` proves the predecessor consequences needed
  by existing consumers without changing their statements.

## Proof status of the installed types

All 27 registered nodes are **PROVED**: each has a complete proof whose axiom closure
contains no `sorryAx` (`ledger/holes.json` records no open hole; `check_axioms` inspects 27 rows).
The five author-approved successors are installed under their updated versions.

## Verification certificate

`CERTIFICATE.md` is generated from actual checks of the revised source and its 27 registered
roots. The previous revision at `43f17b80…` had 32 registered roots and source pin
`04d3cbfad3cce1b373752f3cc2db3c7e2c34c155cea0727a3ddeb0b0e21c7f59`; its certificate and
proof evidence remain historical evidence for that scope. The current certificate is not made
by editing those old receipts.


