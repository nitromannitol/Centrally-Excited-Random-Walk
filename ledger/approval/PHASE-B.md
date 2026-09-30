# Phase B approval packet: the frozen surface

For the author's approval. Nothing below is frozen yet: `freeze.py` runs only after this packet is
approved. Every declaration was elaborated at the pinned toolchain against the committed vocabulary
(`CERW/Model/*`). The text comes from the audited file `scratch/Anchors.lean` (sha256 `0ca9ad7c…`).

**What happens on approval.** Each declaration goes into its own file below. The file gets the
imports it needs and a docstring quoting the paper, and the declaration sits between
`-- FROZEN-STATEMENT-BEGIN/END` markers. The theorems get the single body `by sorry`, registered as
`DRAFT_SORRY`. The External is registered as `FROZEN`. The block bytes are exactly the declaration
text shown here.

## Gate evidence

* NL twins: `ledger/nl/<id>.tex`.
* REVIEWED readings and hazard declarations: `ledger/readings.yaml`.
* Refute-first audit (fresh instance): `ledger/audits/prefreeze-refute-first-audit.md`. All PASS, EXCESS 0
  everywhere, no DEFECT, one CONCERN (below).
* Three independent readings, all "no discrepancy": `ledger/audits/prefreeze-reading-{A,B,C}.md`.
* Consumption prototypes: the `example` blocks of the audited file, which elaborate.
* Non-vacuity: `CERW.Support.Guards.exists_cerw_realization`, compiled with clean axioms.

## One ruling requested: the planar remark in `eq-hausdorff`

The paper says (cerw.tex:224-225): "The inner-radius error in the plane is at most
$Cn^{1/6}\sqrt{\log(n+2)}$ in lattice units." There are two readings:

* **(A) One-sided, as drafted.** `B(0, aN − Cn^{1/6}√L) ∩ ℤ² ⊆ A_n`: the inner inclusion of
  eq:sandwich at d = 2.
* **(B) Two-sided, recommended.** Reading (A), and also that some unvisited site lies within
  `aN + Cn^{1/6}√L`. This is what "error" says, and it is exactly eq:inradius at d = 2,
  `|b − aN| ≤ CNQ = Cn^{1/6}√L`, which the proof establishes anyway through the contact site `z`.
  It is strictly stronger than (A) and costs nothing extra. It elaborates as
  `scratch/AnchorsTwoSided.lean`; the only change is the conjunct shown after the declarations.

**Recommendation: (B).** Under the standing delegation, (B) is frozen unless the author says
otherwise.

## Common header of the transient file (each frozen file imports what it uses)

```lean
import CERW.Model
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.MetricSpace.HausdorffDistance
import LatticeProb.Walk.SimpleTransfer
import LatticeProb.Walk.SRW

universe u

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)
```

## `ext-lattice-kernel`: `CERW.External.LatticePotentialKernel`

* File: `CERW/External/LatticePotentialKernel.lean`
* Kind: definition
* State on registration: `FROZEN`
* Manifest source: `cerw-flat.tex:345-359 (eq:kernel-asymptotics, local-times.tex:5-19; Lawler–Limic Thm 4.3.1, Cor 4.3.3, Thm 4.4.4)`

```lean
def CERW.External.LatticePotentialKernel (d : ℕ) : Prop :=
  (d = 2 →
    ∃ b : Site 2 → ℝ,
      (∀ x, Tendsto (fun M : ℕ => LatticeProb.srwGreen 2 M 0 - LatticeProb.srwGreen 2 M x)
        atTop (𝓝 (b x))) ∧
      ∃ κ C R : ℝ, 1 ≤ R ∧ ∀ x : Site 2, R ≤ euclidNorm x →
        |b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤ C * euclidNorm x ^ (-2 : ℝ)) ∧
  (3 ≤ d →
    ∃ C R : ℝ, 1 ≤ R ∧ ∀ x : Site d, R ≤ euclidNorm x →
      |LatticeProb.srwGreenInf d x
          - 2 / (((d : ℝ) - 2) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)
            * euclidNorm x ^ (2 - (d : ℝ))|
        ≤ C * euclidNorm x ^ (-(d : ℝ)))
```

## `thm-shape`: `CERW.Frozen.ball_shape`

* File: `CERW/Frozen/BallShape.lean`
* Kind: theorem
* State on registration: `DRAFT_SORRY`
* Manifest source: `cerw-flat.tex:135-160 (label thm:shape)`

```lean
theorem CERW.Frozen.ball_shape {d : ℕ} (hd : 2 ≤ d)
    (hK : CERW.External.LatticePotentialKernel d)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < a → ∀ᶠ n in atTop,
        {x : Site d | euclidNorm x < (a - η) * N n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆ ↑(CERW.visitedRange (X · ω) n) ∧
        (↑(CERW.visitedRange (X · ω) n) : Set (Site d)) ⊆
          {x | euclidNorm x < (a + η) * N n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) / N n - 2 * d * ε * max (a - euclidNorm x / N n) 0|
          ≤ η) ∧
      Tendsto (fun n => ((CERW.visitedRange (X · ω) n).card : ℝ) / N n ^ d) atTop
        (𝓝 (ωd * a ^ d)) ∧
      (∀ x : Site d,
        Tendsto (fun n => (CERW.localTime (X · ω) n x : ℝ) / N n) atTop (𝓝 (2 * d * ε * a))) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x) := by
  sorry
```

## `thm-fluctuations`: `CERW.Frozen.fluctuation_bounds`

* File: `CERW/Frozen/FluctuationBounds.lean`
* Kind: theorem
* State on registration: `DRAFT_SORRY`
* Manifest source: `cerw-flat.tex:186-213 (label thm:fluctuations)`

```lean
theorem CERW.Frozen.fluctuation_bounds {d : ℕ} (hd : 2 ≤ d)
    (hK : CERW.External.LatticePotentialKernel d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let N : ℕ → ℝ := fun n => (n : ℝ) ^ ((1 : ℝ) / (d + 1))
    let L : ℕ → ℝ := fun n => Real.log (n + 2)
    let Q : ℕ → ℝ := fun n =>
      if d = 2 then (L n / N n) ^ ((1 : ℝ) / 2) else (L n / N n) ^ ((d : ℝ) / (2 * d - 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      {x : Site d | euclidNorm x < (a - C * Q n) * N n} ⊆ ↑(CERW.departureRange Y n) ∧
      (↑(CERW.departureRange Y n) : Set (Site d)) ⊆ ↑(CERW.visitedRange Y n) ∧
      (↑(CERW.visitedRange Y n) : Set (Site d)) ⊆
        {x | euclidNorm x < (a + C * Q n ^ ((1 : ℝ) / d) * L n) * N n} ∧
      volume (((N n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a)
          + ENNReal.ofReal |((CERW.departureRange Y n).card : ℝ) / N n ^ d - ωd * a ^ d|
        ≤ ENNReal.ofReal (C * Q n) ∧
      ∀ x : Site d,
        |(CERW.localTime Y n x : ℝ) / N n - 2 * d * ε * max (a - euclidNorm x / N n) 0|
          ≤ C * Q n ^ ((1 : ℝ) / d)
    (∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Good C (X · ω) n) := by
  sorry
```

## `eq-hausdorff`: `CERW.Frozen.hausdorff_bound`

* File: `CERW/Frozen/HausdorffBound.lean`
* Kind: theorem
* State on registration: `DRAFT_SORRY`
* Manifest source: `cerw-flat.tex:215-225 (label eq:hausdorff and the planar remark)`

```lean
theorem CERW.Frozen.hausdorff_bound {d : ℕ} (hd : 2 ≤ d)
    (hK : CERW.External.LatticePotentialKernel d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∃ n₀ : ℕ, 0 < C ∧ 0 < n₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        let L : ℝ := Real.log (n + 2)
        μ {ω | ¬ (Metric.hausdorffEDist
                    ((fun x => N⁻¹ • CERW.toSpace x) '' ↑(CERW.visitedRange (X · ω) n))
                    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) a)
                  ≤ ENNReal.ofReal (C * (if d = 2 then (n : ℝ) ^ (-(1 : ℝ) / 12) * L ^ ((5 : ℝ) / 4)
                      else (n : ℝ) ^ (-(1 : ℝ) / ((d + 1) * (2 * d - 1)))
                        * L ^ ((2 * d : ℝ) / (2 * d - 1)))) ∧
                  (d = 2 → {x : Site d | euclidNorm x < a * N - C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L} ⊆ ↑(CERW.departureRange (X · ω) n)))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  sorry
```

## `lem-local`: `CERW.Frozen.local_time_potential`

* File: `CERW/Frozen/LocalTimePotential.lean`
* Kind: theorem
* State on registration: `DRAFT_SORRY`
* Manifest source: `cerw-flat.tex:397-414 (label lem:local, local-times.tex:57-74)`

```lean
theorem CERW.Frozen.local_time_potential {d : ℕ} (hd : 2 ≤ d)
    (hK : CERW.External.LatticePotentialKernel d) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p →
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let L : ℝ := Real.log (n + 2)
        let lam : ℝ := if d = 2 then L ^ 2 else L
        let e : ℝ → ℝ := fun m =>
          if d = 2 then Real.sqrt m * L + L else Real.sqrt (m * L) + L
        μ {ω | ¬ ((CERW.maxLocalTime (X · ω) n : ℝ)
                    ≤ Cd * ε * ((CERW.departureRange (X · ω) n).card : ℝ) ^ ((1 : ℝ) / d)
                      + C * lam ∧
                  (∀ s t : ℕ, s < t → t ≤ n →
                    (CERW.intervalMax (X · ω) s t : ℝ)
                      ≤ Cd * ε * (CERW.freshCount (X · ω) s t : ℝ) ^ ((1 : ℝ) / d) + C * lam) ∧
                  ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
                    |CERW.cellLocalTime (X · ω) n y
                        - CERW.potential d ε (CERW.cellSet (X · ω) n) y|
                      ≤ C * e (CERW.maxLocalTime (X · ω) n))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  sorry
```

## `lem-geometry`: `CERW.Frozen.potential_geometry`

* File: `CERW/Frozen/PotentialGeometry.lean`
* Kind: theorem
* State on registration: `DRAFT_SORRY`
* Manifest source: `cerw-flat.tex:497-514 (label lem:geometry, local-times.tex:157-174)`

```lean
theorem CERW.Frozen.potential_geometry {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ ε : ℝ, 0 < ε →
      (∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
        let R : ℝ := (volume D).toReal
        (∀ y, |CERW.potential d ε D y| ≤ Cd * ε * R ^ ((1 : ℝ) / d)) ∧
        (∀ y z, |CERW.potential d ε D y - CERW.potential d ε D z|
            ≤ Cd * ε * R ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
        (∀ s : ℝ, 0 < s →
          (d * ωd)⁻¹ * ∫ θ, CERW.potential d ε D (s • (θ : EuclideanSpace ℝ (Fin d)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
            = 2 * d * ε * CERW.tail d D s)) ∧
      ∀ b : ℝ, 0 < b → ∀ y : EuclideanSpace ℝ (Fin d),
        CERW.potential d ε (Metric.ball 0 b) y = 2 * d * ε * max (b - ‖y‖) 0 := by
  sorry
```

## `lem-radial`: `CERW.Frozen.radial_test`

* File: `CERW/Frozen/RadialTest.lean`
* Kind: theorem
* State on registration: `DRAFT_SORRY`
* Manifest source: `cerw-flat.tex:581-601 (label lem:radial, coarse-radius.tex:38-58)`

```lean
theorem CERW.Frozen.radial_test {d : ℕ} (hd : 2 ≤ d)
    (hK : CERW.External.LatticePotentialKernel d) :
    let bd : ℕ := ⌈Real.sqrt d / 2⌉₊ + 6
    ∃ r₀ : ℕ, 2 * bd < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p →
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let L : ℝ := Real.log (n + 2)
        μ {ω | ¬ ∀ r : ℕ, r₀ ≤ r → r ≤ n →
            CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) + bd)
              ≤ C * CERW.shellMax (X · ω) n r
                  * (CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) - bd)
                    - CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) + bd))
                + C * (Real.sqrt ((CERW.maxLocalTime (X · ω) n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ))
                        * CERW.tail d (CERW.cellSet (X · ω) n) ((r : ℝ) - bd) * L)
                    + (r : ℝ) ^ (1 - (d : ℝ)) * L)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  sorry
```

## `prop-coarse`: `CERW.Frozen.coarse_bounds`

* File: `CERW/Frozen/CoarseBounds.lean`
* Kind: theorem
* State on registration: `DRAFT_SORRY`
* Manifest source: `cerw-flat.tex:547-561 (label prop:coarse, coarse-radius.tex:4-18)`

```lean
theorem CERW.Frozen.coarse_bounds {d : ℕ} (hd : 2 ≤ d)
    (hK : CERW.External.LatticePotentialKernel d) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
        μ {ω | ¬ (c * N ^ d ≤ ((CERW.departureRange (X · ω) n).card : ℝ) ∧
                  ((CERW.departureRange (X · ω) n).card : ℝ) ≤ C * N ^ d ∧
                  c * N ≤ (CERW.maxLocalTime (X · ω) n : ℝ) ∧
                  (CERW.maxLocalTime (X · ω) n : ℝ) ≤ C * N ∧
                  c * N ≤ CERW.maxRadius (X · ω) n ∧ CERW.maxRadius (X · ω) n ≤ C * N)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  sorry
```

## Variant (B) of the second conjunct of `eq-hausdorff`

```lean
                  (d = 2 → {x : Site d | euclidNorm x < a * N - C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
                    ∃ x : Site d, euclidNorm x < a * N + C * (n : ℝ) ^ ((1 : ℝ) / 6)
                      * Real.sqrt L ∧ x ∉ CERW.departureRange (X · ω) n))}
```
