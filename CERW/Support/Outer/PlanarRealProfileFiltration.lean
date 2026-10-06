import CERW.Support.Outer.PlanarRealProfileAE

/-!
# The finite-prefix event and the legal carrier of the full real-point bundle

`CERW.Support.Outer.PlanarRealProfileAE` assembles, for the centrally excited random walk in the
plane, the almost-sure eventual bundle `PlanarRealDisplays` of the real-point displays of the last
subsection of the outer-radius section (and its version inside the literal event `E7` of
Section 5.1). This module closes the interface of that bundle with the finite-prefix structure of
the walk and with its legal carrier.

* `planarRealProfile_congr` and `planarRealDisplays_congr`: the real-point profile and the bundle at
  time `n` depend only on the positions `X_0, …, X_n`. Every object of the displays (the cell set
  `D_n`, the inner and outer radii, the cell local time, and through them the excess potential) is
  congruent under such an equality; the finite-prefix congruences of `Section5Localization` are
  reused through `open private`.
* `measurableSet_planarRealDisplays_filtration`: the event `{ω | PlanarRealDisplays …(X · ω) n}`
  is the preimage of a set of finite paths under the past path, a countable set, hence belongs to
  `σ(X_0, …, X_n)`; no measurability hypothesis on the uncountable conjunction over real points is
  made. `measurableSet_E7_filtration_of_isCERW` re-exposes the existing measurability of `E7` for
  `IsCERW` walks; `E7` keeps its seven clauses and gains no legality field.
* `planar_real_displays_ae_carrier` carries the whole bundle, including the inner radius bound, to
  the legal carrier: with constants `K` and `C` chosen before the probability space, the walk, the
  sample point and the time, almost surely the carrier agrees with the walk at every time, and for
  all large `n` the sample point is in `E7` of the walk and of the carrier with the bundle at both
  paths. Agreement is almost sure, not pointwise at every sample point: at the illegal sample
  points the carrier is a fixed straight path, a device that carries no meaning of its own and is
  never used as a characterization or as an anchor of a source statement.
* `PlanarRealWitness` and `planarRealDisplays_witness` extract, from the bundle at a path from the
  origin, the objects used by the consumers: positive-area excess set, integrable kernel, finite
  supremum, real interior and exterior non-lattice points; `exists_realization_planar_real_carrier`
  applies everything at an actual planar walk with `ε = 1/4`.

The module uses `CERW.Support.Outer.PlanarRealProfileAE`, whose independent review is pending; no
statement here is a premise of a source theorem.
-/

universe u

open MeasureTheory Filter Topology
open scoped symmDiff
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.PlanarRealFiltration

open CERW CERW.Support.Law CERW.Support.Outer.PlanarReal CERW.Support.Outer.PlanarRealAE
  CERW.Support.Outer.SourceDisplays CERW.Support.Norm.ContactEvent
  CERW.Support.Norm.Section5Localization
open private cellSet_congr cellLocalTime_congr maxRadius_congr
  from CERW.Support.Norm.Section5Localization
open private toSpace_ne_of_not_int quarter_ne_int norm_smul_single
  from CERW.Support.Outer.PlanarRealProfile

variable {d : ℕ}

/-! ## The displays depend only on the finite prefix -/

/-- The real-point profile at time `n` depends only on the positions up to time `n`: the cell set,
the cell local time, the inner radius and the outer radius are congruent. -/
theorem planarRealProfile_congr {ε C : ℝ} {x y : ℕ → Site d} {n : ℕ}
    (h : ∀ j ≤ n, x j = y j) :
    PlanarRealProfile d ε C x n ↔ PlanarRealProfile d ε C y n := by
  have hcell : cellSet x n = cellSet y n := cellSet_congr h
  have hclt : cellLocalTime x n = cellLocalTime y n := cellLocalTime_congr h
  have hmax : maxRadius x n = maxRadius y n := maxRadius_congr h
  have hinn : innerRadius x n = innerRadius y n := by
    unfold innerRadius
    rw [hcell]
  simp only [PlanarRealProfile, hcell, hclt, hmax, hinn]

/-- The bundle of the real-point displays at time `n` depends only on the positions up to time
`n`. -/
theorem planarRealDisplays_congr {ε C : ℝ} {x y : ℕ → Site d} {n : ℕ}
    (h : ∀ j ≤ n, x j = y j) :
    PlanarRealDisplays d ε C x n ↔ PlanarRealDisplays d ε C y n := by
  have hcell : cellSet x n = cellSet y n := cellSet_congr h
  have hclt : cellLocalTime x n = cellLocalTime y n := cellLocalTime_congr h
  have hinn : innerRadius x n = innerRadius y n := by
    unfold innerRadius
    rw [hcell]
  simp only [PlanarRealDisplays, planarRealProfile_congr h, hclt, hinn]

/-- The event of the bundle is the preimage, under the past path up to time `n`, of a set of
finite paths. -/
theorem planarRealDisplays_eq_preimage {Ω : Type*} (X : ℕ → Ω → Site d) (ε C : ℝ) (n : ℕ) :
    {ω | PlanarRealDisplays d ε C (fun j => X j ω) n} =
      pastPath X n ⁻¹' {p | PlanarRealDisplays d ε C (extendPath p) n} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  exact planarRealDisplays_congr fun j hj => (extendPath_pastPath X hj ω).symm

/-- The event of the real-point profile is the preimage of a set of finite paths. -/
theorem planarRealProfile_eq_preimage {Ω : Type*} (X : ℕ → Ω → Site d) (ε C : ℝ) (n : ℕ) :
    {ω | PlanarRealProfile d ε C (fun j => X j ω) n} =
      pastPath X n ⁻¹' {p | PlanarRealProfile d ε C (extendPath p) n} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  exact planarRealProfile_congr fun j hj => (extendPath_pastPath X hj ω).symm

/-- **Finite-prefix measurability of the bundle.** The event that the bundle of the real-point
displays holds at time `n` belongs to `ℱ_n = σ(X_0, …, X_n)`. -/
theorem measurableSet_planarRealDisplays_filtration {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ j, Measurable (X j)) (ε C : ℝ) (n : ℕ) :
    MeasurableSet[pathFiltration hX n] {ω | PlanarRealDisplays d ε C (fun j => X j ω) n} := by
  rw [planarRealDisplays_eq_preimage]
  exact ⟨_, (Set.to_countable _).measurableSet, rfl⟩

/-- **Finite-prefix measurability of the real-point profile.** -/
theorem measurableSet_planarRealProfile_filtration {Ω : Type*} [MeasurableSpace Ω]
    {X : ℕ → Ω → Site d} (hX : ∀ j, Measurable (X j)) (ε C : ℝ) (n : ℕ) :
    MeasurableSet[pathFiltration hX n] {ω | PlanarRealProfile d ε C (fun j => X j ω) n} := by
  rw [planarRealProfile_eq_preimage]
  exact ⟨_, (Set.to_countable _).measurableSet, rfl⟩

/-- The event of the bundle is measurable. -/
theorem measurableSet_planarRealDisplays {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ j, Measurable (X j)) (ε C : ℝ) (n : ℕ) :
    MeasurableSet {ω | PlanarRealDisplays d ε C (fun j => X j ω) n} :=
  (pathFiltration hX).le n _ (measurableSet_planarRealDisplays_filtration hX ε C n)

/-! ### Wrappers for centrally excited random walk -/

/-- **`E7` belongs to `ℱ_n` for centrally excited random walk.** The literal event of Section 5.1
for the Euclidean norm and the drift field `x ↦ u_x`, with its seven clauses and no legality
field, belongs to `σ(X_0, …, X_n)`. -/
theorem measurableSet_E7_filtration_of_isCERW {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ε : ℝ} {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (K : EventConstants) (n : ℕ) :
    MeasurableSet[pathFiltration hX.measurable n]
      (E7 (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n) :=
  measurableSet_E7_filtration hX.measurable _ ε _ K n

/-- **The bundle belongs to `ℱ_n` for centrally excited random walk.** -/
theorem measurableSet_planarRealDisplays_filtration_of_isCERW {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ε : ℝ} {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (C : ℝ) (n : ℕ) :
    MeasurableSet[pathFiltration hX.measurable n]
      {ω | PlanarRealDisplays d ε C (fun j => X j ω) n} :=
  measurableSet_planarRealDisplays_filtration hX.measurable ε C n

/-! ## The bundle on the legal carrier -/

/-- At a sample point where the carrier agrees with the path at every time, the carrier is in the
event `E7` exactly when the path is. -/
theorem mem_E7_legalCarrier_iff {Ω : Type*} {X : ℕ → Ω → Site d} (hd : 1 ≤ d) {ω : Ω}
    (h : ∀ j, legalCarrier hd X j ω = X j ω) (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (ε : ℝ)
    (ξ : Site d → EuclideanSpace ℝ (Fin d)) (K : EventConstants) (n : ℕ) :
    ω ∈ E7 Ψ ε ξ K (legalCarrier hd X) n ↔ ω ∈ E7 Ψ ε ξ K X n := by
  have hp : (fun j => legalCarrier hd X j ω) = fun j => X j ω := funext h
  simp only [E7, Set.mem_setOf_eq, hp]

/-- **The legal carrier of a centrally excited random walk is a centrally excited random walk.**
This is the transport of the law along the almost-sure equality (`isDriftCERW_legalCarrier`, which
compares the laws of the first `n + 1` positions through the full cylinder events). -/
theorem isCERW_legalCarrier {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ε : ℝ}
    {X : ℕ → Ω → Site d} (hd : 1 ≤ d) (hX : IsCERW μ ε X) :
    IsCERW μ ε (legalCarrier hd X) :=
  (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε _).2
    (isDriftCERW_legalCarrier hd ((CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).1 hX))

/-- **The full bundle on the legal carrier.** Let `0 < ε < 1/2`. There are constants `K` of the
event `E7` and `C`, chosen before the probability space, the walk, the sample point and the time,
such that for every centrally excited random walk `X` in the plane:

* `E7` and the event of the bundle, for the walk and for its legal carrier, belong to the
  respective `σ`-algebras generated by the first `n + 1` positions;
* the legal carrier is again a centrally excited random walk (`isCERW_legalCarrier`), the illegal
  sample points are null, and the carrier agrees with the walk at every time almost surely (not at
  every sample point);
* almost surely, for all large `n`, the sample point is in `E7` and has `PlanarRealDisplays` for
  the walk, and the same holds for the carrier, with the sharp inner radius bound.

The carrier statement is the original statement transported along the almost-sure equality. -/
theorem planar_real_displays_ae_carrier {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ)) :
    ∃ (K : EventConstants) (C : ℝ), 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2) (hX : IsCERW μ ε X),
        (∀ n : ℕ, MeasurableSet[pathFiltration hX.measurable n]
          (E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n)) ∧
        (∀ n : ℕ, MeasurableSet[pathFiltration hX.measurable n]
          {ω | PlanarRealDisplays 2 ε C (fun j => X j ω) n}) ∧
        (∀ n : ℕ, MeasurableSet[pathFiltration
            (fun j => legalCarrier_measurable (by norm_num : 1 ≤ 2) hX.measurable j) n]
          (E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K
            (legalCarrier (by norm_num : 1 ≤ 2) X) n)) ∧
        (∀ n : ℕ, MeasurableSet[pathFiltration
            (fun j => legalCarrier_measurable (by norm_num : 1 ≤ 2) hX.measurable j) n]
          {ω | PlanarRealDisplays 2 ε C (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n}) ∧
        IsCERW μ ε (legalCarrier (by norm_num : 1 ≤ 2) X) ∧
        (∀ᵐ ω ∂μ, ω ∈ legalSet X) ∧
        (∀ᵐ ω ∂μ, ∀ j, legalCarrier (by norm_num : 1 ≤ 2) X j ω = X j ω) ∧
        (∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K X n ∧
          PlanarRealDisplays 2 ε C (fun j => X j ω) n) ∧
        (∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) ε (fun z => unitDir (toSpace z)) K
              (legalCarrier (by norm_num : 1 ≤ 2) X) n ∧
            PlanarRealDisplays 2 ε C (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n) := by
  obtain ⟨K, C, hC, hall⟩ := planar_real_displays_ae_on_E7.{u} hε hεd
  refine ⟨K, C, hC, fun μ _ X hX => ?_⟩
  obtain ⟨hleg, hev⟩ := hall μ X hX
  have hmeas : ∀ j, Measurable (legalCarrier (by norm_num : 1 ≤ 2) X j) := fun j =>
    legalCarrier_measurable (by norm_num : 1 ≤ 2) hX.measurable j
  have hceq : ∀ᵐ ω ∂μ, ∀ j, legalCarrier (by norm_num : 1 ≤ 2) X j ω = X j ω :=
    legalCarrier_ae_eq (by norm_num : 1 ≤ 2)
      ((CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).1 hX)
  refine ⟨measurableSet_E7_filtration_of_isCERW hX K,
    measurableSet_planarRealDisplays_filtration_of_isCERW hX C,
    measurableSet_E7_filtration hmeas _ ε _ K,
    measurableSet_planarRealDisplays_filtration hmeas ε C, isCERW_legalCarrier (by norm_num) hX,
    hleg, hceq, hev, ?_⟩
  filter_upwards [hceq, hev] with ω hω hωn
  filter_upwards [hωn] with n hn
  have hp : (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) = fun j => X j ω := funext hω
  refine ⟨(mem_E7_legalCarrier_iff (by norm_num : 1 ≤ 2) hω _ ε _ K n).2 hn.1, ?_⟩
  rw [hp]
  exact hn.2

/-! ## Consumption at an actual planar walk -/

/-- **The objects extracted from the bundle at a path.** For a planar path `Y`, a time `n` and a
constant `C`, with `ε = 1/4`, `b = R_in(n)`, `E = D_n ∖ B(0, b)` and `Z = √r_n (log n)^{3/2}`:
`b ≥ 1/2`; `E` is measurable, bounded and of positive area; the potential integrand is integrable
on `E` at every real point and `|U_E|` has a finite supremum; the real point `e₁/4`, which is not a
lattice site, lies in `B(0, b)` with the excess potential bound and both forms of the inner
estimate; and a real point beyond `b + w`, which is not a lattice site, has `ℓ~_n = 0`, cone
`≤ C Z` and the uniform bound. -/
def PlanarRealWitness (C : ℝ) (Y : ℕ → Site 2) (n : ℕ) : Prop :=
  1 / 2 ≤ innerRadius Y n ∧
  MeasurableSet (cellSet Y n \
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius Y n)) ∧
  Bornology.IsBounded (cellSet Y n \
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius Y n)) ∧
  0 < volume (cellSet Y n \
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius Y n)) ∧
  BddAbove (Set.range fun z : EuclideanSpace ℝ (Fin 2) =>
    |potential 2 (1 / 4 : ℝ) (cellSet Y n \
      Metric.ball 0 (innerRadius Y n)) z|) ∧
  (∀ y : EuclideanSpace ℝ (Fin 2), IntegrableOn
    (fun v : EuclideanSpace ℝ (Fin 2) => inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ 2)
    (cellSet Y n \
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius Y n))) ∧
  (∃ y₁ : EuclideanSpace ℝ (Fin 2), ‖y₁‖ < innerRadius Y n ∧
    (∀ x : Site 2, toSpace x ≠ y₁) ∧
    potential 2 (1 / 4 : ℝ) (cellSet Y n \
      Metric.ball 0 (innerRadius Y n)) y₁ ≤
      C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2)) ∧
    |cellLocalTime Y n y₁ -
        2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₁‖) 0| ≤
      C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2)) ∧
    |cellLocalTime Y n y₁ -
        2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₁‖) 0| ≤
      C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2) +
        |innerRadius Y n - sourceRadius 2 (1 / 4 : ℝ) n|)) ∧
  (∃ y₂ : EuclideanSpace ℝ (Fin 2),
    innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt (2 : ℕ)) < ‖y₂‖ ∧
    (∀ x : Site 2, toSpace x ≠ y₂) ∧
    cellLocalTime Y n y₂ = 0 ∧
    2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₂‖) 0 ≤
      C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2)) ∧
    |cellLocalTime Y n y₂ -
        2 * (2 : ℕ) * (1 / 4 : ℝ) * max (sourceRadius 2 (1 / 4 : ℝ) n - ‖y₂‖) 0| ≤
      C * (Real.sqrt (sourceRadius 2 (1 / 4 : ℝ) n) * Real.log n ^ ((3 : ℝ) / 2)))

/-- **The bundle at a path from the origin yields the witnesses.** For a planar path from the origin
and `n ≥ 1`, the bundle with `ε = 1/4` implies `PlanarRealWitness`: the inner radius is at least
`1/2`, the excess set has positive area (`volume_cellSet_diff_ball_innerRadius_pos`), its kernel
is integrable (`integrableOn_potentialIntegrand`) and `|U_E|` is bounded (`bddAbove_abs_potential`),
and the points `e₁/4` and `(b + w + 1/3) e₁ + e₂/4` satisfy the displays. -/
theorem planarRealDisplays_witness {C : ℝ} {Y : ℕ → Site 2} {n : ℕ} (h0 : Y 0 = 0) (hn : 1 ≤ n)
    (hD : PlanarRealDisplays 2 (1 / 4 : ℝ) C Y n) : PlanarRealWitness C Y n := by
  have hb := half_le_innerRadius (by omega : 1 ≤ 2) Y n hn h0
  have hw := width_nonneg (d := 2) (by omega) Y n
  have hEm : MeasurableSet (cellSet Y n \
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius Y n)) :=
    (CERW.Support.Occupation.measurableSet_cellSet Y n).diff measurableSet_ball
  have hEb : Bornology.IsBounded (cellSet Y n \
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (innerRadius Y n)) :=
    (Metric.isBounded_ball.subset
      (CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ 2) Y n)).subset
      Set.sdiff_subset
  have hvol := volume_cellSet_diff_ball_innerRadius_pos (d := 2) le_rfl Y n hn h0
  have hbdd := bddAbove_abs_potential (d := 2) (by omega) (by norm_num : (0 : ℝ) ≤ 1 / 4) hEm hEb
  refine ⟨hb, hEm, hEb, hvol, hbdd,
    fun y => CERW.Support.Geometry.integrableOn_potentialIntegrand (by omega) hEm
      hEb.measure_lt_top.ne y, ?_, ?_⟩
  · refine ⟨(1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_, ?_, ?_⟩
    · rw [norm_smul_single, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith
    · intro x
      refine toSpace_ne_of_not_int (0 : Fin 2) fun m => ?_
      have h10 : ((1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 = 1 / 4 := by
        simp
      rw [h10]
      exact quarter_ne_int m
    · have hy1b : ‖(1 / 4 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)‖ ≤
          innerRadius Y n := by
        rw [norm_smul_single, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        linarith
      exact ⟨hD.1.1 _ (hy1b.trans (le_add_of_nonneg_right hw)), hD.2.2.1 _ hy1b,
        hD.1.2.1 _ hy1b⟩
  · obtain ⟨y₂, hy20, hy21⟩ : ∃ y : EuclideanSpace ℝ (Fin 2),
        y 0 = innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt (2 : ℕ)) + 1 / 3 ∧
          y 1 = 1 / 4 :=
      ⟨(innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt (2 : ℕ)) + 1 / 3) •
          EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (1 / 4 : ℝ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ), by simp, by simp⟩
    have hy2 : y₂ 0 ≤ ‖y₂‖ := (Real.le_norm_self (y₂ 0)).trans (PiLp.norm_apply_le y₂ 0)
    rw [hy20] at hy2
    have hfar : innerRadius Y n + (maxRadius Y n - innerRadius Y n + 2 * Real.sqrt (2 : ℕ)) <
        ‖y₂‖ := lt_of_lt_of_le (lt_add_of_pos_right _ (by norm_num)) hy2
    have hbn : innerRadius Y n ≤ ‖y₂‖ := le_trans (le_add_of_nonneg_right hw) hfar.le
    exact ⟨y₂, hfar, fun x => toSpace_ne_of_not_int (1 : Fin 2) fun m => by
        rw [hy21]; exact quarter_ne_int m,
      (hD.1.2.2.1 y₂ hbn).2.2.2 hfar, hD.2.2.2 y₂ hbn, hD.1.2.2.2 y₂⟩

/-- **Consumer of the finite-prefix event and of the carrier bundle.** There are a probability space
carrying centrally excited random walk in the plane with `ε = 1/4`, constants `K` and `C`, and a
sample point `ω` with a time `n ≥ 3` such that: `E7` and the event of the bundle, for the walk and
for the legal carrier, belong to the respective finite-prefix `σ`-algebras; the carrier bundle holds
almost surely for all large `n`; the sample point is legal and lies in `E7` of the walk and of the
carrier; the bundle holds at the walk and at the carrier (the carrier started at the origin at every
sample point, so the witnesses apply to it); and the witnesses of `PlanarRealWitness` hold for the
carrier path: a measurable, bounded excess set of positive area, an interior real non-lattice point
and an exterior real non-lattice point. -/
theorem exists_realization_planar_real_carrier :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2) (hX : IsCERW μ (1 / 4 : ℝ) X),
      ∃ (K : EventConstants) (C : ℝ), 0 < C ∧
        (∀ n : ℕ, MeasurableSet[pathFiltration hX.measurable n]
          (E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (1 / 4 : ℝ)
            (fun z => unitDir (toSpace z)) K X n)) ∧
        (∀ n : ℕ, MeasurableSet[pathFiltration hX.measurable n]
          {ω | PlanarRealDisplays 2 (1 / 4 : ℝ) C (fun j => X j ω) n}) ∧
        (∀ n : ℕ, MeasurableSet[pathFiltration
            (fun j => legalCarrier_measurable (by norm_num : 1 ≤ 2) hX.measurable j) n]
          {ω | PlanarRealDisplays 2 (1 / 4 : ℝ) C
            (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n}) ∧
        (∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (1 / 4 : ℝ)
              (fun z => unitDir (toSpace z)) K (legalCarrier (by norm_num : 1 ≤ 2) X) n ∧
            PlanarRealDisplays 2 (1 / 4 : ℝ) C
              (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n) ∧
        ∃ (ω : Ω) (n : ℕ), 3 ≤ n ∧ ω ∈ legalSet X ∧
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (1 / 4 : ℝ)
            (fun z => unitDir (toSpace z)) K X n ∧
          ω ∈ E7 (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (1 / 4 : ℝ)
            (fun z => unitDir (toSpace z)) K (legalCarrier (by norm_num : 1 ≤ 2) X) n ∧
          PlanarRealDisplays 2 (1 / 4 : ℝ) C (fun j => X j ω) n ∧
          PlanarRealDisplays 2 (1 / 4 : ℝ) C
            (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n ∧
          PlanarRealWitness C (fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω) n := by
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hεd : (1 / 4 : ℝ) < 1 / ((2 : ℕ) : ℝ) := by norm_num
  obtain ⟨Ω, hΩ, μ, hμ, X, hX⟩ := CERW.Support.Law.exists_isCERW (d := 2) (by omega) hε.le hεd
  obtain ⟨K, C, hC, hall⟩ := planar_real_displays_ae_carrier.{0} hε hεd
  obtain ⟨hmE, hmD, -, hmDc, -, hleg, -, hev, hevc⟩ := hall μ X hX
  refine ⟨Ω, hΩ, μ, hμ, X, hX, K, C, hC, hmE, hmD, hmDc, hevc, ?_⟩
  haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
  obtain ⟨ω, hωL, hω, hωc⟩ := (hleg.and (hev.and hevc)).exists
  obtain ⟨n, ⟨hE, hD⟩, ⟨hEc, hDc⟩, hn3⟩ :=
    (hω.and (hωc.and (eventually_ge_atTop 3))).exists
  exact ⟨ω, n, hn3, hωL, hE, hEc, hD, hDc,
    planarRealDisplays_witness (Y := fun j => legalCarrier (by norm_num : 1 ≤ 2) X j ω)
      (legalCarrier_typing (by norm_num : 1 ≤ 2) X ω).1 (by omega) hDc⟩

end CERW.Support.Outer.PlanarRealFiltration
