import CERW.Frozen.SharpWidth
import CERW.Frozen.DriftCrossing
import CERW.Frozen.OuterCrossing
import CERW.Frozen.ContactPotential
import CERW.Support.Main.NormGuards
import CERW.Support.Law.Existence

/-!
# Guards for the source events of the crossing, outer crossing, contact and width statements

`lem:crossing`, `lem:outer-crossing`, `lem:contact` and part (iv) of `thm:sharp` are stated on the events of
the source: the vector event of Section 4, the finite family of radial directions of Section 4, the event of
Section 5 with its nearest point map and the contact estimate, and the three clauses of the difference of the
radii. Each guard applies the frozen statement at an inhabited model and uses its conclusion. The Euclidean norm
and the `ℓ¹` norm of the plane have `ε = 1/4`, which satisfies the ellipticity condition. The crossing lemma is
applied at the first step of a path of the walk, the outer crossing lemma at the visited site of largest norm of
a path of the legal carrier, the contact estimate at a point of the closure of the complement of the cell set that
attains the infimum of the norm, and the width statement at `a = 0` and `a = 1`. `contact_potential_old_form` and
`sharp_width_two_clauses` derive the registered earlier forms of the contact estimate and of the first two clauses
of part (iv) from the frozen statements.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

open CERW CERW.Support.Norm CERW.Support.Norm.ContactEvent CERW.Support.Norm.Section5Localization
  CERW.Support.Norm.CoarseCrossing CERW.Support.RevisedPaper

namespace CERW.Support.Guards.SourceEvents

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

private theorem isNorm_euclid : IsNorm (fun v : E2 => ‖v‖) :=
  ⟨norm_add_le, fun t x => by simp only [norm_smul, Real.norm_eq_abs],
    fun _ hx => norm_eq_zero.mp hx⟩

/-- The `ℓ¹` norm on the plane. -/
def l1 (v : E2) : ℝ := |v 0| + |v 1|

private theorem isNorm_l1 : IsNorm l1 := by
  refine ⟨fun x y => ?_, fun t x => ?_, fun x hx => ?_⟩
  · simp only [l1, PiLp.add_apply]
    linarith [abs_add_le (x 0) (y 0), abs_add_le (x 1) (y 1)]
  · simp only [l1, PiLp.smul_apply, smul_eq_mul, abs_mul]
    ring
  · have h0 := abs_nonneg (x 0)
    have h1 := abs_nonneg (x 1)
    simp only [l1] at hx
    have hx0 : x 0 = 0 := abs_eq_zero.1 (by linarith)
    have hx1 : x 1 = 0 := abs_eq_zero.1 (by linarith)
    ext i
    fin_cases i
    · simpa using hx0
    · simpa using hx1

private theorem hell_euclid : ∀ i : Fin 2, (1 / 4 : ℝ) * (fun v : E2 => ‖v‖) (coordVec i) <
    1 / ((2 : ℕ) : ℝ) := by
  intro i
  simp [coordVec]
  norm_num

private theorem hell_l1 : ∀ i : Fin 2, (1 / 4 : ℝ) * l1 (coordVec i) < 1 / ((2 : ℕ) : ℝ) := by
  intro i
  fin_cases i <;> simp [l1, coordVec] <;> norm_num

/-- A sample point outside a set of measure less than one exists. -/
private theorem exists_not_mem_of_measure_lt_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {S : Set Ω} (h : μ S < 1) : ∃ ω, ω ∉ S := by
  by_contra hcon
  push Not at hcon
  have : S = Set.univ := Set.eq_univ_of_forall hcon
  rw [this, measure_univ] at h
  exact lt_irrefl _ h

/-- A large time at which `C n^{-1} < 1`. -/
private theorem exists_time_small {C : ℝ} (hC : 0 < C) (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ 2 ≤ n ∧ ENNReal.ofReal (C * (n : ℝ) ^ (-1 : ℝ)) < 1 := by
  refine ⟨max (max n₀ 2) (⌈C⌉₊ + 1), (le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _), ?_⟩
  set n : ℕ := max (max n₀ 2) (⌈C⌉₊ + 1) with hn
  have hnC : C < n := by
    have h1 : C < ((⌈C⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil C]
    exact h1.trans_le (by exact_mod_cast le_max_right _ _)
  have hnpos : (0 : ℝ) < n := lt_trans hC hnC
  rw [← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr ?_
  rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_lt_one hnpos]
  exact hnC


/-- For a norm and a nonempty set `E`, a point of the closure of `E` attains the infimum of the
norm over `E`: the contact point of the source. -/
private theorem exists_contact_point {d : ℕ} (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : IsNorm Ψ) {E : Set (EuclideanSpace ℝ (Fin d))} (hE : E.Nonempty) :
    ∃ y₀ ∈ closure E, Ψ y₀ = sInf (Ψ '' E) := by
  obtain ⟨e, he⟩ := hE
  obtain ⟨hc0, hc⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hcont := CERW.Generic.Norm.norm_continuous hΨ
  have hnonneg : ∀ y, 0 ≤ Ψ y := fun y =>
    (mul_nonneg hc0.le (norm_nonneg y)).trans (hc y)
  set S : Set (EuclideanSpace ℝ (Fin d)) := closure E ∩ {y | Ψ y ≤ Ψ e} with hS
  have hScomp : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_closure.inter (isClosed_le hcont continuous_const)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := Ψ e / normMin Ψ)).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff, le_div_iff₀ hc0]
    have h1 := hc y
    have h2 : Ψ y ≤ Ψ e := hy.2
    linarith [mul_comm (normMin Ψ) ‖y‖]
  have hSne : S.Nonempty := ⟨e, subset_closure he, show Ψ e ≤ Ψ e from le_rfl⟩
  obtain ⟨y₀, hy₀S, hmin⟩ := hScomp.exists_isMinOn hSne hcont.continuousOn
  have hle : ∀ y ∈ E, Ψ y₀ ≤ Ψ y := by
    intro y hy
    by_cases h : Ψ y ≤ Ψ e
    · exact hmin ⟨subset_closure hy, h⟩
    · exact hy₀S.2.trans (not_le.mp h).le
  have hbdd : BddBelow (Ψ '' E) := ⟨0, by rintro _ ⟨y, -, rfl⟩; exact hnonneg y⟩
  refine ⟨y₀, hy₀S.1, le_antisymm ?_ ?_⟩
  · exact le_csInf ⟨Ψ e, e, he, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact hle y hy)
  · by_contra hlt
    push Not at hlt
    obtain ⟨y, hyU, hyE⟩ := mem_closure_iff.mp hy₀S.1 {y | Ψ y < sInf (Ψ '' E)}
      (isOpen_lt hcont continuous_const) hlt
    exact absurd (csInf_le hbdd ⟨y, hyE, rfl⟩) (not_le.mpr hyU)



/-- A sample point of an event whose complement has measure less than one, at which a random
variable that is zero almost surely is zero. -/
private theorem exists_mem_and_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → Site 2} (h0 : μ {ω | Y ω ≠ 0} = 0) {E : Set Ω} (hE : μ Eᶜ < 1) :
    ∃ ω, ω ∈ E ∧ Y ω = 0 := by
  have hS : μ (Eᶜ ∪ {ω | Y ω ≠ 0}) < 1 :=
    lt_of_le_of_lt (measure_union_le _ _) (by rw [h0, add_zero]; exact hE)
  obtain ⟨ω, hω⟩ := exists_not_mem_of_measure_lt_one hS
  rw [Set.mem_union, not_or] at hω
  exact ⟨ω, not_not.mp hω.1, not_not.mp hω.2⟩

/-! ### `lem:crossing` -/

/-- The crossing lemma at the Euclidean norm of the plane with `ε = 1/4`: on the vector event, at a sample point of the event with `X 0 = 0`, the first step of the path satisfies the crossing bound for the first coordinate direction. -/
theorem crossing_applies_euclid :
    ∃ (ξ : Site 2 → E2) (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ) (X : ℕ → Ω → Site 2) (C : ℝ) (n : ℕ),
      CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X ∧ 0 < C ∧ 2 ≤ n ∧
      ∃ ω, X 0 ω = 0 ∧
        inner ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
            (CERW.toSpace (X 1 ω) - CERW.toSpace (X 0 ω)) ≤
          C * Real.sqrt ((((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) * Real.log n) := by
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨ξ, hξ, hξ0, Ω, hΩ, μ, hμ, X, hX⟩ :=
    CERW.Support.Main.norm_hypotheses_inhabited (by norm_num) isNorm_euclid hε hell_euclid
  obtain ⟨C, hC, hmain⟩ := CERW.Frozen.drift_crossing.{0} (d := 2) le_rfl _ isNorm_euclid
    (1 / 4 : ℝ) hε hell_euclid 1 one_pos
  obtain ⟨n, -, hn2, hsmall⟩ := exists_time_small hC 2
  obtain ⟨hprob, hconc⟩ := hmain ξ hξ hξ0 μ X hX n hn2
  have hlt := lt_of_le_of_lt hprob hsmall
  obtain ⟨ω, hωE, hω0⟩ := exists_mem_and_zero hX.start hlt
  refine ⟨ξ, Ω, hΩ, μ, hμ, X, C, n, hX, hC, hn2, ω, hω0, ?_⟩
  refine hconc ω hωE (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (by simp) 0 1 one_pos
    (by omega) ?_
  intro j hj0 hj1 _
  have hj : j = 0 := by omega
  subst hj
  rw [hω0, hξ0, inner_zero_right]


/-! ### `lem:contact` -/

/-- The event of the contact lemma at a norm `Ψ` of the plane with `ε = 1/4`: the nearest point map exists, and at a sample point of an event of positive probability the cell set has the lower occupation bound of the source. -/
theorem contact_event_applies {Ψ : E2 → ℝ} (hΨ : CERW.IsNorm Ψ)
    (hell : ∀ i : Fin 2, (1 / 4 : ℝ) * Ψ (CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ)) :
    ∃ (ξ : Site 2 → E2) (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ) (X : ℕ → Ω → Site 2) (c_co C : ℝ) (n : ℕ)
      (P : E2 → E2),
      CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X ∧ 0 < c_co ∧ 0 < C ∧
      (∀ y, Ψ (P y) ≤ ((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))) ∧
      ∃ ω, c_co * (((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))) ^ 2 ≤
          ((CERW.departureRange (fun j => X j ω) n).card : ℝ) := by
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨ξ, hξ, hξ0, Ω, hΩ, μ, hμ, X, hX⟩ :=
    CERW.Support.Main.norm_hypotheses_inhabited (by norm_num) hΨ hε hell
  obtain ⟨hex, hmain⟩ := CERW.Frozen.contact_potential.{0} (d := 2) le_rfl Ψ hΨ (1 / 4 : ℝ) hε hell
  obtain ⟨c_co, C_co, C_loc, C_vec, C_mart, C_quad, C_lin, C, hc, hCco, hCloc, hCvec, hCmart,
    hCquad, hClin, hC, n₀, hn₀, h⟩ := hmain 1 one_pos
  obtain ⟨n, hnn₀, hn2, hsmall⟩ := exists_time_small hC n₀
  obtain ⟨P, ⟨hmem, hmin⟩, -⟩ := hex n
  obtain ⟨hprob, hae⟩ := h ξ hξ hξ0 μ X hX n hnn₀ P hmem hmin
  have hlt := lt_of_le_of_lt hprob hsmall
  obtain ⟨ω, hω⟩ := exists_not_mem_of_measure_lt_one hlt
  have hωE := not_not.mp hω
  exact ⟨ξ, Ω, hΩ, μ, hμ, X, c_co, C, n, P, hX, hc, hC, hmem, ω, hωE.1.1⟩

example := contact_event_applies isNorm_euclid hell_euclid

example := contact_event_applies isNorm_l1 hell_l1


/-- If the complement of an event has measure less than one and almost every sample point of the event has a
property, then some sample point of the event has it. -/
private theorem exists_mem_of_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Set Ω} {P : Ω → Prop} (hE : μ Eᶜ < 1) (h : ∀ᵐ ω ∂μ, ω ∈ E → P ω) :
    ∃ ω, ω ∈ E ∧ P ω := by
  by_contra hcon
  push Not at hcon
  have hne : ∀ᵐ ω ∂μ, ω ∈ Eᶜ := by
    filter_upwards [h] with ω hω hmem
    exact hcon ω hmem (hω hmem)
  have hE0 : μ {ω | ¬ ω ∈ Eᶜ} = 0 := ae_iff.mp hne
  have hset : {ω | ¬ ω ∈ Eᶜ} = E := by
    ext ω
    simp
  rw [hset] at hE0
  have h1 : μ Set.univ ≤ μ E + μ Eᶜ := measure_univ_le_add_compl E
  rw [measure_univ, hE0, zero_add] at h1
  exact absurd hE (not_lt.mpr h1)

/-- The almost sure contact statement, consumed at a contact point: at a sample point of the event outside
the exceptional null set, at a point of the closure of the complement of the cell set that attains the infimum of the norm,
the contact bound holds, with the lower occupation bound of the event. -/
theorem contact_applies {Ψ : E2 → ℝ} (hΨ : CERW.IsNorm Ψ)
    (hell : ∀ i : Fin 2, (1 / 4 : ℝ) * Ψ (CERW.coordVec i) < 1 / ((2 : ℕ) : ℝ)) :
    ∃ (ξ : Site 2 → E2) (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ) (X : ℕ → Ω → Site 2) (c_co C : ℝ) (n : ℕ),
      CERW.IsDriftCERW μ (1 / 4 : ℝ) ξ X ∧ 0 < c_co ∧ 0 < C ∧
      ∃ (ω : Ω) (y₀ : E2),
        c_co * (((((2 : ℕ) : ℝ) + 1) * n /
          (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))) ^ 2 ≤
          ((CERW.departureRange (fun j => X j ω) n).card : ℝ) ∧
        Ψ y₀ = CERW.normInnerRadius Ψ (fun j => X j ω) n ∧
        y₀ ∈ closure (CERW.cellSet (fun j => X j ω) n)ᶜ ∧
        CERW.normPotential 2 (1 / 4 : ℝ) Ψ (CERW.cellSet (fun j => X j ω) n) y₀ ≤
          C * (((((2 : ℕ) : ℝ) + 1) * n /
            (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))) *
          (if (2 : ℕ) = 2 then Real.sqrt (Real.log n / (((((2 : ℕ) : ℝ) + 1) * n /
            (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))))
          else Real.log n / (((((2 : ℕ) : ℝ) + 1) * n /
            (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)))) := by
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨ξ, hξ, hξ0, Ω, hΩ, μ, hμ, X, hX⟩ :=
    CERW.Support.Main.norm_hypotheses_inhabited (by norm_num) hΨ hε hell
  obtain ⟨hex, hmain⟩ := CERW.Frozen.contact_potential.{0} (d := 2) le_rfl Ψ hΨ (1 / 4 : ℝ) hε hell
  obtain ⟨c_co, C_co, C_loc, C_vec, C_mart, C_quad, C_lin, C, hc, -, -, -, -, -, -, hC, n₀, hn₀, h⟩ :=
    hmain 1 one_pos
  obtain ⟨n, hnn₀, hn2, hsmall⟩ := exists_time_small hC n₀
  obtain ⟨P, ⟨hmem, hmin⟩, -⟩ := hex n
  obtain ⟨hprob, hae⟩ := h ξ hξ hξ0 μ X hX n hnn₀ P hmem hmin
  obtain ⟨ω, hωE, hcon⟩ := exists_mem_of_ae (lt_of_le_of_lt hprob hsmall) hae
  have hcompl : ((CERW.cellSet (fun j => X j ω) n)ᶜ).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hempty
    have hsub := CERW.Support.Occupation.cellSet_subset_ball (by norm_num : 1 ≤ 2)
      (fun j => X j ω) n
    rw [hempty] at hsub
    exact (NormedSpace.unbounded_univ ℝ E2) (Metric.isBounded_ball.subset hsub)
  obtain ⟨y₀, hy₀cl, hy₀⟩ := exists_contact_point (by norm_num : 1 ≤ 2) hΨ hcompl
  exact ⟨ξ, Ω, hΩ, μ, hμ, X, c_co, C, n, hX, hc, hC, ω, y₀, hωE.1.1, hy₀, hy₀cl,
    hcon y₀ hy₀ hy₀cl⟩

example := contact_applies isNorm_euclid hell_euclid

example := contact_applies isNorm_l1 hell_l1

/-! ### `thm:sharp` part (iv) -/

/-- The radius `r_n` of the paper at `d = 2`, `ε = 1/4`. -/
noncomputable def rr (n : ℕ) : ℝ :=
  ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * (1 / 4 : ℝ) *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))

/-- The third clause of part (iv) at `d = 2`, `ε = 1/4`: the `limsup` of the probability of a gap at most `a √r_n` is at most `0` at `a = 0` and below `1` at `a = 1`. -/
theorem sharp_width_gap_applies :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 4 : ℝ) X ∧
      limsup (fun n => μ {ω | CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n ≤
        (0 : ℝ) * Real.sqrt (rr n)}) atTop ≤ 0 ∧
      limsup (fun n => μ {ω | CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n ≤
        (1 : ℝ) * Real.sqrt (rr n)}) atTop <
          1 := by
  have hε0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hε1 : (1 / 4 : ℝ) < 1 / ((2 : ℕ) : ℝ) := by norm_num
  obtain ⟨Ω, hΩ, μ, hμ, X, hX⟩ := CERW.Support.Law.exists_isCERW (d := 2) (by norm_num)
    hε0.le hε1
  obtain ⟨-, -, hc⟩ := CERW.Frozen.sharp_width.{0} (d := 2) rfl (1 / 4 : ℝ) hε0 hε1
  refine ⟨Ω, hΩ, μ, hμ, X, hX, ?_, ?_⟩
  · have h0 := hc 0 le_rfl μ X hX
    have hz : ENNReal.ofReal (1 - Real.exp (-(3 * (1 / 4 : ℝ) * (0 : ℝ) ^ 2 / Real.pi))) = 0 := by
      simp
    rw [hz] at h0
    exact h0
  · have h1 := hc 1 zero_le_one μ X hX
    refine lt_of_le_of_lt h1 ?_
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr ?_
    have : 0 < Real.exp (-(3 * (1 / 4 : ℝ) * (1 : ℝ) ^ 2 / Real.pi)) := Real.exp_pos _
    linarith


/-! ### The frozen statements imply the earlier forms of the contact estimate and of part (iv) -/

/-- The statement of the registered version 1 of `lem:contact` follows from the almost sure statement: the event estimate gives the probability bound and the almost sure conclusion gives the inclusion of the exceptional sets. -/
theorem contact_potential_old_form {d : ℕ} (hd : 2 ≤ d) :
    ∀ Ψ : EuclideanSpace ℝ (Fin d) → ℝ, CERW.IsNorm Ψ →
    ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
    let r : ℕ → ℝ := fun n =>
      ((d + 1) * n / (2 * d * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1))
    let q : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∀ y₀ : EuclideanSpace ℝ (Fin d),
            Ψ y₀ = CERW.normInnerRadius Ψ (X · ω) n →
            y₀ ∈ closure (CERW.cellSet (X · ω) n)ᶜ →
            CERW.normPotential d ε Ψ (CERW.cellSet (X · ω) n) y₀ ≤ C * r n * q n}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro Ψ hΨ ε hε hell r q p hp
  obtain ⟨hex, hmain⟩ := CERW.Frozen.contact_potential.{u} hd Ψ hΨ ε hε hell
  obtain ⟨c_co, C_co, C_loc, C_vec, C_mart, C_quad, C_lin, C, -, -, -, -, -, -, -, hC, n₀, -, h⟩ :=
    hmain p hp
  refine ⟨C, hC, n₀, fun ξ hξ hξ0 Ω _ μ _ X hX n hn => ?_⟩
  obtain ⟨P, ⟨hmem, hmin⟩, -⟩ := hex n
  obtain ⟨hprob, hae⟩ := h ξ hξ hξ0 μ X hX n hn P hmem hmin
  exact le_trans (measure_mono_ae (by
    filter_upwards [hae] with ω hω hs hE
    exact hs (fun y₀ h1 h2 => hω hE y₀ h1 h2))) hprob

/-- The first two clauses of `thm:sharp` part (iv) follow from the three-clause statement. -/
theorem sharp_width_two_clauses {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    (∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let E : Set Ω := {ω | c * Real.sqrt (r n * Real.log n)
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n}
        MeasurableSet E ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ E) ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
        (Real.sqrt (Real.pi / (3 * ε)) - δ) * Real.sqrt (r n * Real.log (Real.log n))
          ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n) := by
  intro ωd ε hε0 hε1 r
  have h := CERW.Frozen.sharp_width.{u} hd ε hε0 hε1
  exact ⟨h.1, h.2.1⟩

/-! ### `lem:outer-crossing` -/

private theorem normMax_pos_euclid : 0 < normMax (fun v : E2 => ‖v‖) := by
  have hd1 : 1 ≤ 2 := by norm_num
  obtain ⟨hcpos, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le isNorm_euclid hd1
  exact lt_of_lt_of_le hcpos
    (CERW.Support.Norm.ProjectionGeometry.normMin_le_normMax isNorm_euclid hd1)

/-- The outer crossing lemma at the Euclidean norm of the plane with `ε = 1/4`, on a path of the legal carrier: at the visited site of largest norm, the radial direction of the cap satisfies the deterministic bound. -/
theorem outer_crossing_applies_euclid :
    ∃ (ξ : Site 2 → E2) (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ) (X : ℕ → Ω → Site 2) (C_ev C : ℝ) (n : ℕ),
      IsDriftCERW μ (1 / 4 : ℝ) ξ X ∧ (∀ ω, PathTyping 2 (fun j => X j ω)) ∧ 0 < C_ev ∧ 0 < C ∧
      2 ≤ n ∧
      ∃ (ω : Ω) (j₀ : ℕ) (q : E2), j₀ ≤ n ∧ q ∈ radialDirections 2 (fun v : E2 => ‖v‖) n ∧
        0 < inner ℝ q (toSpace (X j₀ ω)) ∧
        inner ℝ q (toSpace (X j₀ ω)) ≤
          max (inner ℝ q (toSpace (X j₀ ω)) - inner ℝ q (toSpace (X j₀ ω)) / 2) 0 +
            C * (1 + ((((departureRange (fun j => X j ω) n).filter
              (fun z => (0 : ℝ) ≤ inner ℝ q (toSpace z))).sup
                (localTime (fun j => X j ω) n) : ℕ) : ℝ)) * Real.log n := by
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨ξ, hξ, hξ0, Ω, hΩ, μ, hμ, X0, hX0⟩ :=
    CERW.Support.Main.norm_hypotheses_inhabited (by norm_num) isNorm_euclid hε hell_euclid
  have hX : IsDriftCERW μ (1 / 4 : ℝ) ξ (legalCarrier (by norm_num : 1 ≤ 2) X0) :=
    isDriftCERW_legalCarrier (by norm_num) hX0
  have hty : ∀ ω, PathTyping 2 (fun j => legalCarrier (by norm_num : 1 ≤ 2) X0 j ω) :=
    legalCarrier_typing (by norm_num) X0
  set X := legalCarrier (by norm_num : 1 ≤ 2) X0 with hXdef
  have hΛ := normMax_pos_euclid
  obtain ⟨C_ev, hCev, hprob, hdet⟩ := CERW.Frozen.outer_crossing.{0} (d := 2) le_rfl _
    isNorm_euclid (1 / 4 : ℝ) hε hell_euclid 1 one_pos
  obtain ⟨C, hC, hdet'⟩ := hdet (normMax (fun v : E2 => ‖v‖) / 2) (half_pos hΛ)
  obtain ⟨n, -, hn2, hsmall⟩ := exists_time_small hCev 2
  have hp' := hprob ξ hξ hξ0 μ X hX n hn2
  have hlt := lt_of_le_of_lt hp' hsmall
  obtain ⟨ω, hω⟩ := exists_not_mem_of_measure_lt_one hlt
  obtain ⟨hvec, hrad⟩ := not_not.mp hω
  obtain ⟨hx0, hstep⟩ := hty ω
  set x : ℕ → Site 2 := fun j => X j ω with hx
  -- the visited site of largest Euclidean norm
  obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun j => ‖toSpace (x j)‖) ⟨0, by simp⟩
  have hj₀n : j₀ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₀mem)
  have hmax : ∀ j ≤ n, ‖toSpace (x j)‖ ≤ ‖toSpace (x j₀)‖ := fun j hj =>
    hj₀max j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hz1 : ‖toSpace (x 1)‖ = 1 := by
    have h := CERW.Support.Law.euclidNorm_of_mem_unitSteps (hstep 0)
    rw [hx0, sub_zero] at h
    rw [norm_toSpace, h]
  have hzpos : 0 < ‖toSpace (x j₀)‖ := by
    have h1 : ‖toSpace (x 1)‖ ≤ ‖toSpace (x j₀)‖ := hmax 1 (by omega)
    rw [hz1] at h1
    exact lt_of_lt_of_le one_pos h1
  set z : Site 2 := x j₀ with hz
  set q : E2 := capDirection (fun v : E2 => ‖v‖) z with hq
  have hqmem : q ∈ capDirections (fun v : E2 => ‖v‖) n := by
    refine capDirection_mem_capDirections ?_
    exact (CERW.Support.Occupation.euclidNorm_le_of_steps x hx0 hstep j₀).trans
      (by exact_mod_cast hj₀n)
  have hqinner : ∀ w : E2, inner ℝ q w = normMax (fun v : E2 => ‖v‖) * ‖toSpace z‖⁻¹ *
      inner ℝ (toSpace z) w := by
    intro w
    simp only [hq, capDirection, real_inner_smul_left]
    ring
  have hT : inner ℝ q (toSpace z) = normMax (fun v : E2 => ‖v‖) * ‖toSpace z‖ := by
    rw [hqinner, real_inner_self_eq_norm_sq]
    field_simp
  have hTpos : 0 < inner ℝ q (toSpace z) := by
    rw [hT]
    exact mul_pos hΛ hzpos
  have hqmaxj : ∀ j ≤ n, inner ℝ q (toSpace (x j)) ≤ inner ℝ q (toSpace z) := by
    intro j hj
    rw [hqinner, hqinner, real_inner_self_eq_norm_sq]
    have hcs : inner ℝ (toSpace z) (toSpace (x j)) ≤ ‖toSpace z‖ ^ 2 :=
      calc inner ℝ (toSpace z) (toSpace (x j)) ≤ ‖toSpace z‖ * ‖toSpace (x j)‖ :=
            real_inner_le_norm _ _
        _ ≤ ‖toSpace z‖ * ‖toSpace z‖ := mul_le_mul_of_nonneg_left (hmax j hj) (norm_nonneg _)
        _ = ‖toSpace z‖ ^ 2 := by ring
    have hcoef : 0 ≤ normMax (fun v : E2 => ‖v‖) * ‖toSpace z‖⁻¹ :=
      mul_nonneg hΛ.le (inv_nonneg.mpr (norm_nonneg _))
    exact mul_le_mul_of_nonneg_left hcs hcoef
  have hdrift : ∀ j ≤ n, inner ℝ q (toSpace z) - inner ℝ q (toSpace z) / 2 <
      inner ℝ q (toSpace (x j)) → normMax (fun v : E2 => ‖v‖) / 2 ≤ inner ℝ q (ξ (x j)) := by
    intro j hj hgt
    have hξeq := field_eq_unitDir hξ hξ0
    rw [hξeq]
    show normMax (fun v : E2 => ‖v‖) / 2 ≤ inner ℝ q (unitDir (toSpace (x j)))
    have hhalf : inner ℝ q (toSpace z) / 2 < inner ℝ q (toSpace (x j)) := by linarith
    have hxjpos : 0 < ‖toSpace (x j)‖ := by
      refine norm_pos_iff.mpr fun h0 => ?_
      rw [h0, inner_zero_right] at hhalf
      linarith
    have hlin : inner ℝ q (unitDir (toSpace (x j))) =
        ‖toSpace (x j)‖⁻¹ * inner ℝ q (toSpace (x j)) := by
      simp only [unitDir, real_inner_smul_right]
    rw [hlin]
    have h1 : ‖toSpace z‖⁻¹ ≤ ‖toSpace (x j)‖⁻¹ :=
      inv_anti₀ hxjpos (hmax j hj)
    have hhalfpos : 0 < inner ℝ q (toSpace (x j)) := lt_trans (by linarith) hhalf
    calc normMax (fun v : E2 => ‖v‖) / 2 = ‖toSpace z‖⁻¹ * (inner ℝ q (toSpace z) / 2) := by
          rw [hT]
          field_simp
      _ ≤ ‖toSpace z‖⁻¹ * inner ℝ q (toSpace (x j)) :=
          mul_le_mul_of_nonneg_left hhalf.le (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ ‖toSpace (x j)‖⁻¹ * inner ℝ q (toSpace (x j)) :=
          mul_le_mul_of_nonneg_right h1 hhalfpos.le
  have hqrad : q ∈ radialDirections 2 (fun v : E2 => ‖v‖) n := by
    rcases Finset.mem_insert.mp (capDirections_subset_insert_radialDirections _ n hqmem) with
      h0 | h
    · rw [h0, inner_zero_left] at hTpos
      exact absurd hTpos (lt_irrefl _)
    · exact h
  have hconc := hdet' ξ hξ hξ0 n hn2 q (norm_capDirection_le hΛ.le z) x hx0 hstep hvec
    (hrad q hqrad) j₀ hj₀n hqmaxj (inner ℝ q (toSpace z) / 2) (half_pos hTpos) hdrift 0 le_rfl
  refine ⟨ξ, Ω, hΩ, μ, hμ, X, C_ev, C, n, hX, hty, hCev, hC, hn2, ω, j₀, q, hj₀n, hqrad,
    hTpos, ?_⟩
  exact hconc

end CERW.Support.Guards.SourceEvents
