import CERW.Frozen.NormShapeRates
import CERW.Frozen.LayerPotential
import CERW.Frozen.MoreauCap
import CERW.Frozen.ContactPotential
import CERW.Frozen.OuterCrossing
import CERW.Support.Drift.Existence
import CERW.Support.Drift.StepProb
import CERW.Support.Drift.Bridge
import CERW.Generic.Norm.Subgradient

/-!
# Non-vacuity of the norm-shape rates, the layer potential, the Moreau cap, the contact
potential and the outer crossing

Each guard fixes the Euclidean norm in the plane and applies the frozen theorem at that norm, with
every hypothesis built explicitly. For the two probabilistic statements (`norm_shape_rates` and
`contact_potential`) the walk with `ε = 1/4` and the subgradient field `x ↦ x/|x|` exists. For the
three deterministic statements a concrete instance of all the hypotheses is exhibited: an annulus
for the layer potential, a point of norm `2` for the Moreau cap, and a straight path along the first
axis for the outer crossing.
-/

namespace CERW.Support.Guards

open MeasureTheory
open LatticeProb (Site euclidNorm)

/-! ### The Euclidean norm, its subgradients, and the sphere -/

/-- The Euclidean norm is a norm in the sense of `CERW.IsNorm`. -/
private theorem isNorm_euclidean {d : ℕ} :
    CERW.IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) :=
  ⟨norm_add_le, fun t x => by simp only [norm_smul, Real.norm_eq_abs],
    fun _ hx => norm_eq_zero.mp hx⟩

/-- The standard basis vectors have Euclidean norm one. -/
private theorem norm_coordVec {d : ℕ} (i : Fin d) : ‖CERW.coordVec i‖ = 1 := by
  simp [CERW.coordVec]

/-- The image of the Euclidean unit sphere under the Euclidean norm is `{1}`. -/
private theorem image_norm_sphere {d : ℕ} (hd : 1 ≤ d) :
    (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) '' Metric.sphere 0 1 = {1} := by
  ext t
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · rintro rfl
    exact ⟨CERW.coordVec ⟨0, hd⟩, by rw [mem_sphere_zero_iff_norm]; exact norm_coordVec _,
      norm_coordVec _⟩

/-- The largest value of the Euclidean norm on the Euclidean unit sphere is `1`. -/
private theorem normMax_euclidean {d : ℕ} (hd : 1 ≤ d) :
    CERW.normMax (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) = 1 := by
  rw [CERW.normMax, image_norm_sphere hd, csSup_singleton]

/-- The least value of the Euclidean norm on the Euclidean unit sphere is `1`. -/
private theorem normMin_euclidean {d : ℕ} (hd : 1 ≤ d) :
    CERW.normMin (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) = 1 := by
  rw [CERW.normMin, image_norm_sphere hd, csInf_singleton]

/-- A nonzero lattice site embeds to a nonzero vector of `ℝ^d`. -/
private theorem toSpace_ne_zero {d : ℕ} {x : Site d} (hx : x ≠ 0) :
    CERW.toSpace x ≠ (0 : EuclideanSpace ℝ (Fin d)) := by
  intro h
  apply hx
  funext i
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
  simpa using hi

/-- The direction `v/|v|` is a subgradient of the Euclidean norm at every `v ≠ 0`. -/
private theorem isSubgradient_norm_unitDir {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    CERW.IsSubgradient (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) v (CERW.unitDir v) := by
  intro y
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hinner : inner ℝ (CERW.unitDir v) (y - v) = ‖v‖⁻¹ * (inner ℝ v y - ‖v‖ ^ 2) := by
    rw [CERW.unitDir, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
  have hcs : inner ℝ v y ≤ ‖v‖ * ‖y‖ := real_inner_le_norm v y
  have hle : ‖v‖⁻¹ * inner ℝ v y ≤ ‖y‖ := by
    calc ‖v‖⁻¹ * inner ℝ v y ≤ ‖v‖⁻¹ * (‖v‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hpos.le)
      _ = ‖y‖ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have hexp : ‖v‖ + ‖v‖⁻¹ * (inner ℝ v y - ‖v‖ ^ 2) = ‖v‖⁻¹ * inner ℝ v y := by
    field_simp
    ring
  show ‖v‖ + inner ℝ (CERW.unitDir v) (y - v) ≤ ‖y‖
  rw [hinner, hexp]
  exact hle

/-- The field `x ↦ x/|x|` is a subgradient of the Euclidean norm at every nonzero site. -/
private theorem unitDir_isSubgradient {d : ℕ} {x : Site d} (hx : x ≠ 0) :
    CERW.IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x)
      (CERW.unitDir (CERW.toSpace x)) :=
  isSubgradient_norm_unitDir (toSpace_ne_zero hx)

/-- The field `x ↦ x/|x|` vanishes at the origin. -/
private theorem unitDir_toSpace_zero {d : ℕ} :
    CERW.unitDir (CERW.toSpace (0 : Site d)) = 0 := by
  have h0 : CERW.toSpace (0 : Site d) = 0 := by
    ext i
    simp
  rw [h0]
  exact CERW.unitDir_zero

/-- Every coordinate of a direction `v/|v|` has absolute value at most one. -/
private theorem abs_unitDir_apply_le {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |CERW.unitDir v i| ≤ 1 := by
  have h := (PiLp.norm_apply_le (CERW.unitDir v) i).trans (CERW.norm_unitDir_le v)
  simpa using h

/-- For the Euclidean norm with the field `x ↦ x/|x|` and `0 < ε ≤ 1/d`, the walk exists. -/
private theorem exists_euclidean_walk {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε ≤ 1 / (d : ℝ)) :
    ∃ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ x : Site d, x ≠ 0 →
        CERW.IsSubgradient (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) ∧
      ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X := by
  refine ⟨fun x => CERW.unitDir (CERW.toSpace x), fun x hx => unitDir_isSubgradient hx,
    unitDir_toSpace_zero, ?_⟩
  refine CERW.Support.Drift.exists_isDriftCERW hd hε.le (fun z i => ?_)
  calc ε * |CERW.unitDir (CERW.toSpace z) i| ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left (abs_unitDir_apply_le _ i) hε.le
    _ ≤ 1 / (d : ℝ) := by rw [mul_one]; exact hεd

/-- In the plane, `ε = 1/4` meets the ellipticity condition for the Euclidean norm. -/
private theorem plane_ellipticity :
    ∀ i : Fin 2, (1 / 4 : ℝ) * (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (CERW.coordVec i) <
      1 / ((2 : ℕ) : ℝ) := by
  intro i
  show (1 / 4 : ℝ) * ‖CERW.coordVec i‖ < 1 / ((2 : ℕ) : ℝ)
  rw [norm_coordVec]
  norm_num

/-! ### `norm_shape_rates` -/

/-- In the plane, for the Euclidean norm and `ε = 1/4`, the radii and local-time estimates of
`norm_shape_rates` hold with probability at least `1 - C n^{-p}` for every drift field of
subgradients. -/
theorem norm_shape_rates_applies :
    let Ψ : EuclideanSpace ℝ (Fin 2) → ℝ := fun v => ‖v‖
    let ε : ℝ := 1 / 4
    let r : ℕ → ℝ := fun n =>
      ((2 + 1) * n / (2 * 2 * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (2 + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (|CERW.normInnerRadius Ψ (X · ω) n - r n|
                    ≤ C * (r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)) ∧
                  CERW.normMaxRadius Ψ (X · ω) n - r n
                    ≤ C * (r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)) ∧
                  ∀ x : Site 2,
                    |(CERW.localTime (X · ω) n x : ℝ)
                        - 2 * 2 * ε * max (r n - Ψ (CERW.toSpace x)) 0|
                      ≤ C * (r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) :=
  CERW.Frozen.norm_shape_rates (d := 2) (by norm_num) _ isNorm_euclidean (1 / 4) (by norm_num)
    plane_ellipticity

/-- In the plane, for the Euclidean norm and `ε = 1/4`, there are a subgradient field `ξ` with
`ξ 0 = 0` and a probability space carrying the walk driven by `ξ`. -/
theorem norm_shape_rates_inhabited :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        CERW.IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (CERW.toSpace x) (ξ x)) ∧
      ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4) ξ X :=
  exists_euclidean_walk (by norm_num) (by norm_num) (by norm_num)

/-! ### `layer_potential` -/

/-- For the Euclidean norm in the plane and `ε = 1/4`, the potential of the annulus
`1 ≤ |v| ≤ 2` is at most `2 · 2 · (1/4) · 1 = 1` in absolute value at every point. -/
theorem layer_potential_applies (y : EuclideanSpace ℝ (Fin 2)) :
    |CERW.normPotential 2 (1 / 4) (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖)
        {v | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} y| ≤ 1 := by
  have hDm : MeasurableSet {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} :=
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)).measurableSet
  have hD : {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} ⊆
      {v | (1 : ℝ) ≤ (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖) v ∧
        (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖) v ≤ 1 + 1} := by
    intro v hv
    exact ⟨hv.1, by linarith [hv.2]⟩
  have h := CERW.Frozen.layer_potential (d := 2) (by norm_num) isNorm_euclidean
    (ε := 1 / 4) (by norm_num) (a := 1) (b := 1) (by norm_num) one_pos hDm hD y
  refine h.trans ?_
  norm_num

/-- The annulus `1 ≤ |v| ≤ 2` of the layer-potential guard has positive volume. -/
theorem layer_potential_inhabited :
    0 < volume {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} := by
  have hc : ‖(EuclideanSpace.single (0 : Fin 2) (3 / 2 : ℝ))‖ = 3 / 2 := by
    simp
  have hsub : Metric.ball (EuclideanSpace.single (0 : Fin 2) (3 / 2 : ℝ)) (1 / 4) ⊆
      {v : EuclideanSpace ℝ (Fin 2) | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 2} := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm] at hv
    have h := abs_norm_sub_norm_le v (EuclideanSpace.single (0 : Fin 2) (3 / 2 : ℝ))
    rw [hc] at h
    have h' := abs_le.mp (h.trans hv.le)
    exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
  exact lt_of_lt_of_le (Metric.measure_ball_pos _ _ (by norm_num)) (measure_mono hsub)

/-! ### `moreau_cap` -/

/-- For the Euclidean norm in the plane, `τ = 1` and `x = y = (2, 0)`, every subgradient `ξ` of
the norm at `y` satisfies `1/2 ≤ ⟨∇F_1(y), ξ⟩`. -/
theorem moreau_cap_applies :
    let y : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 2
    ∀ ξ : EuclideanSpace ℝ (Fin 2), CERW.IsSubgradient (fun v => ‖v‖) y ξ →
      1 / 2 ≤ inner ℝ
        (gradient (CERW.moreauEnvelope (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) 1) y) ξ := by
  intro y ξ hξ
  have hc := normMin_euclidean (d := 2) (by norm_num)
  have hΛ := normMax_euclidean (d := 2) (by norm_num)
  have hy : ‖y‖ = 2 := by simp [y]
  have key := CERW.Frozen.moreau_cap (d := 2) (by norm_num) isNorm_euclidean one_pos y y
  dsimp only at key
  rw [hc, hΛ] at key
  have h := key (le_refl _) (by norm_num) (by rw [hy]; norm_num) ξ hξ
  norm_num at h
  simpa only [inner_gradient_left] using h

/-- For the Euclidean norm in the plane, `τ = 1` and `y = (2, 0)`, the subgradients of the norm
at `y` form a nonempty set, each element of which satisfies the bound of the Moreau cap. -/
theorem moreau_cap_inhabited :
    ∃ ξ : EuclideanSpace ℝ (Fin 2),
      CERW.IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (EuclideanSpace.single 0 2) ξ ∧
      1 / 2 ≤ inner ℝ (gradient (CERW.moreauEnvelope
        (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) 1) (EuclideanSpace.single 0 2)) ξ := by
  have hy : (EuclideanSpace.single 0 2 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    simp at this
  exact ⟨_, isSubgradient_norm_unitDir hy, moreau_cap_applies _ (isSubgradient_norm_unitDir hy)⟩

/-! ### `contact_potential` -/

/-- In the plane, for the Euclidean norm and `ε = 1/4`, the potential of the cell set at the
inner-radius points is at most `C r_n q_n` with probability at least `1 - C n^{-p}` for all large
`n`. -/
theorem contact_potential_applies :
    let Ψ : EuclideanSpace ℝ (Fin 2) → ℝ := fun v => ‖v‖
    let ε : ℝ := 1 / 4
    let r : ℕ → ℝ := fun n =>
      ((2 + 1) * n / (2 * 2 * ε * CERW.normBallVolume Ψ)) ^ ((1 : ℝ) / (2 + 1))
    let q : ℕ → ℝ := fun n => Real.sqrt (Real.log n / r n)
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ ε ξ X → ∀ n : ℕ, n₀ ≤ n →
        μ {ω | ¬ ∀ y₀ : EuclideanSpace ℝ (Fin 2),
            Ψ y₀ = CERW.normInnerRadius Ψ (X · ω) n →
            y₀ ∈ closure (CERW.cellSet (X · ω) n)ᶜ →
            CERW.normPotential 2 ε Ψ (CERW.cellSet (X · ω) n) y₀ ≤ C * r n * q n}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) :=
  CERW.Frozen.contact_potential (d := 2) (by norm_num) _ isNorm_euclidean (1 / 4) (by norm_num)
    plane_ellipticity

/-- In the plane, for the Euclidean norm and `ε = 1/4`, there are a subgradient field `ξ` with
`ξ 0 = 0` and a probability space carrying the walk driven by `ξ`. -/
theorem contact_potential_inhabited :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        CERW.IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (CERW.toSpace x) (ξ x)) ∧
      ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), CERW.IsDriftCERW μ (1 / 4) ξ X :=
  exists_euclidean_walk (by norm_num) (by norm_num) (by norm_num)

/-! ### `outer_crossing` -/

/-- The inner product of `e_i` with an embedded site is the `i`-th coordinate. -/
private theorem inner_coordVec_toSpace {d : ℕ} (i : Fin d) (z : Site d) :
    inner ℝ (CERW.coordVec i) (CERW.toSpace z) = ((z i : ℤ) : ℝ) := by
  simp [CERW.coordVec, EuclideanSpace.inner_single_left]

/-- A unit step changes every coordinate by at most one. -/
private theorem abs_apply_le_one_of_mem_unitSteps {d : ℕ} {e : Site d}
    (he : e ∈ CERW.unitSteps d) (j : Fin d) : |((e j : ℤ) : ℝ)| ≤ 1 := by
  obtain ⟨i, rfl | rfl⟩ := CERW.mem_unitSteps.mp he
  · by_cases h : j = i
    · subst h
      simp [LatticeProb.unit]
    · simp [LatticeProb.unit, h]
  · by_cases h : j = i
    · subst h
      simp [LatticeProb.unit]
    · simp [LatticeProb.unit, h]

/-- A function that changes by at most one along unit steps has a Dynkin martingale of absolute
value at most `2t` at time `t`, for the drift walk with ellipticity `ε ≤ 1/d`. -/
private theorem abs_dynkinMart_le {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    {f : Site d → ℝ} (hf : ∀ z e, e ∈ CERW.unitSteps d → |f (z + e) - f z| ≤ 1)
    {x : ℕ → Site d} (hx : ∀ j, x (j + 1) - x j ∈ CERW.unitSteps d) (t : ℕ) :
    |CERW.dynkinMart (CERW.driftStepProb d ε ξ) f x t| ≤ 2 * t := by
  have hstep : ∀ j, |f (x (j + 1)) - f (x j)| ≤ 1 := fun j => by
    have h := hf (x j) (x (j + 1) - x j) (hx j)
    rwa [add_sub_cancel] at h
  have hmean : ∀ j, |CERW.stepMean (CERW.driftStepProb d ε ξ) f x j| ≤ 1 := by
    intro j
    unfold CERW.stepMean
    calc |∑ e ∈ CERW.unitSteps d,
          CERW.driftStepProb d ε ξ x j e * (f (x j + e) - f (x j))|
        ≤ ∑ e ∈ CERW.unitSteps d,
          |CERW.driftStepProb d ε ξ x j e * (f (x j + e) - f (x j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ CERW.unitSteps d, CERW.driftStepProb d ε ξ x j e := by
          refine Finset.sum_le_sum fun e he => ?_
          have hp := CERW.Support.Drift.driftStepProb_nonneg hε hξ x j e
          rw [abs_mul, abs_of_nonneg hp]
          calc CERW.driftStepProb d ε ξ x j e * |f (x j + e) - f (x j)|
              ≤ CERW.driftStepProb d ε ξ x j e * 1 :=
                mul_le_mul_of_nonneg_left (hf _ _ he) hp
            _ = CERW.driftStepProb d ε ξ x j e := mul_one _
      _ = 1 := CERW.Support.Drift.sum_driftStepProb hd ε ξ x j
  have hdiff : ∀ s : ℕ, |f (x s) - f (x 0)| ≤ s := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      calc |f (x (s + 1)) - f (x 0)|
          = |(f (x (s + 1)) - f (x s)) + (f (x s) - f (x 0))| := by ring_nf
        _ ≤ |f (x (s + 1)) - f (x s)| + |f (x s) - f (x 0)| := abs_add_le _ _
        _ ≤ 1 + s := add_le_add (hstep s) ih
        _ = ((s + 1 : ℕ) : ℝ) := by push_cast; ring
  have hsum : |∑ j ∈ Finset.range t, CERW.stepMean (CERW.driftStepProb d ε ξ) f x j| ≤ t := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range t, |CERW.stepMean (CERW.driftStepProb d ε ξ) f x j|
        ≤ ∑ _j ∈ Finset.range t, (1 : ℝ) := Finset.sum_le_sum fun j _ => hmean j
      _ = t := by simp
  unfold CERW.dynkinMart
  calc |f (x t) - f (x 0) - ∑ j ∈ Finset.range t, CERW.stepMean (CERW.driftStepProb d ε ξ) f x j|
      ≤ |f (x t) - f (x 0)| +
        |∑ j ∈ Finset.range t, CERW.stepMean (CERW.driftStepProb d ε ξ) f x j| := abs_sub _ _
    _ ≤ t + t := add_le_add (hdiff t) hsum
    _ = 2 * t := by ring

/-- The position `X_u` and the drift sum of `Z_u` in `outer_crossing` have norm at most
`|X_u| + ε u` when every direction `ξ z` has norm at most one. -/
private theorem norm_position_add_drift_le {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    {ξ : Site d → EuclideanSpace ℝ (Fin d)} (hξ : ∀ z, ‖ξ z‖ ≤ 1) (x : ℕ → Site d) (u : ℕ) :
    ‖CERW.toSpace (x u) + ε • ∑ j ∈ Finset.range u,
        (if x j ∉ CERW.departureRange x j then ξ (x j) else 0)‖
      ≤ ‖CERW.toSpace (x u)‖ + ε * u := by
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
  refine mul_le_mul_of_nonneg_left ?_ hε
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ Finset.range u, ‖if x j ∉ CERW.departureRange x j then ξ (x j) else 0‖
      ≤ ∑ _j ∈ Finset.range u, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs
        · simp
        · exact hξ (x j)
    _ = u := by simp

/-- On the straight path along the first axis in the plane, with `q = e₁`, `h = 1`, `n = 2`,
for the Euclidean norm with `ε = 1/4`, `α = 1/2` and `C₁ = 20`, all hypotheses of
`outer_crossing` hold, and its constant `C` bounds the top of the walk in direction `q` by the
level `max (T - 1) b` plus `C (1 + M_b) log n`. -/
theorem outer_crossing_applies :
    let x : ℕ → Site 2 := fun j => (j : ℤ) • LatticeProb.unit 0
    let q : EuclideanSpace ℝ (Fin 2) := CERW.coordVec 0
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 ≤ b →
      inner ℝ q (CERW.toSpace (x 2)) ≤ max (inner ℝ q (CERW.toSpace (x 2)) - 1) b +
        C * (1 + ((((CERW.departureRange x 2).filter
          (fun z => b ≤ inner ℝ q (CERW.toSpace z))).sup (CERW.localTime x 2) : ℕ) : ℝ)) *
          Real.log 2 := by
  intro x q
  have hΛ := normMax_euclidean (d := 2) (by norm_num)
  have hq1 : ‖q‖ = 1 := norm_coordVec 0
  have hqz : ∀ z : Site 2, inner ℝ q (CERW.toSpace z) = ((z 0 : ℤ) : ℝ) :=
    fun z => inner_coordVec_toSpace 0 z
  have hx0 : x 0 = 0 := by simp [x]
  have hxj : ∀ j : ℕ, ((x j 0 : ℤ) : ℝ) = j := fun j => by simp [x, LatticeProb.unit]
  have hqx : ∀ j : ℕ, inner ℝ q (CERW.toSpace (x j)) = j := fun j => by rw [hqz, hxj]
  have hxs : ∀ j : ℕ, CERW.toSpace (x j) = (j : ℝ) • q := fun j => by
    ext i
    fin_cases i
    · simp [x, q, CERW.coordVec, LatticeProb.unit]
    · simp [x, q, CERW.coordVec, LatticeProb.unit]
  have hxn : ∀ j : ℕ, ‖CERW.toSpace (x j)‖ = j := fun j => by
    rw [hxs, norm_smul, hq1]
    simp
  have hsteps : ∀ j, x (j + 1) - x j ∈ CERW.unitSteps 2 := fun j => by
    refine CERW.mem_unitSteps.mpr ⟨0, Or.inl ?_⟩
    simp only [x]
    rw [← sub_smul]
    have hcoeff : (((j + 1 : ℕ) : ℤ) - ((j : ℕ) : ℤ)) = 1 := by push_cast; ring
    rw [hcoeff, one_smul]
  have hξ1 : ∀ z : Site 2, ‖CERW.unitDir (CERW.toSpace z)‖ ≤ 1 := fun z => CERW.norm_unitDir_le _
  have hξc : ∀ (z : Site 2) (i : Fin 2),
      (1 / 4 : ℝ) * |CERW.unitDir (CERW.toSpace z) i| ≤ 1 / ((2 : ℕ) : ℝ) := fun z i => by
    have := abs_unitDir_apply_le (CERW.toSpace z) i
    norm_num
    linarith
  have hlog := Real.log_two_gt_d9
  obtain ⟨C, hC, hmain⟩ := CERW.Frozen.outer_crossing (d := 2) (by norm_num) _ isNorm_euclidean
    (1 / 4) (by norm_num) plane_ellipticity (1 / 2) (by norm_num) 20 (by norm_num)
  refine ⟨C, hC, fun b hb => ?_⟩
  have hmain' := hmain (fun z => CERW.unitDir (CERW.toSpace z))
    (fun z hz => unitDir_isSubgradient hz) unitDir_toSpace_zero 2 le_rfl q
    (by rw [hΛ, hq1]) x hx0 hsteps
  dsimp only at hmain'
  refine hmain' ?_ ?_ 2 le_rfl ?_ 1 one_pos ?_ b hb
  · intro s t hst ht
    have hst' : (s : ℝ) + 1 ≤ t := by exact_mod_cast hst
    have ht' : (t : ℝ) ≤ 2 := by exact_mod_cast ht
    have h1 := norm_position_add_drift_le (ε := 1 / 4) (by norm_num) hξ1 x t
    have h2 := norm_position_add_drift_le (ε := 1 / 4) (by norm_num) hξ1 x s
    rw [hxn] at h1 h2
    have hlog' : (1 / 4 : ℝ) ≤ ((t : ℝ) - s) * Real.log ((2 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    have hsq : (1 / 2 : ℝ) ≤ Real.sqrt (((t : ℝ) - s) * Real.log ((2 : ℕ) : ℝ)) :=
      Real.le_sqrt_of_sq_le (by linarith)
    refine (norm_sub_le _ _).trans ?_
    linarith
  · intro k hk
    have hf : ∀ z e, e ∈ CERW.unitSteps 2 →
        |max (inner ℝ q (CERW.toSpace (z + e)) - (k : ℝ) * CERW.normMax
            (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖)) 0 -
          max (inner ℝ q (CERW.toSpace z) - (k : ℝ) * CERW.normMax
            (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖)) 0| ≤ 1 := by
      intro z e he
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      rw [hqz, hqz]
      have h := abs_apply_le_one_of_mem_unitSteps he 0
      have hadd : (((z + e) 0 : ℤ) : ℝ) = ((z 0 : ℤ) : ℝ) + ((e 0 : ℤ) : ℝ) := by
        simp
      rw [hadd]
      simpa using h
    have h1 := abs_dynkinMart_le (d := 2) (by norm_num) (ε := 1 / 4) (by norm_num) hξc
      (f := fun z => max (inner ℝ q (CERW.toSpace z) - (k : ℝ) * CERW.normMax
        (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖)) 0) hf hsteps 2
    refine h1.trans ?_
    have h0 := Real.sqrt_nonneg
      (Real.log ((2 : ℕ) : ℝ) * ∑ z ∈ (CERW.departureRange x 2).filter
        (fun z => (k : ℝ) * CERW.normMax (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) -
          CERW.normMax (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) < inner ℝ q (CERW.toSpace z)),
        (CERW.localTime x 2 z : ℝ))
    have hl : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
    rw [hl] at h0 ⊢
    push_cast
    linarith
  · intro j hj
    rw [hqx, hqx]
    exact_mod_cast hj
  · intro j hj hlt
    have hj2 : j = 2 := by
      simp only [hqx] at hlt
      have hlt' : (1 : ℝ) < (j : ℝ) := by
        have hcast : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
        rw [hcast] at hlt
        exact hlt
      have h3 : 1 < j := by exact_mod_cast hlt'
      omega
    subst hj2
    show (1 / 2 : ℝ) ≤ inner ℝ q (CERW.unitDir (CERW.toSpace (x 2)))
    rw [CERW.unitDir, real_inner_smul_right, hxn, hqx]
    norm_num

end CERW.Support.Guards
