import CERW.Frozen.FluctuationRates
import CERW.Frozen.InnerRadius
import CERW.Frozen.NearFar
import CERW.Frozen.OuterRadius
import CERW.Frozen.SharpRadii
import CERW.Support.Law.Existence

/-!
# Guards for the radii results

Non-vacuity guards for `CERW.Frozen.inner_radius`, `outer_radius`, `near_far`,
`fluctuation_rates` and `sharp_radii`. Each probabilistic statement is applied at `d = 2`,
`ε = 1/4`, `p = 1`, and the hypothesis `IsCERW μ ε X` is shown to be inhabited there.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Guards

/-- In the plane with `ε = 1/4`, there is a probability space carrying centrally excited random
walk, so the hypothesis `IsCERW μ ε X` of the radii results can be met. -/
theorem inner_radius_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 4) X :=
  CERW.Support.Law.exists_isCERW (by norm_num) (by norm_num) (by norm_num)

/-- The inner-radius, volume and local-time bounds hold at `d = 2`, `ε = 1/4`, `p = 1`. -/
theorem inner_radius_applies :
    let d : ℕ := 2
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let ε : ℝ := 1 / 4
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let q : ℕ → ℝ := fun n =>
      if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n
    let p : ℝ := 1
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (|CERW.innerRadius (X · ω) n - r n| ≤ C * r n * q n ∧
                  volume (((r n)⁻¹ • CERW.cellSet (X · ω) n) ∆
                      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
                    ≤ ENNReal.ofReal (C * q n) ∧
                  ∀ y : EuclideanSpace ℝ (Fin d),
                    |CERW.cellLocalTime (X · ω) n y - 2 * d * ε * max (r n - ‖y‖) 0|
                      ≤ C * r n * q n ^ ((1 : ℝ) / d))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) :=
  CERW.Frozen.inner_radius (d := 2) (by norm_num) (1 / 4) (by norm_num) (by norm_num) 1
    one_pos

/-- In the plane with `ε = 1/4`, there is a probability space carrying centrally excited random
walk, so the hypothesis `IsCERW μ ε X` of the outer-radius result can be met. -/
theorem outer_radius_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 4) X :=
  CERW.Support.Law.exists_isCERW (by norm_num) (by norm_num) (by norm_num)

/-- The outer-radius bound holds at `d = 2`, `ε = 1/4`, `p = 1`. -/
theorem outer_radius_applies :
    let d : ℕ := 2
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let ε : ℝ := 1 / 4
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let p : ℝ := 1
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ CERW.maxRadius (X · ω) n ≤ r n + C *
            (if d = 2 then Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
              else Real.log n ^ ((d : ℝ) + 1))}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) :=
  CERW.Frozen.outer_radius (d := 2) (by norm_num) (1 / 4) (by norm_num) (by norm_num) 1
    one_pos

/-- The centre `(3/2) e₀` of the ball used as the set `D` in the near-far guard. -/
private noncomputable abbrev nearFarCentre : EuclideanSpace ℝ (Fin 2) :=
  (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- The centre `(3/2) e₀` has norm `3/2`. -/
private theorem norm_nearFarCentre : ‖nearFarCentre‖ = 3 / 2 := by
  simp [nearFarCentre, norm_smul]

/-- The ball of radius `1/4` about `(3/2) e₀` lies in the annulus `1 ≤ |v| ≤ 2`. -/
private theorem ball_subset_annulus :
    Metric.ball nearFarCentre (1 / 4) ⊆ {v | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ 1 + 1} := by
  intro v hv
  have hdist : ‖v - nearFarCentre‖ < 1 / 4 := by
    rwa [Metric.mem_ball, dist_eq_norm] at hv
  have h1 : ‖nearFarCentre‖ - ‖v‖ ≤ ‖v - nearFarCentre‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  have h2 : ‖v‖ - ‖nearFarCentre‖ ≤ ‖v - nearFarCentre‖ := norm_sub_norm_le _ _
  rw [norm_nearFarCentre] at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- The volume of the ball of radius `1/4` is `π/16`, which is positive and at most `1`. -/
private theorem volume_ball_nearFar :
    volume (Metric.ball nearFarCentre (1 / 4)) = ENNReal.ofReal (Real.pi / 16) := by
  rw [EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- The near-far bound on the positive potential holds in the plane for `ε = 1/4`, `w = b = λ = 1`
and the ball of radius `1/4` about `(3/2) e₀` in the annulus `1 ≤ |v| ≤ 2`. -/
theorem near_far_applies :
    let d : ℕ := 2
    let ε : ℝ := 1 / 4
    let w : ℝ := 1
    let b : ℝ := 1
    let lam : ℝ := 1
    let D : Set (EuclideanSpace ℝ (Fin d)) :=
      Metric.ball ((3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (1 / 4)
    ∃ C : ℝ, 0 < C ∧ ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
      CERW.positivePotential d ε D y ≤ C * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + C * lam := by
  obtain ⟨C, hC, h⟩ := CERW.Frozen.near_far (d := 2) le_rfl (1 / 4) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun y hy1 hy2 => ?_⟩
  have hpi : Real.pi / 16 ≤ 1 := by linarith [Real.pi_lt_four]
  refine h 1 1 1 le_rfl le_rfl le_rfl (Metric.ball nearFarCentre (1 / 4))
    Metric.isOpen_ball.measurableSet ball_subset_annulus ?_ ?_ y hy1 hy2
  · intro u _ t ht
    calc volume (Metric.ball nearFarCentre (1 / 4) ∩ Metric.ball ((1 + 1 : ℝ) • u) t)
        ≤ volume (Metric.ball nearFarCentre (1 / 4)) := measure_mono Set.inter_subset_left
      _ = ENNReal.ofReal (Real.pi / 16) := volume_ball_nearFar
      _ ≤ ENNReal.ofReal (1 * t ^ (2 - 1)) :=
          ENNReal.ofReal_le_ofReal (by simpa using hpi.trans ht)
  · intro y
    have hexp : (2 : ℝ) - ((2 : ℕ) : ℝ) = 0 := by norm_num
    simp only [hexp, Real.rpow_zero, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
    rw [MeasureTheory.measureReal_def, volume_ball_nearFar,
      ENNReal.toReal_ofReal (by positivity)]
    linarith

/-- The ball of radius `1/4` about `(3/2) e₀` in the plane has positive volume, and the annulus
`1 ≤ |y| ≤ 2` that carries the conclusion of the near-far lemma contains points. -/
theorem near_far_inhabited :
    0 < volume (Metric.ball ((3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (1 / 4)) ∧
      ∃ y : EuclideanSpace ℝ (Fin 2), 1 ≤ ‖y‖ ∧ ‖y‖ ≤ 1 + 1 := by
  refine ⟨?_, nearFarCentre, ?_, ?_⟩
  · rw [volume_ball_nearFar]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  · rw [norm_nearFarCentre]
    norm_num
  · rw [norm_nearFarCentre]
    norm_num

/-- In the plane with `ε = 1/4`, there is a probability space carrying centrally excited random
walk, so the hypothesis `IsCERW μ ε X` of the fluctuation bounds can be met. -/
theorem fluctuation_rates_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 4) X :=
  CERW.Support.Law.exists_isCERW (by norm_num) (by norm_num) (by norm_num)

/-- The fluctuation bounds, with high probability and almost surely eventually, hold at `d = 2`,
`ε = 1/4`, `p = 1`. -/
theorem fluctuation_rates_applies :
    let d : ℕ := 2
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let ε : ℝ := 1 / 4
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let Good : ℝ → (ℕ → Site d) → ℕ → Prop := fun C Y n =>
      (if d = 2 then
          |CERW.innerRadius Y n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
            CERW.maxRadius Y n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
        else
          |CERW.innerRadius Y n - r n| ≤ C * Real.log n ∧
            CERW.maxRadius Y n - r n ≤ C * Real.log n ^ ((d : ℝ) + 1)) ∧
      volume (((r n)⁻¹ • CERW.cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          ≤ ENNReal.ofReal
            (C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) ∧
      ∀ x : Site d,
        |(CERW.localTime Y n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ C * if d = 2 then Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)
            else Real.sqrt (r n * Real.log n)
    let p : ℝ := 1
    ∃ C : ℝ, 0 < C ∧
      (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ Good C (X · ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p))) ∧
      (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Good C (X · ω) n) :=
  CERW.Frozen.fluctuation_rates (d := 2) (by norm_num) (1 / 4) (by norm_num) (by norm_num) 1
    one_pos

/-- In the plane with `ε = 1/4`, there is a probability space carrying centrally excited random
walk, so the hypothesis `IsCERW μ ε X` of the sharpness of the radii can be met. -/
theorem sharp_radii_inhabited :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), CERW.IsCERW μ (1 / 4) X :=
  CERW.Support.Law.exists_isCERW (by norm_num) (by norm_num) (by norm_num)

/-- The polynomial lower bounds for the inner and outer radii in the plane hold at `ε = 1/4`,
`p = 1`. -/
theorem sharp_radii_applies :
    let d : ℕ := 2
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let ε : ℝ := 1 / 4
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    let p : ℝ := 1
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
        let Ein : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ r n - CERW.innerRadius (X · ω) n}
        let Eout : Set Ω :=
          {ω | c * Real.sqrt (r n * Real.log n) ≤ CERW.maxRadius (X · ω) n - r n}
        MeasurableSet Ein ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Ein ∧
          MeasurableSet Eout ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ Eout :=
  CERW.Frozen.sharp_radii (d := 2) rfl (1 / 4) (by norm_num) (by norm_num) 1 one_pos

end CERW.Support.Guards
