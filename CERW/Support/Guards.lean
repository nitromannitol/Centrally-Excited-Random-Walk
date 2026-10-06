import CERW.Model
import CERW.Support.Law
import CERW.Support.Guards.DriftCrossing
import CERW.Support.Guards.ExpDeviation
import CERW.Support.Guards.ExpDeviationConsumers
import CERW.Support.Guards.ExpDeviationModel
import CERW.Support.Guards.LimitLaws
import CERW.Support.Guards.LowerBounds
import CERW.Support.Guards.NormPotential
import CERW.Support.Guards.NormRates
import CERW.Support.Guards.NormShape
import CERW.Support.Guards.Radii
import CERW.Support.Guards.SourceEvents

/-!
# Guards: the vocabulary says what the paper says

Each guard pins one value of a definition that can be checked by hand against the paper.
`ω₂ = π` and `ω₃ = 4π/3` pin `unitBallVolume`. The first-departure probability of the
outward step from `(3, 4)` pins the sign and normalization of `eq:kernel`. The local times
over the departure range sum to the elapsed time. The first ranges are `A_0 = ∅` and
`V_0 = {X_0}`. The radius `a` of `eq:scale` solves `2dε ω_d a^{d+1}/(d+1) = 1`, the equation
that determines it in the proof. The existence of centrally excited random walk, the
non-vacuity witness for `IsCERW`, is `CERW.Support.Law.exists_isCERW`.
-/

namespace CERW.Support.Guards

open MeasureTheory LatticeProb CERW

/-- The area of the unit disc: `ω₂ = π`. -/
theorem unitBallVolume_two : unitBallVolume 2 = Real.pi := by
  rw [unitBallVolume, EuclideanSpace.volume_ball_fin_two]
  simp [ENNReal.toReal_ofReal Real.pi_pos.le]

/-- The volume of the unit ball of `ℝ³`: `ω₃ = 4π/3`. -/
theorem unitBallVolume_three : unitBallVolume 3 = Real.pi * 4 / 3 := by
  rw [unitBallVolume, EuclideanSpace.volume_ball_fin_three]
  simp [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi * 4 / 3)]

/-- At `x = (3, 4)`, with `|x| = 5` and `ε = 1/4`, the first departure steps outward to
`x + e₁` with probability `1/4 - (1/8)(3/5) = 7/40`, below the simple random walk value `1/4`:
the drift points to the origin. -/
theorem firstStep_three_four :
    firstStep 2 (1 / 4) ![3, 4] (unit 0) = 7 / 40 := by
  have hnorm : euclidNorm (![3, 4] : Site 2) = 5 := by
    rw [euclidNorm, Fin.sum_univ_two]
    norm_num
  rw [Support.Law.firstStep_unit, hnorm]
  norm_num

/-- The departure local times over the departure range sum to the elapsed time:
`Σ_{x ∈ A_n} ℓ_n(x) = n`. -/
theorem sum_localTime {d : ℕ} (X : ℕ → Site d) (n : ℕ) :
    ∑ x ∈ departureRange X n, localTime X n x = n := by
  simp only [departureRange, localTime]
  rw [← Finset.card_eq_sum_card_image X (Finset.range n), Finset.card_range]

/-- Before the first step nothing has been departed: `A_0 = ∅`. -/
theorem departureRange_zero {d : ℕ} (X : ℕ → Site d) : departureRange X 0 = ∅ := by
  simp [departureRange]

/-- The range at time zero is the starting point: `V_0 = {X_0}`. -/
theorem visitedRange_zero {d : ℕ} (X : ℕ → Site d) : visitedRange X 0 = {X 0} := by
  simp [visitedRange]

/-- The radius `a = ((d+1)/(2dεω_d))^{1/(d+1)}` of `eq:scale` is the positive root of
`2dε ω_d a^{d+1}/(d+1) = 1` (the equation before `eq:inradius`). -/
theorem limitRadius_spec {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    let a : ℝ := ((d + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))
    2 * d * ε * unitBallVolume d * a ^ (d + 1) / (d + 1) = 1 := by
  intro a
  have hω := unitBallVolume_pos d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hbase : 0 < ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d) := by positivity
  have hpow : a ^ (d + 1) = ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
    have hexp : (1 : ℝ) / (d + 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [hexp, Real.rpow_one]
  rw [hpow]
  field_simp

/-- The hypothesis family of the paper's probabilistic results is inhabited: in every dimension
`d ≥ 2` there are a parameter `0 < ε < 1/d` and a probability space carrying centrally excited
random walk with that parameter. -/
theorem exists_cerw_realization {d : ℕ} (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / (d : ℝ) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site d), IsCERW μ ε X := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine ⟨1 / (2 * d), by positivity, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) hdR]
    linarith
  · exact Support.Law.exists_isCERW (by omega) (by positivity)
      (by rw [div_lt_div_iff₀ (by positivity) hdR]; linarith)

end CERW.Support.Guards
