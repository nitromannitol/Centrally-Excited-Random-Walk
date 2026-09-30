import CERW.Support.Occupation.CellIntegral
import CERW.Support.Occupation.CellNorm
import CERW.Support.Geometry.Holder
import CERW.Support.Geometry.Bound

/-!
# The mass error

`eq:coarse-masserror`, before the mass identity is inserted: if `D_n ⊆ B(0, S)` and
`|ℓ̃_n - U_{D_n}| ≤ δ` on `B(0, S)`, then `|n - ∫_{B(0,S)} U_{D_n}| ≤ ω_d S^d δ`. The cell
local time integrates to `n` over any measurable superset of `D_n`, and the error is integrated
over a ball of volume `ω_d S^d`.
-/

namespace CERW.Support.Coarse

open MeasureTheory LatticeProb CERW CERW.Support.Occupation CERW.Support.Geometry
open scoped NNReal ENNReal

variable {d : ℕ}

/-- The cell-center map is measurable. -/
private theorem measurable_cellCenter :
    Measurable (cellCenter : EuclideanSpace ℝ (Fin d) → Site d) := by
  rw [measurable_pi_iff]
  intro i
  exact Measurable.floor
    (((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))).add_const (1 / 2))

/-- The local time, as a function of the site, is measurable. -/
private theorem measurable_localTime (X : ℕ → Site d) (n : ℕ) :
    Measurable (fun x : Site d => (localTime X n x : ℝ)) :=
  measurable_of_countable _

/-- The cell local time is measurable. -/
private theorem measurable_cellLocalTime (X : ℕ → Site d) (n : ℕ) :
    Measurable (cellLocalTime X n) :=
  (measurable_localTime X n).comp measurable_cellCenter

/-- A function on `ℝ^d` satisfying a Hölder bound of exponent `1/2` is continuous. -/
private theorem continuous_of_holder_half {A : ℝ} (hA : 0 ≤ A)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : ∀ y z, |f y - f z| ≤ A * ‖y - z‖ ^ ((1 : ℝ) / 2)) : Continuous f := by
  have hholder : HolderWith (NNReal.mk A hA) (1 / 2 : ℝ≥0) f := by
    intro y z
    rw [edist_dist, edist_dist]
    rw [← ENNReal.ofReal_eq_coe_nnreal hA]
    rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num)]
    rw [← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.dist_eq, dist_eq_norm] using h y z)
  exact hholder.continuous (by norm_num)

/-- `|n - ∫_{B(0,S)} U_{D_n}| ≤ ω_d S^d δ` when `D_n ⊆ B(0, S)` and `|ℓ̃_n - U_{D_n}| ≤ δ`
there. -/
theorem abs_sub_integral_potential_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (X : ℕ → Site d)
    (n : ℕ) {S δ : ℝ} (hS : 0 < S) (hDS : cellSet X n ⊆ Metric.ball 0 S)
    (happrox : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime X n y - potential d ε (cellSet X n) y| ≤ δ) :
    |(n : ℝ) - ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        potential d ε (cellSet X n) y| ≤ unitBallVolume d * S ^ d * δ := by
  have hDmeas : MeasurableSet (cellSet X n) := measurableSet_cellSet X n
  have hDfin : volume (cellSet X n) ≠ ⊤ := by
    rw [volume_cellSet]
    exact ENNReal.natCast_ne_top _
  have hballmeas : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) :=
    measurableSet_ball
  have hballfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) < ∞ :=
    measure_ball_lt_top
  -- the cell local time integrates to `n` on the ball
  have hcellint : ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      cellLocalTime X n y = n :=
    setIntegral_cellLocalTime_of_subset X n hballmeas hDS
  -- the potential is Hölder, hence continuous and integrable on the ball
  obtain ⟨C, hC0, hCholder⟩ := exists_potential_holder hd
  have hholder : ∀ y z, |potential d ε (cellSet X n) y - potential d ε (cellSet X n) z| ≤
      C * ε * (volume (cellSet X n)).toReal ^ ((1 : ℝ) / (2 * d)) *
        ‖y - z‖ ^ ((1 : ℝ) / 2) :=
    fun y z => hCholder ε hε (cellSet X n) hDmeas hDfin y z
  have hA0 : 0 ≤ C * ε * (volume (cellSet X n)).toReal ^ ((1 : ℝ) / (2 * d)) := by
    positivity
  have hcont : Continuous (potential d ε (cellSet X n)) :=
    continuous_of_holder_half hA0 hholder
  have hpotint : IntegrableOn (potential d ε (cellSet X n))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) :=
    ((hcont.continuousOn).integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
        Metric.ball_subset_closedBall
  -- the cell local time is bounded, hence integrable on the ball
  have hcellint_on : IntegrableOn (cellLocalTime X n)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) := by
    refine IntegrableOn.of_bound hballfin
      (measurable_cellLocalTime X n).aestronglyMeasurable.restrict (maxLocalTime X n : ℝ) ?_
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (cellLocalTime_nonneg X n v)]
    show (localTime X n (cellCenter v) : ℝ) ≤ (maxLocalTime X n : ℝ)
    exact_mod_cast localTime_le_maxLocalTime X n (cellCenter v)
  -- rewrite the difference as the integral of the pointwise error
  have hsub := integral_sub hcellint_on hpotint
  have hmain : ‖∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        (cellLocalTime X n y - potential d ε (cellSet X n) y)‖
        = |(n : ℝ) - ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
            potential d ε (cellSet X n) y| := by
    rw [hsub, hcellint, Real.norm_eq_abs]
  -- bound the error integral by `δ` times the volume of the ball
  have hbound : ‖∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        (cellLocalTime X n y - potential d ε (cellSet X n) y)‖
        ≤ δ * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal :=
    norm_setIntegral_le_of_norm_le_const hballfin fun y hy => by
      rw [Real.norm_eq_abs]
      exact happrox y hy
  -- the volume of the ball is `S ^ d * ω_d`
  have hvol : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal =
      S ^ d * unitBallVolume d := by
    rw [Measure.addHaar_ball_of_pos (μ := volume) (0 : EuclideanSpace ℝ (Fin d)) hS,
      finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hfinal : δ * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal =
      unitBallVolume d * S ^ d * δ := by
    rw [hvol]
    ring
  rw [← hmain]
  exact hbound.trans_eq hfinal

end CERW.Support.Coarse
