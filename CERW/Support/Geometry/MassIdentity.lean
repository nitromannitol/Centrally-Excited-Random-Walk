import CERW.Support.Geometry.Newton
import CERW.Support.Geometry.Holder
import CERW.Generic.Newton.Polar

/-!
# The mass identity

`eq:massidentity`: if `D ⊆ B(0, S)`, then `∫_{B(0,S)} U_D = 2ε ∫_D |v| dv`. In polar coordinates the
integral of `U_D` over the ball is `∫_0^S r^{d-1} σ_d 2dε F(r) dr`, by Newton's spherical average
`eq:newton`. Exchanging the integrals in `F`, `∫_0^S r^{d-1} F(r) dr = (d σ_d)⁻¹ ∫_D |v| dv`.
-/

namespace CERW.Support.Geometry

open MeasureTheory CERW

variable {d : ℕ}

/-- The radial integral of the exchanged weight: for `0 ≤ t ≤ S`,
`∫_0^S 1{r < t} r^{d-1} dr = t^d / d`. -/
private lemma integral_Ioo_indicator_pow (hd : 1 ≤ d) {S t : ℝ} (ht0 : 0 ≤ t) (htS : t ≤ S) :
    ∫ r in Set.Ioo 0 S, (Set.Iio t).indicator (fun r : ℝ => r ^ (d - 1)) r = t ^ d / d := by
  rw [setIntegral_indicator measurableSet_Iio, Set.Ioo_inter_Iio, min_eq_right htS,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht0, integral_pow]
  have h1 : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have h2 : ((d - 1 : ℕ) : ℝ) + 1 = d := by
    rw [Nat.cast_sub hd, Nat.cast_one, sub_add_cancel]
  rw [h1, h2, zero_pow (by omega), sub_zero]

/-- The exchanged weight `r ↦ 1{r < |v|} r^{d-1} |v|^{1-d}` integrates over `(0, S)` to `|v|/d`
whenever `|v| ≤ S`. -/
private lemma integral_Ioo_exchange (hd : 2 ≤ d) {S : ℝ} (v : EuclideanSpace ℝ (Fin d))
    (hvS : ‖v‖ ≤ S) :
    ∫ r in Set.Ioo 0 S, (if r < ‖v‖ then r ^ (d - 1) * ‖v‖ ^ (1 - (d : ℝ)) else 0) =
      ‖v‖ / d := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact this.ne'
  have hind : ∀ r : ℝ, (if r < ‖v‖ then r ^ (d - 1) * ‖v‖ ^ (1 - (d : ℝ)) else 0) =
      ‖v‖ ^ (1 - (d : ℝ)) * (Set.Iio ‖v‖).indicator (fun r : ℝ => r ^ (d - 1)) r := by
    intro r
    by_cases hr : r < ‖v‖
    · simp only [hr, if_true, Set.indicator_of_mem (Set.mem_Iio.mpr hr)]
      ring
    · simp only [hr, if_false, Set.indicator_of_notMem (mt Set.mem_Iio.mp hr), mul_zero]
  simp_rw [hind]
  rw [integral_const_mul, integral_Ioo_indicator_pow (by omega) (norm_nonneg v) hvS]
  have hmul : ‖v‖ ^ (1 - (d : ℝ)) * ‖v‖ ^ d = ‖v‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add' (norm_nonneg v) (by linarith), sub_add_cancel,
      Real.rpow_one]
  rw [← mul_div_assoc, hmul]

/-- The exchanged weight is jointly integrable over `(0, S) × D`. -/
private lemma integrable_exchange (hd : 2 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (S : ℝ) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      if p.1 < ‖p.2‖ then p.1 ^ (d - 1) * ‖p.2‖ ^ (1 - (d : ℝ)) else 0)
      ((volume.restrict (Set.Ioo 0 S)).prod (volume.restrict D)) := by
  have hmeas : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      if p.1 < ‖p.2‖ then p.1 ^ (d - 1) * ‖p.2‖ ^ (1 - (d : ℝ)) else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd.norm)
      ((measurable_fst.pow_const _).mul (measurable_snd.norm.pow_const _)) measurable_const
  have hker : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ))) D := by
    simpa using (Generic.Kernel.integrableOn_and_setIntegral_le (d := d) (by omega) hD hDfin 0).1
  have hbound : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      S ^ (d - 1) * ‖p.2‖ ^ (1 - (d : ℝ)))
      ((volume.restrict (Set.Ioo 0 S)).prod (volume.restrict D)) := by
    have hc : Integrable (fun _ : ℝ => S ^ (d - 1)) (volume.restrict (Set.Ioo 0 S)) :=
      integrable_const _
    exact hc.mul_prod hker
  refine hbound.mono' hmeas.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (measurableSet_Ioo.prod hD) fun p hp => ?_
  have hnn : 0 ≤ ‖p.2‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  split_ifs
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hp.1.1.le _) hnn)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp.1.1.le hp.1.2.le _) hnn
  · rw [norm_zero]
    exact mul_nonneg (pow_nonneg (hp.1.2.le.trans' hp.1.1.le) _) hnn

/-- The radial average of the weighted exterior volume: for `D ⊆ B(0, S)`,
`∫_0^S r^{d-1} F(r) dr = (d σ_d)⁻¹ ∫_D |v| dv`, by Tonelli. -/
private lemma integral_Ioo_pow_mul_tail (hd : 2 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {S : ℝ} (hDS : D ⊆ Metric.ball 0 S) :
    ∫ r in Set.Ioo 0 S, r ^ (d - 1) * tail d D r =
      (d * unitBallVolume d)⁻¹ * ((d : ℝ)⁻¹ * ∫ v in D, ‖v‖) := by
  have hDfin : volume D ≠ ⊤ := (measure_mono hDS |>.trans_lt measure_ball_lt_top).ne
  have hpt : ∀ r : ℝ, r ^ (d - 1) * tail d D r = (d * unitBallVolume d)⁻¹ *
      ∫ v in D, (if r < ‖v‖ then r ^ (d - 1) * ‖v‖ ^ (1 - (d : ℝ)) else 0) := by
    intro r
    have hset : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | r < ‖v‖} :=
      measurableSet_lt measurable_const measurable_norm
    have hind : ∀ v : EuclideanSpace ℝ (Fin d),
        (if r < ‖v‖ then r ^ (d - 1) * ‖v‖ ^ (1 - (d : ℝ)) else 0) =
          {v : EuclideanSpace ℝ (Fin d) | r < ‖v‖}.indicator
            (fun v => r ^ (d - 1) * ‖v‖ ^ (1 - (d : ℝ))) v := fun v => by
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    simp_rw [hind]
    rw [setIntegral_indicator hset, integral_const_mul, tail]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_integral_swap (integrable_exchange hd hD hDfin S)]
  congr 1
  rw [setIntegral_congr_fun hD fun v hv => integral_Ioo_exchange hd v
    (mem_ball_zero_iff.mp (hDS hv)).le, integral_div, inv_mul_eq_div]

/-- A function on `ℝ^d` satisfying a Hölder bound of exponent `1/2` is continuous. -/
private lemma continuous_of_holder_half {A : ℝ} (hA : 0 ≤ A)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : ∀ y z, |f y - f z| ≤ A * ‖y - z‖ ^ ((1 : ℝ) / 2)) : Continuous f := by
  have hholder : HolderWith A.toNNReal (1 / 2 : NNReal) f := by
    intro y z
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num)]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal A * _
    rw [← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.dist_eq, dist_eq_norm] using h y z)
  exact hholder.continuous (by norm_num)

/-- The potential of a measurable set of finite volume is integrable on every ball. -/
private lemma integrableOn_ball_potential (hd : 2 ≤ d) (ε : ℝ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (S : ℝ) :
    IntegrableOn (potential d ε D) (Metric.ball 0 S) := by
  obtain ⟨C, hC0, hC⟩ := exists_potential_holder hd
  have hcont1 : Continuous (potential d 1 D) :=
    continuous_of_holder_half (A := C * 1 * (volume D).toReal ^ ((1 : ℝ) / (2 * d)))
      (by positivity) fun y z => hC 1 zero_le_one D hD hDfin y z
  have hscale : potential d ε D = fun y => ε * potential d 1 D y := by
    funext y
    unfold potential
    ring
  have hcont : Continuous (potential d ε D) := by
    rw [hscale]
    exact continuous_const.mul hcont1
  exact (hcont.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set Metric.ball_subset_closedBall

/-- `eq:massidentity`: for a bounded measurable `D ⊆ B(0, S)`, `∫_{B(0,S)} U_D = 2ε ∫_D |v| dv`. -/
theorem integral_ball_potential (hd : 2 ≤ d) (ε : ℝ) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {S : ℝ} (hDS : D ⊆ Metric.ball 0 S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, potential d ε D y =
      2 * ε * ∫ v in D, ‖v‖ := by
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDS
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hω := unitBallVolume_pos d
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact this.ne'
  have hint := integrableOn_ball_potential hd ε hD hDfin S
  have hpolar := Generic.Newton.integral_eq_integral_Ioi_sphere (by omega : 1 ≤ d)
    ((integrable_indicator_iff measurableSet_ball).2 hint)
  rw [integral_indicator measurableSet_ball] at hpolar
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      r ^ (d - 1) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S).indicator (potential d ε D)
          (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      (Set.Iio S).indicator (fun r : ℝ => r ^ (d - 1) * ∫ θ : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin d)) 1, potential d ε D (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) r := by
    intro r hr
    have hnorm : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := fun θ => by
      have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
        rw [← dist_zero_right]
        exact Metric.mem_sphere.mp θ.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hθ, mul_one]
    by_cases hrS : r < S
    · rw [Set.indicator_of_mem (Set.mem_Iio.mpr hrS)]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      exact Set.indicator_of_mem (mem_ball_zero_iff.mpr (by rw [hnorm θ]; exact hrS)) _
    · rw [Set.indicator_of_notMem (mt Set.mem_Iio.mp hrS)]
      have hz : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S).indicator (potential d ε D)
            (r • (θ : EuclideanSpace ℝ (Fin d))) = 0 := fun θ =>
        Set.indicator_of_notMem (fun h => hrS (by rw [← hnorm θ]; exact mem_ball_zero_iff.mp h)) _
      simp [hz]
  rw [hpolar, setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  have hsph : ∀ r ∈ Set.Ioo (0 : ℝ) S,
      r ^ (d - 1) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        potential d ε D (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * d * ε * (d * unitBallVolume d) * (r ^ (d - 1) * tail d D r) := by
    intro r hr
    have h := sphere_average_potential hd ε hD hDb hr.1
    have h' : ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        potential d ε D (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        d * unitBallVolume d * (2 * d * ε * tail d D r) := by
      rw [← h]
      field_simp
    rw [h']
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hsph, integral_const_mul,
    integral_Ioo_pow_mul_tail hd hD hDS]
  field_simp

end CERW.Support.Geometry
