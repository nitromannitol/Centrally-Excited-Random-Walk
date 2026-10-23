import CERW.LimitShapes.Curvature.NearFarKernel
import CERW.Support.Outer.NearFar

/-! # The near–far estimate with a bounded radius ratio (`lem:near-far`) -/

open MeasureTheory Filter
open private lintegral_far_le integrableOn_rpow_two_sub
  norm_unitDir_of_ne ball_subset_cap
  from CERW.Support.Outer.NearFar

namespace CERW.LimitShapes.Curvature

open CERW MeasureTheory CERW.Generic.Kernel CERW.Support.Geometry CERW.Support.Outer

/-- The near–far estimate of `lem:near-far` with a bounded radius ratio. -/
theorem exists_positivePotential_bound_of_cap {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b w lam : ℝ), 0 < b → 1 ≤ w → w ≤ K * b → 1 ≤ lam →
      ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
        (∀ v ∈ D, b ≤ ‖v‖ ∧ ‖v‖ ≤ b + w) →
        (∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ∀ t : ℝ, w ≤ t →
          volume.real (D ∩ Metric.ball ((b + w) • u) t) ≤ lam * t ^ (d - 1)) →
        (∀ y : EuclideanSpace ℝ (Fin d), ∫ v in D,
          ‖v - y‖ ^ ((2 : ℝ) - d) ≤ lam * b) →
      ∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ → ‖y‖ ≤ b + w →
        positivePotential d ε D y ≤
          C * ((lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + lam) := by
  have hd1 : 1 ≤ d := by omega
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = d * unitBallVolume d
      * (2 ^ (d - 1) / unitBallVolume d) ^ ((1 : ℝ) / d) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = 1 / 2 + (K + 2) / 2 * 2 ^ d * 2 ^ (d - 1) := ⟨_, rfl⟩
  have hK₁pos : 0 < K₁ := by
    rw [hK₁]
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    positivity
  have hK₂pos : 0 < K₂ := by rw [hK₂]; positivity
  refine ⟨2 * ε / unitBallVolume d * (K₁ + K₂), by positivity, ?_⟩
  intro b w lam hb hw hwb hlam D hD hDsub hcap hint y hyb hyb'
  have hwpos : 0 < w := by linarith
  have hlam0 : 0 < lam := by linarith
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith)
  have hDball : D ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (b + w) :=
    fun v hv => mem_closedBall_zero_iff.mpr (hDsub v hv).2
  have hDfin : volume D ≠ ⊤ :=
    ((measure_mono hDball).trans_lt measure_closedBall_lt_top).ne
  have hcap' : ∀ t : ℝ, w ≤ t →
      volume (D ∩ Metric.ball y t) ≤ ENNReal.ofReal (2 ^ (d - 1) * lam * t ^ (d - 1)) := by
    intro t ht
    calc volume (D ∩ Metric.ball y t)
        ≤ volume (D ∩ Metric.ball ((b + w) • unitDir y) (2 * t)) :=
          measure_mono (Set.inter_subset_inter_right _ (ball_subset_cap hyb hyb' hy0 ht))
      _ ≤ ENNReal.ofReal (lam * (2 * t) ^ (d - 1)) :=
          (ENNReal.ofReal_toReal
            (measure_ne_top_of_subset Set.inter_subset_left hDfin)).symm.le.trans
            (ENNReal.ofReal_le_ofReal (hcap _ (norm_unitDir_of_ne hy0) _ (by linarith)))
      _ = ENNReal.ofReal (2 ^ (d - 1) * lam * t ^ (d - 1)) := by
          rw [mul_pow]
          congr 1
          ring
  have hmeasf : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
      max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0) := by
    have hdir : Measurable (fun v : EuclideanSpace ℝ (Fin d) => unitDir v) := by
      change Measurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖⁻¹ • v)
      fun_prop
    have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
      measurable_id.sub measurable_const
    exact ((hdir.inner hsub).div (hsub.norm.pow_const d)).max measurable_const
  have hBm : MeasurableSet (Metric.ball y w) := Metric.isOpen_ball.measurableSet
  have hnear : ∫⁻ v in D ∩ Metric.ball y w,
      ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
      ≤ ENNReal.ofReal (K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)) := by
    have hfin' : volume (D ∩ Metric.ball y w) ≠ ⊤ :=
      measure_ne_top_of_subset Set.inter_subset_left hDfin
    obtain ⟨hint1, hle1⟩ := integrableOn_and_setIntegral_le hd1 (hD.inter hBm) hfin' y
    have hV : (volume (D ∩ Metric.ball y w)).toReal ≤ 2 ^ (d - 1) * lam * w ^ (d - 1) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hcap' w le_rfl)
    calc ∫⁻ v in D ∩ Metric.ball y w,
          ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
        ≤ ∫⁻ v in D ∩ Metric.ball y w, ENNReal.ofReal (‖v - y‖ ^ (1 - (d : ℝ))) :=
          setLIntegral_mono' (hD.inter hBm) fun v _ => ENNReal.ofReal_le_ofReal
            (max_le ((le_abs_self _).trans (abs_potentialIntegrand_le v y))
              (Real.rpow_nonneg (norm_nonneg _) _))
      _ = ENNReal.ofReal (∫ v in D ∩ Metric.ball y w, ‖v - y‖ ^ (1 - (d : ℝ))) :=
          (ofReal_integral_eq_lintegral_ofReal hint1
            (Filter.Eventually.of_forall fun v => Real.rpow_nonneg (norm_nonneg _) _)).symm
      _ ≤ ENNReal.ofReal (d * unitBallVolume d
            * ((volume (D ∩ Metric.ball y w)).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)) :=
          ENNReal.ofReal_le_ofReal hle1
      _ ≤ ENNReal.ofReal (K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          have hpow : ((volume (D ∩ Metric.ball y w)).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)
              ≤ (2 ^ (d - 1) / unitBallVolume d) ^ ((1 : ℝ) / d)
                * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) := by
            rw [← Real.mul_rpow (by positivity) (by positivity)]
            refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
            calc (volume (D ∩ Metric.ball y w)).toReal / unitBallVolume d
                ≤ 2 ^ (d - 1) * lam * w ^ (d - 1) / unitBallVolume d :=
                  div_le_div_of_nonneg_right hV hω.le
              _ = 2 ^ (d - 1) / unitBallVolume d * (lam * w ^ (d - 1)) := by ring
          calc d * unitBallVolume d
                * ((volume (D ∩ Metric.ball y w)).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)
              ≤ d * unitBallVolume d * ((2 ^ (d - 1) / unitBallVolume d) ^ ((1 : ℝ) / d)
                * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)) :=
                mul_le_mul_of_nonneg_left hpow (by positivity)
            _ = K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) := by rw [hK₁]; ring
  have hsubm : Measurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v - y‖) :=
    measurable_norm.comp (measurable_id.sub_const y)
  have hg2 : ∫⁻ v in D, ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)))
      ≤ ENNReal.ofReal (lam / 2) := by
    have hR : ∀ v ∈ D, ‖v - y‖ ≤ 2 * (b + w) := fun v hv =>
      calc ‖v - y‖ ≤ ‖v‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ 2 * (b + w) := by linarith [(hDsub v hv).2]
    have hint2 := (integrableOn_rpow_two_sub hd hD hDfin y hR).const_mul (1 / (2 * b))
    rw [← ofReal_integral_eq_lintegral_ofReal hint2
      (Filter.Eventually.of_forall fun v => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul]
    calc 1 / (2 * b) * ∫ v in D, ‖v - y‖ ^ (2 - (d : ℝ)) ≤ 1 / (2 * b) * (lam * b) :=
          mul_le_mul_of_nonneg_left (hint y) (by positivity)
      _ = lam / 2 := by field_simp
  have hg3 : ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal ((K + 2) * w / 2 * (‖v - y‖ ^ d)⁻¹)
      ≤ ENNReal.ofReal ((K + 2) / 2 * 2 ^ d * 2 ^ (d - 1) * lam) := by
    have hfar := lintegral_far_le hd1 hD y hwpos (by positivity) hcap'
    have hmeas3 : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹)) :=
      ENNReal.measurable_ofReal.comp (hsubm.pow_const d).inv
    calc ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal ((K + 2) * w / 2 * (‖v - y‖ ^ d)⁻¹)
        = ENNReal.ofReal ((K + 2) * w / 2)
            * ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal ((‖v - y‖ ^ d)⁻¹) := by
          rw [← lintegral_const_mul _ hmeas3]
          refine lintegral_congr fun v => ?_
          exact ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal ((K + 2) * w / 2) * ENNReal.ofReal (2 ^ d * (2 ^ (d - 1) * lam) / w) :=
          mul_le_mul_right hfar _
      _ = ENNReal.ofReal ((K + 2) / 2 * 2 ^ d * 2 ^ (d - 1) * lam) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  have hfar : ∫⁻ v in D \ Metric.ball y w,
      ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
      ≤ ENNReal.ofReal (K₂ * lam) := by
    have hpt : ∀ v ∈ D \ Metric.ball y w,
        ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
        ≤ ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)))
          + ENNReal.ofReal ((K + 2) * w / 2 * (‖v - y‖ ^ d)⁻¹) := by
      intro v hv
      have hvy : w ≤ ‖v - y‖ := by
        have := hv.2
        rwa [mem_ball_iff_norm, not_lt] at this
      obtain ⟨hv1, hv2⟩ := hDsub v hv.1
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (integrand_far_le_of_ratio hb hwpos hK hwb hv1 hv2 hyb hvy)
    have hmeas2 : Measurable (fun v : EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)))) :=
      ENNReal.measurable_ofReal.comp ((hsubm.pow_const _).const_mul _)
    calc ∫⁻ v in D \ Metric.ball y w,
          ENNReal.ofReal (max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
        ≤ ∫⁻ v in D \ Metric.ball y w, (ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ)))
            + ENNReal.ofReal ((K + 2) * w / 2 * (‖v - y‖ ^ d)⁻¹)) :=
          setLIntegral_mono' (hD.diff hBm) hpt
      _ = (∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal (1 / (2 * b) * ‖v - y‖ ^ (2 - (d : ℝ))))
          + ∫⁻ v in D \ Metric.ball y w, ENNReal.ofReal ((K + 2) * w / 2 * (‖v - y‖ ^ d)⁻¹) :=
          lintegral_add_left hmeas2 _
      _ ≤ ENNReal.ofReal (lam / 2) + ENNReal.ofReal ((K + 2) / 2 * 2 ^ d * 2 ^ (d - 1) * lam) :=
          add_le_add ((lintegral_mono_set Set.sdiff_subset).trans hg2) hg3
      _ = ENNReal.ofReal (K₂ * lam) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), hK₂]
          congr 1
          ring
  have key : ∫ v in D, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      ≤ K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + K₂ * lam := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (f := fun v : EuclideanSpace ℝ (Fin d) =>
        max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0)
      (Filter.Eventually.of_forall fun v => le_max_right _ _) hmeasf.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    rw [← lintegral_inter_add_sdiff _ D hBm]
    refine (add_le_add hnear hfar).trans_eq ?_
    exact (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hX : 0 ≤ (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) := by positivity
  rw [positivePotential]
  calc 2 * ε / unitBallVolume d * ∫ v in D, max (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) 0
      ≤ 2 * ε / unitBallVolume d * (K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) + K₂ * lam) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ ≤ 2 * ε / unitBallVolume d * ((K₁ + K₂) * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)
          + (K₁ + K₂) * lam) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1 : K₁ * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d)
            ≤ (K₁ + K₂) * (lam * w ^ (d - 1)) ^ ((1 : ℝ) / d) :=
          mul_le_mul_of_nonneg_right (by linarith) hX
        have h2 : K₂ * lam ≤ (K₁ + K₂) * lam := mul_le_mul_of_nonneg_right (by linarith) hlam0.le
        linarith
    _ = _ := by ring

end CERW.LimitShapes.Curvature
