import CERW.Generic.Newton.GaussFlux
import CERW.Generic.Newton.BallSymmetry
import CERW.Generic.Newton.Polar
import CERW.Support.Geometry.Bound
import CERW.Support.Geometry.TailBounds

/-!
# Newton's theorem for the inward-drift potential

`eq:kernel-average`: for `v ≠ 0`, `s > 0` and `|v| ≠ s`,
`∫_{S} u_v · K(v - sθ) dσ(θ) = σ_d |v|^{1-d} 1{|v| > s}`. The swap identity
`u · K(ru - sθ) = θ · K(rθ - su)` turns the left side into `|v|^{1-d}` times the flux of `K(· - su)`
through the sphere of radius `|v|`, which is Gauss's flux theorem. Integrating over `D` by Fubini
gives `eq:newton`: the spherical mean of `U_D` at radius `s` is `2dε F(s)`. For a centred ball `U_D`
is radial, and `F(s) = (b - s)_+`, which gives `eq:ballpotential`.
-/

namespace CERW.Support.Geometry

open MeasureTheory CERW CERW.Generic.Kernel CERW.Generic.Newton

variable {d : ℕ}

/-- `eq:kernel-average`: for `v ≠ 0`, `s > 0` and `|v| ≠ s`,
`∫_S u_v · K(v - sθ) dσ(θ) = σ_d |v|^{1-d} 1{s < |v|}`. -/
theorem integral_sphere_inner_newtonField (hd : 2 ≤ d) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ≠ 0) {s : ℝ} (hs : 0 < s) (hvs : ‖v‖ ≠ s) :
    ∫ θ, inner ℝ (unitDir v) (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      if s < ‖v‖ then d * unitBallVolume d * ‖v‖ ^ (1 - (d : ℝ)) else 0 := by
  have hrpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hun : ‖unitDir v‖ = 1 := by
    rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hrpos.ne']
  have hvu : v = ‖v‖ • unitDir v := by
    rw [unitDir, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  have hsn : ‖s • unitDir v‖ = s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, hun, mul_one]
  have hθ : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := fun θ => by
    rw [← dist_zero_right]
    exact Metric.mem_sphere.mp θ.2
  have hswap : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      inner ℝ (unitDir v) (newtonField (v - s • (θ : EuclideanSpace ℝ (Fin d)))) =
        inner ℝ (θ : EuclideanSpace ℝ (Fin d))
          (newtonField (‖v‖ • (θ : EuclideanSpace ℝ (Fin d)) - s • unitDir v)) := by
    intro θ
    have h := inner_newtonField_swap hun (hθ θ) ‖v‖ s
    rwa [← hvu] at h
  have hflux := flux_eq hd (s • unitDir v) hrpos (by rw [hsn]; exact hvs)
  rw [hsn] at hflux
  unfold flux at hflux
  simp_rw [hswap]
  have hcancel := pow_smul_rpow_one_sub (d := d) (by omega) hrpos
  rw [smul_eq_mul] at hcancel
  set I := ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
    inner ℝ (θ : EuclideanSpace ℝ (Fin d))
      (newtonField (‖v‖ • (θ : EuclideanSpace ℝ (Fin d)) - s • unitDir v))
    ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere with hI
  have hIeq : I = ‖v‖ ^ (1 - (d : ℝ)) * (‖v‖ ^ (d - 1) * I) := by
    rw [← mul_assoc, mul_comm (‖v‖ ^ (1 - (d : ℝ))), hcancel, one_mul]
  rw [hIeq, hflux]
  split_ifs
  · ring
  · ring

/-- The potential's integrand, as a function of the sphere point `θ` and the position `v`, is
jointly measurable. -/
private lemma measurable_potentialPair (s : ℝ) :
    Measurable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
        EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir p.2) (p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))) /
        ‖p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))‖ ^ d) := by
  have hdir : Measurable (fun v : EuclideanSpace ℝ (Fin d) => unitDir v) := by
    change Measurable (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖⁻¹ • v)
    fun_prop
  have hsub : Measurable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
      EuclideanSpace ℝ (Fin d) => p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))) :=
    measurable_snd.sub ((measurable_subtype_coe.comp measurable_fst).const_smul s)
  exact ((hdir.comp measurable_snd).inner hsub).div (hsub.norm.pow_const d)

/-- The potential's integrand is integrable for the product of the sphere measure and Lebesgue
measure restricted to a measurable set of finite volume. -/
private lemma integrable_potentialPair (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (s : ℝ) :
    Integrable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ×
        EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir p.2) (p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))) /
        ‖p.2 - s • (p.1 : EuclideanSpace ℝ (Fin d))‖ ^ d)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.prod
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict D)) := by
  have hmeas := measurable_potentialPair (d := d) s
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun θ =>
    integrableOn_potentialIntegrand hd hD hDfin (s • (θ : EuclideanSpace ℝ (Fin d))), ?_⟩
  refine Integrable.mono' (integrable_const (d * unitBallVolume d *
    ((volume D).toReal / unitBallVolume d) ^ ((1 : ℝ) / d)))
    hmeas.norm.aestronglyMeasurable.integral_prod_right' ?_
  refine Filter.Eventually.of_forall fun θ => ?_
  obtain ⟨hint, hle⟩ := integrableOn_and_setIntegral_le hd hD hDfin
    (s • (θ : EuclideanSpace ℝ (Fin d)))
  have hint' := integrableOn_potentialIntegrand hd hD hDfin (s • (θ : EuclideanSpace ℝ (Fin d)))
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
  refine le_trans ?_ hle
  refine setIntegral_mono hint'.norm hint fun v => ?_
  rw [Real.norm_eq_abs]
  exact abs_potentialIntegrand_le v _

/-- Lebesgue-almost every point is nonzero and has norm different from a given radius. -/
private lemma ae_ne_zero_and_norm_ne (hd : 2 ≤ d) (s : ℝ) :
    ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ≠ 0 ∧ ‖v‖ ≠ s := by
  haveI : NeZero d := ⟨by omega⟩
  have h0 : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), v ≠ 0 := by
    rw [ae_iff]
    simp
  have h1 : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), ‖v‖ ≠ s := by
    rw [ae_iff]
    have := Measure.addHaar_sphere (volume : Measure (EuclideanSpace ℝ (Fin d))) 0 s
    simpa [Metric.sphere] using this
  filter_upwards [h0, h1] with v hv0 hv1 using ⟨hv0, hv1⟩

/-- The spherical integral of the potential of `D` at radius `s` is the weighted exterior integral
of `D`, by Fubini and the kernel average. -/
private lemma integral_sphere_potential (hd : 2 ≤ d) (ε : ℝ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    {s : ℝ} (hs : 0 < s) :
    ∫ θ, potential d ε D (s • (θ : EuclideanSpace ℝ (Fin d)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * ε / unitBallVolume d * (d * unitBallVolume d *
        ∫ v in D ∩ {v | s < ‖v‖}, ‖v‖ ^ (1 - (d : ℝ))) := by
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hnull := ae_ne_zero_and_norm_ne hd s
  have hset : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖} :=
    measurableSet_lt measurable_const measurable_norm
  unfold potential
  rw [integral_const_mul]
  congr 1
  rw [integral_integral_swap (integrable_potentialPair (by omega) hD hDfin s)]
  have hpt : ∀ v ∈ D, v ≠ 0 → ‖v‖ ≠ s →
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        inner ℝ (unitDir v) (v - s • (θ : EuclideanSpace ℝ (Fin d))) /
          ‖v - s • (θ : EuclideanSpace ℝ (Fin d))‖ ^ d
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        {v : EuclideanSpace ℝ (Fin d) | s < ‖v‖}.indicator
          (fun v => d * unitBallVolume d * ‖v‖ ^ (1 - (d : ℝ))) v := by
    intro v _ hv0 hvs
    simp_rw [← inner_newtonField]
    rw [integral_sphere_inner_newtonField hd hv0 hs hvs, Set.indicator_apply]
    rfl
  rw [setIntegral_congr_ae hD (hnull.mono fun v hv hvD => hpt v hvD hv.1 hv.2),
    setIntegral_indicator hset, integral_const_mul]

/-- `eq:newton`: for a bounded measurable `D` and `s > 0`, the spherical mean of `U_D` at radius `s`
is `2dε F(s)`. -/
theorem sphere_average_potential (hd : 2 ≤ d) (ε : ℝ) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D) {s : ℝ} (hs : 0 < s) :
    (d * unitBallVolume d)⁻¹ * ∫ θ, potential d ε D (s • (θ : EuclideanSpace ℝ (Fin d)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * d * ε * tail d D s := by
  have hω := unitBallVolume_pos d
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact this.ne'
  rw [integral_sphere_potential hd ε hD hDb hs, tail]
  field_simp

/-- The potential of a centred ball at its centre is `2dεb`. -/
private lemma potential_ball_zero (hd : 2 ≤ d) (ε : ℝ) {b : ℝ} (hb : 0 < b) :
    potential d ε (Metric.ball 0 b) 0 = 2 * d * ε * b := by
  have hω := unitBallVolume_pos d
  have hd1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpt : ∀ v : EuclideanSpace ℝ (Fin d),
      inner ℝ (unitDir v) (v - 0) / ‖v - 0‖ ^ d = ‖v‖ ^ (1 - (d : ℝ)) := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp only [unitDir_zero, sub_zero, inner_zero_left, norm_zero, zero_div]
      exact (Real.zero_rpow (by linarith)).symm
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      rw [sub_zero, unitDir, real_inner_smul_left, real_inner_self_eq_norm_mul_norm,
        ← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul]
      exact div_pow_eq_rpow_sub hvpos d
  unfold potential
  simp_rw [hpt]
  rw [(integrableOn_ball_zero_and_integral_eq (by omega) hb).2]
  field_simp

/-- The weighted exterior volume of a centred ball of radius `b` is `(b - s)_+`. -/
private lemma tail_ball (hd : 2 ≤ d) {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    tail d (Metric.ball 0 b) s = max (b - s) 0 := by
  haveI : NeZero d := ⟨by omega⟩
  have hω := unitBallVolume_pos d
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact this.ne'
  rcases le_or_gt b s with hbs | hsb
  · rw [tail_eq_zero_of_subset Metric.ball_subset_closedBall hbs, max_eq_right (by linarith)]
  · rw [max_eq_left (by linarith)]
    have hset : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b ∩ {v | s < ‖v‖} =
        Metric.ball 0 b \ Metric.closedBall 0 s := by
      ext v
      simp [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right, and_comm]
    have hae : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) s =ᵐ[volume] Metric.ball 0 s :=
      (ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
        (Measure.addHaar_closedBall_eq_addHaar_ball volume 0 s).le
        measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne).symm
    obtain ⟨hIb, hVb⟩ := integrableOn_ball_zero_and_integral_eq (d := d) (by omega) hb
    obtain ⟨-, hVs⟩ := integrableOn_ball_zero_and_integral_eq (d := d) (by omega) hs
    unfold tail
    rw [hset, setIntegral_sdiff measurableSet_closedBall hIb (Metric.closedBall_subset_ball hsb),
      setIntegral_congr_set hae, hVb, hVs]
    field_simp

/-- `eq:ballpotential`: `U_{B(0,b)}(y) = 2dε (b - |y|)_+` for every `b > 0` and `y`. -/
theorem potential_ball (hd : 2 ≤ d) (ε : ℝ) {b : ℝ} (hb : 0 < b)
    (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε (Metric.ball 0 b) y = 2 * d * ε * max (b - ‖y‖) 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [potential_ball_zero hd ε hb, norm_zero, sub_zero, max_eq_left hb.le]
  · have hs : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hω := unitBallVolume_pos d
    have hd0 : (d : ℝ) ≠ 0 := by
      have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      exact this.ne'
    have h := sphere_average_potential hd ε (D := Metric.ball 0 b)
      Metric.isOpen_ball.measurableSet Metric.isBounded_ball hs
    have hconst : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        potential d ε (Metric.ball 0 b) (‖y‖ • (θ : EuclideanSpace ℝ (Fin d))) =
          potential d ε (Metric.ball 0 b) y := fun θ => by
      refine potential_ball_eq_of_norm_eq ε b ?_
      have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
        rw [← dist_zero_right]
        exact Metric.mem_sphere.mp θ.2
      rw [norm_smul, norm_norm, hθ, mul_one]
    have hσ : ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).real Set.univ =
        d * unitBallVolume d := by
      rw [MeasureTheory.Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
      rfl
    simp_rw [hconst] at h
    rw [integral_const, hσ, smul_eq_mul, tail_ball hd hb hs] at h
    rw [← h]
    field_simp

end CERW.Support.Geometry
