import CERW.Support.Geometry.Assembly
import CERW.Generic.Newton.CapAverage
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Geometry.TailBasic
import CERW.Support.Occupation.CellNorm

/-!
# Shell local times and the exterior volume

`eq:shell`, deterministically. Let `D = D_n` with `s = |A_n|^{1/d} ≥ 6`, and suppose
`|ℓ̃_n - U_D| ≤ δ` on the ball `|y| ≤ B₀ s + 4`, with `0 ≤ δ ≤ s`. For `r ∈ [s, B₀ s]` and a site
`x` with `||x| - r| ≤ 3`, put `h = U_D(x) + δ ≥ ℓ_n(x)` and `t = |x|`. The function `U_D + δ` is
nonnegative on the sphere of radius `t` and `½`-Hölder with constant `O(ε √s)`. Its spherical mean
is `2dε F(t) + δ` (`eq:newton`). The cap estimate `eq:cap-average` then bounds `h`. With
`α = 1/(2d - 1)` and `β = (d - 1)/(2d - 1)`, this gives
`ℓ_n(x) ≤ C B₀^β s^{1-α} [F(r - b) + δ]^α` for `b ≥ 3`. The constant `C` depends only on `d`.
-/

namespace CERW.Support.Coarse

open MeasureTheory LatticeProb CERW CERW.Support.Geometry

variable {d : ℕ}

/-- The two cases of the cap estimate, in pure real form. If `h ≤ A √t`, the cap estimate for
`A` bounds `h ^ (2d-1)` by `s ^ (2d-2) t ^ (d-1) F`; otherwise it applies with `A' = h / √t`,
which gives `c h ≤ M`, and `h ≤ C₂ s` supplies the remaining powers of `h`. In both cases
`h ^ (2d-1) ≤ K B₀ ^ (d-1) s ^ (2d-2) F`, with `t ≤ 2 B₀ s`, `A ^ 2 ≤ Cd ^ 2 s`, `M ≤ K₀ F`. -/
private lemma power_bound (hd : 1 ≤ d)
    {c Cd C₂ K₀ A t h s B₀ M F : ℝ}
    (hc : 0 < c) (hC₂ : 0 ≤ C₂) (hK₀ : 0 ≤ K₀) (hA : 0 < A) (ht : 0 < t)
    (hh : 0 ≤ h) (hs : 0 < s) (hB₀ : 1 ≤ B₀) (hF : 0 ≤ F)
    (hAsq : A ^ 2 ≤ Cd ^ 2 * s) (hts : t ≤ 2 * B₀ * s) (hhs : h ≤ C₂ * s)
    (hcap : ∀ A' : ℝ, A ≤ A' → h ≤ A' * Real.sqrt t →
      c * h ^ (2 * d - 1) / (A' ^ (2 * d - 2) * t ^ (d - 1)) ≤ M)
    (hM : M ≤ K₀ * F) :
    h ^ (2 * (d - 1) + 1) ≤
      K₀ / c * (Cd ^ (2 * (d - 1)) * 2 ^ (d - 1) + C₂ ^ (2 * (d - 1))) * B₀ ^ (d - 1) *
        s ^ (2 * (d - 1)) * F := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e2 : 2 * (m + 1) - 2 = 2 * m := by omega
  simp only [e1, e2, Nat.add_sub_cancel] at hcap ⊢
  have hB0 : 0 < B₀ := by linarith
  have hBm : 1 ≤ B₀ ^ m := one_le_pow₀ hB₀
  have hX : 0 ≤ K₀ * F * B₀ ^ m * s ^ (2 * m) := by positivity
  suffices key : c * h ^ (2 * m + 1) ≤
      K₀ * (Cd ^ (2 * m) * 2 ^ m + C₂ ^ (2 * m)) * B₀ ^ m * s ^ (2 * m) * F by
    have := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hc.le)
    calc h ^ (2 * m + 1) = c⁻¹ * (c * h ^ (2 * m + 1)) := by field_simp
      _ ≤ c⁻¹ * (K₀ * (Cd ^ (2 * m) * 2 ^ m + C₂ ^ (2 * m)) * B₀ ^ m * s ^ (2 * m) * F) := this
      _ = _ := by field_simp
  by_cases hcase : h ≤ A * Real.sqrt t
  · have h1 := hcap A le_rfl hcase
    rw [div_le_iff₀ (by positivity)] at h1
    have hAm : A ^ (2 * m) ≤ (Cd ^ 2 * s) ^ m := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg A) hAsq m
    have htm : t ^ m ≤ (2 * B₀ * s) ^ m := pow_le_pow_left₀ ht.le hts m
    have h2 : M * (A ^ (2 * m) * t ^ m) ≤ K₀ * F * ((Cd ^ 2 * s) ^ m * (2 * B₀ * s) ^ m) := by
      have hM0 : 0 ≤ K₀ * F := by positivity
      calc M * (A ^ (2 * m) * t ^ m) ≤ K₀ * F * (A ^ (2 * m) * t ^ m) := by
            gcongr
        _ ≤ _ := by gcongr
    have h3 : (Cd ^ 2 * s) ^ m * (2 * B₀ * s) ^ m =
        Cd ^ (2 * m) * 2 ^ m * B₀ ^ m * s ^ (2 * m) := by
      rw [← mul_pow, show Cd ^ 2 * s * (2 * B₀ * s) = Cd ^ 2 * 2 * B₀ * s ^ 2 by ring]
      simp only [mul_pow, pow_mul]
    have h4 : 0 ≤ K₀ * F * B₀ ^ m * s ^ (2 * m) * C₂ ^ (2 * m) := by positivity
    rw [h3] at h2
    linarith [h1, h2, h4]
  · have hlt : A * Real.sqrt t < h := not_le.mp hcase
    have hsq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hhpos : 0 < h := lt_of_le_of_lt (by positivity) hlt
    have hA' : A ≤ h / Real.sqrt t := (le_div_iff₀ hsq).mpr hlt.le
    have h1 := hcap (h / Real.sqrt t) hA' (le_of_eq (div_mul_cancel₀ h hsq.ne').symm)
    have hpow : (h / Real.sqrt t) ^ (2 * m) * t ^ m = h ^ (2 * m) := by
      rw [div_pow, pow_mul, pow_mul, Real.sq_sqrt ht.le]
      field_simp
    rw [hpow] at h1
    have h2 : c * h ≤ M := by
      have : c * h ^ (2 * m + 1) / h ^ (2 * m) = c * h := by
        rw [pow_succ]
        field_simp
      rwa [this] at h1
    have h3 : c * h ≤ K₀ * F := h2.trans hM
    have h4 : h ^ (2 * m) ≤ (C₂ * s) ^ (2 * m) := pow_le_pow_left₀ hh hhs _
    have hCd2 : 0 ≤ Cd ^ (2 * m) := by
      rw [pow_mul]
      positivity
    have h5 : 0 ≤ K₀ * F * B₀ ^ m * s ^ (2 * m) * (Cd ^ (2 * m) * 2 ^ m) := by positivity
    have h6 : K₀ * F * s ^ (2 * m) * C₂ ^ (2 * m) ≤
        K₀ * F * s ^ (2 * m) * C₂ ^ (2 * m) * B₀ ^ m :=
      le_mul_of_one_le_right (by positivity) hBm
    calc c * h ^ (2 * m + 1) = h ^ (2 * m) * (c * h) := by ring
      _ ≤ (C₂ * s) ^ (2 * m) * (K₀ * F) := by gcongr
      _ = K₀ * F * s ^ (2 * m) * C₂ ^ (2 * m) := by rw [mul_pow]; ring
      _ ≤ _ := by nlinarith [h5, h6]

/-- Taking the `(2d - 1)`-th root of `h ^ (2d - 1) ≤ K B ^ (d-1) s ^ (2d-2) F` gives
`h ≤ K ^ α B ^ β s ^ (1 - α) F ^ α` with `α = 1/(2d - 1)` and `β = (d - 1)/(2d - 1)`. -/
private lemma root_bound (hd : 1 ≤ d) {K B s F h : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hs : 0 ≤ s) (hF : 0 ≤ F) (hh : 0 ≤ h)
    (hbound : h ^ (2 * (d - 1) + 1) ≤ K * B ^ (d - 1) * s ^ (2 * (d - 1)) * F) :
    h ≤ K ^ (1 / (2 * (d : ℝ) - 1)) * B ^ (((d : ℝ) - 1) / (2 * d - 1)) *
      s ^ (1 - 1 / (2 * (d : ℝ) - 1)) * F ^ (1 / (2 * (d : ℝ) - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hbound
  have e1 : 2 * ((m + 1 : ℕ) : ℝ) - 1 = ((2 * m + 1 : ℕ) : ℝ) := by push_cast; ring
  have hα : (1 : ℝ) / (2 * ((m + 1 : ℕ) : ℝ) - 1) = ((2 * m + 1 : ℕ) : ℝ)⁻¹ := by
    rw [e1, one_div]
  have hβ : (((m + 1 : ℕ) : ℝ) - 1) / (2 * ((m + 1 : ℕ) : ℝ) - 1) =
      (m : ℝ) * ((2 * m + 1 : ℕ) : ℝ)⁻¹ := by
    rw [e1, div_eq_mul_inv]
    push_cast
    ring
  have hγ : 1 - 1 / (2 * ((m + 1 : ℕ) : ℝ) - 1) =
      ((2 * m : ℕ) : ℝ) * ((2 * m + 1 : ℕ) : ℝ)⁻¹ := by
    rw [hα]
    push_cast
    field_simp
    ring
  rw [hγ, hα, hβ]
  have hα0 : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ)⁻¹ := by positivity
  calc h = (h ^ (2 * m + 1)) ^ (((2 * m + 1 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast hh (by omega)).symm
    _ ≤ (K * B ^ m * s ^ (2 * m) * F) ^ (((2 * m + 1 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hbound hα0
    _ = _ := by
        rw [Real.mul_rpow (by positivity) hF, Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow hK (by positivity), ← Real.rpow_natCast B m, ← Real.rpow_natCast s (2 * m),
          ← Real.rpow_mul hB, ← Real.rpow_mul hs]

/-- A function with a `1/2`-Hölder modulus is continuous. -/
private lemma continuous_of_holder_half {f : EuclideanSpace ℝ (Fin d) → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ y z, |f y - f z| ≤ A * ‖y - z‖ ^ ((1 : ℝ) / 2)) : Continuous f := by
  have hholder : HolderWith A.toNNReal (1 / 2 : NNReal) f := by
    intro y z
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num)]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal A * _
    rw [← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.dist_eq, dist_eq_norm] using h y z)
  exact hholder.continuous (by norm_num)

/-- The weighted exterior volume of a measurable set of finite volume is nonincreasing in the
radius, including across radius zero. -/
private lemma tail_le_of_le (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) {u t : ℝ} (hut : u ≤ t) :
    tail d D t ≤ tail d D u := by
  have hc : 0 ≤ ((d : ℝ) * unitBallVolume d)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le)
  have hInt : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ))) D := by
    simpa using (CERW.Generic.Kernel.integrableOn_and_setIntegral_le hd hD hDfin 0).1
  have hsub : D ∩ {v | t < ‖v‖} ⊆ D ∩ {v | u < ‖v‖} :=
    Set.inter_subset_inter_right D fun v hv => lt_of_le_of_lt hut hv
  have hmeas : MeasurableSet (D ∩ {v : EuclideanSpace ℝ (Fin d) | u < ‖v‖}) :=
    hD.inter (measurableSet_lt measurable_const measurable_norm)
  simp only [tail]
  refine mul_le_mul_of_nonneg_left (setIntegral_mono_set (hInt.mono_set Set.inter_subset_left)
    (ae_restrict_of_forall_mem hmeas fun v _ => Real.rpow_nonneg (norm_nonneg v) _)
    (Filter.Eventually.of_forall fun v hv => hsub hv)) hc

/-- The spherical integral of a continuous function plus a constant `δ` is the integral of the
function plus `σ_d δ`, where `σ_d = d ω_d` is the total mass of the sphere measure. -/
private lemma integral_sphere_add_const {U : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Continuous U) (t δ : ℝ) :
    ∫ θ, (U (t • (θ : EuclideanSpace ℝ (Fin d))) + δ)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      ∫ θ, U (t • (θ : EuclideanSpace ℝ (Fin d)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere + d * unitBallVolume d * δ := by
  have hcont : Continuous fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      U (t • (θ : EuclideanSpace ℝ (Fin d))) :=
    hU.comp ((continuous_const : Continuous fun _ : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1 => t).smul continuous_subtype_val)
  have hint : Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      U (t • (θ : EuclideanSpace ℝ (Fin d))))
      (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
    obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ :
      Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1))).exists_bound_of_continuousOn
        hcont.continuousOn
    exact Integrable.of_bound hcont.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun θ => hC θ (Set.mem_univ θ))
  have hσ : ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere).real Set.univ =
      d * unitBallVolume d := by
    rw [MeasureTheory.Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
    rfl
  rw [integral_add hint (integrable_const δ), integral_const, hσ, smul_eq_mul]

/-- `eq:shell`: under the local approximation `|ℓ̃_n - U_{D_n}| ≤ δ` on `|y| ≤ B₀ s + 4` with
`0 ≤ δ ≤ s`, `s = |A_n|^{1/d} ≥ 6`, `2 ≤ B₀` and `s ≤ r ≤ B₀ s`, every site `x` with
`||x| - r| ≤ 3` has `ℓ_n(x) ≤ C B₀^β s^{1-α} [F(r - b) + δ]^α` for `b ≥ 3`. -/
theorem exists_shell_bound (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ (X : ℕ → Site d) (n : ℕ) (δ s B₀ r b : ℝ),
      s = ((departureRange X n).card : ℝ) ^ ((1 : ℝ) / d) → 6 ≤ s → 0 ≤ δ → δ ≤ s →
      2 ≤ B₀ → s ≤ r → r ≤ B₀ * s → 3 ≤ b →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ B₀ * s + 4 →
        |cellLocalTime X n y - potential d ε (cellSet X n) y| ≤ δ) →
      ∀ x : Site d, |euclidNorm x - r| ≤ 3 →
        (localTime X n x : ℝ) ≤ C * B₀ ^ (((d : ℝ) - 1) / (2 * d - 1)) *
          s ^ (1 - 1 / (2 * (d : ℝ) - 1)) *
          (tail d (cellSet X n) (r - b) + δ) ^ (1 / (2 * (d : ℝ) - 1)) := by
  obtain ⟨Cd, hCd0, hgeo⟩ := potential_geometry hd
  obtain ⟨c, hc0, hcap⟩ := CERW.Generic.Newton.exists_le_integral_sphere_of_holder hd
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hω := unitBallVolume_pos d
  refine ⟨(2 * (d * unitBallVolume d) / c *
    (Cd ^ (2 * (d - 1)) * 2 ^ (d - 1) + (Cd + 1) ^ (2 * (d - 1)))) ^ (1 / (2 * (d : ℝ) - 1)),
    by positivity, ?_⟩
  intro ε hε hεd X n δ s B₀ r b hs hs6 hδ0 hδs hB₀ hsr hrB hb happrox x hx
  have hdε : (d : ℝ) * ε ≤ 1 := by
    have := (lt_div_iff₀ hd0).mp hεd
    linarith
  have hε1 : ε ≤ 1 := by
    have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    nlinarith
  have hspos : 0 < s := by linarith
  have hDm : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDb : Bornology.IsBounded (cellSet X n) :=
    Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 X n)
  have hDfin : volume (cellSet X n) ≠ ⊤ := hDb.measure_lt_top.ne
  have hvol : (volume (cellSet X n)).toReal = ((departureRange X n).card : ℝ) := by
    rw [CERW.Support.Occupation.volume_cellSet]
    simp
  have hgeo' : (∀ y, |potential d ε (cellSet X n) y| ≤
        Cd * ε * (volume (cellSet X n)).toReal ^ ((1 : ℝ) / d)) ∧
      (∀ y z, |potential d ε (cellSet X n) y - potential d ε (cellSet X n) z| ≤
        Cd * ε * (volume (cellSet X n)).toReal ^ ((1 : ℝ) / (2 * d)) *
          ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
      (∀ t : ℝ, 0 < t →
        ((d : ℝ) * unitBallVolume d)⁻¹ * ∫ θ, potential d ε (cellSet X n)
          (t • (θ : EuclideanSpace ℝ (Fin d)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
          = 2 * d * ε * tail d (cellSet X n) t) := (hgeo ε hε).1 _ hDm hDb
  obtain ⟨hsup, hhol, hsph⟩ := hgeo'
  have hR0 : 0 ≤ (volume (cellSet X n)).toReal := ENNReal.toReal_nonneg
  have hRs : (volume (cellSet X n)).toReal ^ ((1 : ℝ) / d) = s := by
    rw [hvol]
    exact hs.symm
  have hRs2 : (volume (cellSet X n)).toReal ^ ((1 : ℝ) / (2 * d)) = s ^ ((1 : ℝ) / 2) := by
    rw [← hRs, ← Real.rpow_mul hR0]
    congr 1
    ring
  rw [hRs] at hsup
  rw [hRs2] at hhol
  set U : EuclideanSpace ℝ (Fin d) → ℝ := potential d ε (cellSet X n) with hU
  set A : ℝ := Cd * ε * s ^ ((1 : ℝ) / 2) with hA
  have hApos : 0 < A := by positivity
  have hAsq : A ^ 2 ≤ Cd ^ 2 * s := by
    have h1 : (s ^ ((1 : ℝ) / 2)) ^ 2 = s := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hspos.le]
    have h2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
    calc A ^ 2 = Cd ^ 2 * ε ^ 2 * (s ^ ((1 : ℝ) / 2)) ^ 2 := by rw [hA]; ring
      _ = Cd ^ 2 * ε ^ 2 * s := by rw [h1]
      _ ≤ Cd ^ 2 * 1 * s := by gcongr
      _ = Cd ^ 2 * s := by ring
  set t : ℝ := euclidNorm x with ht
  have hxn : ‖toSpace x‖ = t := norm_toSpace x
  have ht3 := abs_le.mp hx
  have htpos : 0 < t := by linarith
  have hBs : 12 ≤ B₀ * s := by nlinarith
  have htup : t ≤ 2 * B₀ * s := by linarith
  have hnorm : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      ‖t • (θ : EuclideanSpace ℝ (Fin d))‖ = t := fun θ => by
    have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      rw [← dist_zero_right]
      exact Metric.mem_sphere.mp θ.2
    rw [norm_smul, hθ, mul_one, Real.norm_eq_abs, abs_of_pos htpos]
  have hgnn : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      0 ≤ U (t • (θ : EuclideanSpace ℝ (Fin d))) + δ := fun θ => by
    have h1 := happrox (t • (θ : EuclideanSpace ℝ (Fin d))) (by rw [hnorm θ]; linarith)
    have h2 := cellLocalTime_nonneg X n (t • (θ : EuclideanSpace ℝ (Fin d)))
    have h3 := (abs_le.mp h1).2
    linarith
  let θ₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    ⟨t⁻¹ • toSpace x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, hxn, norm_inv, Real.norm_eq_abs,
        abs_of_pos htpos]
      exact inv_mul_cancel₀ htpos.ne'⟩
  have hθ₀ : t • (θ₀ : EuclideanSpace ℝ (Fin d)) = toSpace x := by
    show t • (t⁻¹ • toSpace x) = toSpace x
    rw [smul_inv_smul₀ htpos.ne']
  have hapx := happrox (toSpace x) (by rw [hxn]; linarith)
  rw [cellLocalTime_of_mem_cell X n (toSpace_mem_cell x)] at hapx
  set h : ℝ := U (toSpace x) + δ with hh
  have hℓ : (localTime X n x : ℝ) ≤ h := by
    have := (abs_le.mp hapx).2
    linarith
  have hh0 : 0 ≤ h := (Nat.cast_nonneg _).trans hℓ
  have hhs : h ≤ (Cd + 1) * s := by
    have h1 := (abs_le.mp (hsup (toSpace x))).2
    have h2 : Cd * ε * s ≤ Cd * s := by nlinarith [mul_pos hCd0 hspos]
    linarith
  have hholg : ∀ A', A ≤ A' → ∀ y z,
      |(U y + δ) - (U z + δ)| ≤ A' * ‖y - z‖ ^ ((1 : ℝ) / 2) := fun A' hA' y z => by
    rw [add_sub_add_right_eq_sub]
    exact (hhol y z).trans
      (mul_le_mul_of_nonneg_right hA' (Real.rpow_nonneg (norm_nonneg _) _))
  have hUcont : Continuous U := continuous_of_holder_half hApos.le hhol
  have hne : (d : ℝ) * unitBallVolume d ≠ 0 := by positivity
  have hI : ∫ θ, U (t • (θ : EuclideanSpace ℝ (Fin d)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      d * unitBallVolume d * (2 * d * ε * tail d (cellSet X n) t) := by
    rw [← hsph t htpos]
    exact (mul_inv_cancel_left₀ hne _).symm
  set M : ℝ := ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
    (U (t • (θ : EuclideanSpace ℝ (Fin d))) + δ)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere with hMdef
  have hFnn : 0 ≤ tail d (cellSet X n) t := tail_nonneg _ _
  have hFmono : tail d (cellSet X n) t ≤ tail d (cellSet X n) (r - b) :=
    tail_le_of_le hd1 hDm hDfin (by linarith)
  have hM : M ≤ 2 * (d * unitBallVolume d) * (tail d (cellSet X n) (r - b) + δ) := by
    have hσ : 0 < (d : ℝ) * unitBallVolume d := by positivity
    have h1 : 2 * d * ε * tail d (cellSet X n) t ≤ 2 * tail d (cellSet X n) (r - b) := by
      have := mul_le_of_le_one_left hFnn hdε
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hσ.le
    have h3 := mul_nonneg hσ.le hδ0
    rw [hMdef, integral_sphere_add_const hUcont t δ, hI]
    nlinarith
  have hcap' : ∀ A', A ≤ A' → h ≤ A' * Real.sqrt t →
      c * h ^ (2 * d - 1) / (A' ^ (2 * d - 2) * t ^ (d - 1)) ≤ M := fun A' hA' hle =>
    hcap (fun y => U y + δ) A' t h θ₀ (hApos.trans_le hA') htpos hh0 hle hgnn
      (hholg A' hA') (le_of_eq (by show h = U (t • (θ₀ : EuclideanSpace ℝ (Fin d))) + δ
                                   rw [hθ₀]))
  have hFpos : 0 ≤ tail d (cellSet X n) (r - b) + δ :=
    add_nonneg (tail_nonneg _ _) hδ0
  have hbound := power_bound hd1 (C₂ := Cd + 1) (K₀ := 2 * (d * unitBallVolume d)) hc0
    (by linarith) (by positivity) hApos htpos hh0 hspos (by linarith) hFpos hAsq htup hhs
    hcap' hM
  exact hℓ.trans (root_bound hd1 (by positivity) (by linarith) hspos.le hFpos hh0 hbound)

end CERW.Support.Coarse
