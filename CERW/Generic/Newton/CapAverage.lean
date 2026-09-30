import CERW.Generic.Newton.Cap

/-!
# A Hölder function with a large value has a large spherical mean

`eq:cap-average`, abstracted: let `g ≥ 0` on the sphere of radius `t`, with modulus
`|g(y) - g(z)| ≤ A |y - z|^{1/2}`, and let `g(tθ₀) ≥ h` with `h ≤ A √t`. Then `g ≥ h/2`
on the cap of chord radius `(h/(2A))²` around `tθ₀`. That cap has angular radius at most `1/4`,
and its measure is at least `c_d (h²/(A² t))^{d-1}`. So
`∫_S g(tθ) dσ(θ) ≥ c h^{2d-1}/(A^{2d-2} t^{d-1})`.
-/

namespace CERW.Generic.Newton

open MeasureTheory

variable {d : ℕ}

/-- A function satisfying a `1/2`-Hölder bound with a positive constant is continuous. -/
private lemma holder_continuous {g : EuclideanSpace ℝ (Fin d) → ℝ} {A : ℝ} (hA : 0 < A)
    (h : ∀ y z, |g y - g z| ≤ A * ‖y - z‖ ^ ((1 : ℝ) / 2)) : Continuous g := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨(ε / A) ^ 2, by positivity, fun a ha => ?_⟩
  rw [dist_eq_norm] at ha
  have hsqrt_lt : ‖a - b‖ ^ ((1 : ℝ) / 2) < ε / A := by
    rw [← Real.sqrt_eq_rpow]
    have h1 : Real.sqrt ‖a - b‖ < Real.sqrt ((ε / A) ^ 2) :=
      Real.sqrt_lt_sqrt (norm_nonneg _) ha
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ε / A)] at h1
  have hmul : A * ‖a - b‖ ^ ((1 : ℝ) / 2) < ε := by
    calc A * ‖a - b‖ ^ ((1 : ℝ) / 2) < A * (ε / A) := by gcongr
      _ = ε := by field_simp
  rw [Real.dist_eq]
  have hb := h a b
  linarith

/-- The algebraic identity relating the cap estimate for `h ^ 2 / (4 A ^ 2 t)` to the constant
`(d/8) (1/(16 √d)) ^ (d-1)` times `h ^ (2d-1) / (A ^ (2d-2) t ^ (d-1))`. -/
private lemma cap_algebra (hd : 2 ≤ d) {A t h : ℝ} (hA : 0 < A) (ht : 0 < t) (hh : 0 < h) :
    ((d : ℝ) / 8 * (1 / (16 * Real.sqrt d)) ^ (d - 1)) * h ^ (2 * d - 1) /
        (A ^ (2 * d - 2) * t ^ (d - 1))
      = ((d : ℝ) / 4 * ((h ^ 2 / (4 * A ^ 2 * t)) / (4 * Real.sqrt d)) ^ (d - 1)) *
          (h / 2) := by
  have h2d1 : 2 * d - 1 = 2 * (d - 1) + 1 := by omega
  have h2d2 : 2 * d - 2 = 2 * (d - 1) := by omega
  rw [h2d1, h2d2, pow_succ]
  conv_lhs => rw [pow_mul, pow_mul, div_pow, mul_pow, one_pow]
  conv_rhs => rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow]
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hh2 : (0 : ℝ) < h ^ 2 := pow_pos hh 2
  field_simp
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
  rw [← pow_mul]
  rw [← pow_mul, Nat.mul_comm (d - 1) 2]
  ring

/-- `eq:cap-average`: a nonnegative `½`-Hölder function on a sphere of radius `t` that reaches `h`
somewhere has spherical integral at least `c h^{2d-1}/(A^{2d-2} t^{d-1})`. -/
theorem exists_le_integral_sphere_of_holder (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (A t h : ℝ)
      (θ₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1), 0 < A → 0 < t → 0 ≤ h →
      h ≤ A * Real.sqrt t →
      (∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        0 ≤ g (t • (θ : EuclideanSpace ℝ (Fin d)))) →
      (∀ y z, |g y - g z| ≤ A * ‖y - z‖ ^ ((1 : ℝ) / 2)) →
      h ≤ g (t • (θ₀ : EuclideanSpace ℝ (Fin d))) →
        c * h ^ (2 * d - 1) / (A ^ (2 * d - 2) * t ^ (d - 1)) ≤
          ∫ θ, g (t • (θ : EuclideanSpace ℝ (Fin d)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere := by
  refine ⟨(d : ℝ) / 8 * (1 / (16 * Real.sqrt d)) ^ (d - 1), ?_, ?_⟩
  · have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    positivity
  · intro g A t h θ₀ hA ht hh hht hgnn hholder hhθ
    by_cases hh0 : h = 0
    · subst h
      rw [zero_pow (by omega : 2 * d - 1 ≠ 0), mul_zero, zero_div]
      exact integral_nonneg fun θ => hgnn θ
    · have hhpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
      let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1
      let F : S → ℝ := fun θ => g (t • (θ : EuclideanSpace ℝ (Fin d)))
      let μ : Measure S := (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
      have hg_cont : Continuous g := holder_continuous hA hholder
      have hF_cont : Continuous F :=
        hg_cont.comp ((continuous_const : Continuous fun _ : S => t).smul continuous_subtype_val)
      have hF_int : Integrable F μ := by
        obtain ⟨C, hC⟩ :=
          (isCompact_univ : IsCompact (Set.univ : Set S)).exists_bound_of_continuousOn
            hF_cont.continuousOn
        exact Integrable.of_bound hF_cont.aestronglyMeasurable C
          (Filter.Eventually.of_forall fun θ => hC θ (Set.mem_univ θ))
      have hF_nn : 0 ≤ F := fun θ => hgnn θ
      set εa : ℝ := h ^ 2 / (4 * A ^ 2 * t) with hεa_def
      set ρ : ℝ := (h / (2 * A)) ^ 2 with hρ_def
      have hεa_pos : 0 < εa := by rw [hεa_def]; positivity
      have hsq : h ^ 2 ≤ A ^ 2 * t := by
        have h1 : h ^ 2 ≤ (A * Real.sqrt t) ^ 2 := pow_le_pow_left₀ hh hht 2
        rwa [mul_pow, Real.sq_sqrt ht.le] at h1
      have hεa_le_one : εa ≤ 1 := by
        rw [hεa_def, div_le_one (by positivity : (0 : ℝ) < 4 * A ^ 2 * t)]
        nlinarith [hsq, sq_nonneg A, sq_nonneg t, ht]
      have ht_εa : t * εa = ρ := by
        rw [hεa_def, hρ_def]
        field_simp
        ring
      have hρ_sqrt : ρ ^ ((1 : ℝ) / 2) = h / (2 * A) := by
        rw [hρ_def, ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ h / (2 * A))]
      have hcap_lower : ∀ θ ∈ Metric.ball θ₀ εa, h / 2 ≤ F θ := by
        intro θ hθ
        have hdist : dist θ θ₀ < εa := Metric.mem_ball.mp hθ
        have hnorm_eq : ‖t • (θ : EuclideanSpace ℝ (Fin d)) -
              t • (θ₀ : EuclideanSpace ℝ (Fin d))‖ = t * dist θ θ₀ := by
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg ht.le, ← dist_eq_norm,
            ← Subtype.dist_eq]
        have hnorm_lt : ‖t • (θ : EuclideanSpace ℝ (Fin d)) -
              t • (θ₀ : EuclideanSpace ℝ (Fin d))‖ < ρ := by
          rw [hnorm_eq, ← ht_εa]
          exact mul_lt_mul_of_pos_left hdist ht
        have hrpow_le : ‖t • (θ : EuclideanSpace ℝ (Fin d)) -
              t • (θ₀ : EuclideanSpace ℝ (Fin d))‖ ^ ((1 : ℝ) / 2) ≤
            ρ ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (norm_nonneg _) hnorm_lt.le (by norm_num)
        have hmul_le : A * ‖t • (θ : EuclideanSpace ℝ (Fin d)) -
              t • (θ₀ : EuclideanSpace ℝ (Fin d))‖ ^ ((1 : ℝ) / 2) ≤ h / 2 := by
          rw [hρ_sqrt] at hrpow_le
          calc A * ‖t • (θ : EuclideanSpace ℝ (Fin d)) -
                t • (θ₀ : EuclideanSpace ℝ (Fin d))‖ ^ ((1 : ℝ) / 2)
              ≤ A * (h / (2 * A)) := by gcongr
            _ = h / 2 := by field_simp
        have hbound := hholder (t • (θ : EuclideanSpace ℝ (Fin d)))
          (t • (θ₀ : EuclideanSpace ℝ (Fin d)))
        have hlow := (abs_le.mp hbound).1
        show h / 2 ≤ g (t • (θ : EuclideanSpace ℝ (Fin d)))
        linarith
      have hmono : ∫ θ in Metric.ball θ₀ εa, (h / 2) ∂μ ≤
          ∫ θ in Metric.ball θ₀ εa, F θ ∂μ := by
        refine setIntegral_mono_on (integrableOn_const (C := h / 2))
          hF_int.integrableOn measurableSet_ball ?_
        intro θ hθ
        exact hcap_lower θ hθ
      change (d : ℝ) / 8 * (1 / (16 * Real.sqrt d)) ^ (d - 1) * h ^ (2 * d - 1) /
          (A ^ (2 * d - 2) * t ^ (d - 1)) ≤ ∫ θ, F θ ∂μ
      calc (d : ℝ) / 8 * (1 / (16 * Real.sqrt d)) ^ (d - 1) * h ^ (2 * d - 1) /
              (A ^ (2 * d - 2) * t ^ (d - 1))
          = ((d : ℝ) / 4 * (εa / (4 * Real.sqrt d)) ^ (d - 1)) * (h / 2) :=
            cap_algebra hd hA ht hhpos
        _ ≤ μ.real (Metric.ball θ₀ εa) * (h / 2) := by
            apply mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact le_toSphere_ball (by omega : 1 ≤ d) hεa_pos hεa_le_one θ₀
        _ = ∫ θ in Metric.ball θ₀ εa, (h / 2) ∂μ := by
            rw [setIntegral_const, smul_eq_mul]
        _ ≤ ∫ θ in Metric.ball θ₀ εa, F θ ∂μ := hmono
        _ ≤ ∫ θ, F θ ∂μ :=
            setIntegral_le_integral hF_int (Filter.Eventually.of_forall hF_nn)

end CERW.Generic.Newton
