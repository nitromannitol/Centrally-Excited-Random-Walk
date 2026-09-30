import CERW.Generic.Kernel.NewtonField
import CERW.Generic.Kernel.RadialPower

/-!
# The `L^q` modulus of the Newtonian field

For `q = 2d/(2d-1)`, `∫ |K(v - y) - K(v - z)|^q dv ≤ C_d |y - z|^{q/2}`: the `q`-th power of
`eq:kernel-modulus`. With `r = |y - z|`, the region `|v - z| < 2r` contributes `O(r^{d - q(d-1)})`
because both singularities have order `d - 1 < d/q`. The region `|v - z| ≥ 2r` contributes
`O(r^{q + d - dq})` because the difference decays like `r |v - z|^{-d}` and `dq > d`. Both
exponents equal `q/2 = d/(2d-1)`.
-/

namespace CERW.Generic.Kernel

open MeasureTheory CERW

variable {d : ℕ}

/-- The Newtonian field is measurable. -/
theorem measurable_newtonField :
    Measurable (newtonField : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
  (measurable_norm.pow_const d).inv.smul measurable_id

/-- For `p ≥ 0` and `a, b ≥ 0`, `(a + b)^p ≤ 2^p (a^p + b^p)`. -/
lemma add_rpow_le_two_rpow_mul_add {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
  have hm : a + b ≤ 2 * max a b := by
    have h1 := le_max_left a b
    have h2 := le_max_right a b
    linarith
  calc (a + b) ^ p ≤ (2 * max a b) ^ p := Real.rpow_le_rpow (by positivity) hm hp
    _ = 2 ^ p * max a b ^ p := Real.mul_rpow (by norm_num) (le_max_of_le_left ha)
    _ ≤ 2 ^ p * (a ^ p + b ^ p) := by
        gcongr
        rcases max_choice a b with h | h <;> rw [h]
        · have := Real.rpow_nonneg hb p
          linarith
        · have := Real.rpow_nonneg ha p
          linarith

/-- Near field: `|K(a) - K(b)|^q ≤ 2^q (|a|^{-s} + |b|^{-s})` with `s = q (d - 1)`. -/
lemma norm_newtonField_sub_rpow_le (hd : 2 ≤ d) {q : ℝ} (hq : 0 ≤ q)
    (a b : EuclideanSpace ℝ (Fin d)) :
    ‖newtonField a - newtonField b‖ ^ q
      ≤ 2 ^ q * (‖a‖ ^ (-(q * ((d : ℝ) - 1))) + ‖b‖ ^ (-(q * ((d : ℝ) - 1)))) := by
  have h1 : ‖newtonField a - newtonField b‖ ≤ ‖a‖ ^ (1 - (d : ℝ)) + ‖b‖ ^ (1 - (d : ℝ)) := by
    rw [← norm_newtonField hd a, ← norm_newtonField hd b]
    exact norm_sub_le _ _
  have hexp : (1 - (d : ℝ)) * q = -(q * ((d : ℝ) - 1)) := by ring
  calc ‖newtonField a - newtonField b‖ ^ q
      ≤ (‖a‖ ^ (1 - (d : ℝ)) + ‖b‖ ^ (1 - (d : ℝ))) ^ q :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hq
    _ ≤ 2 ^ q * ((‖a‖ ^ (1 - (d : ℝ))) ^ q + (‖b‖ ^ (1 - (d : ℝ))) ^ q) :=
        add_rpow_le_two_rpow_mul_add (Real.rpow_nonneg (norm_nonneg _) _)
          (Real.rpow_nonneg (norm_nonneg _) _) hq
    _ = 2 ^ q * (‖a‖ ^ (-(q * ((d : ℝ) - 1))) + ‖b‖ ^ (-(q * ((d : ℝ) - 1)))) := by
        rw [← Real.rpow_mul (norm_nonneg a), ← Real.rpow_mul (norm_nonneg b), hexp]

/-- Far field: if `2 |a - b| ≤ |b|`, then
`|K(a) - K(b)|^q ≤ A^q |a - b|^q |b|^{-(d q)}` with `A = 2^d + 2 d 3^{d-1}`. -/
lemma norm_newtonField_sub_rpow_le_of_far {q : ℝ} (hq : 0 ≤ q)
    {a b : EuclideanSpace ℝ (Fin d)} (h : 2 * ‖a - b‖ ≤ ‖b‖) :
    ‖newtonField a - newtonField b‖ ^ q
      ≤ (2 ^ d + 2 * d * 3 ^ (d - 1)) ^ q * ‖a - b‖ ^ q * ‖b‖ ^ (-((d : ℝ) * q)) := by
  have h1 := norm_newtonField_sub_le h
  have hA : (0 : ℝ) ≤ 2 ^ d + 2 * d * 3 ^ (d - 1) := by positivity
  calc ‖newtonField a - newtonField b‖ ^ q
      ≤ ((2 ^ d + 2 * d * 3 ^ (d - 1)) * ‖a - b‖ / ‖b‖ ^ d) ^ q :=
        Real.rpow_le_rpow (norm_nonneg _) h1 hq
    _ = (2 ^ d + 2 * d * 3 ^ (d - 1)) ^ q * ‖a - b‖ ^ q * ‖b‖ ^ (-((d : ℝ) * q)) := by
        rw [Real.div_rpow (mul_nonneg hA (norm_nonneg _)) (pow_nonneg (norm_nonneg _) d),
          Real.mul_rpow hA (norm_nonneg _), ← Real.rpow_natCast ‖b‖ d,
          ← Real.rpow_mul (norm_nonneg b), Real.rpow_neg (norm_nonneg b), div_eq_mul_inv]

/-- Integrability and the value of `∫_{B(w, ρ)} |v - w|^{-s}` for `s < d`. -/
theorem integrableOn_ball_sub_rpow_neg_and_integral_eq (hd : 1 ≤ d) {s ρ : ℝ} (hs : s < d)
    (w : EuclideanSpace ℝ (Fin d)) (hρ : 0 < ρ) :
    IntegrableOn (fun v => ‖v - w‖ ^ (-s)) (Metric.ball w ρ) ∧
      ∫ v in Metric.ball w ρ, ‖v - w‖ ^ (-s)
        = d * unitBallVolume d * ρ ^ ((d : ℝ) - s) / ((d : ℝ) - s) := by
  obtain ⟨hint, hval⟩ := integrableOn_ball_rpow_neg_and_integral_eq (d := d) hd hs hρ
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin d))) w
  have hemb := measurableEmbedding_subRight w
  have hball : Metric.ball w ρ = (fun v : EuclideanSpace ℝ (Fin d) => v - w) ⁻¹'
      Metric.ball 0 ρ := by
    ext v
    simp only [Set.mem_preimage, mem_ball_iff_norm, sub_zero]
  rw [hball]
  refine ⟨?_, ?_⟩
  · exact (hmp.integrableOn_comp_preimage hemb (f := fun v => ‖v‖ ^ (-s))).mpr hint
  · rw [hmp.setIntegral_preimage_emb hemb (fun v => ‖v‖ ^ (-s)), hval]

/-- The scaling bound for exponents `q = 2 e` with `d - q (d - 1) = e` and `d q - d = e`: there is
a constant `C` with `∫ |K(u - w) - K(u)|^q ≤ C |w|^e` for every `w ≠ 0`, the integrand being
integrable. -/
theorem exists_integral_le_of_exponents (hd : 2 ≤ d) {q e : ℝ} (he : 0 < e) (hq : q = 2 * e)
    (hs : (d : ℝ) - q * ((d : ℝ) - 1) = e) (hdq : (d : ℝ) * q - d = e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EuclideanSpace ℝ (Fin d), 0 < ‖w‖ →
      Integrable (fun u => ‖newtonField (u - w) - newtonField u‖ ^ q) ∧
      ∫ u, ‖newtonField (u - w) - newtonField u‖ ^ q ≤ C * ‖w‖ ^ e := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hσpos : 0 < (d : ℝ) * unitBallVolume d := mul_pos hd0 (unitBallVolume_pos d)
  refine ⟨2 ^ q * (d * unitBallVolume d) * (2 ^ e + 3 ^ e) / e
    + (2 ^ d + 2 * d * 3 ^ (d - 1)) ^ q * (d * unitBallVolume d) * 2 ^ (-e) / e,
    by positivity, ?_⟩
  intro w hw
  set r : ℝ := ‖w‖ with hr
  have hf : Measurable (fun u : EuclideanSpace ℝ (Fin d) =>
      ‖newtonField (u - w) - newtonField u‖ ^ q) :=
    ((measurable_newtonField.comp (measurable_id.sub_const w)).sub
      measurable_newtonField).norm.pow_const q
  obtain ⟨hI1, hV1⟩ := integrableOn_ball_rpow_neg_and_integral_eq (d := d) (s := q * (d - 1))
    (ρ := 2 * r) hd1 (by linarith) (by positivity)
  obtain ⟨hI2, hV2⟩ := integrableOn_ball_sub_rpow_neg_and_integral_eq (d := d)
    (s := q * (d - 1)) (ρ := 3 * r) hd1 (by linarith) w (by positivity)
  obtain ⟨hI3, hV3⟩ := integrableOn_compl_ball_rpow_neg_and_integral_eq (d := d) (s := d * q)
    (ρ := 2 * r) hd1 (by linarith) (by positivity)
  rw [hs] at hV1 hV2
  have hexp3 : (d : ℝ) - d * q = -e := by linarith
  rw [hexp3, hdq] at hV3
  set B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 (2 * r) with hB
  have hnear : ∀ u : EuclideanSpace ℝ (Fin d), ‖newtonField (u - w) - newtonField u‖ ^ q
      ≤ 2 ^ q * (‖u - w‖ ^ (-(q * ((d : ℝ) - 1))) + ‖u‖ ^ (-(q * ((d : ℝ) - 1)))) :=
    fun u => norm_newtonField_sub_rpow_le hd hq0 _ _
  have hfar : ∀ u ∈ Bᶜ, ‖newtonField (u - w) - newtonField u‖ ^ q
      ≤ (2 ^ d + 2 * d * 3 ^ (d - 1)) ^ q * r ^ q * ‖u‖ ^ (-((d : ℝ) * q)) := by
    intro u hu
    have hu' : 2 * r ≤ ‖u‖ := by
      have : ¬ ‖u‖ < 2 * r := by simpa [hB, mem_ball_zero_iff] using hu
      exact not_lt.mp this
    have hsub : ‖u - w - u‖ = r := by rw [sub_sub_cancel_left, norm_neg]
    have := norm_newtonField_sub_rpow_le_of_far (d := d) hq0 (a := u - w) (b := u)
      (by rw [hsub]; exact hu')
    rwa [hsub] at this
  have hsubset : B ⊆ Metric.ball w (3 * r) := by
    intro u hu
    rw [hB, mem_ball_zero_iff] at hu
    rw [mem_ball_iff_norm]
    calc ‖u - w‖ ≤ ‖u‖ + ‖w‖ := norm_sub_le _ _
      _ < 3 * r := by linarith
  have hI2B : IntegrableOn (fun u : EuclideanSpace ℝ (Fin d) =>
      ‖u - w‖ ^ (-(q * ((d : ℝ) - 1)))) B := hI2.mono_set hsubset
  have hgB : IntegrableOn (fun u : EuclideanSpace ℝ (Fin d) =>
      2 ^ q * (‖u - w‖ ^ (-(q * ((d : ℝ) - 1))) + ‖u‖ ^ (-(q * ((d : ℝ) - 1))))) B :=
    (hI2B.add hI1).const_mul _
  have hgC : IntegrableOn (fun u : EuclideanSpace ℝ (Fin d) =>
      (2 ^ d + 2 * d * 3 ^ (d - 1)) ^ q * r ^ q * ‖u‖ ^ (-((d : ℝ) * q))) Bᶜ :=
    hI3.const_mul _
  have hfB : IntegrableOn (fun u : EuclideanSpace ℝ (Fin d) =>
      ‖newtonField (u - w) - newtonField u‖ ^ q) B := by
    refine Integrable.mono' hgB hf.aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_ball (fun u _ => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hnear u
  have hfC : IntegrableOn (fun u : EuclideanSpace ℝ (Fin d) =>
      ‖newtonField (u - w) - newtonField u‖ ^ q) Bᶜ := by
    refine Integrable.mono' hgC hf.aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_ball.compl (fun u hu => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hfar u hu
  have hfint : Integrable (fun u : EuclideanSpace ℝ (Fin d) =>
      ‖newtonField (u - w) - newtonField u‖ ^ q) := by
    have := hfB.union hfC
    rwa [Set.union_compl_self, integrableOn_univ] at this
  refine ⟨hfint, ?_⟩
  rw [← integral_add_compl measurableSet_ball hfint]
  have hnearInt : ∫ u in B, ‖newtonField (u - w) - newtonField u‖ ^ q
      ≤ 2 ^ q * ((d * unitBallVolume d) * (3 * r) ^ e / e
        + (d * unitBallVolume d) * (2 * r) ^ e / e) := by
    calc ∫ u in B, ‖newtonField (u - w) - newtonField u‖ ^ q
        ≤ ∫ u in B, 2 ^ q * (‖u - w‖ ^ (-(q * ((d : ℝ) - 1)))
            + ‖u‖ ^ (-(q * ((d : ℝ) - 1)))) :=
          setIntegral_mono_on hfB hgB measurableSet_ball (fun u _ => hnear u)
      _ = 2 ^ q * ((∫ u in B, ‖u - w‖ ^ (-(q * ((d : ℝ) - 1))))
            + ∫ u in B, ‖u‖ ^ (-(q * ((d : ℝ) - 1)))) := by
          rw [integral_const_mul, integral_add hI2B hI1]
      _ ≤ 2 ^ q * ((∫ u in Metric.ball w (3 * r), ‖u - w‖ ^ (-(q * ((d : ℝ) - 1))))
            + ∫ u in B, ‖u‖ ^ (-(q * ((d : ℝ) - 1)))) := by
          have hmono := setIntegral_mono_set hI2
            (Filter.Eventually.of_forall (fun u => Real.rpow_nonneg (norm_nonneg _) _))
            hsubset.eventuallyLE
          exact mul_le_mul_of_nonneg_left (by linarith [hmono]) (by positivity)
      _ = 2 ^ q * ((d * unitBallVolume d) * (3 * r) ^ e / e
            + (d * unitBallVolume d) * (2 * r) ^ e / e) := by
          rw [hV2, hV1]
  have hfarInt : ∫ u in Bᶜ, ‖newtonField (u - w) - newtonField u‖ ^ q
      ≤ (2 ^ d + 2 * d * 3 ^ (d - 1)) ^ q * r ^ q
        * ((d * unitBallVolume d) * (2 * r) ^ (-e) / e) := by
    calc ∫ u in Bᶜ, ‖newtonField (u - w) - newtonField u‖ ^ q
        ≤ ∫ u in Bᶜ, (2 ^ d + 2 * d * 3 ^ (d - 1)) ^ q * r ^ q * ‖u‖ ^ (-((d : ℝ) * q)) :=
          setIntegral_mono_on hfC hgC measurableSet_ball.compl hfar
      _ = _ := by rw [integral_const_mul, hV3]
  have hrr : r ^ q * r ^ (-e) = r ^ e := by
    rw [← Real.rpow_add hw, hq]
    congr 1
    ring
  have hfinal : 2 ^ q * ((d * unitBallVolume d) * (3 * r) ^ e / e
        + (d * unitBallVolume d) * (2 * r) ^ e / e)
      + (2 ^ d + 2 * d * 3 ^ (d - 1)) ^ q * r ^ q
        * ((d * unitBallVolume d) * (2 * r) ^ (-e) / e)
      = (2 ^ q * (d * unitBallVolume d) * (2 ^ e + 3 ^ e) / e
        + (2 ^ d + 2 * d * 3 ^ (d - 1)) ^ q * (d * unitBallVolume d) * 2 ^ (-e) / e)
        * r ^ e := by
    rw [Real.mul_rpow (by norm_num) hw.le, Real.mul_rpow (by norm_num) hw.le,
      Real.mul_rpow (by norm_num) hw.le, ← hrr]
    ring
  calc _ ≤ _ := add_le_add hnearInt hfarInt
    _ = _ := hfinal

/-- `eq:kernel-modulus`, `q`-th power: with `q = 2d/(2d-1)`, the field difference
`K(· - y) - K(· - z)` is `q`-integrable with `∫ |K(v - y) - K(v - z)|^q ≤ C_d |y - z|^{q/2}`. -/
theorem exists_kernel_modulus (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y z : EuclideanSpace ℝ (Fin d),
      Integrable (fun v => ‖newtonField (v - y) - newtonField (v - z)‖ ^
        (2 * (d : ℝ) / (2 * d - 1))) ∧
      ∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^ (2 * (d : ℝ) / (2 * d - 1))
        ≤ C * ‖y - z‖ ^ ((d : ℝ) / (2 * d - 1)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d - 1 := by linarith
  have hden' : (2 : ℝ) * d - 1 ≠ 0 := hden.ne'
  have hinv : (2 * (d : ℝ) - 1) * (2 * (d : ℝ) - 1)⁻¹ = 1 := mul_inv_cancel₀ hden'
  obtain ⟨C, hC0, hC⟩ := exists_integral_le_of_exponents hd
    (q := 2 * (d : ℝ) / (2 * d - 1)) (e := (d : ℝ) / (2 * d - 1)) (by positivity)
    (by ring)
    (by simp only [div_eq_mul_inv]; linear_combination (-(d : ℝ)) * hinv)
    (by simp only [div_eq_mul_inv]; linear_combination (d : ℝ) * hinv)
  refine ⟨C, hC0, fun y z => ?_⟩
  by_cases hyz : y = z
  · subst hyz
    have hq : (2 * (d : ℝ) / (2 * d - 1)) ≠ 0 := by positivity
    have he : ((d : ℝ) / (2 * d - 1)) ≠ 0 := by positivity
    simp [Real.zero_rpow hq, Real.zero_rpow he]
  · have hw : 0 < ‖y - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
    obtain ⟨hint, hle⟩ := hC (y - z) hw
    have hfun : (fun v : EuclideanSpace ℝ (Fin d) =>
        ‖newtonField (v - y) - newtonField (v - z)‖ ^ (2 * (d : ℝ) / (2 * d - 1)))
        = fun v => (fun u : EuclideanSpace ℝ (Fin d) =>
          ‖newtonField (u - (y - z)) - newtonField u‖ ^ (2 * (d : ℝ) / (2 * d - 1))) (v - z) := by
      funext v
      beta_reduce
      rw [sub_sub_sub_cancel_right]
    rw [hfun]
    exact ⟨hint.comp_sub_right z, (integral_sub_right_eq_self _ z).trans_le hle⟩

end CERW.Generic.Kernel
