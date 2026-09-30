import CERW.Generic.Kernel.Modulus
import CERW.Support.Geometry.Bound

/-!
# Hölder continuity of the potential

`eq:holder`: `|U_D(y) - U_D(z)| ≤ C_d ε |D|^{1/(2d)} |y - z|^{1/2}`. The difference of the
potentials is `(2ε/ω_d) ∫_D u_v · (K(v - y) - K(v - z)) dv`, and `|u_v| ≤ 1`. Hölder's inequality
with the exponents `2d` and `q = 2d/(2d - 1)` bounds it by `|D|^{1/(2d)}` times the `L^q` norm of
`K(· - y) - K(· - z)`, which is `O(|y - z|^{1/2})` by `eq:kernel-modulus`.
-/

namespace CERW.Support.Geometry

open MeasureTheory CERW CERW.Generic.Kernel

variable {d : ℕ}

/-- Hölder's inequality on a set of finite volume, against the constant function `1`. -/
lemma abs_setIntegral_le_rpow_mul_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ} (hpq : p.HolderConjugate q) {D : Set α} (hDfin : μ D ≠ ⊤) {f g : α → ℝ}
    (hfg : ∀ v, |f v| ≤ g v) (hgm : AEStronglyMeasurable g μ)
    (hgi : Integrable (fun v => g v ^ q) μ) :
    |∫ v in D, f v ∂μ| ≤ (μ D).toReal ^ (1 / p) * (∫ v, g v ^ q ∂μ) ^ (1 / q) := by
  haveI : IsFiniteMeasure (μ.restrict D) := isFiniteMeasure_restrict.2 hDfin
  have hg0 : ∀ v, 0 ≤ g v := fun v => (abs_nonneg _).trans (hfg v)
  have hq : 0 < q := hpq.symm.pos
  have hp : 0 < p := hpq.pos
  have hgL : MemLp g (ENNReal.ofReal q) μ := by
    rw [← integrable_norm_rpow_iff (p := ENNReal.ofReal q) hgm (by simp [hq]) (by simp),
      ENNReal.toReal_ofReal hq.le]
    simpa [Real.norm_of_nonneg (hg0 _)] using hgi
  have hgD : Integrable g (μ.restrict D) := by
    have := (hgL.restrict D).mono_exponent (p := 1) (by simpa using hpq.symm.lt.le)
    exact memLp_one_iff_integrable.1 this
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict D) hpq
    (f := fun _ => (1 : ℝ)) (g := g) (Filter.Eventually.of_forall fun _ => zero_le_one)
    (Filter.Eventually.of_forall hg0) (memLp_const 1) (hgL.restrict D)
  simp only [one_mul, Real.one_rpow, integral_const, Measure.real, smul_eq_mul, mul_one,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  have hnn : 0 ≤ ∫ v in D, g v ^ q ∂μ :=
    setIntegral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (hg0 _) _)
  have hle : ∫ v in D, g v ^ q ∂μ ≤ ∫ v, g v ^ q ∂μ :=
    setIntegral_le_integral hgi (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (hg0 _) _)
  have h1 : |∫ v in D, f v ∂μ| ≤ ∫ v in D, g v ∂μ := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hgD (Filter.Eventually.of_forall hfg)
  refine h1.trans (h.trans ?_)
  gcongr


/-- The difference of two potential integrands is the inner product of the direction with the
difference of the Newtonian fields. -/
lemma potentialIntegrand_sub (y z v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d - inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d =
      inner ℝ (unitDir v) (newtonField (v - y) - newtonField (v - z)) := by
  rw [← inner_newtonField, ← inner_newtonField, ← inner_sub_right]

/-- The difference of two potential integrands is bounded by the norm of the field difference. -/
lemma abs_potentialIntegrand_sub_le (y z v : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d - inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d| ≤
      ‖newtonField (v - y) - newtonField (v - z)‖ := by
  rw [potentialIntegrand_sub]
  calc |inner ℝ (unitDir v) (newtonField (v - y) - newtonField (v - z))|
      ≤ ‖unitDir v‖ * ‖newtonField (v - y) - newtonField (v - z)‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖newtonField (v - y) - newtonField (v - z)‖ :=
        mul_le_mul_of_nonneg_right (norm_unitDir_le v) (norm_nonneg _)
    _ = ‖newtonField (v - y) - newtonField (v - z)‖ := one_mul _

/-- `eq:holder`: `|U_D(y) - U_D(z)| ≤ C_d ε |D|^{1/(2d)} |y - z|^{1/2}` for every measurable `D` of
finite volume. -/
theorem exists_potential_holder (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 ≤ ε → ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D →
      volume D ≠ ⊤ → ∀ y z : EuclideanSpace ℝ (Fin d),
        |potential d ε D y - potential d ε D z| ≤
          C * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d - 1 := by linarith
  have hω := unitBallVolume_pos d
  obtain ⟨C, hC0, hC⟩ := exists_kernel_modulus hd
  refine ⟨2 / unitBallVolume d * C ^ ((2 * (d : ℝ) - 1) / (2 * d)), by positivity, ?_⟩
  intro ε hε D hD hDfin y z
  obtain ⟨hgi, hgint⟩ := hC y z
  have hpq : (2 * (d : ℝ)).HolderConjugate (2 * d / (2 * d - 1)) := by
    refine Real.holderConjugate_iff.mpr ⟨by linarith, ?_⟩
    field_simp
    ring
  have hgm : AEStronglyMeasurable (fun v => ‖newtonField (v - y) - newtonField (v - z)‖) volume :=
    (((measurable_newtonField.comp (measurable_id.sub_const y)).sub
      (measurable_newtonField.comp (measurable_id.sub_const z))).norm).aestronglyMeasurable
  have hH := abs_setIntegral_le_rpow_mul_rpow hpq hDfin
    (f := fun v => inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d -
      inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d)
    (fun v => abs_potentialIntegrand_sub_le y z v) hgm hgi
  have hsub : potential d ε D y - potential d ε D z = 2 * ε / unitBallVolume d *
      ∫ v in D, (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d -
        inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d) := by
    rw [integral_sub (integrableOn_potentialIntegrand (by omega) hD hDfin y)
      (integrableOn_potentialIntegrand (by omega) hD hDfin z), potential, potential]
    ring
  have hmod : (∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^ (2 * (d : ℝ) / (2 * d - 1))) ^
      (1 / (2 * (d : ℝ) / (2 * d - 1))) ≤
        C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
    have h1 : 1 / (2 * (d : ℝ) / (2 * d - 1)) = (2 * d - 1) / (2 * d) := by
      field_simp
    have hnn : 0 ≤ ∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^
        (2 * (d : ℝ) / (2 * d - 1)) :=
      integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    calc (∫ v, ‖newtonField (v - y) - newtonField (v - z)‖ ^ (2 * (d : ℝ) / (2 * d - 1))) ^
          (1 / (2 * (d : ℝ) / (2 * d - 1)))
        ≤ (C * ‖y - z‖ ^ ((d : ℝ) / (2 * d - 1))) ^ ((2 * (d : ℝ) - 1) / (2 * d)) := by
          rw [h1]
          exact Real.rpow_le_rpow hnn hgint (by positivity)
      _ = C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
          rw [Real.mul_rpow hC0 (Real.rpow_nonneg (norm_nonneg _) _), ← Real.rpow_mul
            (norm_nonneg _)]
          congr 2
          rw [div_mul_div_comm, div_eq_div_iff (mul_pos hden (by positivity)).ne' two_ne_zero]
          ring
  rw [hsub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ε / unitBallVolume d)]
  calc 2 * ε / unitBallVolume d * |∫ v in D, (inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d -
        inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d)|
      ≤ 2 * ε / unitBallVolume d * ((volume D).toReal ^ (1 / (2 * (d : ℝ))) *
          (C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2))) := by
        gcongr
        exact hH.trans (by gcongr)
    _ = 2 / unitBallVolume d * C ^ ((2 * (d : ℝ) - 1) / (2 * d)) * ε *
          (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) := by
        ring

/-- A function on `ℝ^d` satisfying a Hölder bound of exponent `1/2` is continuous. -/
theorem continuous_of_holder_half {A : ℝ} (hA : 0 ≤ A)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : ∀ y z, |f y - f z| ≤ A * ‖y - z‖ ^ ((1 : ℝ) / 2)) : Continuous f := by
  have hholder : HolderWith A.toNNReal (1 / 2 : NNReal) f := by
    intro y z
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num)]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal A * _
    rw [← ENNReal.ofReal_mul hA]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.dist_eq, dist_eq_norm] using h y z)
  exact hholder.continuous (by norm_num)

end CERW.Support.Geometry
