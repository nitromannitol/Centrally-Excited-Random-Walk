import CERW.Support.Statements
import CERW.Support.Drift.Dynkin
import CERW.Generic.Martingale.Dyadic
import CERW.Generic.Martingale.Clamp
import CERW.Support.Norm.Geometry
import CERW.Support.Geometry.TailBasic
import CERW.Support.Geometry.Holder
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Occupation.CellNorm
import CERW.Generic.Newton.CapAverage
import CERW.Generic.Newton.Polar
import CERW.Generic.Kernel.RadialPacking
import CERW.Support.Occupation.CellIntegral
import CERW.Support.Occupation.Facts
import CERW.Support.Coarse.Sstar
import CERW.Support.Coarse.Tail
import CERW.Support.Coarse.RadiusArith
import CERW.Support.Main.ScaleLimits
import CERW.Support.Law.ScaleArith
import CERW.Support.Occupation.SiteArith
import CERW.Support.Coarse.CardTail
import CERW.Support.Coarse.CrossingArith
import CERW.Support.Crossing.Kinematics
import CERW.Support.Crossing.Contradiction
import CERW.Support.Norm.VectorBound

/-!
# The occupation and radius bounds for the norm walk

`prop:norm-coarse` of the paper, assembled from the local time bound (`lem:norm-local`), the radial
test (`lem:norm-radial`) and the drift crossing bound (`lem:drift-crossing`), for the centrally
excited random walk with a drift field `ξ` (a subgradient of a norm `Ψ`). The route is that of the
Euclidean case (`CERW.Support.Coarse.Assembly`):

1. `eq:vector` for the compensated position `Z_t = X_t + ε Σ_{j<t} I_j ξ(X_j)`: each coordinate is
   a Dynkin martingale with increments at most `2` and conditional variances at most `1`, and
   Freedman's inequality at dyadic brackets applies on every interval
   (`CERW.Support.Norm.VectorBound`).
2. `eq:shell` for the norm potential: the spherical mean of `U_D` lies below `2dε Λ_Ψ F(t)`.
3. The mass identity `∫_{B(0,S)} U_D = 2ε ∫_D Ψ` and `Ψ ≥ c_Ψ |·|` turn the radial packing
   inequality into an upper bound for the mass scale.
4. The outer radius bound uses the drift crossing bound: for `B₁ + 1 ≥ 4 Λ_Ψ² / c_Ψ²`, every
   site `y` with `v · y > (B₁ - 1) s` and `|y| < (B₁ + 1) s` has `v · ξ(y) ≥ 0`, because `ξ(y)`
   makes an angle at most `arccos (c_Ψ / Λ_Ψ)` with `y`. The projected displacement is then at
   most `C √((t - s) L)`, and `freshCount ≤ m` replaces the Young inequality of the Euclidean case.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

open CERW.Support.Statements
open Finset CERW CERW.Support.Drift CERW.Support.Law

variable {d : ℕ}
section NormFacts

variable {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The extreme values of a norm on the Euclidean unit sphere satisfy `c_Ψ ≤ Λ_Ψ`. -/
private lemma normMin_le_normMax (hd : 1 ≤ d) (hΨ : IsNorm Ψ) : normMin Ψ ≤ normMax Ψ := by
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h1 := (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd).2 (coordVec (⟨0, by omega⟩ : Fin d))
  have h2 := CERW.Generic.Norm.le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h1 h2
  linarith

/-- The unit ball of a norm has positive volume. -/
private lemma normBallVolume_pos (hd : 1 ≤ d) (hΨ : IsNorm Ψ) : 0 < normBallVolume Ψ := by
  obtain ⟨hc, hle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc (normMin_le_normMax hd hΨ)
  have hlow : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / normMax Ψ) ⊆
      {y | Ψ y < 1} := by
    intro y hy
    rw [mem_ball_zero_iff, lt_div_iff₀ hΛ] at hy
    have := CERW.Generic.Norm.le_normMax_mul hΨ y
    simp only [Set.mem_setOf_eq]
    nlinarith
  have hup : {y | Ψ y < 1} ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / normMin Ψ) := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    rw [mem_ball_zero_iff, lt_div_iff₀ hc]
    have := hle y
    nlinarith
  unfold normBallVolume
  refine ENNReal.toReal_pos ?_ ?_
  · exact (lt_of_lt_of_le (Metric.measure_ball_pos volume _ (one_div_pos.mpr hΛ))
      (measure_mono hlow)).ne'
  · exact ((measure_mono hup).trans_lt measure_ball_lt_top).ne

/-- A subgradient `ξ` of a norm at a nonzero site `x` satisfies `c_Ψ |x| ≤ ξ · x` and
`|ξ| ≤ Λ_Ψ`; the zero vector satisfies the second. -/
private lemma subgradient_bounds (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {x ξ : EuclideanSpace ℝ (Fin d)}
    (h : IsSubgradient Ψ x ξ) : normMin Ψ * ‖x‖ ≤ inner ℝ ξ x ∧ ‖ξ‖ ≤ normMax Ψ := by
  obtain ⟨heuler, hle⟩ := CERW.Generic.Norm.subgradient_euler hΨ h
  refine ⟨?_, ?_⟩
  · rw [heuler]
    exact (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd).2 x
  · have h1 : ‖ξ‖ ^ 2 ≤ normMax Ψ * ‖ξ‖ := by
      calc ‖ξ‖ ^ 2 = inner ℝ ξ ξ := (real_inner_self_eq_norm_sq ξ).symm
        _ ≤ Ψ ξ := hle ξ
        _ ≤ normMax Ψ * ‖ξ‖ := CERW.Generic.Norm.le_normMax_mul hΨ ξ
    rcases eq_or_lt_of_le (norm_nonneg ξ) with h0 | hpos
    · rw [← h0]
      exact (lt_of_lt_of_le (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd).1
        (normMin_le_normMax hd hΨ)).le
    · nlinarith

end NormFacts

section Shell

variable {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The two cases of the cap estimate, in pure real form. If `h ≤ A √t`, the cap estimate for
`A` bounds `h ^ (2d-1)` by `s ^ (2d-2) t ^ (d-1) F`; otherwise it applies with `A' = h / √t`,
which gives `c h ≤ M`, and `h ≤ C₂ s` supplies the remaining powers of `h`. In both cases
`h ^ (2d-1) ≤ K B₀ ^ (d-1) s ^ (2d-2) F`, with `t ≤ 2 B₀ s`, `A ^ 2 ≤ Cd ^ 2 s`, `M ≤ K₀ F`. -/
private lemma shell_power_bound (hd : 1 ≤ d)
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
private lemma shell_root_bound (hd : 1 ≤ d) {K B s F h : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
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

/-- The weighted exterior volume of a measurable set of finite volume is nonincreasing in the
radius, including across radius zero. -/
private lemma tail_le_tail_of_le (hd : 1 ≤ d) {D : Set (EuclideanSpace ℝ (Fin d))}
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

/-- `eq:shell` for the norm potential: under the local approximation
`|ℓ̃_n - U_{D_n}| ≤ δ` on `|y| ≤ B₀ s + 4` with `0 ≤ δ ≤ s`, `s = |A_n|^{1/d} ≥ 6`, `2 ≤ B₀` and
`s ≤ r ≤ B₀ s`, every site `x` with `||x| - r| ≤ 3` has
`ℓ_n(x) ≤ C B₀^β s^{1-α} [F(r - b) + δ]^α` for `b ≥ 3`. The constant `C` depends only on `d`, `Ψ`
and `ε`. -/
private theorem exists_norm_shell_bound (hd : 2 ≤ d) (hΨ : IsNorm Ψ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (X : ℕ → Site d) (n : ℕ) (δ s B₀ r b : ℝ),
      s = ((departureRange X n).card : ℝ) ^ ((1 : ℝ) / d) → 6 ≤ s → 0 ≤ δ → δ ≤ s →
      2 ≤ B₀ → s ≤ r → r ≤ B₀ * s → 3 ≤ b →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ B₀ * s + 4 →
        |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤ δ) →
      ∀ x : Site d, |euclidNorm x - r| ≤ 3 →
        (localTime X n x : ℝ) ≤ C * B₀ ^ (((d : ℝ) - 1) / (2 * d - 1)) *
          s ^ (1 - 1 / (2 * (d : ℝ) - 1)) *
          (tail d (cellSet X n) (r - b) + δ) ^ (1 / (2 * (d : ℝ) - 1)) := by
  obtain ⟨Cd, hCd0, hgeo⟩ := CERW.Support.Norm.norm_potential_geometry hd Ψ hΨ
  obtain ⟨c, hc0, hcap⟩ := CERW.Generic.Newton.exists_le_integral_sphere_of_holder hd
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hω := unitBallVolume_pos d
  obtain ⟨hcΨ, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hcΨ (normMin_le_normMax hd1 hΨ)
  intro ε hε
  set K₀ : ℝ := d * unitBallVolume d * (2 * d * ε * normMax Ψ + 1) with hK₀
  have hK₀0 : 0 < K₀ := by positivity
  refine ⟨(K₀ / c * ((Cd * ε) ^ (2 * (d - 1)) * 2 ^ (d - 1) +
    (Cd * ε + 1) ^ (2 * (d - 1)))) ^ (1 / (2 * (d : ℝ) - 1)), by positivity, ?_⟩
  intro X n δ s B₀ r b hs hs6 hδ0 hδs hB₀ hsr hrB hb happrox x hx
  have hspos : 0 < s := by linarith
  have hDm : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDb : Bornology.IsBounded (cellSet X n) :=
    Metric.isBounded_ball.subset (CERW.Support.Occupation.cellSet_subset_ball hd1 X n)
  have hDfin : volume (cellSet X n) ≠ ⊤ := hDb.measure_lt_top.ne
  have hvol : (volume (cellSet X n)).toReal = ((departureRange X n).card : ℝ) := by
    rw [CERW.Support.Occupation.volume_cellSet]
    simp
  have hgeo' : (∀ y, |normPotential d ε Ψ (cellSet X n) y| ≤
        Cd * ε * (volume (cellSet X n)).toReal ^ ((1 : ℝ) / d)) ∧
      (∀ y z, |normPotential d ε Ψ (cellSet X n) y - normPotential d ε Ψ (cellSet X n) z| ≤
        Cd * ε * (volume (cellSet X n)).toReal ^ ((1 : ℝ) / (2 * d)) *
          ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
      (∀ t : ℝ, 0 < t →
        ((d : ℝ) * unitBallVolume d)⁻¹ * ∫ θ, normPotential d ε Ψ (cellSet X n)
          (t • (θ : EuclideanSpace ℝ (Fin d)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
          ≤ 2 * d * ε * normMax Ψ * tail d (cellSet X n) t) := by
    obtain ⟨h1, h2, h3⟩ := hgeo ε hε _ hDm hDb
    refine ⟨h1, h2, fun t ht => ?_⟩
    obtain ⟨hAB, -, hBle, -⟩ := h3 t ht
    exact hAB.trans_le hBle
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
  set U : EuclideanSpace ℝ (Fin d) → ℝ := normPotential d ε Ψ (cellSet X n) with hU
  set A : ℝ := Cd * ε * s ^ ((1 : ℝ) / 2) with hA
  have hApos : 0 < A := by positivity
  have hAsq : A ^ 2 ≤ (Cd * ε) ^ 2 * s := by
    have h1 : (s ^ ((1 : ℝ) / 2)) ^ 2 = s := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hspos.le]
    refine le_of_eq ?_
    calc A ^ 2 = (Cd * ε) ^ 2 * (s ^ ((1 : ℝ) / 2)) ^ 2 := by rw [hA]; ring
      _ = (Cd * ε) ^ 2 * s := by rw [h1]
  set t : ℝ := euclidNorm x with ht
  have hxn : ‖toSpace x‖ = t := norm_toSpace x
  have ht3 := abs_le.mp hx
  have htpos : 0 < t := by linarith
  have hBs : 12 ≤ B₀ * s := by nlinarith only [hB₀, hs6]
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
  have hhs : h ≤ (Cd * ε + 1) * s := by
    have h1 := (abs_le.mp (hsup (toSpace x))).2
    rw [hh, hU]
    linarith only [h1, hδs]
  have hholg : ∀ A', A ≤ A' → ∀ y z,
      |(U y + δ) - (U z + δ)| ≤ A' * ‖y - z‖ ^ ((1 : ℝ) / 2) := fun A' hA' y z => by
    rw [add_sub_add_right_eq_sub]
    exact (hhol y z).trans
      (mul_le_mul_of_nonneg_right hA' (Real.rpow_nonneg (norm_nonneg _) _))
  have hUcont : Continuous U :=
    CERW.Support.Geometry.continuous_of_holder_half hApos.le hhol
  have hne : (d : ℝ) * unitBallVolume d ≠ 0 := by positivity
  set I : ℝ := ∫ θ, U (t • (θ : EuclideanSpace ℝ (Fin d)))
    ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere with hIdef
  have hI : I ≤ d * unitBallVolume d * (2 * d * ε * normMax Ψ * tail d (cellSet X n) t) := by
    have h1 := hsph t htpos
    have hpos : 0 < (d : ℝ) * unitBallVolume d := by positivity
    calc I = d * unitBallVolume d * (((d : ℝ) * unitBallVolume d)⁻¹ * I) :=
          (mul_inv_cancel_left₀ hne _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hpos.le
  set M : ℝ := ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
    (U (t • (θ : EuclideanSpace ℝ (Fin d))) + δ)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere with hMdef
  have hFnn : 0 ≤ tail d (cellSet X n) t := CERW.Support.Geometry.tail_nonneg _ _
  have hFmono : tail d (cellSet X n) t ≤ tail d (cellSet X n) (r - b) :=
    tail_le_tail_of_le hd1 hDm hDfin (by linarith)
  have hM : M ≤ K₀ * (tail d (cellSet X n) (r - b) + δ) := by
    have hΛ' : 0 ≤ 2 * d * ε * normMax Ψ := by positivity
    have h1 : 2 * d * ε * normMax Ψ * tail d (cellSet X n) t ≤
        2 * d * ε * normMax Ψ * tail d (cellSet X n) (r - b) :=
      mul_le_mul_of_nonneg_left hFmono hΛ'
    have hFr : 0 ≤ tail d (cellSet X n) (r - b) := CERW.Support.Geometry.tail_nonneg _ _
    rw [hMdef, integral_sphere_add_const hUcont t δ]
    have h2 : d * unitBallVolume d * (2 * d * ε * normMax Ψ * tail d (cellSet X n) t) +
        d * unitBallVolume d * δ ≤ K₀ * (tail d (cellSet X n) (r - b) + δ) := by
      rw [hK₀]
      have hdω : 0 ≤ (d : ℝ) * unitBallVolume d := by positivity
      have h3 : 2 * d * ε * normMax Ψ * tail d (cellSet X n) (r - b) + δ ≤
          (2 * d * ε * normMax Ψ + 1) * (tail d (cellSet X n) (r - b) + δ) := by
        linarith only [mul_nonneg hΛ' hδ0, hFr]
      calc d * unitBallVolume d * (2 * d * ε * normMax Ψ * tail d (cellSet X n) t) +
            d * unitBallVolume d * δ
          = d * unitBallVolume d * (2 * d * ε * normMax Ψ * tail d (cellSet X n) t + δ) := by
            ring
        _ ≤ d * unitBallVolume d * (2 * d * ε * normMax Ψ * tail d (cellSet X n) (r - b) + δ) :=
            mul_le_mul_of_nonneg_left (by linarith) hdω
        _ ≤ d * unitBallVolume d * ((2 * d * ε * normMax Ψ + 1) *
            (tail d (cellSet X n) (r - b) + δ)) := mul_le_mul_of_nonneg_left h3 hdω
        _ = _ := by ring
    linarith [hI, h2]
  have hcap' : ∀ A', A ≤ A' → h ≤ A' * Real.sqrt t →
      c * h ^ (2 * d - 1) / (A' ^ (2 * d - 2) * t ^ (d - 1)) ≤ M := fun A' hA' hle =>
    hcap (fun y => U y + δ) A' t h θ₀ (hApos.trans_le hA') htpos hh0 hle hgnn
      (hholg A' hA') (le_of_eq (by show h = U (t • (θ₀ : EuclideanSpace ℝ (Fin d))) + δ
                                   rw [hθ₀]))
  have hFpos : 0 ≤ tail d (cellSet X n) (r - b) + δ :=
    add_nonneg (CERW.Support.Geometry.tail_nonneg _ _) hδ0
  have hbound := shell_power_bound hd1 (Cd := Cd * ε) (C₂ := Cd * ε + 1) (K₀ := K₀) hc0
    (by positivity) hK₀0.le hApos htpos hh0 hspos (by linarith) hFpos hAsq htup hhs
    hcap' hM
  exact hℓ.trans (shell_root_bound hd1 (by positivity) (by linarith) hspos.le hFpos hh0 hbound)

end Shell

section Mass

variable {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

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

/-- The exchanged weight `r ↦ 1{r < |v|} r^{d-1} Ψ(v) |v|^{-d}` integrates over `(0, S)` to
`Ψ(v)/d` whenever `|v| ≤ S`. -/
private lemma integral_Ioo_exchange_weighted (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {S : ℝ}
    (v : EuclideanSpace ℝ (Fin d)) (hvS : ‖v‖ ≤ S) :
    ∫ r in Set.Ioo 0 S, (if r < ‖v‖ then r ^ (d - 1) * (Ψ v / ‖v‖ ^ d) else 0) = Ψ v / d := by
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 : Ψ 0 = 0 := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1
    simp [h0]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hind : ∀ r : ℝ, (if r < ‖v‖ then r ^ (d - 1) * (Ψ v / ‖v‖ ^ d) else 0) =
      (Ψ v / ‖v‖ ^ d) * (Set.Iio ‖v‖).indicator (fun r : ℝ => r ^ (d - 1)) r := by
    intro r
    by_cases hr : r < ‖v‖
    · simp only [hr, if_true, Set.indicator_of_mem (Set.mem_Iio.mpr hr)]
      ring
    · simp only [hr, if_false, Set.indicator_of_notMem (mt Set.mem_Iio.mp hr), mul_zero]
  simp_rw [hind]
  rw [integral_const_mul, integral_Ioo_indicator_pow (by omega) (norm_nonneg v) hvS]
  have hne : ‖v‖ ^ d ≠ 0 := pow_ne_zero d hvpos.ne'
  field_simp

/-- The exchanged weight is jointly integrable over `(0, S) × D`. -/
private lemma integrable_exchange_weighted (hd : 2 ≤ d) (hΨ : IsNorm Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (S : ℝ) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      if p.1 < ‖p.2‖ then p.1 ^ (d - 1) * (Ψ p.2 / ‖p.2‖ ^ d) else 0)
      ((volume.restrict (Set.Ioo 0 S)).prod (volume.restrict D)) := by
  have hd1 : 1 ≤ d := by omega
  have hΨm : Measurable Ψ := (CERW.Generic.Norm.norm_continuous hΨ).measurable
  have hmeas : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      if p.1 < ‖p.2‖ then p.1 ^ (d - 1) * (Ψ p.2 / ‖p.2‖ ^ d) else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd.norm)
      ((measurable_fst.pow_const _).mul ((hΨm.comp measurable_snd).div
        (measurable_snd.norm.pow_const _))) measurable_const
  have hker : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ))) D := by
    simpa using (CERW.Generic.Kernel.integrableOn_and_setIntegral_le (d := d) hd1 hD hDfin 0).1
  have hbound : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      S ^ (d - 1) * (normMax Ψ * ‖p.2‖ ^ (1 - (d : ℝ))))
      ((volume.restrict (Set.Ioo 0 S)).prod (volume.restrict D)) := by
    have hc : Integrable (fun _ : ℝ => S ^ (d - 1)) (volume.restrict (Set.Ioo 0 S)) :=
      integrable_const _
    exact hc.mul_prod (hker.const_mul (normMax Ψ))
  refine hbound.mono' hmeas.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (measurableSet_Ioo.prod hD) fun p hp => ?_
  have hnn : 0 ≤ ‖p.2‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hΛ : 0 ≤ normMax Ψ :=
    (lt_of_lt_of_le (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1).1
      (normMin_le_normMax hd1 hΨ)).le
  split_ifs with hlt
  · have hvpos : 0 < ‖p.2‖ := lt_of_le_of_lt hp.1.1.le hlt
    have hΨle : Ψ p.2 ≤ normMax Ψ * ‖p.2‖ := CERW.Generic.Norm.le_normMax_mul hΨ p.2
    have hΨ0 : 0 ≤ Ψ p.2 := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 p.2
    have hdiv : Ψ p.2 / ‖p.2‖ ^ d ≤ normMax Ψ * ‖p.2‖ ^ (1 - (d : ℝ)) := by
      rw [← Geometry.div_pow_eq_rpow_sub hvpos d, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hΨle (pow_pos hvpos d).le
    have hdiv0 : 0 ≤ Ψ p.2 / ‖p.2‖ ^ d := div_nonneg hΨ0 (pow_pos hvpos d).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hp.1.1.le _) hdiv0)]
    exact mul_le_mul (pow_le_pow_left₀ hp.1.1.le hp.1.2.le _) hdiv hdiv0
      (pow_nonneg (hp.1.1.le.trans hp.1.2.le) _)
  · rw [norm_zero]
    exact mul_nonneg (pow_nonneg (hp.1.2.le.trans' hp.1.1.le) _) (mul_nonneg hΛ hnn)

/-- The radial average of the spherical mean: for `D ⊆ B(0, S)`,
`∫_0^S r^{d-1} ∫_{D ∩ {|v| > r}} Ψ(v) |v|^{-d} dv dr = d⁻¹ ∫_D Ψ`, by Tonelli. -/
private lemma integral_Ioo_pow_mul_weighted (hd : 2 ≤ d) (hΨ : IsNorm Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) {S : ℝ}
    (hDS : D ⊆ Metric.ball 0 S) :
    ∫ r in Set.Ioo 0 S, r ^ (d - 1) * ∫ v in D ∩ {v | r < ‖v‖}, Ψ v / ‖v‖ ^ d =
      (d : ℝ)⁻¹ * ∫ v in D, Ψ v := by
  have hDfin : volume D ≠ ⊤ := (measure_mono hDS |>.trans_lt measure_ball_lt_top).ne
  have hpt : ∀ r : ℝ, r ^ (d - 1) * ∫ v in D ∩ {v | r < ‖v‖}, Ψ v / ‖v‖ ^ d =
      ∫ v in D, (if r < ‖v‖ then r ^ (d - 1) * (Ψ v / ‖v‖ ^ d) else 0) := by
    intro r
    have hset : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | r < ‖v‖} :=
      measurableSet_lt measurable_const measurable_norm
    have hind : ∀ v : EuclideanSpace ℝ (Fin d),
        (if r < ‖v‖ then r ^ (d - 1) * (Ψ v / ‖v‖ ^ d) else 0) =
          {v : EuclideanSpace ℝ (Fin d) | r < ‖v‖}.indicator
            (fun v => r ^ (d - 1) * (Ψ v / ‖v‖ ^ d)) v := fun v => by
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    simp_rw [hind]
    rw [setIntegral_indicator hset, integral_const_mul, Set.inter_comm]
  simp_rw [hpt]
  rw [integral_integral_swap (integrable_exchange_weighted hd hΨ hD hDfin S)]
  rw [setIntegral_congr_fun hD fun v hv => integral_Ioo_exchange_weighted hd hΨ v
    (mem_ball_zero_iff.mp (hDS hv)).le, integral_div, inv_mul_eq_div]

/-- `eq:massidentity` for the norm potential: for a bounded measurable `D ⊆ B(0, S)`,
`∫_{B(0,S)} U_D = 2ε ∫_D Ψ(v) dv`. -/
private theorem integral_ball_normPotential (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) {S : ℝ}
    (hDS : D ⊆ Metric.ball 0 S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, normPotential d ε Ψ D y =
      2 * ε * ∫ v in D, Ψ v := by
  have hd1 : 1 ≤ d := by omega
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDS
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hω := unitBallVolume_pos d
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact this.ne'
  obtain ⟨Cd, hCd0, hgeo⟩ := CERW.Support.Norm.norm_potential_geometry hd Ψ hΨ
  have hgeo' : (∀ y z, |normPotential d ε Ψ D y - normPotential d ε Ψ D z| ≤
        Cd * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
      (∀ s : ℝ, 0 < s → ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          normPotential d ε Ψ D (s • (θ : EuclideanSpace ℝ (Fin d)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        d * unitBallVolume d * (2 * ε / unitBallVolume d *
          ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d)) := by
    obtain ⟨-, h2, h3⟩ := hgeo ε hε D hD hDb
    refine ⟨h2, fun s hs => ?_⟩
    obtain ⟨hAB, -, -, -⟩ := h3 s hs
    have hAB' : ((d : ℝ) * unitBallVolume d)⁻¹ * ∫ θ : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin d)) 1, normPotential d ε Ψ D (s • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        2 * ε / unitBallVolume d * ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d := hAB
    rw [← hAB']
    exact (mul_inv_cancel_left₀ (by positivity) _).symm
  obtain ⟨hhol, hsph⟩ := hgeo'
  have hcont : Continuous (normPotential d ε Ψ D) :=
    CERW.Support.Geometry.continuous_of_holder_half (by positivity) hhol
  have hint : IntegrableOn (normPotential d ε Ψ D) (Metric.ball 0 S) :=
    (hcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
      Metric.ball_subset_closedBall
  have hpolar := CERW.Generic.Newton.integral_eq_integral_Ioi_sphere hd1
    ((integrable_indicator_iff measurableSet_ball).2 hint)
  rw [integral_indicator measurableSet_ball] at hpolar
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      r ^ (d - 1) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S).indicator (normPotential d ε Ψ D)
          (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      (Set.Iio S).indicator (fun r : ℝ => r ^ (d - 1) * ∫ θ : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin d)) 1, normPotential d ε Ψ D
          (r • (θ : EuclideanSpace ℝ (Fin d)))
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
          (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S).indicator (normPotential d ε Ψ D)
            (r • (θ : EuclideanSpace ℝ (Fin d))) = 0 := fun θ =>
        Set.indicator_of_notMem (fun h => hrS (by rw [← hnorm θ]; exact mem_ball_zero_iff.mp h)) _
      simp [hz]
  rw [hpolar, setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  have hsph' : ∀ r ∈ Set.Ioo (0 : ℝ) S,
      r ^ (d - 1) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        normPotential d ε Ψ D (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * ε * d * (r ^ (d - 1) * ∫ v in D ∩ {v | r < ‖v‖}, Ψ v / ‖v‖ ^ d) := by
    intro r hr
    rw [hsph r hr.1]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hsph', integral_const_mul,
    integral_Ioo_pow_mul_weighted hd hΨ hD hDS]
  field_simp

end Mass

section MassBound

variable {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The cell-center map is measurable. -/
private theorem measurable_cellCenter :
    Measurable (cellCenter : EuclideanSpace ℝ (Fin d) → Site d) := by
  rw [measurable_pi_iff]
  intro i
  exact Measurable.floor
    (((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))).add_const (1 / 2))

/-- The cell local time is measurable. -/
private theorem measurable_cellLocalTime (X : ℕ → Site d) (n : ℕ) :
    Measurable (cellLocalTime X n) :=
  (measurable_of_countable (fun x : Site d => (localTime X n x : ℝ))).comp measurable_cellCenter

/-- `|n - ∫_{B(0,S)} U_{D_n}| ≤ ω_d S^d δ` when `D_n ⊆ B(0, S)` and `|ℓ̃_n - U_{D_n}| ≤ δ`
there, for the norm potential. -/
private theorem abs_sub_integral_normPotential_le (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    (hε : 0 < ε) (X : ℕ → Site d) (n : ℕ) {S δ : ℝ} (hS : 0 < S)
    (hDS : cellSet X n ⊆ Metric.ball 0 S)
    (happrox : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤ δ) :
    |(n : ℝ) - ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        normPotential d ε Ψ (cellSet X n) y| ≤ unitBallVolume d * S ^ d * δ := by
  have hDmeas : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDb : Bornology.IsBounded (cellSet X n) := Metric.isBounded_ball.subset hDS
  have hballmeas : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) :=
    measurableSet_ball
  have hballfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) < ⊤ :=
    measure_ball_lt_top
  have hcellint : ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      cellLocalTime X n y = n :=
    CERW.Support.Occupation.setIntegral_cellLocalTime_of_subset X n hballmeas hDS
  obtain ⟨Cd, hCd0, hgeo⟩ := CERW.Support.Norm.norm_potential_geometry hd Ψ hΨ
  have hholder : ∀ y z, |normPotential d ε Ψ (cellSet X n) y -
      normPotential d ε Ψ (cellSet X n) z| ≤
      Cd * ε * (volume (cellSet X n)).toReal ^ ((1 : ℝ) / (2 * d)) *
        ‖y - z‖ ^ ((1 : ℝ) / 2) := (hgeo ε hε _ hDmeas hDb).2.1
  have hcont : Continuous (normPotential d ε Ψ (cellSet X n)) :=
    CERW.Support.Geometry.continuous_of_holder_half (by positivity) hholder
  have hpotint : IntegrableOn (normPotential d ε Ψ (cellSet X n))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) :=
    ((hcont.continuousOn).integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
        Metric.ball_subset_closedBall
  have hcellint_on : IntegrableOn (cellLocalTime X n)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) := by
    refine IntegrableOn.of_bound hballfin
      (measurable_cellLocalTime X n).aestronglyMeasurable.restrict (maxLocalTime X n : ℝ) ?_
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (cellLocalTime_nonneg X n v)]
    show (localTime X n (cellCenter v) : ℝ) ≤ (maxLocalTime X n : ℝ)
    exact_mod_cast localTime_le_maxLocalTime X n (cellCenter v)
  have hsub := integral_sub hcellint_on hpotint
  have hmain : ‖∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        (cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y)‖
        = |(n : ℝ) - ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
            normPotential d ε Ψ (cellSet X n) y| := by
    rw [hsub, hcellint, Real.norm_eq_abs]
  have hbound : ‖∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        (cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y)‖
        ≤ δ * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal :=
    norm_setIntegral_le_of_norm_le_const hballfin fun y hy => by
      rw [Real.norm_eq_abs]
      exact happrox y hy
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

/-- The mass inequality for the norm potential: the mass identity, the mass error and the radial
packing inequality give `2 ε c_Ψ (d/(d+1)) ω_d^{-1/d} s^{d+1} ≤ n + ω_d S^d δ` for
`s = R_n^{1/d}`. -/
private lemma norm_mass_inequality (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (x : ℕ → Site d) (n : ℕ) {S δ s : ℝ} (hs : s = ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d))
    (hspos : 0 < s) (hS : 0 < S) (hDS : cellSet x n ⊆ Metric.ball 0 S)
    (happrox : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime x n y - normPotential d ε Ψ (cellSet x n) y| ≤ δ) :
    2 * ε * normMin Ψ * ((d : ℝ) / (d + 1) * unitBallVolume d ^ (-(1 : ℝ) / d)) *
        s ^ (d + 1) ≤ n + unitBallVolume d * S ^ d * δ := by
  have hd1 : 1 ≤ d := by omega
  have hD : MeasurableSet (cellSet x n) := CERW.Support.Occupation.measurableSet_cellSet x n
  have hDb : Bornology.IsBounded (cellSet x n) := Metric.isBounded_ball.subset hDS
  have hsd : s ^ d = ((departureRange x n).card : ℝ) := by
    rw [hs]
    exact CERW.Generic.Kernel.rpow_one_div_natCast_pow (Nat.cast_nonneg _) hd1
  have hpack := CERW.Generic.Kernel.le_setIntegral_norm hd1 hD hDb
  have hRpos : 0 < ((departureRange x n).card : ℝ) := by
    rw [← hsd]
    exact pow_pos hspos d
  rw [CERW.Support.Occupation.volume_cellSet, ENNReal.toReal_natCast] at hpack
  have hRpow : ((departureRange x n).card : ℝ) ^ (1 + (1 : ℝ) / d) = s ^ (d + 1) := by
    rw [Real.rpow_add hRpos, Real.rpow_one, ← hs, ← hsd, pow_succ]
  rw [hRpow] at hpack
  have hid := integral_ball_normPotential hd hΨ hε hD hDS
  have herr := abs_sub_integral_normPotential_le hd hΨ hε x n hS hDS happrox
  rw [hid] at herr
  have h1 := (abs_le.mp herr).1
  obtain ⟨hc₀, hle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hcont : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  have hΨint : IntegrableOn Ψ (cellSet x n) :=
    (hcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
      (hDS.trans Metric.ball_subset_closedBall)
  have hnint : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (cellSet x n) :=
    (continuous_norm.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
      (hDS.trans Metric.ball_subset_closedBall)
  have hmono : normMin Ψ * ∫ v in cellSet x n, ‖v‖ ≤ ∫ v in cellSet x n, Ψ v := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hnint.const_mul _) hΨint hD fun v _ => hle v
  have h2 := mul_le_mul_of_nonneg_left hpack (by positivity : 0 ≤ 2 * ε * normMin Ψ)
  have h3 := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 2 * ε)
  nlinarith [h1, h2, h3]

end MassBound

section OuterRadius

open CERW.Support.Crossing CERW.Support.Occupation

/-- A unit vector that makes a small angle with `x` has a nonnegative inner product with any
vector `ξ` that makes an angle at most `arccos(c/Λ)` with `x`: if `c ‖x‖ ≤ ξ · x`, `‖ξ‖ ≤ Λ`,
`κ ‖x‖ ≤ v · x` and `2 (1 - κ) Λ² ≤ c²`, then `0 ≤ v · ξ`. -/
private lemma inner_nonneg_of_close {v x ξ : EuclideanSpace ℝ (Fin d)} {c Λ κ : ℝ}
    (hc : 0 < c) (hΛ : 0 < Λ) (hv : ‖v‖ = 1) (hxpos : 0 < ‖x‖) (hx : c * ‖x‖ ≤ inner ℝ ξ x)
    (hξ : ‖ξ‖ ≤ Λ) (hvx : κ * ‖x‖ ≤ inner ℝ v x) (hκ : 2 * (1 - κ) * Λ ^ 2 ≤ c ^ 2) :
    0 ≤ inner ℝ v ξ := by
  set a : ℝ := ‖x‖ with ha
  set w : EuclideanSpace ℝ (Fin d) := a • v - x with hw
  have hw2 : ‖w‖ ^ 2 ≤ 2 * a ^ 2 * (1 - κ) := by
    have h1 : ‖w‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 - 2 * (a * inner ℝ v x) + ‖x‖ ^ 2 := by
      rw [hw, norm_sub_sq_real, norm_smul, real_inner_smul_left, mul_pow, Real.norm_eq_abs,
        sq_abs]
    rw [h1, hv, ← ha]
    nlinarith [mul_le_mul_of_nonneg_left hvx hxpos.le]
  have hinner : a * inner ℝ v ξ = inner ℝ ξ x + inner ℝ ξ w := by
    rw [hw, inner_sub_right, real_inner_smul_right, real_inner_comm ξ v]
    ring
  have hprod : ‖ξ‖ * ‖w‖ ≤ c * a := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity) ?_
    calc (‖ξ‖ * ‖w‖) ^ 2 = ‖ξ‖ ^ 2 * ‖w‖ ^ 2 := by ring
      _ ≤ Λ ^ 2 * (2 * a ^ 2 * (1 - κ)) := by
          gcongr
      _ = (2 * (1 - κ) * Λ ^ 2) * a ^ 2 := by ring
      _ ≤ c ^ 2 * a ^ 2 := by gcongr
      _ = (c * a) ^ 2 := by ring
  have hlow : -(‖ξ‖ * ‖w‖) ≤ inner ℝ ξ w := by
    have := abs_le.mp (abs_real_inner_le_norm ξ w)
    linarith [this.1]
  have hfin : 0 ≤ a * inner ℝ v ξ := by
    rw [hinner]
    linarith
  exact nonneg_of_mul_nonneg_right hfin hxpos

/-- The scale `c n^{1/(d+1)}` eventually exceeds any given bound. -/
private lemma exists_le_mul_rpow {c : ℝ} (hc : 0 < c) (K : ℝ) :
    ∃ n₂ : ℕ, ∀ n : ℕ, n₂ ≤ n → K ≤ c * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)) := by
  have hpos : 0 < (1 : ℝ) / ((d : ℝ) + 1) := by positivity
  have ht : Filter.Tendsto (fun n : ℕ => c * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc
      ((tendsto_rpow_atTop hpos).comp tendsto_natCast_atTop_atTop)
  exact Filter.eventually_atTop.1 (ht.eventually_ge_atTop K)

/-- The number of first departures in `[s, t)` is at most the number of distinct sites visited
there: a first departure visits a site not visited before. -/
private lemma freshCount_le_card_image (x : ℕ → Site d) (s t : ℕ) :
    freshCount x s t ≤ ((Finset.Ico s t).image x).card := by
  classical
  unfold freshCount
  refine Finset.card_le_card_of_injOn x (fun j hj => ?_) ?_
  · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, rfl⟩)
  · intro i hi j hj hij
    have hi' := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
    have hj' := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hj'.2 (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hlt, hij⟩)
    · exact hi'.2 (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hlt, hij.symm⟩)

/-- A crossing interval `[s, t)`, with `t ≤ n`, whose sites satisfy `v · x > (B₀ - 1) σ` and
`|x| < (B₀ + 1) σ`, visits at most `C σ L` distinct sites when the coarse tail
`F((B₀ - 2) σ) ≤ C_t σ^{2-d} L` holds and `σ ≥ max 1 √d`. -/
private lemma card_crossing_le_path (hd : 1 ≤ d) (x : ℕ → Site d) (n s t : ℕ)
    (v : EuclideanSpace ℝ (Fin d)) {B₀ Ct σ L : ℝ} (hB₀ : 3 ≤ B₀) (hσ : 1 ≤ σ)
    (hσd : Real.sqrt d ≤ σ) (htn : t ≤ n) (hv : ‖v‖ = 1)
    (hsite : ∀ j ∈ Finset.Ico s t, (B₀ - 1) * σ < inner ℝ v (toSpace (x j)) ∧
      euclidNorm (x j) < (B₀ + 1) * σ)
    (htail : tail d (cellSet x n) ((B₀ - 2) * σ) ≤ Ct * σ ^ (2 - (d : ℝ)) * L) :
    (((Finset.Ico s t).image x).card : ℝ) ≤
      d * unitBallVolume d * (B₀ + 2) ^ ((d : ℝ) - 1) * Ct * σ * L := by
  have hσpos : 0 < σ := lt_of_lt_of_le one_pos hσ
  have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hS : ((Finset.Ico s t).image x) ⊆ departureRange x n := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 htn), rfl⟩
  have hρ : Real.sqrt d / 2 < (B₀ - 1) * σ := by nlinarith
  have hρR : (B₀ - 1) * σ ≤ (B₀ + 1) * σ := by nlinarith
  have hSR : ∀ y ∈ ((Finset.Ico s t).image x),
      (B₀ - 1) * σ < euclidNorm y ∧ euclidNorm y < (B₀ + 1) * σ := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨lt_of_lt_of_le (hsite j hj).1 (inner_toSpace_le_euclidNorm hv _), (hsite j hj).2⟩
  have hcard := CERW.Support.Coarse.card_le_tail hd x n hS hρ hρR hSR
  have hD : MeasurableSet (cellSet x n) := measurableSet_cellSet _ n
  have hDb : Bornology.IsBounded (cellSet x n) :=
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d)))
      (r := maxRadius x n + Real.sqrt d)).subset (cellSet_subset_ball hd _ n)
  have hmono : tail d (cellSet x n) ((B₀ - 1) * σ - Real.sqrt d / 2) ≤
      tail d (cellSet x n) ((B₀ - 2) * σ) := by
    refine CERW.Support.Geometry.tail_antitoneOn hD hDb ?_ ?_ ?_
    · exact Set.mem_Ioi.mpr (by nlinarith)
    · exact Set.mem_Ioi.mpr (by nlinarith)
    · nlinarith
  have hbase : (B₀ + 1) * σ + Real.sqrt d / 2 ≤ (B₀ + 2) * σ := by nlinarith
  have hexp : 0 ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hpow : ((B₀ + 1) * σ + Real.sqrt d / 2) ^ ((d : ℝ) - 1) ≤
      (B₀ + 2) ^ ((d : ℝ) - 1) * σ ^ ((d : ℝ) - 1) := by
    rw [← Real.mul_rpow (by linarith) hσpos.le]
    exact Real.rpow_le_rpow (by positivity) hbase hexp
  have hA : 0 ≤ (d : ℝ) * unitBallVolume d :=
    mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le
  have hT : 0 ≤ tail d (cellSet x n) ((B₀ - 1) * σ - Real.sqrt d / 2) :=
    CERW.Support.Geometry.tail_nonneg _ _
  have hσσ : σ ^ ((d : ℝ) - 1) * σ ^ (2 - (d : ℝ)) = σ := by
    rw [← Real.rpow_add hσpos, show (d : ℝ) - 1 + (2 - d) = 1 by ring, Real.rpow_one]
  calc (((Finset.Ico s t).image x).card : ℝ)
      ≤ d * unitBallVolume d * ((B₀ + 1) * σ + Real.sqrt d / 2) ^ ((d : ℝ) - 1) *
          tail d (cellSet x n) ((B₀ - 1) * σ - Real.sqrt d / 2) := hcard
    _ ≤ d * unitBallVolume d * ((B₀ + 2) ^ ((d : ℝ) - 1) * σ ^ ((d : ℝ) - 1)) *
          (Ct * σ ^ (2 - (d : ℝ)) * L) := by
        gcongr
        exact hmono.trans htail
    _ = d * unitBallVolume d * (B₀ + 2) ^ ((d : ℝ) - 1) * Ct *
          (σ ^ ((d : ℝ) - 1) * σ ^ (2 - (d : ℝ))) * L := by ring
    _ = d * unitBallVolume d * (B₀ + 2) ^ ((d : ℝ) - 1) * Ct * σ * L := by rw [hσσ]

/-- The numeric contradiction at the heart of `exists_maxRadius_le_norm`: from
`m ≤ C₁ σ L` and `σ² ≤ A L m (m^{1/d} + L²)`, `L ≥ 1`, we get
`σ² ≤ A (C₁^γ + C₁) (σ^γ L^{2γ} + σ L⁴)` with `γ = 1 + 1/d`. -/
private lemma crossing_numeric {σ L m A C₁ : ℝ} (hd : 1 ≤ d) (hσ : 0 < σ) (hL : 1 ≤ L)
    (hm0 : 0 ≤ m) (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hm : m ≤ C₁ * σ * L)
    (h : σ ^ 2 ≤ A * L * m * (m ^ ((1 : ℝ) / d) + L ^ 2)) :
    σ ^ 2 ≤ A * (C₁ ^ (1 + (1 : ℝ) / d) + C₁) *
      (σ ^ (1 + (1 : ℝ) / d) * L ^ (2 * (1 + (1 : ℝ) / d)) + σ * L ^ (4 : ℝ)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL0 : 0 < L := by linarith
  have hinv : 0 < (1 : ℝ) / d := by positivity
  have hσL : 0 ≤ C₁ * σ * L := by positivity
  have hmpow : m ^ ((1 : ℝ) / d) ≤ (C₁ * σ * L) ^ ((1 : ℝ) / d) :=
    Real.rpow_le_rpow hm0 hm hinv.le
  have hstep : A * L * m * (m ^ ((1 : ℝ) / d) + L ^ 2) ≤
      A * L * (C₁ * σ * L) * ((C₁ * σ * L) ^ ((1 : ℝ) / d) + L ^ 2) := by
    have h1 : m * (m ^ ((1 : ℝ) / d) + L ^ 2) ≤
        (C₁ * σ * L) * ((C₁ * σ * L) ^ ((1 : ℝ) / d) + L ^ 2) :=
      mul_le_mul hm (add_le_add hmpow le_rfl) (by positivity) hσL
    have hAL : 0 ≤ A * L := by positivity
    calc A * L * m * (m ^ ((1 : ℝ) / d) + L ^ 2)
        = A * L * (m * (m ^ ((1 : ℝ) / d) + L ^ 2)) := by ring
      _ ≤ A * L * ((C₁ * σ * L) * ((C₁ * σ * L) ^ ((1 : ℝ) / d) + L ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 hAL
      _ = _ := by ring
  have hγ : (0 : ℝ) < 1 + (1 : ℝ) / d := by linarith
  have hsplit : (C₁ * σ * L) ^ ((1 : ℝ) / d) = C₁ ^ ((1 : ℝ) / d) * σ ^ ((1 : ℝ) / d) *
      L ^ ((1 : ℝ) / d) := by
    rw [Real.mul_rpow (by positivity) hL0.le, Real.mul_rpow hC₁ hσ.le]
  have hC₁γ : C₁ ^ (1 + (1 : ℝ) / d) = C₁ * C₁ ^ ((1 : ℝ) / d) := by
    rw [Real.rpow_add' hC₁ hγ.ne', Real.rpow_one]
  have hσγ : σ ^ (1 + (1 : ℝ) / d) = σ * σ ^ ((1 : ℝ) / d) := by
    rw [Real.rpow_add hσ, Real.rpow_one]
  have hLexp : L ^ (2 + (1 : ℝ) / d) ≤ L ^ (2 * (1 + (1 : ℝ) / d)) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hLsplit : L ^ (2 + (1 : ℝ) / d) = L ^ 2 * L ^ ((1 : ℝ) / d) := by
    rw [Real.rpow_add hL0, show L ^ (2 : ℝ) = L ^ 2 by norm_num]
  have hL4 : L ^ (4 : ℝ) = L ^ 4 := by norm_num
  have hterm1 : A * L * (C₁ * σ * L) * (C₁ * σ * L) ^ ((1 : ℝ) / d) ≤
      A * (C₁ ^ (1 + (1 : ℝ) / d) * (σ ^ (1 + (1 : ℝ) / d) * L ^ (2 * (1 + (1 : ℝ) / d)))) := by
    have hpos : 0 ≤ A * (C₁ ^ (1 + (1 : ℝ) / d) * σ ^ (1 + (1 : ℝ) / d)) := by positivity
    calc A * L * (C₁ * σ * L) * (C₁ * σ * L) ^ ((1 : ℝ) / d)
        = A * (C₁ ^ (1 + (1 : ℝ) / d) * σ ^ (1 + (1 : ℝ) / d)) * L ^ (2 + (1 : ℝ) / d) := by
          rw [hsplit, hC₁γ, hσγ, hLsplit]
          ring
      _ ≤ A * (C₁ ^ (1 + (1 : ℝ) / d) * σ ^ (1 + (1 : ℝ) / d)) *
            L ^ (2 * (1 + (1 : ℝ) / d)) := mul_le_mul_of_nonneg_left hLexp hpos
      _ = _ := by ring
  have hterm2 : A * L * (C₁ * σ * L) * L ^ 2 = A * (C₁ * (σ * L ^ (4 : ℝ))) := by
    rw [hL4]
    ring
  have hCγ : 0 ≤ C₁ ^ (1 + (1 : ℝ) / d) := Real.rpow_nonneg hC₁ _
  have ha : 0 ≤ σ ^ (1 + (1 : ℝ) / d) * L ^ (2 * (1 + (1 : ℝ) / d)) :=
    mul_nonneg (Real.rpow_nonneg hσ.le _) (Real.rpow_nonneg hL0.le _)
  have hb : 0 ≤ σ * L ^ (4 : ℝ) := mul_nonneg hσ.le (Real.rpow_nonneg hL0.le _)
  calc σ ^ 2 ≤ A * L * m * (m ^ ((1 : ℝ) / d) + L ^ 2) := h
    _ ≤ A * L * (C₁ * σ * L) * ((C₁ * σ * L) ^ ((1 : ℝ) / d) + L ^ 2) := hstep
    _ = A * L * (C₁ * σ * L) * (C₁ * σ * L) ^ ((1 : ℝ) / d) +
          A * L * (C₁ * σ * L) * L ^ 2 := by ring
    _ ≤ A * (C₁ ^ (1 + (1 : ℝ) / d) * (σ ^ (1 + (1 : ℝ) / d) *
            L ^ (2 * (1 + (1 : ℝ) / d)))) + A * (C₁ * (σ * L ^ (4 : ℝ))) := by
          rw [hterm2]
          exact add_le_add hterm1 le_rfl
    _ ≤ A * (C₁ ^ (1 + (1 : ℝ) / d) + C₁) * (σ ^ (1 + (1 : ℝ) / d) *
          L ^ (2 * (1 + (1 : ℝ) / d)) + σ * L ^ (4 : ℝ)) := by
          have hcross1 : 0 ≤ C₁ ^ (1 + (1 : ℝ) / d) * (σ * L ^ (4 : ℝ)) := mul_nonneg hCγ hb
          have hcross2 : 0 ≤ C₁ * (σ ^ (1 + (1 : ℝ) / d) *
              L ^ (2 * (1 + (1 : ℝ) / d))) := mul_nonneg hC₁ ha
          nlinarith [mul_nonneg hA hcross1, mul_nonneg hA hcross2]

end OuterRadius

section OuterRadiusNorm

open CERW.Support.Crossing CERW.Support.Occupation CERW.Support.Coarse

/-- `eq:HvsR` for the norm walk: on a path from the origin with unit steps, in a drift field `ξ`
whose value at a site `y ≠ 0` satisfies `c_Ψ |y| ≤ ξ(y) · y` and `|ξ(y)| ≤ Λ_Ψ`, if the projected
displacement bound (the output of `drift_crossing`) and `eq:interval` hold on `[0, n]`,
`s = R_n^{1/d} ≥ c N`, and the coarse tail `F((B₁ - 2) s) ≤ C_t s^{2-d} L` holds, then
`H_n ≤ (B₁ + 1) s` for all large `n`, for `B₁ + 1 ≥ 4 Λ_Ψ² / c_Ψ²`. -/
private lemma exists_maxRadius_le_norm (hd : 2 ≤ d) {Cv CI Ct B₁ c cΨ Λ : ℝ}
    (hCI : 0 ≤ CI) (hCt : 0 ≤ Ct) (hB₁ : 3 ≤ B₁) (hc : 0 < c)
    (hcΨ : 0 < cΨ) (hΛ : 0 < Λ) (hB : 4 * Λ ^ 2 ≤ (B₁ + 1) * cΨ ^ 2) :
    ∃ n₀ : ℕ, ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ), n₀ ≤ n →
      x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) →
      (∀ y : Site d, y ≠ 0 → cΨ * euclidNorm y ≤ inner ℝ (ξ y) (toSpace y) ∧ ‖ξ y‖ ≤ Λ) →
      (∀ (u : EuclideanSpace ℝ (Fin d)) (s t : ℕ), s < t → t ≤ n → ‖u‖ = 1 →
        (∀ j : ℕ, s ≤ j → j < t → x j ∉ departureRange x j → 0 ≤ inner ℝ u (ξ (x j))) →
        inner ℝ u (toSpace (x t) - toSpace (x s)) ≤
          Cv * Real.sqrt (((t : ℝ) - s) * Real.log (n + 2))) →
      (∀ s t : ℕ, s < t → t ≤ n →
        (intervalMax x s t : ℝ) ≤
          CI * (freshCount x s t : ℝ) ^ ((1 : ℝ) / d) + CI * Real.log (n + 2) ^ 2) →
      c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) →
      tail d (cellSet x n) ((B₁ - 2) * ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d)) ≤
        Ct * (((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d)) ^ (2 - (d : ℝ)) *
          Real.log (n + 2) →
      maxRadius x n ≤ (B₁ + 1) * ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set γ : ℝ := 1 + (1 : ℝ) / d with hγdef
  have hγlt : γ < 2 := by
    rw [hγdef]
    have : (1 : ℝ) / d ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hdR
    linarith
  set C₁ : ℝ := d * unitBallVolume d * (B₁ + 2) ^ ((d : ℝ) - 1) * Ct with hC₁def
  set A : ℝ := Cv ^ 2 * CI with hAdef
  have hC₁ : 0 ≤ C₁ := by
    have hB₂ : 0 ≤ (B₁ + 2) ^ ((d : ℝ) - 1) := Real.rpow_nonneg (by linarith) _
    have hω : 0 ≤ (d : ℝ) * unitBallVolume d :=
      mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le
    exact mul_nonneg (mul_nonneg hω hB₂) hCt
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) hCI
  have hCγ : 0 ≤ C₁ ^ γ := Real.rpow_nonneg hC₁ _
  have hCf : 0 < A * (C₁ ^ γ + C₁) + 1 := by
    have : 0 ≤ A * (C₁ ^ γ + C₁) := mul_nonneg hA (by linarith)
    linarith
  obtain ⟨n₁, hn₁⟩ := eventually_lt_sq (d := d) hγlt hCf hc
  obtain ⟨n₂, hn₂⟩ := exists_le_mul_rpow (d := d) hc ((d : ℝ) + 1)
  refine ⟨max (max n₁ n₂) 2, ?_⟩
  intro ξ x n hn h0 hstep hξ hproj hint hscale htail
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn2' : n₂ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  by_contra hcon
  rw [not_le] at hcon
  set σ : ℝ := ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) with hσdef
  set L : ℝ := Real.log (n + 2) with hLdef
  have hL : 1 ≤ L := one_le_log_add_two hn2
  have hσge : (d : ℝ) + 1 ≤ σ := (hn₂ n hn2').trans hscale
  have hσ1 : 1 ≤ σ := by linarith
  have hσpos : 0 < σ := by linarith
  have hσd : Real.sqrt d ≤ σ := by
    refine le_trans ?_ hσge
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith only [hdR], by nlinarith only [hdR]⟩
  have hb : 0 ≤ (B₁ - 1) * σ := mul_nonneg (by linarith only [hB₁]) hσpos.le
  have hbpos : 0 < (B₁ - 1) * σ := mul_pos (by linarith only [hB₁]) hσpos
  obtain ⟨s', t, hst, htn, v, hv, hsite, hgain⟩ :=
    exists_crossing_interval (Ω := Unit) (fun j _ => x j) () n h0 hstep
      (b := (B₁ - 1) * σ) (r := (B₁ + 1) * σ) hb (by linarith only [hσ1]) hcon
  have hsite' : ∀ j ∈ Finset.Ico s' t, (B₁ - 1) * σ < inner ℝ v (toSpace (x j)) ∧
      euclidNorm (x j) < (B₁ + 1) * σ := hsite
  have hκ0 : 0 ≤ (B₁ - 1) / (B₁ + 1) := div_nonneg (by linarith) (by linarith)
  have hκΛ : 2 * (1 - (B₁ - 1) / (B₁ + 1)) * Λ ^ 2 ≤ cΨ ^ 2 := by
    have hB1 : 0 < B₁ + 1 := by linarith
    have h1 : 2 * (1 - (B₁ - 1) / (B₁ + 1)) = 4 / (B₁ + 1) := by
      field_simp
      ring
    rw [h1, div_mul_eq_mul_div, div_le_iff₀ hB1]
    linarith
  have hdir : ∀ j : ℕ, s' ≤ j → j < t → x j ∉ departureRange x j →
      0 ≤ inner ℝ v (ξ (x j)) := by
    intro j hsj hjt _
    obtain ⟨hvx, hxr⟩ := hsite' j (Finset.mem_Ico.mpr ⟨hsj, hjt⟩)
    have hne : x j ≠ 0 := by
      intro h
      rw [h, toSpace_zero, inner_zero_right] at hvx
      linarith
    obtain ⟨hξ1, hξ2⟩ := hξ (x j) hne
    have hle := inner_toSpace_le_euclidNorm hv (x j)
    have hxpos : 0 < ‖toSpace (x j)‖ := by
      rw [norm_toSpace]
      linarith
    refine inner_nonneg_of_close hcΨ hΛ hv hxpos ?_ hξ2 ?_ hκΛ
    · rw [norm_toSpace]
      exact hξ1
    · rw [norm_toSpace]
      have h1 : (B₁ - 1) / (B₁ + 1) * euclidNorm (x j) ≤
          (B₁ - 1) / (B₁ + 1) * ((B₁ + 1) * σ) :=
        mul_le_mul_of_nonneg_left hxr.le hκ0
      have h2 : (B₁ - 1) / (B₁ + 1) * ((B₁ + 1) * σ) = (B₁ - 1) * σ := by
        field_simp
      linarith
  have hproj' := hproj v s' t hst htn hv hdir
  have hgain' : σ ≤ inner ℝ v (toSpace (x t) - toSpace (x s')) := by
    have : (B₁ + 1) * σ - ((B₁ - 1) * σ + 1) ≤ inner ℝ v (toSpace (x t) - toSpace (x s')) :=
      hgain
    linarith
  have hts : 0 ≤ ((t : ℝ) - s') * L := by
    have : (s' : ℝ) ≤ t := by exact_mod_cast hst.le
    exact mul_nonneg (by linarith) (by linarith)
  have hsq : σ ^ 2 ≤ Cv ^ 2 * (((t : ℝ) - s') * L) := by
    have h1 : σ ≤ Cv * Real.sqrt (((t : ℝ) - s') * L) := hgain'.trans hproj'
    calc σ ^ 2 ≤ (Cv * Real.sqrt (((t : ℝ) - s') * L)) ^ 2 := pow_le_pow_left₀ hσpos.le h1 2
      _ = Cv ^ 2 * (((t : ℝ) - s') * L) := by rw [mul_pow, Real.sq_sqrt hts]
  set m : ℕ := ((Finset.Ico s' t).image x).card with hm
  have hdur : ((t : ℝ) - s') ≤ (m : ℝ) * (intervalMax x s' t : ℝ) := by
    have h := sub_le_card_mul_intervalMax x s' t
    have hcast : ((t - s' : ℕ) : ℝ) ≤ (m : ℝ) * (intervalMax x s' t : ℝ) := by
      exact_mod_cast h
    rwa [Nat.cast_sub hst.le] at hcast
  have hk : (freshCount x s' t : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast freshCount_le_card_image x s' t
  have hM : (intervalMax x s' t : ℝ) ≤ CI * ((m : ℝ) ^ ((1 : ℝ) / d) + L ^ 2) := by
    have h1 := hint s' t hst htn
    have h2 : (freshCount x s' t : ℝ) ^ ((1 : ℝ) / d) ≤ (m : ℝ) ^ ((1 : ℝ) / d) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hk (by positivity)
    calc (intervalMax x s' t : ℝ)
        ≤ CI * (freshCount x s' t : ℝ) ^ ((1 : ℝ) / d) + CI * L ^ 2 := h1
      _ ≤ CI * (m : ℝ) ^ ((1 : ℝ) / d) + CI * L ^ 2 := by
          gcongr
      _ = CI * ((m : ℝ) ^ ((1 : ℝ) / d) + L ^ 2) := by ring
  have hsq' : σ ^ 2 ≤ A * L * (m : ℝ) * ((m : ℝ) ^ ((1 : ℝ) / d) + L ^ 2) := by
    have h1 : ((t : ℝ) - s') ≤ (m : ℝ) * (CI * ((m : ℝ) ^ ((1 : ℝ) / d) + L ^ 2)) :=
      hdur.trans (mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg m))
    calc σ ^ 2 ≤ Cv ^ 2 * (((t : ℝ) - s') * L) := hsq
      _ ≤ Cv ^ 2 * (((m : ℝ) * (CI * ((m : ℝ) ^ ((1 : ℝ) / d) + L ^ 2))) * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by linarith))
            (sq_nonneg _)
      _ = A * L * (m : ℝ) * ((m : ℝ) ^ ((1 : ℝ) / d) + L ^ 2) := by
          rw [hAdef]
          ring
  have hcardm : (m : ℝ) ≤ C₁ * σ * L :=
    card_crossing_le_path hd1 x n s' t v hB₁ hσ1 hσd htn hv hsite' htail
  have hnum := crossing_numeric hd1 hσpos hL (Nat.cast_nonneg m) hA hC₁ hcardm hsq'
  have hlt := hn₁ n hn1 σ hscale
  have hX : 0 ≤ σ ^ γ * L ^ (2 * γ) + σ * L ^ (4 : ℝ) :=
    add_nonneg (mul_nonneg (Real.rpow_nonneg hσpos.le _) (Real.rpow_nonneg (by linarith) _))
      (mul_nonneg hσpos.le (Real.rpow_nonneg (by linarith) _))
  have h3 := mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1) :
      A * (C₁ ^ γ + C₁) ≤ A * (C₁ ^ γ + C₁) + 1) hX
  linarith

end OuterRadiusNorm

section Deterministic

variable {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The `(d+1)`-st power of `n^{1/(d+1)}` is `n`. -/
private lemma rpow_frac_pow {x : ℝ} (hx : 0 ≤ x) (d : ℕ) :
    (x ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have hexp : ((1 : ℝ) / (d + 1)) * (((d + 1 : ℕ) : ℝ)) = 1 := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  rw [hexp, Real.rpow_one]

/-- A bound on every local time in the shell `||x| - r| ≤ 3` bounds the shell maximum. -/
private lemma shellMax_le_of_forall (x : ℕ → Site d) (n r : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ z : Site d, |euclidNorm z - r| ≤ 3 → (localTime x n z : ℝ) ≤ K) :
    (shellMax x n r : ℝ) ≤ K := by
  have h1 : shellMax x n r ≤ ⌊K⌋₊ := by
    unfold shellMax
    apply Finset.sup_le
    intro z hz
    exact Nat.le_floor (h z (Finset.mem_filter.mp hz).2)
  exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hK)

/-- If `s² ≤ n` and `t² ≤ n` for a real `n ≥ 0`, then `t s ≤ n`. -/
private lemma mul_le_of_sq_le_sq {s t n : ℝ} (hn : 0 ≤ n)
    (h1 : s ^ 2 ≤ n) (h2 : t ^ 2 ≤ n) : t * s ≤ n := by
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [mul_self_lt_mul_self hn hcon, mul_le_mul h2 h1 (sq_nonneg s) hn]

/-- The real-variable form of the last step: the six bounds follow from the scale bounds
`c_s N ≤ s ≤ C_m N`, `M ≤ C_s s`, `H ≤ (B₀ + 1) s`, `n ≤ M R`, `R = s^d` and `s ≤ 2H + 1`. -/
private lemma exists_final_constants {cs Cs Cm B₀ : ℝ} (hcs : 0 < cs)
    (hCs : 0 < Cs) (hCm : 0 < Cm) (hB₀ : 0 ≤ B₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ N s R M H nn : ℝ, 0 < N → nn = N ^ (d + 1) → R = s ^ d →
      0 ≤ M → 2 ≤ cs * N → cs * N ≤ s → s ≤ Cm * N → M ≤ Cs * s → H ≤ (B₀ + 1) * s →
      nn ≤ M * R → s ≤ 2 * H + 1 →
      c * N ^ d ≤ R ∧ R ≤ C * N ^ d ∧ c * N ≤ M ∧ M ≤ C * N ∧ c * N ≤ H ∧ H ≤ C * N := by
  have hCmd : 0 < Cm ^ d := pow_pos hCm d
  have hcsd : 0 < cs ^ d := pow_pos hcs d
  refine ⟨min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4),
    max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm), ?_, ?_, ?_⟩
  · exact lt_min (lt_min hcsd (inv_pos.mpr hCmd)) (by linarith)
  · exact lt_max_of_lt_left (lt_max_of_lt_left hCmd)
  intro N s R M H nn hN hnn hR hM0 h2 hcsN hsCm hMs hHs hnM hsH
  have hc1 : min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4) ≤ cs ^ d :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4) ≤ (Cm ^ d)⁻¹ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4) ≤ cs / 4 := min_le_right _ _
  have hC1 : Cm ^ d ≤ max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : Cs * Cm ≤ max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm) :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hC3 : (B₀ + 1) * Cm ≤ max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm) := le_max_right _ _
  set c := min (min (cs ^ d) (Cm ^ d)⁻¹) (cs / 4) with hc
  set C := max (max (Cm ^ d) (Cs * Cm)) ((B₀ + 1) * Cm) with hC
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact le_min (le_min hcsd.le (inv_pos.mpr hCmd).le) (by linarith)
  have hNd : 0 < N ^ d := pow_pos hN d
  have hcsN0 : 0 < cs * N := mul_pos hcs hN
  have hs0 : 0 < s := lt_of_lt_of_le hcsN0 hcsN
  have hRlow : cs ^ d * N ^ d ≤ R := by
    rw [hR, ← mul_pow]
    exact pow_le_pow_left₀ hcsN0.le hcsN d
  have hRup : R ≤ Cm ^ d * N ^ d := by
    rw [hR, ← mul_pow]
    exact pow_le_pow_left₀ hs0.le hsCm d
  have hR0 : 0 ≤ R := by rw [hR]; exact pow_nonneg hs0.le d
  have hN1 : N ^ (d + 1) = N ^ d * N := pow_succ N d
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hc1 hNd.le).trans hRlow
  · exact hRup.trans (mul_le_mul_of_nonneg_right hC1 hNd.le)
  · have h1 : N ^ d * N ≤ M * (Cm ^ d * N ^ d) := by
      calc N ^ d * N = nn := by rw [hnn, hN1]
        _ ≤ M * R := hnM
        _ ≤ M * (Cm ^ d * N ^ d) := mul_le_mul_of_nonneg_left hRup hM0
    have h2 : N ≤ M * Cm ^ d := by
      have h3 : N ^ d * N ≤ N ^ d * (M * Cm ^ d) := by
        calc N ^ d * N ≤ M * (Cm ^ d * N ^ d) := h1
          _ = N ^ d * (M * Cm ^ d) := by ring
      exact le_of_mul_le_mul_left h3 hNd
    have h4 : (Cm ^ d)⁻¹ * N ≤ M := by
      rw [inv_mul_le_iff₀ hCmd]
      linarith
    exact (mul_le_mul_of_nonneg_right hc2 hN.le).trans h4
  · calc M ≤ Cs * s := hMs
      _ ≤ Cs * (Cm * N) := mul_le_mul_of_nonneg_left hsCm hCs.le
      _ = (Cs * Cm) * N := by ring
      _ ≤ C * N := mul_le_mul_of_nonneg_right hC2 hN.le
  · have h1 : cs * N / 4 ≤ H := by linarith
    calc c * N ≤ cs / 4 * N := mul_le_mul_of_nonneg_right hc3 hN.le
      _ = cs * N / 4 := by ring
      _ ≤ H := h1
  · calc H ≤ (B₀ + 1) * s := hHs
      _ ≤ (B₀ + 1) * (Cm * N) := mul_le_mul_of_nonneg_left hsCm (by linarith)
      _ = ((B₀ + 1) * Cm) * N := by ring
      _ ≤ C * N := mul_le_mul_of_nonneg_right hC3 hN.le

end Deterministic

section Core

open CERW.Support.Coarse CERW.Support.Occupation

variable {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The deterministic core of `prop:norm-coarse`: for the constants `K`, `C_r`, the radial test
start `ρ₀`, there are constants `c, C` and a threshold `n₀` such that, on a path whose local time
bound, interval bound, approximation bound, radial test and projected displacement bound hold,
the six bounds of `eq:coarse` hold. -/
private lemma norm_coarse_deterministic (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    {K Cr Cv ρ₀ : ℝ} (hK : 0 < K) (hCr : 0 < Cr) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)) (x : ℕ → Site d) (n : ℕ), n₀ ≤ n → x 0 = 0 →
        (∀ j, x (j + 1) - x j ∈ unitSteps d) →
        (∀ y : Site d, y ≠ 0 →
          normMin Ψ * euclidNorm y ≤ inner ℝ (ξ y) (toSpace y) ∧ ‖ξ y‖ ≤ normMax Ψ) →
        (maxLocalTime x n : ℝ) ≤
          K * ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) + K * Real.log (n + 2) ^ 2 →
        (∀ s t : ℕ, s < t → t ≤ n →
          (intervalMax x s t : ℝ) ≤
            K * (freshCount x s t : ℝ) ^ ((1 : ℝ) / d) + K * Real.log (n + 2) ^ 2) →
        (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
          |cellLocalTime x n y - normPotential d ε Ψ (cellSet x n) y| ≤
            K * (Real.sqrt (maxLocalTime x n) * Real.log (n + 2) + Real.log (n + 2))) →
        (∀ r : ℕ, ρ₀ ≤ r → r ≤ n →
          tail d (cellSet x n) ((r : ℝ) + 4 * d) ≤
            Cr * shellMax x n r * (tail d (cellSet x n) ((r : ℝ) - 4 * d) -
              tail d (cellSet x n) ((r : ℝ) + 4 * d)) +
            Cr * (Real.sqrt ((maxLocalTime x n : ℝ) * (r : ℝ) ^ (1 - (d : ℝ)) *
                tail d (cellSet x n) ((r : ℝ) - 4 * d) * Real.log (n + 2)) +
              (r : ℝ) ^ (1 - (d : ℝ)) * Real.log (n + 2))) →
        (∀ (u : EuclideanSpace ℝ (Fin d)) (s t : ℕ), s < t → t ≤ n → ‖u‖ = 1 →
          (∀ j : ℕ, s ≤ j → j < t → x j ∉ departureRange x j → 0 ≤ inner ℝ u (ξ (x j))) →
          inner ℝ u (toSpace (x t) - toSpace (x s)) ≤
            Cv * Real.sqrt (((t : ℝ) - s) * Real.log (n + 2))) →
        c * ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d ≤ ((departureRange x n).card : ℝ) ∧
          ((departureRange x n).card : ℝ) ≤ C * ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ d ∧
          c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ (maxLocalTime x n : ℝ) ∧
          (maxLocalTime x n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ∧
          c * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ≤ maxRadius x n ∧
          maxRadius x n ≤ C * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdR1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  obtain ⟨hcΨ, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hcΨ (normMin_le_normMax hd1 hΨ)
  obtain ⟨cs, Cs, hcs, hCs, hsst⟩ := exists_sstar_bounds hd1 (Cd := K) (C := K) hK.le hK.le
  set C₁ : ℝ := K * Cs + Cs with hC₁
  have hC₁pos : 0 < C₁ := add_pos (mul_pos hK hCs) hCs
  obtain ⟨Csh, hCsh, hshell⟩ := exists_norm_shell_bound hd hΨ ε hε
  have hbd1 : (1 : ℝ) ≤ 4 * (d : ℝ) := by linarith only [hdR1]
  obtain ⟨B₀, Ct, hB₀, hCt, n₁, htail⟩ := exists_coarse_tail hd (Crad := Cr) (C₁ := C₁)
    (Csh := Csh) (c := cs) (bd := 4 * (d : ℝ)) (r₀ := ρ₀) hCr hC₁pos hCsh hcs hbd1
  set B₁ : ℝ := max B₀ (4 * normMax Ψ ^ 2 / normMin Ψ ^ 2) with hB₁def
  have hB₀B₁ : B₀ ≤ B₁ := le_max_left _ _
  have hB₁3 : 3 ≤ B₁ := hB₀.trans hB₀B₁
  have hB₁pos : 0 < B₁ := by linarith
  have hBcond : 4 * normMax Ψ ^ 2 ≤ (B₁ + 1) * normMin Ψ ^ 2 := by
    have h1 : 4 * normMax Ψ ^ 2 / normMin Ψ ^ 2 ≤ B₁ := le_max_right _ _
    rw [div_le_iff₀ (pow_pos hcΨ 2)] at h1
    nlinarith [pow_pos hcΨ 2]
  obtain ⟨n₂, hH⟩ := exists_maxRadius_le_norm hd (Cv := Cv) (CI := K) (Ct := Ct) (B₁ := B₁)
    (c := cs) (cΨ := normMin Ψ) (Λ := normMax Ψ) hK.le hCt.le hB₁3 hcs hcΨ hΛ hBcond
  have hwd : 0 < unitBallVolume d := unitBallVolume_pos d
  set cp : ℝ := 2 * ε * normMin Ψ * ((d : ℝ) / (d + 1) * unitBallVolume d ^ (-(1 : ℝ) / d))
    with hcp
  have hcp0 : 0 < cp :=
    mul_pos (mul_pos (mul_pos two_pos hε) hcΨ)
      (mul_pos (div_pos hdR (by linarith only [hdR])) (Real.rpow_pos_of_pos hwd _))
  set Cq : ℝ := unitBallVolume d * (B₁ + 2) ^ d * (K * Cs) with hCq
  have hCq0 : 0 ≤ Cq :=
    (mul_pos (mul_pos hwd (pow_pos (by linarith only [hB₁3]) d)) (mul_pos hK hCs)).le
  obtain ⟨Cm, hCm, hmass⟩ := exists_le_of_mass (d := d) hcp0 hcs hCq0
  obtain ⟨c, C, hc, hC, hfin⟩ := exists_final_constants (d := d) hcs hCs hCm hB₁pos.le
  have hdp1 : (0 : ℝ) < 1 / (d + 1) := div_pos one_pos (by linarith only [hdR])
  have hNtend : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / (d + 1))) Filter.atTop
      Filter.atTop :=
    (tendsto_rpow_atTop hdp1).comp tendsto_natCast_atTop_atTop
  have hNlarge : ∀ᶠ n : ℕ in Filter.atTop, (d : ℝ) + 6 ≤ cs * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    filter_upwards [hNtend.eventually_ge_atTop (((d : ℝ) + 6) / cs)] with n hn
    rw [div_le_iff₀ hcs] at hn
    linarith only [hn]
  have hθ : 0 < cs / (K * Cs) ^ 2 := div_pos hcs (pow_pos (mul_pos hK hCs) 2)
  have hlim := CERW.Support.Main.tendsto_log_rpow_div_rpow (2 : ℝ)
    (c := (1 : ℝ) / (d + 1)) hdp1
  have hLsmall : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (n + 2) ^ 2 ≤ cs / (K * Cs) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    filter_upwards [hlim.eventually_le_const hθ, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hNpos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hnpos _
    rw [Real.rpow_two, div_le_iff₀ hNpos] at hn
    exact hn
  have hBlarge : ∀ᶠ n : ℕ in Filter.atTop, (B₁ + 2) ^ 2 ≤ (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop ⌈(B₁ + 2) ^ 2⌉₊] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    (hsst.and (hmass.and (hNlarge.and (hLsmall.and (hBlarge.and (
      (Filter.eventually_ge_atTop n₁).and ((Filter.eventually_ge_atTop n₂).and
        (Filter.eventually_ge_atTop 2))))))))
  refine ⟨c, C, hc, hC, max n₀ 2, le_max_right _ _, ?_⟩
  intro ξ x n hn h0 hstep hξ hM hint happ hrad hproj
  obtain ⟨hsstn, hmassn, hN6, hLn, hen, hn1, hn2, hn3⟩ := hn₀ n ((le_max_left _ _).trans hn)
  set R : ℕ := (departureRange x n).card with hRdef
  set s : ℝ := (R : ℝ) ^ ((1 : ℝ) / d) with hs
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN
  set L : ℝ := Real.log (n + 2) with hLdef
  have hn2' : 2 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : 0 < N := Real.rpow_pos_of_pos hnpos _
  have hL1 : 1 ≤ L := one_le_log_add_two hn2'
  have hsd : s ^ d = (R : ℝ) :=
    CERW.Generic.Kernel.rpow_one_div_natCast_pow (Nat.cast_nonneg _) hd1
  have hnMR : (n : ℝ) ≤ (maxLocalTime x n : ℝ) * (R : ℝ) := by
    exact_mod_cast le_maxLocalTime_mul_card x n
  obtain ⟨hcsN, hMs, hsqrt⟩ := hsstn (maxLocalTime x n : ℝ) s (Nat.cast_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by rw [hsd]; exact hnMR) hM
  have hd6 : (d : ℝ) + 6 ≤ cs * N := hN6
  have hcsN0 : 0 < cs * N := mul_pos hcs hN0
  have hs0 : 0 < s := lt_of_lt_of_le hcsN0 hcsN
  have hs6 : 6 ≤ s := by linarith only [hd6, hcsN, hdR]
  have hsd' : Real.sqrt d ≤ s := by
    have h1 : Real.sqrt d ≤ (d : ℝ) + 6 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith only [hdR], by nlinarith only [hdR]⟩
    linarith only [h1, hd6, hcsN]
  set δ : ℝ := K * Cs * Real.sqrt s * L with hδ
  have hδ0 : 0 ≤ δ :=
    mul_nonneg (mul_nonneg (mul_pos hK hCs).le (Real.sqrt_nonneg s)) (by linarith only [hL1])
  have hδC : δ ≤ C₁ * Real.sqrt s * L := by
    have h1 : K * Cs ≤ C₁ := by linarith only [hC₁, hCs]
    have h2 : 0 ≤ Real.sqrt s * L := mul_nonneg (Real.sqrt_nonneg s) (by linarith only [hL1])
    calc δ = (K * Cs) * (Real.sqrt s * L) := by rw [hδ]; ring
      _ ≤ C₁ * (Real.sqrt s * L) := mul_le_mul_of_nonneg_right h1 h2
      _ = C₁ * Real.sqrt s * L := by ring
  have hδs : δ ≤ s := by
    have h1 : K * Cs * L ≤ Real.sqrt s := by
      apply Real.le_sqrt_of_sq_le
      have h2 : (K * Cs) ^ 2 * L ^ 2 ≤ (K * Cs) ^ 2 * (cs / (K * Cs) ^ 2 * N) :=
        mul_le_mul_of_nonneg_left hLn (sq_nonneg _)
      have h3 : (K * Cs) ^ 2 * (cs / (K * Cs) ^ 2 * N) = cs * N := by
        field_simp
      calc (K * Cs * L) ^ 2 = (K * Cs) ^ 2 * L ^ 2 := by ring
        _ ≤ cs * N := h2.trans_eq h3
        _ ≤ s := hcsN
    have h2 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    calc δ = (K * Cs * L) * Real.sqrt s := by rw [hδ]; ring
      _ ≤ Real.sqrt s * Real.sqrt s := mul_le_mul_of_nonneg_right h1 h2
      _ = s := Real.mul_self_sqrt hs0.le
  have hlocal : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
      |cellLocalTime x n y - normPotential d ε Ψ (cellSet x n) y| ≤ δ := by
    intro y hy
    refine (happ y hy).trans ?_
    calc K * (Real.sqrt (maxLocalTime x n) * L + L) ≤ K * (Cs * Real.sqrt s * L) := by
          exact mul_le_mul_of_nonneg_left hsqrt hK.le
      _ = δ := by rw [hδ]; ring
  have hRn : (R : ℝ) ≤ n := by exact_mod_cast card_departureRange_le x n
  have hBs : (B₁ + 2) * s ≤ n := by
    have h1 : s ^ 2 ≤ n := by
      calc s ^ 2 ≤ s ^ d := pow_le_pow_right₀ (by linarith only [hs6]) hd
        _ = R := hsd
        _ ≤ n := hRn
    exact mul_le_of_sq_le_sq hnpos.le h1 hen
  have hBs4 : B₁ * s + 4 ≤ 2 * n := by linarith only [hBs, hs6, hnpos]
  have hB₀2 : (2 : ℝ) ≤ B₀ := by linarith only [hB₀]
  have hMC₁ : (maxLocalTime x n : ℝ) ≤ C₁ * s :=
    hMs.trans (mul_le_mul_of_nonneg_right (by linarith [mul_pos hK hCs]) hs0.le)
  have hshellC : ∀ r : ℕ, s ≤ r → (r : ℝ) ≤ B₀ * s →
      (shellMax x n r : ℝ) ≤ Csh * B₀ ^ (((d : ℝ) - 1) / (2 * d - 1)) *
        s ^ (1 - 1 / (2 * (d : ℝ) - 1)) *
        (tail d (cellSet x n) ((r : ℝ) - 4 * d) + δ) ^ (1 / (2 * (d : ℝ) - 1)) := by
    intro r hsr hrB
    have hB₀s : B₀ * s ≤ B₁ * s := mul_le_mul_of_nonneg_right hB₀B₁ hs0.le
    apply shellMax_le_of_forall x n r
    · exact mul_nonneg (mul_nonneg (mul_nonneg hCsh.le (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg hs0.le _))
        (Real.rpow_nonneg (add_nonneg (CERW.Support.Geometry.tail_nonneg _ _) hδ0) _)
    · intro z hz
      exact hshell x n δ s B₀ r (4 * (d : ℝ)) hs hs6 hδ0 hδs hB₀2 hsr hrB
        (by linarith only [hdR1])
        (fun y hy => hlocal y (hy.trans (by linarith only [hB₀s, hBs4]))) z hz
  have hFt := htail x n δ hn1 hcsN hMC₁ hδ0 hδC hrad hshellC
  have hbdd : Bornology.IsBounded (cellSet x n) :=
    Metric.isBounded_ball.subset (cellSet_subset_ball hd1 x n)
  have hFt₁ : tail d (cellSet x n) ((B₁ - 2) * s) ≤ Ct * s ^ (2 - (d : ℝ)) * L := by
    refine le_trans ?_ hFt
    refine CERW.Support.Geometry.tail_antitoneOn (measurableSet_cellSet x n) hbdd ?_ ?_ ?_
    · exact Set.mem_Ioi.mpr (by nlinarith only [hB₀, hs0])
    · exact Set.mem_Ioi.mpr (by nlinarith only [hB₁3, hs0])
    · exact mul_le_mul_of_nonneg_right (by linarith only [hB₀B₁]) hs0.le
  have hHle : maxRadius x n ≤ (B₁ + 1) * s := hH ξ x n hn2 h0 hstep hξ hproj hint hcsN hFt₁
  have hHnn : 0 ≤ maxRadius x n :=
    (LatticeProb.euclidNorm_nonneg (x 0)).trans (euclidNorm_le_maxRadius x (Nat.zero_le n))
  set S : ℝ := (B₁ + 1) * s + Real.sqrt d with hSdef
  have hS0 : 0 < S :=
    add_pos_of_pos_of_nonneg (mul_pos (by linarith only [hB₁pos]) hs0) (Real.sqrt_nonneg _)
  have hSs : S ≤ (B₁ + 2) * s := by linarith only [hSdef, hsd']
  have hDS : cellSet x n ⊆ Metric.ball 0 S :=
    (cellSet_subset_ball hd1 x n).trans
      (Metric.ball_subset_ball (by linarith only [hHle, hSdef]))
  have hball : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime x n y - normPotential d ε Ψ (cellSet x n) y| ≤ δ := by
    intro y hy
    apply hlocal y
    have h1 : ‖y‖ < S := mem_ball_zero_iff.mp hy
    linarith only [h1, hSs, hBs, hnpos]
  have hmi := norm_mass_inequality hd hΨ hε x n hs hs0 hS0 hDS hball
  have herr : unitBallVolume d * S ^ d * δ ≤ Cq * s ^ ((d : ℝ) + 1 / 2) * L := by
    have h1 : S ^ d ≤ ((B₁ + 2) * s) ^ d := pow_le_pow_left₀ hS0.le hSs d
    have h2 : s ^ ((d : ℝ) + 1 / 2) = s ^ d * Real.sqrt s := by
      rw [Real.rpow_add hs0, Real.rpow_natCast, Real.sqrt_eq_rpow]
    have h3 : unitBallVolume d * S ^ d * δ ≤ unitBallVolume d * ((B₁ + 2) * s) ^ d * δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hwd.le) hδ0
    calc unitBallVolume d * S ^ d * δ ≤ unitBallVolume d * ((B₁ + 2) * s) ^ d * δ := h3
      _ = Cq * s ^ ((d : ℝ) + 1 / 2) * L := by
          rw [h2, hδ, hCq, mul_pow]
          ring
  have hsCm : s ≤ Cm * N := hmassn s hcsN (hmi.trans (add_le_add le_rfl herr))
  have hsH : s ≤ 2 * maxRadius x n + 1 := by
    have h1 : (R : ℝ) ≤ (2 * maxRadius x n + 1) ^ d :=
      (Nat.cast_le.mpr (Finset.card_le_card
        (departureRange_subset_ballFinset x n))).trans
        (LatticeProb.card_ballFinset_le d hHnn)
    rw [← hsd] at h1
    exact le_of_pow_le_pow_left₀ (by omega) (by linarith only [hHnn]) h1
  have hnN : (n : ℝ) = N ^ (d + 1) := (rpow_frac_pow hnpos.le d).symm
  exact hfin N s R (maxLocalTime x n : ℝ) (maxRadius x n) n hN0 hnN hsd.symm (Nat.cast_nonneg _)
    (by linarith only [hd6, hdR]) hcsN hsCm hMs hHle hnMR hsH

end Core

section Assembly

variable {Ψ : EuclideanSpace ℝ (Fin d)  → ℝ}

/-- Rescaling the six bounds of `eq:coarse` from `N` to `κ N` for a fixed `κ > 0`. -/
private lemma scale_bounds {c C κ : ℝ} (hc : 0 < c) (hC : 0 < C) (hκ : 0 < κ) (d : ℕ) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ N R M H : ℝ, 0 ≤ N →
      c * N ^ d ≤ R → R ≤ C * N ^ d → c * N ≤ M → M ≤ C * N → c * N ≤ H → H ≤ C * N →
      c' * (κ * N) ^ d ≤ R ∧ R ≤ C' * (κ * N) ^ d ∧ c' * (κ * N) ≤ M ∧ M ≤ C' * (κ * N) ∧
        c' * (κ * N) ≤ H ∧ H ≤ C' * (κ * N) := by
  have hκd : 0 < κ ^ d := pow_pos hκ d
  refine ⟨min (c / κ ^ d) (c / κ), max (C / κ ^ d) (C / κ),
    lt_min (div_pos hc hκd) (div_pos hc hκ), lt_max_of_lt_left (div_pos hC hκd), ?_⟩
  intro N R M H hN h1 h2 h3 h4 h5 h6
  have hNd : 0 ≤ N ^ d := pow_nonneg hN d
  have hc1 : min (c / κ ^ d) (c / κ) * κ ^ d ≤ c := by
    calc min (c / κ ^ d) (c / κ) * κ ^ d ≤ c / κ ^ d * κ ^ d :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hκd.le
      _ = c := div_mul_cancel₀ c hκd.ne'
  have hc2 : min (c / κ ^ d) (c / κ) * κ ≤ c := by
    calc min (c / κ ^ d) (c / κ) * κ ≤ c / κ * κ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hκ.le
      _ = c := div_mul_cancel₀ c hκ.ne'
  have hC1 : C ≤ max (C / κ ^ d) (C / κ) * κ ^ d := by
    calc C = C / κ ^ d * κ ^ d := (div_mul_cancel₀ C hκd.ne').symm
      _ ≤ max (C / κ ^ d) (C / κ) * κ ^ d :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hκd.le
  have hC2 : C ≤ max (C / κ ^ d) (C / κ) * κ := by
    calc C = C / κ * κ := (div_mul_cancel₀ C hκ.ne').symm
      _ ≤ max (C / κ ^ d) (C / κ) * κ := mul_le_mul_of_nonneg_right (le_max_right _ _) hκ.le
  have hpow : (κ * N) ^ d = κ ^ d * N ^ d := mul_pow κ N d
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpow]
    calc min (c / κ ^ d) (c / κ) * (κ ^ d * N ^ d)
        = (min (c / κ ^ d) (c / κ) * κ ^ d) * N ^ d := by ring
      _ ≤ c * N ^ d := mul_le_mul_of_nonneg_right hc1 hNd
      _ ≤ R := h1
  · rw [hpow]
    calc R ≤ C * N ^ d := h2
      _ ≤ (max (C / κ ^ d) (C / κ) * κ ^ d) * N ^ d := mul_le_mul_of_nonneg_right hC1 hNd
      _ = max (C / κ ^ d) (C / κ) * (κ ^ d * N ^ d) := by ring
  · calc min (c / κ ^ d) (c / κ) * (κ * N) = (min (c / κ ^ d) (c / κ) * κ) * N := by ring
      _ ≤ c * N := mul_le_mul_of_nonneg_right hc2 hN
      _ ≤ M := h3
  · calc M ≤ C * N := h4
      _ ≤ (max (C / κ ^ d) (C / κ) * κ) * N := mul_le_mul_of_nonneg_right hC2 hN
      _ = max (C / κ ^ d) (C / κ) * (κ * N) := by ring
  · calc min (c / κ ^ d) (c / κ) * (κ * N) = (min (c / κ ^ d) (c / κ) * κ) * N := by ring
      _ ≤ c * N := mul_le_mul_of_nonneg_right hc2 hN
      _ ≤ H := h5
  · calc H ≤ C * N := h6
      _ ≤ (max (C / κ ^ d) (C / κ) * κ) * N := mul_le_mul_of_nonneg_right hC2 hN
      _ = max (C / κ ^ d) (C / κ) * (κ * N) := by ring

/-- The error scale of `lem:norm-local` is at most `C (√m L + L)` once `L ≥ 1` and `l ≤ L`. -/
private lemma error_scale_le {C L l m : ℝ} (hC : 0 ≤ C) (hl : l ≤ L) (hL : 1 ≤ L)
    (hm : 0 ≤ m) (d : ℕ) :
    C * l + C * (if d = 2 then Real.sqrt m * l else Real.sqrt (m * l)) ≤
      C * (Real.sqrt m * L + L) := by
  have hL0 : 0 ≤ L := by linarith
  have hsm : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have h1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL
  have h2 : Real.sqrt L ≤ L := by
    have := Real.mul_self_sqrt hL0
    nlinarith
  have h3 : Real.sqrt m * l ≤ Real.sqrt m * L := mul_le_mul_of_nonneg_left hl hsm
  have h5 := mul_le_mul_of_nonneg_left hl hC
  have h6 := mul_le_mul_of_nonneg_left h3 hC
  split_ifs
  · linarith
  · have h4 : Real.sqrt (m * l) ≤ Real.sqrt m * L := by
      calc Real.sqrt (m * l) ≤ Real.sqrt (m * L) := Real.sqrt_le_sqrt (by gcongr)
        _ = Real.sqrt m * Real.sqrt L := Real.sqrt_mul hm L
        _ ≤ Real.sqrt m * L := mul_le_mul_of_nonneg_left h2 hsm
    have h7 := mul_le_mul_of_nonneg_left h4 hC
    linarith

/-- A measure bound for a set covered by three sets of small measure and a null set. -/
private lemma measure_le_of_subset_union_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A₁ A₂ A₃ N B : Set Ω} {a₁ a₂ a₃ c : ENNReal}
    (hsub : B ⊆ A₁ ∪ A₂ ∪ A₃ ∪ N) (h₁ : μ A₁ ≤ a₁) (h₂ : μ A₂ ≤ a₂) (h₃ : μ A₃ ≤ a₃)
    (hN : μ N = 0) (hc : a₁ + a₂ + a₃ ≤ c) : μ B ≤ c := by
  refine (measure_mono hsub).trans ((measure_union_le _ N).trans ?_)
  rw [hN, add_zero]
  refine (measure_union_le _ A₃).trans ((add_le_add (measure_union_le A₁ A₂) h₃).trans ?_)
  exact (add_le_add (add_le_add h₁ h₂) le_rfl).trans hc

end Assembly

/-- `prop:norm-coarse`: the occupation, local time and radius bounds for the walk with drift
field `ξ`, from `lem:norm-local`, `lem:norm-radial` and `lem:drift-crossing`. -/
theorem norm_coarse_bounds_of (hlocal : norm_local_time_potential.{u})
    (hradial : norm_radial_test.{u}) (hcross : drift_crossing) : norm_coarse_bounds.{u} := by
  intro d hd Ψ hΨ ε hε hell r p hp
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨ρ₀, -, hrad⟩ := hradial hd Ψ hΨ
  obtain ⟨Cl, hCl, hloc⟩ := hlocal hd Ψ hΨ ε hε hell p hp
  obtain ⟨Cr, hCr, hrad'⟩ := hrad ε hε hell p hp
  obtain ⟨Cv, hCv, hvec⟩ := VectorBound.exists_driftCompensated_bound hd1 hε.le hp
  obtain ⟨c₁, C₁, hc₁, hC₁, n₀, hn₀, hdet⟩ :=
    norm_coarse_deterministic hd hΨ hε (K := Cl) (Cr := Cr) (Cv := Cv) (ρ₀ := ρ₀) hCl hCr
  have hV : 0 < normBallVolume Ψ := normBallVolume_pos hd1 hΨ
  set κ : ℝ := (((d : ℝ) + 1) / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1)) with hκ
  have hκpos : 0 < κ := Real.rpow_pos_of_pos (by positivity) _
  have hr : ∀ n : ℕ, r n = κ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    intro n
    show (((d : ℝ) + 1) * n / (2 * d * ε * normBallVolume Ψ)) ^ ((1 : ℝ) / (d + 1)) = _
    rw [hκ, ← Real.mul_rpow (by positivity) (Nat.cast_nonneg n), div_mul_eq_mul_div]
  obtain ⟨c', C', hc', hC', hscale⟩ := scale_bounds hc₁ hC₁ hκpos d
  have hn₀p : 0 ≤ (n₀ : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨c', max C' (Cl + Cr + Cv + (n₀ : ℝ) ^ p), hc', lt_max_of_lt_left hC', ?_⟩
  intro ξ hξsub hξ0 Ω _ μ _ X hX n hn
  have hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ) := by
    intro z i
    by_cases hz : z = 0
    · rw [hz, hξ0]
      simp only [PiLp.zero_apply, abs_zero, mul_zero]
      positivity
    · have h1 := CERW.Generic.Norm.subgradient_abs_coord_le hΨ (hξsub z hz) i
      exact (mul_le_mul_of_nonneg_left h1 hε.le).trans (hell i).le
  have hξgeo : ∀ y : Site d, y ≠ 0 →
      normMin Ψ * euclidNorm y ≤ inner ℝ (ξ y) (toSpace y) ∧ ‖ξ y‖ ≤ normMax Ψ := by
    intro y hy
    have h := subgradient_bounds hd1 hΨ (hξsub y hy)
    rwa [norm_toSpace] at h
  by_cases hn₀le : n₀ ≤ n
  · have hnull : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j : ℕ, X (j + 1) ω - X j ω ∈ unitSteps d)} = 0 := by
      refine ae_iff.mp ?_
      filter_upwards [ae_iff.mpr hX.start,
        ae_all_iff.mpr (fun j => ae_sub_mem_unitSteps_drift hd1 hε.le hξ hX j)] with ω h0 h1
      exact ⟨h0, h1⟩
    have hL1 := one_le_log_add_two hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hlogle : Real.log n ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log hnpos (by linarith)
    have hLsq : Real.log n ^ 2 ≤ Real.log ((n : ℝ) + 2) ^ 2 := pow_le_pow_left₀ hlog0 hlogle 2
    refine measure_le_of_subset_union_three (fun ω hω => ?_) (hloc ξ hξsub hξ0 μ X hX n hn)
      (hrad' ξ hξsub hξ0 μ X hX n hn) (hvec hξ hξ0 hX n hn) hnull ?_
    · by_contra hcon
      rw [Set.mem_union, Set.mem_union, Set.mem_union, not_or, not_or, not_or] at hcon
      obtain ⟨⟨⟨hA, hB⟩, hVe⟩, hZ⟩ := hcon
      simp only [Set.mem_setOf_eq, not_not] at hA hB hZ
      simp only [Set.mem_setOf_eq, not_exists, not_and, not_lt] at hVe
      obtain ⟨hM, hint, happ⟩ := hA
      set x : ℕ → Site d := fun j => X j ω with hx
      have hM' : (maxLocalTime x n : ℝ) ≤
          Cl * ((departureRange x n).card : ℝ) ^ ((1 : ℝ) / d) + Cl * Real.log ((n : ℝ) + 2) ^ 2 :=
        hM.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hLsq hCl.le))
      have hint' : ∀ s t : ℕ, s < t → t ≤ n →
          (intervalMax x s t : ℝ) ≤ Cl * (freshCount x s t : ℝ) ^ ((1 : ℝ) / d) +
            Cl * Real.log ((n : ℝ) + 2) ^ 2 := fun s t hst htn =>
        (hint s t hst htn).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hLsq hCl.le))
      have happ' : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
          |cellLocalTime x n y - normPotential d ε Ψ (cellSet x n) y| ≤
            Cl * (Real.sqrt (maxLocalTime x n) * Real.log ((n : ℝ) + 2) +
              Real.log ((n : ℝ) + 2)) := fun y hy =>
        (happ y hy).trans (error_scale_le hCl.le hlogle hL1 (Nat.cast_nonneg _) d)
      have hrad'' : ∀ ρ : ℕ, ρ₀ ≤ ρ → ρ ≤ n →
          tail d (cellSet x n) ((ρ : ℝ) + 4 * d) ≤
            Cr * shellMax x n ρ * (tail d (cellSet x n) ((ρ : ℝ) - 4 * d) -
              tail d (cellSet x n) ((ρ : ℝ) + 4 * d)) +
            Cr * (Real.sqrt ((maxLocalTime x n : ℝ) * (ρ : ℝ) ^ (1 - (d : ℝ)) *
                tail d (cellSet x n) ((ρ : ℝ) - 4 * d) * Real.log ((n : ℝ) + 2)) +
              (ρ : ℝ) ^ (1 - (d : ℝ)) * Real.log ((n : ℝ) + 2)) := by
        intro ρ hρ hρn
        refine (hB ρ hρ hρn).trans ?_
        have hsub : (((departureRange x n).filter
            (fun z => (ρ : ℝ) - 4 * d ≤ euclidNorm z)).sup (localTime x n) : ℕ) ≤
            maxLocalTime x n := Finset.sup_mono (Finset.filter_subset _ _)
        have hsub' : ((((departureRange x n).filter
            (fun z => (ρ : ℝ) - 4 * d ≤ euclidNorm z)).sup (localTime x n) : ℕ) : ℝ) ≤
            (maxLocalTime x n : ℝ) := by exact_mod_cast hsub
        have hρpow : 0 ≤ (ρ : ℝ) ^ (1 - (d : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg ρ) _
        have hT := CERW.Support.Geometry.tail_nonneg (d := d) (cellSet x n) ((ρ : ℝ) - 4 * d)
        have hsq : Real.sqrt ((((departureRange x n).filter
            (fun z => (ρ : ℝ) - 4 * d ≤ euclidNorm z)).sup (localTime x n) : ℕ) *
              (ρ : ℝ) ^ (1 - (d : ℝ)) * tail d (cellSet x n) ((ρ : ℝ) - 4 * d) *
              Real.log n) ≤
            Real.sqrt ((maxLocalTime x n : ℝ) * (ρ : ℝ) ^ (1 - (d : ℝ)) *
              tail d (cellSet x n) ((ρ : ℝ) - 4 * d) * Real.log ((n : ℝ) + 2)) := by
          refine Real.sqrt_le_sqrt ?_
          have hM0 : 0 ≤ (maxLocalTime x n : ℝ) := Nat.cast_nonneg _
          have hMsub0 : (0 : ℝ) ≤ ((((departureRange x n).filter
            (fun z => (ρ : ℝ) - 4 * d ≤ euclidNorm z)).sup (localTime x n) : ℕ) : ℝ) :=
            Nat.cast_nonneg _
          gcongr
        have hlg : (ρ : ℝ) ^ (1 - (d : ℝ)) * Real.log n ≤
            (ρ : ℝ) ^ (1 - (d : ℝ)) * Real.log ((n : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlogle hρpow
        have h1 := mul_le_mul_of_nonneg_left hsq hCr.le
        have h2 := mul_le_mul_of_nonneg_left hlg hCr.le
        linarith
      have hproj' : ∀ (u : EuclideanSpace ℝ (Fin d)) (s t : ℕ), s < t → t ≤ n → ‖u‖ = 1 →
          (∀ j : ℕ, s ≤ j → j < t → x j ∉ departureRange x j → 0 ≤ inner ℝ u (ξ (x j))) →
          inner ℝ u (toSpace (x t) - toSpace (x s)) ≤
            Cv * Real.sqrt (((t : ℝ) - s) * Real.log ((n : ℝ) + 2)) := by
        intro u s t hst htn hu hdir
        have h1 := hcross hε.le ξ x n Cv (fun s t hst htn => hVe s t hst htn) u hu s t hst htn hdir
        refine h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hCv.le)
        have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst.le
        exact mul_le_mul_of_nonneg_left hlogle (by linarith)
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hdet ξ x n hn₀le hZ.1 hZ.2 hξgeo hM' hint' happ' hrad''
        hproj'
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hscale ((n : ℝ) ^ ((1 : ℝ) / (d + 1)))
        ((departureRange x n).card : ℝ) (maxLocalTime x n : ℝ) (maxRadius x n)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) h1 h2 h3 h4 h5 h6
      rw [← hr n] at g1 g2 g3 g4 g5 g6
      have hrn : 0 ≤ r n := by
        rw [hr n]
        exact mul_nonneg hκpos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hCC : C' ≤ max C' (Cl + Cr + Cv + (n₀ : ℝ) ^ p) := le_max_left _ _
      exact hω ⟨g1, g2.trans (mul_le_mul_of_nonneg_right hCC (pow_nonneg hrn d)), g3,
        g4.trans (mul_le_mul_of_nonneg_right hCC hrn), g5,
        g6.trans (mul_le_mul_of_nonneg_right hCC hrn)⟩
    · have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      rw [← ENNReal.ofReal_add (mul_nonneg hCl.le hnp) (mul_nonneg hCr.le hnp),
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hCl.le hnp) (mul_nonneg hCr.le hnp))
          (mul_nonneg hCv.le hnp)]
      refine ENNReal.ofReal_le_ofReal (?_ : _ ≤ _)
      rw [← add_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right
        ((by linarith : Cl + Cr + Cv ≤ Cl + Cr + Cv + (n₀ : ℝ) ^ p).trans (le_max_right _ _)) hnp
  · exact (prob_le_one).trans (ENNReal.one_le_ofReal.mpr
      (one_le_mul_rpow_neg hp (by omega) (not_le.mp hn₀le).le
        ((by linarith : (n₀ : ℝ) ^ p ≤ Cl + Cr + Cv + (n₀ : ℝ) ^ p).trans (le_max_right _ _))))

end CERW.Support.Norm
