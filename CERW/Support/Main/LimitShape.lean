import CERW.Frozen.BallShape
import CERW.Support.Drift.Existence
import CERW.Support.Drift.Bridge
import CERW.Generic.Norm.Subgradient

/-!
# The limit shape theorem in the revised normalization, and the non-vacuity of the norm walk

`limit_shape` is Theorem 1.1 of the revised paper, written with `r_n = ((d+1)n/(2dεω_d))^{1/(d+1)}`;
it follows from the frozen `CERW.Frozen.ball_shape`, since `r_n = a·n^{1/(d+1)}` with
`a = ((d+1)/(2dεω_d))^{1/(d+1)}`. `exists_norm_realization` shows that the hypotheses of the
statements about the walk with norm `Ψ` can be met: for every norm, every choice of subgradients
and every `ε > 0` with `ε max_i Ψ(e_i) < 1/d` there is a realization of the walk.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Main

theorem limit_shape {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Site d) (hX : CERW.IsCERW μ ε X) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ᵐ ω ∂μ,
      (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
        {x : Site d | euclidNorm x < (1 - η) * r n} ⊆ ↑(CERW.departureRange (X · ω) n) ∧
        (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆
          {x | euclidNorm x < (1 + η) * r n}) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
        |(CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|
          ≤ η * r n) ∧
      (∀ x : Site d, ∃ᶠ j in atTop, X j ω = x) := by
  intro ωd r
  have key := CERW.Frozen.ball_shape hd hε hεd μ X hX
  have hω : 0 < ωd := CERW.unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * ωd) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hr : ∀ n : ℕ, r n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    show (((d : ℝ) + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) = _
    rw [show ((d : ℝ) + 1) * n / (2 * d * ε * ωd) =
      (((d : ℝ) + 1) / (2 * d * ε * ωd)) * n by ring]
    exact Real.mul_rpow hc.le (Nat.cast_nonneg n)
  filter_upwards [key] with ω hω'
  obtain ⟨hshape, hprof, -, -, hrec⟩ := hω'
  have hshape' : ∀ η : ℝ, 0 < η → η < a → ∀ᶠ n : ℕ in atTop,
      {x : Site d | euclidNorm x < (a - η) * (n : ℝ) ^ ((1 : ℝ) / (d + 1))} ⊆
        ↑(CERW.departureRange (X · ω) n) ∧
      (↑(CERW.departureRange (X · ω) n) : Set (Site d)) ⊆
        {x | euclidNorm x < (a + η) * (n : ℝ) ^ ((1 : ℝ) / (d + 1))} := by
    intro η h0 h1
    filter_upwards [hshape η h0 h1] with n hn
    exact ⟨hn.1, hn.2.1.trans hn.2.2⟩
  refine ⟨fun η h0 h1 => ?_, fun η h0 => ?_, hrec⟩
  · filter_upwards [hshape' (η * a) (mul_pos h0 ha) (mul_lt_of_lt_one_left ha h1)] with n hn
    rw [hr n]
    have e1 : (a - η * a) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) =
        (1 - η) * (a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) := by ring
    have e2 : (a + η * a) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) =
        (1 + η) * (a * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) := by ring
    rw [e1, e2] at hn
    exact hn
  · filter_upwards [hprof (η * a) (mul_pos h0 ha), eventually_ge_atTop 1] with n hn hn1 x
    have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn1) _
    have hx : |(CERW.localTime (X · ω) n x : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) -
        2 * d * ε * max (a - euclidNorm x / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) 0| ≤ η * a := hn x
    have hmax : max (r n - euclidNorm x) 0 = (n : ℝ) ^ ((1 : ℝ) / (d + 1)) *
        max (a - euclidNorm x / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) 0 := by
      rw [mul_max_of_nonneg _ _ hNpos.le, mul_zero, hr n]
      congr 1
      field_simp
    have hsplit : (CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0 =
        (n : ℝ) ^ ((1 : ℝ) / (d + 1)) *
          ((CERW.localTime (X · ω) n x : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) -
            2 * d * ε * max (a - euclidNorm x / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) 0) := by
      rw [hmax]
      field_simp
    rw [hsplit, abs_mul, abs_of_pos hNpos]
    calc (n : ℝ) ^ ((1 : ℝ) / (d + 1)) *
          |(CERW.localTime (X · ω) n x : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) -
            2 * d * ε * max (a - euclidNorm x / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) 0|
        ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * (η * a) :=
          mul_le_mul_of_nonneg_left hx hNpos.le
      _ = η * r n := by rw [hr n]; ring

/-- For every norm, every choice of subgradients with `ξ 0 = 0`, and every `ε > 0` with
`ε Ψ(e_i) < 1/d`, the walk with norm `Ψ` has a realization. -/
theorem exists_norm_realization {d : ℕ} (hd : 1 ≤ d) {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hΨ : CERW.IsNorm Ψ) {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    (hξ : ∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) (hξ0 : ξ 0 = 0)
    {ε : ℝ} (hε : 0 < ε) (hεΨ : ∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X := by
  refine CERW.Support.Drift.exists_isDriftCERW hd hε.le (fun z i => ?_)
  by_cases hz : z = 0
  · subst hz
    rw [hξ0]
    simp only [PiLp.zero_apply, abs_zero, mul_zero]
    exact one_div_nonneg.mpr (Nat.cast_nonneg d)
  · have h1 : |ξ z i| ≤ Ψ (CERW.coordVec i) :=
      CERW.Generic.Norm.subgradient_abs_coord_le hΨ (hξ z hz) i
    calc ε * |ξ z i| ≤ ε * Ψ (CERW.coordVec i) := mul_le_mul_of_nonneg_left h1 hε.le
      _ ≤ 1 / (d : ℝ) := (hεΨ i).le

/-- A nonzero lattice site embeds to a nonzero vector of `ℝ^d`. -/
private theorem toSpace_ne_zero {d : ℕ} {x : Site d} (hx : x ≠ 0) :
    CERW.toSpace x ≠ (0 : EuclideanSpace ℝ (Fin d)) := by
  intro h
  apply hx
  funext i
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
  simpa using hi

/-- The direction `v/|v|` is a subgradient of the Euclidean norm at every `v ≠ 0`. -/
private theorem isSubgradient_norm_unitDir {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    CERW.IsSubgradient (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) v (CERW.unitDir v) := by
  intro y
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hinner : inner ℝ (CERW.unitDir v) (y - v) = ‖v‖⁻¹ * (inner ℝ v y - ‖v‖ ^ 2) := by
    rw [CERW.unitDir, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
  have hcs : inner ℝ v y ≤ ‖v‖ * ‖y‖ := real_inner_le_norm v y
  have hle : ‖v‖⁻¹ * inner ℝ v y ≤ ‖y‖ := by
    calc ‖v‖⁻¹ * inner ℝ v y ≤ ‖v‖⁻¹ * (‖v‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hpos.le)
      _ = ‖y‖ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have hexp : ‖v‖ + ‖v‖⁻¹ * (inner ℝ v y - ‖v‖ ^ 2) = ‖v‖⁻¹ * inner ℝ v y := by
    field_simp
    ring
  show ‖v‖ + inner ℝ (CERW.unitDir v) (y - v) ≤ ‖y‖
  rw [hinner, hexp]
  exact hle

/-- The Euclidean norm with the field `x/|x|` meets the hypotheses of the norm statements:
it is a norm, `x/|x|` is a subgradient at every `x ≠ 0`, the field vanishes at the origin, and
`ε < 1/d` is the ellipticity condition. -/
theorem euclidean_norm_hypotheses {d : ℕ} {ε : ℝ} (hεd : ε < 1 / (d : ℝ)) :
    CERW.IsNorm (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ∧
    (∀ x : Site d, x ≠ 0 →
      CERW.IsSubgradient (fun v => ‖v‖) (CERW.toSpace x) (CERW.unitDir (CERW.toSpace x))) ∧
    CERW.unitDir (CERW.toSpace (0 : Site d)) = 0 ∧
    ∀ i : Fin d, ε * ‖CERW.coordVec (d := d) i‖ < 1 / (d : ℝ) := by
  refine ⟨⟨norm_add_le, fun t x => ?_, fun x hx => norm_eq_zero.mp hx⟩, fun x hx => ?_,
    ?_, fun i => ?_⟩
  · simp only [norm_smul, Real.norm_eq_abs]
  · exact isSubgradient_norm_unitDir (toSpace_ne_zero hx)
  · have h0 : CERW.toSpace (0 : Site d) = 0 := by
      ext i
      simp
    rw [h0]
    exact CERW.unitDir_zero
  · have hcoord : ‖CERW.coordVec (d := d) i‖ = 1 := by
      simp [CERW.coordVec]
    rw [hcoord, mul_one]
    exact hεd

end CERW.Support.Main
