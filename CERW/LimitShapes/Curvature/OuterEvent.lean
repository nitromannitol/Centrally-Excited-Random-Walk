import CERW.LimitShapes.Curvature.OuterWidth
import CERW.LimitShapes.Curvature.OuterScales
import CERW.LimitShapes.Curvature.OuterProbability

/-! # Outer radius by curvature on the common event

The width estimate and the inner-radius estimate prove Proposition `prop:stronger-outer`.
-/

universe u

namespace CERW.LimitShapes.Curvature

open CERW LatticeProb MeasureTheory
open CERW.Support.Norm.ContactEvent

/-- The outer-radius bound of Proposition `prop:stronger-outer` on the common event. -/
theorem outer_on_event :
    ∀ {d : ℕ} (_hd : 2 ≤ d) {ε : ℝ}, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ K : CERW.LimitShapes.EventConstants,
        0 < K.cCo → 0 ≤ K.CCo → 0 ≤ K.CLoc → 0 ≤ K.CQuad → 0 ≤ K.CMart → 0 < K.CCross →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient
          (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n → PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε ξ K X n →
        maxRadius X n ≤ CERW.Support.Outer.Radius.radius d ε n + C *
          (if d = 2 then Real.sqrt (CERW.Support.Outer.Radius.radius d ε n) *
            Real.log n ^ ((5 : ℝ) / 2) else Real.log n ^ ((d : ℝ) + 1)) := by
  intro d hd ε hε hεd K hc hCo hLoc hQuad hMart hCross
  obtain ⟨Cw, hCw, Nw, hNw, hw⟩ :=
    exists_outer_width_on_event hd hε hεd K hc hCo hLoc hQuad hMart hCross
  obtain ⟨Ci, hCi, Ni, hNi, hi⟩ :=
    CERW.LimitShapes.inner_on_event hd hε hεd K hc hCo hLoc hQuad hMart
  obtain ⟨Ns, hNs, hs⟩ := Energy.exists_site_scale_threshold hd
    CERW.Support.Norm.EuclideanCoarse.isNorm_euclidean hε
  refine ⟨Cw + Ci, add_pos hCw hCi, max Nw (max Ni Ns), by omega, ?_⟩
  intro ξ hξ hξ0 X n hn hpath hev
  have hwidth := hw ξ hξ hξ0 X n (by omega) hpath hev
  have hinner := (hi ξ hξ hξ0 X n (by omega) hpath hev).1
  obtain ⟨hlog, hr, _⟩ := hs n (by omega)
  let r := scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
  let delta := r * contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
  have hrp : 0 < r := by change 2 ≤ r at hr; linarith
  have hd0 : 0 ≤ delta := by
    rw [show delta = r * contactRate d
      (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n from rfl]
    rw [Energy.scale_mul_contactRate _ ε n hrp]
    split_ifs <;> positivity
  have hpow : 1 ≤ Real.log n ^ d := one_le_pow₀ hlog
  have herr : Ci * delta ≤ Ci * delta * Real.log n ^ d :=
    le_mul_of_one_le_right (mul_nonneg hCi.le hd0) hpow
  have hi' : innerRadius X n - r ≤ Ci * delta := by
    have hu := (abs_le.mp hinner).2
    change innerRadius X n - r ≤ Ci * r *
      contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n at hu
    simpa only [delta, mul_assoc] using hu
  have hout : maxRadius X n ≤ r + (Cw + Ci) * (delta * Real.log n ^ d) := by
    change maxRadius X n + 2 * Real.sqrt d - innerRadius X n ≤
      Cw * delta * Real.log n ^ d at hwidth
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  rw [show r = CERW.Support.Outer.Radius.radius d ε n from
    euclidean_scale_eq_radius d ε n,
    show delta * Real.log n ^ d = _ from
      contact_error_mul_log_pow hrp (by linarith)] at hout
  exact hout

/-- The probability endpoint of Proposition `prop:stronger-outer`, proved by curvature. -/
theorem outer_radius_via_curvature : CERW.Support.Statements.outer_radius.{u} :=
  outer_radius_of_event_bound outer_on_event

end CERW.LimitShapes.Curvature
