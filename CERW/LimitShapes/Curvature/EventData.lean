import CERW.LimitShapes.Curvature.EventScales
import CERW.LimitShapes.Curvature.EventGeometry
import CERW.LimitShapes.Energy.Contact
import CERW.LimitShapes.EventConsequences

/-!
# Annular data on the common event

The actual remainder outside the inner ball satisfies the geometric, mass, and potential
bounds used in `eq:mass` and `sec:outer-potential`.
-/

namespace CERW.LimitShapes.Curvature

open CERW LatticeProb MeasureTheory
open CERW.Support.Norm.ContactEvent
open CERW.Support.Norm.EuclideanCoarse
open CERW.Support.Outer.Radius

/-- The annular geometric and potential data on the actual common event. -/
theorem exists_annular_event_data {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / (d : ℝ)) (J : CERW.LimitShapes.EventConstants)
    (hc : 0 < J.cCo) (hCo : 0 ≤ J.CCo) (hLoc : 0 ≤ J.CLoc)
    (hQuad : 0 ≤ J.CQuad) (hMart : 0 ≤ J.CMart) :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
      ∀ (X : ℕ → Site d) (n : ℕ), n₀ ≤ n →
        CERW.Support.Norm.ContactEvent.PathTyping d X →
        CERW.LimitShapes.EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε
          (fun x => CERW.unitDir (CERW.toSpace x)) J X n →
      let r := scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
      let delta := r * contactRate d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n
      let b := CERW.innerRadius X n
      let R := CERW.maxRadius X n + 2 * Real.sqrt d
      let E := CERW.cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b
      0 < b ∧ r / 2 ≤ b ∧ b ≤ 2 * r ∧ 1 ≤ delta ∧
      1 ≤ R - b ∧ b ≤ R ∧ R ≤ A * b ∧
      (∀ v ∈ E, b ≤ ‖v‖ ∧ ‖v‖ ≤ R) ∧
      volume.real E ≤ C * delta * b ^ (d - 1) ∧
      (∀ y : EuclideanSpace ℝ (Fin d), b ≤ ‖y‖ →
        CERW.cellLocalTime X n y / 2 - C * delta ≤ CERW.potential d ε E y) := by
  let Ψ := fun v : EuclideanSpace ℝ (Fin d) => ‖v‖
  have hΨ : IsNorm Ψ := isNorm_euclidean
  have hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ) := by
    intro i
    simpa only [Ψ, coordVec, PiLp.norm_single, norm_one, mul_one] using hεd
  have hξ : ∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (unitDir (toSpace x)) :=
    fun x hx => isSubgradient_unitDir fun hz => hx (eq_zero_of_toSpace_eq_zero hz)
  obtain ⟨Ci, hCi, Ni, hNi, hi⟩ :=
    CERW.LimitShapes.inner_on_event hd hε hεd J hc hCo hLoc hQuad hMart
  obtain ⟨Cs, hCs, Ns, hNs, hs⟩ :=
    Energy.exists_square_one_sided hd hΨ hε hell J hCo hMart
  obtain ⟨Ct, hCt, Nt, hNt, ht⟩ :=
    Energy.contact_potential_from_energy hd Ψ hΨ ε hε hell J hCo hLoc hMart
  obtain ⟨Nq, hNq, hq⟩ := exists_annular_scale_threshold hd hε hCi
  let A : ℝ := 2 * J.CCo + 2 * Real.sqrt d + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith [Real.sqrt_nonneg (d : ℝ)]
  let M : ℝ := (unitBallVolume d / (2 * ε)) * 2 ^ (d - 1) * A ^ (d - 1)
  have hM : 0 < M := by
    dsimp [M]
    exact mul_pos (mul_pos (div_pos (unitBallVolume_pos d) (by positivity))
      (by positivity)) (pow_pos (by linarith) _)
  let C := M * Ct + Cs
  have hC : 0 < C := add_pos (mul_pos hM hCt) hCs
  refine ⟨A, C, hA, hC, max Ni (max Ns (max Nt Nq)), by omega, ?_⟩
  intro X n hn hpath hev
  dsimp only
  let r := scale d Ψ ε n
  let q := contactRate d Ψ ε n
  let b := innerRadius X n
  let R := maxRadius X n + 2 * Real.sqrt d
  let E := cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b
  obtain ⟨hr2, hdelta, hsmall⟩ := hq n (by omega)
  have hr : 0 < r := by linarith
  have hir := (hi _ hξ unitDir_toSpace_zero X n (by omega) hpath hev).1
  change |b - r| ≤ Ci * r * q at hir
  have herr : Ci * r * q ≤ r / 2 := by
    have hm := mul_le_mul_of_nonneg_left hsmall hr.le
    dsimp [r, q] at *
    nlinarith [hm]
  have hbhalf : r / 2 ≤ b := by linarith [(abs_le.mp hir).1]
  have hbupper : b ≤ 2 * r := by linarith [(abs_le.mp hir).2]
  have hb : 0 < b := by linarith
  have hsqrt : 1 ≤ Real.sqrt d := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast (show 1 ≤ d by omega)
  have hbr := innerRadius_le (by omega : 1 ≤ d) X n
  have hwidth : 1 ≤ R - b := by dsimp [R, b]; linarith
  have hbR : b ≤ R := by linarith
  have hcoarse := hev.1.2.2.2.2.2
  have hRA : R ≤ A * b := by
    have hb1 : 1 ≤ b := by linarith
    have hcob : J.CCo * r ≤ 2 * J.CCo * b := by nlinarith
    have hsqb := mul_le_mul_of_nonneg_left hb1 (Real.sqrt_nonneg (d : ℝ))
    dsimp [R, A]
    change maxRadius X n ≤ J.CCo * r at hcoarse
    nlinarith
  obtain ⟨hEm, hband⟩ := annular_measurable_band (by omega : 1 ≤ d) X n
  obtain ⟨y₀, hy₀, hycl⟩ := exists_annular_contact (by omega : 1 ≤ d) X n
  have hcontact := ht _ hξ unitDir_toSpace_zero X n (by omega) hpath hev y₀ hy₀ hycl
  rw [CERW.Support.Inner.normPotential_norm_eq (by omega)] at hcontact
  rw [potential_eq_annular hd ε X n hb y₀ hy₀.ge] at hcontact
  have hmass := measure_le_contact_potential hd hε hb hbR hEm hband y₀ hy₀
  have hfactor : (unitBallVolume d / (2 * ε)) * 2 ^ (d - 1) * R ^ (d - 1) ≤
      M * b ^ (d - 1) := by
    calc
      _ ≤ (unitBallVolume d / (2 * ε)) * 2 ^ (d - 1) * (A * b) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hb.le.trans hbR) hRA _)
          (mul_nonneg (div_nonneg (unitBallVolume_pos d).le (by positivity))
            (by positivity))
      _ = M * b ^ (d - 1) := by rw [mul_pow]; ring
  have hH : 0 ≤ potential d ε E y₀ := by
    have hvol := measureReal_nonneg (μ := volume) (s := E)
    have hfac : 0 < (unitBallVolume d / (2 * ε)) * 2 ^ (d - 1) * R ^ (d - 1) := by
      have hRp : 0 < R := hb.trans_le hbR
      exact mul_pos (mul_pos (div_pos (unitBallVolume_pos d) (by positivity))
        (by positivity)) (pow_pos hRp _)
    nlinarith
  have hmass' : volume.real E ≤ M * Ct * (r * q) * b ^ (d - 1) := by
    calc
      _ ≤ M * b ^ (d - 1) * potential d ε E y₀ :=
        hmass.trans (mul_le_mul_of_nonneg_right hfactor hH)
      _ ≤ M * b ^ (d - 1) * (Ct * r * q) :=
        mul_le_mul_of_nonneg_left hcontact (by positivity)
      _ = _ := by ring
  refine ⟨hb, hbhalf, hbupper, hdelta, hwidth, hbR, hRA, hband, ?_, ?_⟩
  · have hmc : M * Ct ≤ C := by dsimp [C]; linarith
    exact hmass'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmc (by linarith : 0 ≤ r * q)) (by positivity))
  · intro y hy
    have hlo := (hs _ hξ unitDir_toSpace_zero X n (by omega) hpath hev).1 y
    rw [CERW.Support.Inner.normPotential_norm_eq (by omega),
      potential_eq_annular hd ε X n hb y hy] at hlo
    have hsc : Cs ≤ C := by dsimp [C]; linarith [mul_pos hM hCt]
    have hm := mul_le_mul_of_nonneg_right hsc (by linarith : 0 ≤ r * q)
    dsimp [r, q] at *
    nlinarith

end CERW.LimitShapes.Curvature
