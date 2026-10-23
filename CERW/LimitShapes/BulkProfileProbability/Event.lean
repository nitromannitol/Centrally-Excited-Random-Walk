import CERW.LimitShapes.BulkProfileProbability.Scales
import CERW.LimitShapes.Curvature.FluctuationProbabilityAux

/-!
# The bulk profile on the intersection event

Proposition `prop:bulk-profile` follows from the common event and the inner and volume
clauses of Theorem `thm:fluctuations`, using the excess-set potential estimate.
-/

open MeasureTheory Filter Topology
open scoped symmDiff Pointwise
open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes

open CERW
open CERW.Support.Norm.ContactEvent (scale contactRate)
open private exists_contact_setup_core from CERW.Support.Contact.ContactSetup
open private InnerVolume from CERW.Support.Lower.BulkProfile

/-- The common event and fluctuation clauses imply the exact bulk profile at large times. -/
theorem bulk_profile_on_intersection {d : ℕ} (hd : 2 ≤ d) {ε κ A θ : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hA : 0 < A) (hθ : 0 < θ) (hθ1 : θ < 1)
    (K : EventConstants) (hCo : 0 ≤ K.CCo) (hLoc : 0 ≤ K.CLoc)
    (r : ℕ → ℝ) (hr : ∀ n, r n = (κ * n) ^ ((1 : ℝ) / (d + 1)))
    (hrscale : ∀ n, scale d (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n = r n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Y : ℕ → Site d,
      InnerVolume d r A Y n → CERW.Support.Norm.ContactEvent.PathTyping d Y →
      EventEstimates (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε
        (fun x => unitDir (toSpace x)) K Y n →
      ∀ y : Site d, euclidNorm y ≤ θ * r n →
        |(localTime Y n y : ℝ) - 2 * d * ε * (r n - euclidNorm y)| ≤
          C * if d = 2 then Real.sqrt (r n) * Real.log n
            else Real.sqrt (r n * Real.log n) := by
  let V := A + unitBallVolume d * A * d * 2 ^ (d - 1)
  let C := K.CLoc * (2 * Real.sqrt (2 * K.CCo) + 2) +
    (2 * ε / unitBallVolume d) * (((1 - θ) / 2) ^ (d - 1))⁻¹ * V + 2 * d * ε * A
  have hω := unitBallVolume_pos d
  have ht : 0 < (1 - θ) / 2 := by linarith
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hC : 0 < C := by
    have hlast : 0 < 2 * (d : ℝ) * ε * A := by positivity
    have hfirst : 0 ≤ K.CLoc * (2 * Real.sqrt (2 * K.CCo) + 2) := by positivity
    have hmid : 0 ≤ (2 * ε / unitBallVolume d) *
        (((1 - θ) / 2) ^ (d - 1))⁻¹ * V := by positivity
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [bulk_scales_eventually hd hκ hA hθ hθ1 r hr] with n hn
  obtain ⟨hn2, hr1, hl1, hlr, hlog, hs, hyn⟩ := hn
  intro Y hIV hlegal hE y hy
  have hrp : 0 < r n := by linarith
  have hq : 0 ≤ (if d = 2 then Real.sqrt (Real.log n / r n)
      else Real.log n / r n) := by split_ifs <;> positivity
  have he : r n * (if d = 2 then Real.sqrt (Real.log n / r n)
      else Real.log n / r n) =
      if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n := by
    have h := Energy.scale_mul_contactRate
      (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) ε n (by rw [hrscale]; exact hrp)
    simpa only [contactRate, hrscale] using h
  have hin : |innerRadius Y n - r n| ≤
      A * r n * (if d = 2 then Real.sqrt (Real.log n / r n)
        else Real.log n / r n) := by
    rw [mul_assoc, he]
    exact hIV.1
  have hb : 0 < innerRadius Y n := by
    have hR := CERW.Support.Outer.Radius.gd_maxRadius_nonneg Y n
    have hsq := Real.sqrt_nonneg (d : ℝ)
    have hsub := CERW.Support.Occupation.cellSet_subset_ball (by omega : 1 ≤ d) Y n
    exact (exists_contact_setup_core hd Y n (maxRadius Y n + 2 * Real.sqrt d + 1)
      (by omega) hlegal.1 (by linarith)
      (hsub.trans (Metric.ball_subset_ball (by linarith)))).1
  have hs1 : A * (if d = 2 then Real.sqrt (Real.log n / r n)
      else Real.log n / r n) ≤ 1 := hs.trans (by linarith)
  have hvol := bulk_excess_volume_le (by omega : 1 ≤ d) hrp hb.le hA.le hq hs1
    hin hIV.2
  have hM : (maxLocalTime Y n : ℝ) ≤ K.CCo * r n := by
    simpa only [hrscale] using hE.1.2.2.2.1
  have hap : ∀ z : EuclideanSpace ℝ (Fin d), ‖z‖ ≤ θ * r n →
      |cellLocalTime Y n z - potential d ε (cellSet Y n) z| ≤ K.CLoc *
        (if d = 2 then Real.sqrt (maxLocalTime Y n) * Real.log (n + 2) +
          Real.log (n + 2)
        else Real.sqrt (maxLocalTime Y n * Real.log (n + 2)) + Real.log (n + 2)) := by
    intro z hz
    have h := hE.2.1 z (hz.trans hyn)
    rw [CERW.Support.Inner.normPotential_norm_eq (by omega : 1 ≤ d)] at h
    have hlogs : Real.log n ≤ Real.log (n + 2) :=
      Real.log_le_log (by positivity : (0 : ℝ) < n) (by linarith)
    apply h.trans
    split_ifs with hd2
    · calc
        _ ≤ K.CLoc * Real.log (n + 2) + K.CLoc *
            (Real.sqrt (maxLocalTime Y n) * Real.log (n + 2)) := by gcongr
        _ = _ := by ring
    · calc
        _ ≤ K.CLoc * Real.log (n + 2) + K.CLoc *
            Real.sqrt (maxLocalTime Y n * Real.log (n + 2)) := by gcongr
        _ = _ := by ring
  exact bulk_profile_at_site_from_excess hd hε.le hr1 hθ1 hA.le hV hLoc hCo
    Y n hl1 hlr hlog hb hin hs hvol hM hap y hy

end CERW.LimitShapes
