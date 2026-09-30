import CERW.Support.Contact.ContactLower
import CERW.Model.Occupation
import CERW.Support.Occupation.CellSetVolume

/-!
# The contact inequality

The excess volume `m = |D_n \ B(0, b)|` is controlled by the potential at the contact point. By
the lower bound of `eq:contactbound`, `(2ε/ω_d) 2^{1-d} S^{1-d} m ≤ U(y₀)`. If `ℓ_n(z) = 0` at the
unvisited site `z`, and `ℓ_n(z) = U(z) + ρ - M` (`eq:pointwise`) with `|U(y₀) - U(z)| ≤ Δ`
(`eq:cellmodulus`), then `U(y₀) ≤ |ρ| + |M| + Δ`, so `m ≤ C S^{d-1} (|ρ| + |M| + Δ)`.
-/

namespace CERW.Support.Contact

open MeasureTheory LatticeProb CERW

variable {d : ℕ}

/-- The coefficient of the lower bound in `le_potential_contact` and the coefficient of the
upper bound in `volume_sdiff_le_contact` multiply to one. -/
private theorem coeff_mul_one (d : ℕ) {ε S : ℝ} (hε : 0 < ε) (hS : 0 < S) :
    (unitBallVolume d / (2 * ε) * (2 : ℝ) ^ ((d : ℝ) - 1) * S ^ ((d : ℝ) - 1)) *
      (2 * ε / unitBallVolume d *
        ((2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ)))) = 1 := by
  have hw : unitBallVolume d ≠ 0 := (unitBallVolume_pos d).ne'
  have h2e : 2 * ε ≠ 0 := by positivity
  have hp : (2 : ℝ) ^ ((d : ℝ) - 1) * (2 : ℝ) ^ (1 - (d : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show ((d : ℝ) - 1) + (1 - (d : ℝ)) = 0 by ring, Real.rpow_zero]
  have hs : S ^ ((d : ℝ) - 1) * S ^ (1 - (d : ℝ)) = 1 := by
    rw [← Real.rpow_add hS]
    rw [show ((d : ℝ) - 1) + (1 - (d : ℝ)) = 0 by ring, Real.rpow_zero]
  have hεw : unitBallVolume d / (2 * ε) * (2 * ε / unitBallVolume d) = 1 := by
    rw [div_mul_div_comm, mul_comm (2 * ε) (unitBallVolume d),
      div_self (mul_ne_zero hw h2e)]
  calc
    (unitBallVolume d / (2 * ε) * (2 : ℝ) ^ ((d : ℝ) - 1) * S ^ ((d : ℝ) - 1)) *
        (2 * ε / unitBallVolume d *
          ((2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ))))
        = (unitBallVolume d / (2 * ε) * (2 * ε / unitBallVolume d)) *
            ((2 : ℝ) ^ ((d : ℝ) - 1) * (2 : ℝ) ^ (1 - (d : ℝ))) *
              (S ^ ((d : ℝ) - 1) * S ^ (1 - (d : ℝ))) := by ring
    _ = 1 := by rw [hεw, hp, hs]; ring

/-- The contact inequality: `|D_n \ B(0, b)| ≤ (ω_d/(2ε)) 2^{d-1} S^{d-1} (|ρ| + |M| + Δ)`. -/
theorem volume_sdiff_le_contact (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (X : ℕ → Site d) (n : ℕ)
    {b S Δ ρ M : ℝ} (hb : 0 ≤ b) (hS : 0 < S) (hball : Metric.ball 0 b ⊆ cellSet X n)
    (hDS : cellSet X n ⊆ Metric.closedBall 0 S) {y₀ : EuclideanSpace ℝ (Fin d)}
    (hy₀ : ‖y₀‖ = b) {z : Site d} (hz0 : localTime X n z = 0)
    (hpt : (localTime X n z : ℝ) = potential d ε (cellSet X n) (toSpace z) + ρ - M)
    (hmod : |potential d ε (cellSet X n) y₀ - potential d ε (cellSet X n) (toSpace z)| ≤ Δ) :
    (volume (cellSet X n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal ≤
      unitBallVolume d / (2 * ε) * (2 : ℝ) ^ ((d : ℝ) - 1) * S ^ ((d : ℝ) - 1) *
        (|ρ| + |M| + Δ) := by
  have hDm : MeasurableSet (cellSet X n) :=
    CERW.Support.Occupation.measurableSet_cellSet X n
  have hlow := le_potential_contact (d := d) hd (le_of_lt hε) hDm hb hS hball hDS hy₀
  have hlt0 : (localTime X n z : ℝ) = 0 := by rw [hz0]; norm_num
  have hzpot : potential d ε (cellSet X n) (toSpace z) = M - ρ := by
    rw [hlt0] at hpt
    linarith
  have hpy : potential d ε (cellSet X n) y₀ ≤ |ρ| + |M| + Δ := by
    have h := (abs_le.mp hmod).2
    rw [hzpot] at h
    linarith [le_abs_self M, neg_le_abs ρ]
  have hkm : 2 * ε / unitBallVolume d *
        ((2 : ℝ) ^ (1 - (d : ℝ)) * S ^ (1 - (d : ℝ))) *
        (volume (cellSet X n \ Metric.ball 0 b)).toReal ≤ |ρ| + |M| + Δ :=
    le_trans hlow hpy
  have hDk := coeff_mul_one d hε hS
  have hDnonneg : 0 ≤ unitBallVolume d / (2 * ε) *
      (2 : ℝ) ^ ((d : ℝ) - 1) * S ^ ((d : ℝ) - 1) := by
    refine mul_nonneg (mul_nonneg ?_ ?_) ?_
    · exact div_nonneg (unitBallVolume_pos d).le (by positivity)
    · exact Real.rpow_nonneg (by norm_num) _
    · exact Real.rpow_nonneg hS.le _
  have hstep := mul_le_mul_of_nonneg_left hkm hDnonneg
  rw [← mul_assoc, hDk, one_mul] at hstep
  exact hstep

end CERW.Support.Contact
