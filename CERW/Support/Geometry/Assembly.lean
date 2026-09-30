import CERW.Support.Geometry.Holder
import CERW.Support.Geometry.Newton

/-!
# The geometry of the inward-drift potential

`lem:geometry`, assembled: the sup bound `eq:potential-bound`, the Hölder modulus `eq:holder`,
Newton's spherical average `eq:newton`, and the ball potential `eq:ballpotential`, with one
constant `C_d` for the first two.
-/

namespace CERW.Support.Geometry

open MeasureTheory CERW

variable {d : ℕ}

/-- `lem:geometry`: there is `C_d > 0` such that for every `ε > 0` and every bounded measurable
`D` of volume `R`, `‖U_D‖_∞ ≤ C_d ε R^{1/d}`, `|U_D(y) - U_D(z)| ≤ C_d ε R^{1/(2d)} |y - z|^{1/2}`,
and the spherical mean of `U_D` at every radius `s > 0` is `2dε F(s)`. Moreover
`U_{B(0,b)}(y) = 2dε (b - |y|)_+` for every `b > 0`. -/
theorem potential_geometry (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ ε : ℝ, 0 < ε →
      (∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
        let R : ℝ := (volume D).toReal
        (∀ y, |CERW.potential d ε D y| ≤ Cd * ε * R ^ ((1 : ℝ) / d)) ∧
        (∀ y z, |CERW.potential d ε D y - CERW.potential d ε D z|
            ≤ Cd * ε * R ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
        (∀ s : ℝ, 0 < s →
          (d * ωd)⁻¹ * ∫ θ, CERW.potential d ε D (s • (θ : EuclideanSpace ℝ (Fin d)))
              ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere
            = 2 * d * ε * CERW.tail d D s)) ∧
      ∀ b : ℝ, 0 < b → ∀ y : EuclideanSpace ℝ (Fin d),
        CERW.potential d ε (Metric.ball 0 b) y = 2 * d * ε * max (b - ‖y‖) 0 := by
  intro ωd
  obtain ⟨CH, hCH0, hCH⟩ := exists_potential_holder (d := d) hd
  set CB : ℝ := 2 * d * unitBallVolume d ^ (-(1 : ℝ) / d) with hCB
  have hCB0 : 0 ≤ CB := by
    have := unitBallVolume_pos d
    positivity
  refine ⟨CB + CH + 1, by linarith, fun ε hε => ⟨fun D hD hDb => ?_, fun b hb y =>
    potential_ball hd ε hb y⟩⟩
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hR0 : 0 ≤ (volume D).toReal := ENNReal.toReal_nonneg
  refine ⟨fun y => ?_, fun y z => ?_, fun s hs => sphere_average_potential hd ε hD hDb hs⟩
  · calc |potential d ε D y|
        ≤ 2 * d * ε * unitBallVolume d ^ (-(1 : ℝ) / d) * (volume D).toReal ^ ((1 : ℝ) / d) :=
          abs_potential_le (by omega) hε.le hD hDfin y
      _ = CB * ε * (volume D).toReal ^ ((1 : ℝ) / d) := by rw [hCB]; ring
      _ ≤ (CB + CH + 1) * ε * (volume D).toReal ^ ((1 : ℝ) / d) := by
          have := Real.rpow_nonneg hR0 ((1 : ℝ) / d)
          gcongr
          linarith
  · calc |potential d ε D y - potential d ε D z|
        ≤ CH * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2) :=
          hCH ε hε.le D hD hDfin y z
      _ ≤ (CB + CH + 1) * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) *
            ‖y - z‖ ^ ((1 : ℝ) / 2) := by
          have h1 := Real.rpow_nonneg hR0 ((1 : ℝ) / (2 * d))
          have h2 := Real.rpow_nonneg (norm_nonneg (y - z)) ((1 : ℝ) / 2)
          gcongr
          linarith

end CERW.Support.Geometry
