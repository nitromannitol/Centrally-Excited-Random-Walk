import CERW.Frozen.CellGradient
import CERW.Frozen.NormPotentialGeometry
import CERW.Frozen.NormCoarseBounds
import CERW.Frozen.NormRadialTest
import CERW.Frozen.DriftCrossing

/-!
# Guards for the norm potential, the coarse bounds, the radial test and the crossing lemma

The hypotheses of `lem:cell`, `lem:geometry`, `prop:coarse`, `lem:radial` and `lem:crossing`
can all hold together at concrete parameters. The dimension is `d = 2`, the norm is the
Euclidean norm with the subgradients `x/|x|`, and `ε = 1/4`, which satisfies the ellipticity
condition `ε < 1/d`.
-/

namespace CERW.Support.Guards

open MeasureTheory LatticeProb CERW

/-- The Euclidean norm is a norm. -/
private theorem isNorm_euclidean :
    IsNorm (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) :=
  ⟨norm_add_le, fun t x => by simp only [norm_smul, Real.norm_eq_abs], fun x hx =>
    norm_eq_zero.mp hx⟩

/-- At `ε = 1/4` the Euclidean norm satisfies the ellipticity condition `ε Ψ(e_i) < 1/d`. -/
private theorem euclidean_ellipticity :
    ∀ i : Fin 2, (1 / 4 : ℝ) * ‖(coordVec (d := 2) i)‖ < 1 / ((2 : ℕ) : ℝ) := by
  intro i
  have hcoord : ‖coordVec (d := 2) i‖ = 1 := by
    simp [coordVec]
  rw [hcoord]
  norm_num

/-- A nonzero lattice site embeds to a nonzero vector of `ℝ²`. -/
private theorem toSpace_ne_zero {x : Site 2} (hx : x ≠ 0) :
    toSpace x ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
  intro h
  apply hx
  funext i
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v i) h
  simpa using hi

/-- The direction `v/|v|` is a subgradient of the Euclidean norm at every `v ≠ 0`. -/
private theorem isSubgradient_euclidean {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    IsSubgradient (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖) v (unitDir v) := by
  intro y
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hinner : inner ℝ (unitDir v) (y - v) = ‖v‖⁻¹ * (inner ℝ v y - ‖v‖ ^ 2) := by
    rw [unitDir, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq]
  have hcs : inner ℝ v y ≤ ‖v‖ * ‖y‖ := real_inner_le_norm v y
  have hle : ‖v‖⁻¹ * inner ℝ v y ≤ ‖y‖ := by
    calc ‖v‖⁻¹ * inner ℝ v y ≤ ‖v‖⁻¹ * (‖v‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hpos.le)
      _ = ‖y‖ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have hexp : ‖v‖ + ‖v‖⁻¹ * (inner ℝ v y - ‖v‖ ^ 2) = ‖v‖⁻¹ * inner ℝ v y := by
    field_simp
    ring
  show ‖v‖ + inner ℝ (unitDir v) (y - v) ≤ ‖y‖
  rw [hinner, hexp]
  exact hle

/-- The field `x ↦ x/|x|` is a subgradient selection of the Euclidean norm on `ℤ²`, with value
`0` at the origin. -/
private theorem euclidean_selection :
    (∀ x : Site 2, x ≠ 0 →
      IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (toSpace x)
        (unitDir (toSpace x))) ∧ unitDir (toSpace (0 : Site 2)) = 0 := by
  refine ⟨fun x hx => isSubgradient_euclidean (toSpace_ne_zero hx), ?_⟩
  have h0 : toSpace (0 : Site 2) = 0 := by
    ext i
    simp
  rw [h0]
  exact unitDir_zero

/-- Centrally excited random walk with drift field `x/|x|` and `ε = 1/4` exists in dimension
two: there is a probability space carrying a process with this law. -/
private theorem exists_euclidean_realization :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4) (fun x => unitDir (toSpace x)) X := by
  refine CERW.Support.Drift.exists_isDriftCERW (by norm_num) (by norm_num) (fun z i => ?_)
  have h1 : |unitDir (toSpace z) i| ≤ 1 := by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ i).trans (norm_unitDir_le _)
  calc (1 / 4 : ℝ) * |unitDir (toSpace z) i| ≤ (1 / 4 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 1 / ((2 : ℕ) : ℝ) := by norm_num

/-- For the Euclidean norm on `ℝ²` and the field `x/|x|`, a locally finite distributional
Laplacian exists, so the hypotheses of `lem:cell` are all met. -/
theorem cell_gradient_inhabited :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∃ m : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m ∧
        IsDistribLaplacian (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) m := by
  obtain ⟨h1, h2⟩ := euclidean_selection
  exact ⟨fun x => unitDir (toSpace x), h1, h2,
    CERW.Support.Norm.exists_isDistribLaplacian isNorm_euclidean⟩

/-- `lem:cell` for the Euclidean norm on `ℝ²`: there is `C > 0` such that, for every subgradient
selection and every locally finite distributional Laplacian, the cell integral of
`|∇Ψ - ξ(x)|` is at most `C` times the Laplacian mass of the ball of radius `6√2`. -/
theorem cell_gradient_applies :
    ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 →
          IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (toSpace x) (ξ x)) →
        ξ 0 = 0 →
      ∀ m : Measure (EuclideanSpace ℝ (Fin 2)), IsLocallyFiniteMeasure m →
        IsDistribLaplacian (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) m →
      ∀ x : Site 2,
        ENNReal.ofReal (∫ v in cell x,
            ‖gradient (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖) v - ξ x‖)
          ≤ ENNReal.ofReal C * m (Metric.ball (toSpace x) (6 * Real.sqrt 2)) := by
  obtain ⟨C, hC, h⟩ := CERW.Frozen.cell_gradient (d := 2) (by norm_num)
  exact ⟨C, hC, h (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) isNorm_euclidean⟩

/-- The unit disc is a bounded measurable set of positive area, the domain of the potential in
`lem:geometry`. -/
theorem norm_potential_geometry_inhabited :
    MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      Bornology.IsBounded (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ∧
      0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal :=
  ⟨Metric.isOpen_ball.measurableSet, Metric.isBounded_ball,
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne⟩

/-- `lem:geometry` for the Euclidean norm on `ℝ²`, `ε = 1/4` and the unit disc `D`: there is
`C > 0` such that the potential is bounded by `C ε |D|^{1/d}`, Hölder continuous with the stated
modulus, and its spherical averages equal the exterior integral, which lies between
`2dεc_Ψ F(s)` and `2dεΛ_Ψ F(s)` and equals `2dεF(s)` for the Euclidean norm. -/
theorem norm_potential_geometry_applies :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal
    ∃ C : ℝ, 0 < C ∧
      let D : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 1
      let R : ℝ := (volume D).toReal
      (∀ y, |normPotential 2 (1 / 4) (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) D y|
          ≤ C * (1 / 4) * R ^ ((1 : ℝ) / 2)) ∧
      (∀ y z, |normPotential 2 (1 / 4) (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) D y
            - normPotential 2 (1 / 4) (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) D z|
          ≤ C * (1 / 4) * R ^ ((1 : ℝ) / (2 * 2)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
      (∀ s : ℝ, 0 < s →
        let A : ℝ := (2 * ωd)⁻¹ * ∫ θ,
            normPotential 2 (1 / 4) (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) D
              (s • (θ : EuclideanSpace ℝ (Fin 2)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))).toSphere
        let B : ℝ := 2 * (1 / 4) / ωd *
          ∫ v in D ∩ {v | s < ‖v‖}, (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖) v / ‖v‖ ^ 2
        A = B ∧
          2 * 2 * (1 / 4) * normMin (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) * tail 2 D s ≤ B ∧
          B ≤ 2 * 2 * (1 / 4) * normMax (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) * tail 2 D s ∧
          ((∀ v, (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖) v = ‖v‖) →
            B = 2 * 2 * (1 / 4) * tail 2 D s)) := by
  intro ωd
  obtain ⟨C, hC, h⟩ := CERW.Frozen.norm_potential_geometry (d := 2) (by norm_num)
    (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) isNorm_euclidean
  exact ⟨C, hC, h (1 / 4) (by norm_num) (Metric.ball 0 1) Metric.isOpen_ball.measurableSet
    Metric.isBounded_ball⟩

/-- For the Euclidean norm on `ℝ²` and `ε = 1/4`, the hypotheses of `prop:coarse` can all be met:
there is a subgradient selection with value `0` at the origin, and a probability space carrying
centrally excited random walk with that drift field. -/
theorem norm_coarse_bounds_inhabited :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4) ξ X := by
  obtain ⟨h1, h2⟩ := euclidean_selection
  exact ⟨fun x => unitDir (toSpace x), h1, h2, exists_euclidean_realization⟩

/-- `prop:coarse` for the Euclidean norm on `ℝ²`, `ε = 1/4` and `p = 1`: there are `c, C > 0`
such that, for every subgradient selection and every realization of the walk, with probability
at least `1 - C n⁻¹` the range, the maximal local time and the outer radius are comparable to
`r_n²`, `r_n` and `r_n`. -/
theorem norm_coarse_bounds_applies :
    let r : ℕ → ℝ := fun n =>
      ((2 + 1) * n / (2 * 2 * (1 / 4) *
        normBallVolume (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖))) ^ ((1 : ℝ) / (2 + 1))
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 →
          IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (toSpace x) (ξ x)) →
        ξ 0 = 0 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4) ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ (c * r n ^ 2 ≤ ((departureRange (X · ω) n).card : ℝ) ∧
                  ((departureRange (X · ω) n).card : ℝ) ≤ C * r n ^ 2 ∧
                  c * r n ≤ (maxLocalTime (X · ω) n : ℝ) ∧
                  (maxLocalTime (X · ω) n : ℝ) ≤ C * r n ∧
                  c * r n ≤ maxRadius (X · ω) n ∧ maxRadius (X · ω) n ≤ C * r n)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ))) := by
  intro r
  exact CERW.Frozen.norm_coarse_bounds.{0} (d := 2) (by norm_num)
    (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) isNorm_euclidean (1 / 4) (by norm_num)
    euclidean_ellipticity 1 one_pos

/-- For the Euclidean norm on `ℝ²` and `ε = 1/4`, the hypotheses of `lem:radial` can all be met:
there is a subgradient selection with value `0` at the origin, and a probability space carrying
centrally excited random walk with that drift field. -/
theorem norm_radial_test_inhabited :
    ∃ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
      (∀ x : Site 2, x ≠ 0 →
        IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (toSpace x) (ξ x)) ∧ ξ 0 = 0 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4) ξ X :=
  norm_coarse_bounds_inhabited

/-- `lem:radial` for the Euclidean norm on `ℝ²`, `ε = 1/4` and `p = 1`: there are `ρ₀ > 16` and
`C > 0` such that, for every subgradient selection and every realization of the walk, with
probability at least `1 - C n⁻¹` the radial inequality holds for all integers `ρ₀ ≤ ρ ≤ n`. -/
theorem norm_radial_test_applies :
    ∃ ρ₀ : ℝ, 8 * 2 < ρ₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ξ : Site 2 → EuclideanSpace ℝ (Fin 2),
        (∀ x : Site 2, x ≠ 0 →
          IsSubgradient (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (toSpace x) (ξ x)) →
        ξ 0 = 0 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsDriftCERW μ (1 / 4) ξ X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ ρ : ℕ, ρ₀ ≤ ρ → ρ ≤ n →
            tail 2 (cellSet (X · ω) n) ((ρ : ℝ) + 4 * 2)
              ≤ C * (shellMax (X · ω) n ρ : ℝ)
                  * (tail 2 (cellSet (X · ω) n) ((ρ : ℝ) - 4 * 2)
                    - tail 2 (cellSet (X · ω) n) ((ρ : ℝ) + 4 * 2))
                + C * Real.sqrt
                    (((((departureRange (X · ω) n).filter
                        (fun x => (ρ : ℝ) - 4 * 2 ≤ euclidNorm x)).sup
                        (localTime (X · ω) n) : ℕ) : ℝ)
                      * (ρ : ℝ) ^ (1 - (2 : ℝ))
                      * tail 2 (cellSet (X · ω) n) ((ρ : ℝ) - 4 * 2) * Real.log n)
                + C * (ρ : ℝ) ^ (1 - (2 : ℝ)) * Real.log n}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ))) := by
  obtain ⟨ρ₀, hρ₀, h⟩ := CERW.Frozen.norm_radial_test.{0} (d := 2) (by norm_num)
    (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) isNorm_euclidean
  exact ⟨ρ₀, hρ₀, h (1 / 4) (by norm_num) euclidean_ellipticity 1 one_pos⟩

end CERW.Support.Guards
