import CERW.Support.Statements
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.Cells
import CERW.Support.Occupation.CellVolume
import CERW.Support.Occupation.FreshSum
import CERW.Support.Law.Dynkin
import CERW.Support.Contact.Quadratic
import CERW.Generic.Martingale.Clamp
import CERW.Generic.Kernel.RadialPacking
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Lower bounds on the radii of the range in the plane

Theorem 1.3 (`thm:sharp`), parts (i) and (ii), for `d = 2`.

The inner radius and the outer radius are compared with the moment radius `R_mom` by bounds valid
for every path: `R_in ≤ R_mom + C` and `R_out ≥ R_mom - C`. They follow from
`Σ_{|x| < s} |x| = (2 ω₂/3) s³ + O(s²)`, proved by comparison with unit cells, and from
`s³ - t³ ≥ (s - t) s²`.

Part (i), the polynomial lower bounds, comes from the exponential deviation lemma applied to the
quadratic martingale `𝒬`, truncated while the walk is in `B(0, 2 r_n)`. Its bracket lies between
two positive multiples of `r_n⁵` on the event that the walk stays in that ball and the local times
are at most `8 ε r_n`, which `fluctuation_rates` makes likely. A deviation of `𝒬_n` of order
`r_n^{5/2} (log n)^{1/2}` moves the moment radius by order `(r_n log n)^{1/2}`.

Part (ii) follows from the law of the iterated logarithm for the moment radius and the comparison
of the radii with it. `moment_fluctuations` carries the martingale central limit theorem as a
hypothesis besides the law of the iterated logarithm, so the statement used here is the law of
the iterated logarithm alone, `moment_radius_lil`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower

open CERW.Support.Statements

section LatticeSums

open CERW CERW.Support.Occupation CERW.Generic.Kernel

/-- Every point of a planar cell is within distance `1` of the site of the cell. -/
private lemma norm_sub_toSpace_le_one {x : Site 2} {v : EuclideanSpace ℝ (Fin 2)}
    (hv : v ∈ cell x) : ‖v - toSpace x‖ ≤ 1 := by
  refine (norm_sub_toSpace_le_of_mem_cell hv).trans ?_
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
  rw [this]
  linarith

/-- On the cell of `x`, the norm differs from `|x|` by at most `1`. -/
private lemma abs_norm_sub_euclidNorm_le {x : Site 2} {v : EuclideanSpace ℝ (Fin 2)}
    (hv : v ∈ cell x) : |‖v‖ - euclidNorm x| ≤ 1 := by
  have h1 := norm_sub_toSpace_le_one hv
  have h2 := abs_norm_sub_norm_le v (toSpace x)
  rw [norm_toSpace] at h2
  exact h2.trans h1

/-- The norm is integrable on a closed ball. -/
private lemma integrableOn_norm_closedBall (ρ : ℝ) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (Metric.closedBall 0 ρ) :=
  ContinuousOn.integrableOn_compact (ProperSpace.isCompact_closedBall 0 ρ)
    continuous_norm.continuousOn

/-- A planar cell lies in the closed ball of radius `|x| + 1`. -/
private lemma cell_subset_closedBall_one (x : Site 2) :
    cell x ⊆ Metric.closedBall 0 (euclidNorm x + 1) := by
  intro v hv
  rw [mem_closedBall_zero_iff]
  have := abs_norm_sub_euclidNorm_le hv
  linarith [(abs_le.mp this).2]

/-- The norm is integrable on a planar cell. -/
private lemma integrableOn_norm_cell (x : Site 2) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (cell x) :=
  (integrableOn_norm_closedBall (euclidNorm x + 1)).mono_set (cell_subset_closedBall_one x)

/-- The integral of the norm over the cell of `x` is at most `|x| + 1`. -/
private lemma setIntegral_norm_cell_le (x : Site 2) :
    ∫ v in cell x, ‖v‖ ≤ euclidNorm x + 1 := by
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 2) => euclidNorm x + 1) (cell x) :=
    integrableOn_const (by rw [volume_cell]; exact ENNReal.one_ne_top)
  calc ∫ v in cell x, ‖v‖ ≤ ∫ _ in cell x, (euclidNorm x + 1) :=
        setIntegral_mono_on (integrableOn_norm_cell x) hconst (measurableSet_cell x)
          (fun v hv => by
            have := abs_norm_sub_euclidNorm_le hv
            linarith [(abs_le.mp this).2])
    _ = euclidNorm x + 1 := by
        rw [setIntegral_const]
        simp only [measureReal_def, volume_cell, ENNReal.toReal_one, one_smul]

/-- The integral of the norm over the cell of `x` is at least `|x| - 1`. -/
private lemma le_setIntegral_norm_cell (x : Site 2) :
    euclidNorm x - 1 ≤ ∫ v in cell x, ‖v‖ := by
  have hconst : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 2) => euclidNorm x - 1) (cell x) :=
    integrableOn_const (by rw [volume_cell]; exact ENNReal.one_ne_top)
  calc euclidNorm x - 1 = ∫ _ in cell x, (euclidNorm x - 1) := by
        rw [setIntegral_const]
        simp only [measureReal_def, volume_cell, ENNReal.toReal_one, one_smul]
    _ ≤ ∫ v in cell x, ‖v‖ :=
        setIntegral_mono_on hconst (integrableOn_norm_cell x) (measurableSet_cell x)
          (fun v hv => by
            have := abs_norm_sub_euclidNorm_le hv
            linarith [(abs_le.mp this).1])

/-- The sites of a lattice ball number at most `9 s²` when `s ≥ 1`. -/
private lemma card_ballFinset_le_nine (s : ℝ) (hs : 1 ≤ s) :
    ((LatticeProb.ballFinset 2 s).card : ℝ) ≤ 9 * s ^ 2 := by
  have h := LatticeProb.card_ballFinset_le 2 (by linarith : 0 ≤ s)
  refine h.trans ?_
  nlinarith

/-- The integral of the norm over the union of the cells of `F` is the sum over `F` of the
integrals over the cells. -/
private lemma setIntegral_norm_biUnion_cell (F : Finset (Site 2)) :
    ∫ v in ⋃ x ∈ F, cell x, ‖v‖ = ∑ x ∈ F, ∫ v in cell x, ‖v‖ :=
  integral_biUnion_finset F (fun x _ => measurableSet_cell x)
    (fun _ _ _ _ hxy => cell_disjoint hxy) (fun x _ => integrableOn_norm_cell x)

/-- The norm is integrable on the union of the cells of `F`. -/
private lemma integrableOn_norm_biUnion_cell (F : Finset (Site 2)) :
    IntegrableOn (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) (⋃ x ∈ F, cell x) :=
  (integrableOn_finset_iUnion).mpr fun x _ => integrableOn_norm_cell x

/-- The integral of the norm over the planar ball of radius `ρ ≥ 0`. -/
private lemma integral_norm_ball_two {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) ρ, ‖v‖ =
      2 * unitBallVolume 2 / 3 * ρ ^ 3 := by
  rw [integral_ball_norm (by norm_num) hρ]
  norm_num
  ring

/-- A lower bound for the sum of `|x|` over a lattice ball of radius `s ≥ 1`. -/
private lemma sum_norm_ballFinset_ge (s : ℝ) (hs : 1 ≤ s) :
    2 * unitBallVolume 2 / 3 * s ^ 3 - (2 * unitBallVolume 2 + 9) * s ^ 2 ≤
      ∑ x ∈ LatticeProb.ballFinset 2 s, euclidNorm x := by
  set F := LatticeProb.ballFinset 2 s with hF
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (s - 1) ⊆ ⋃ x ∈ F, cell x := by
    intro v hv
    refine Set.mem_iUnion₂.mpr ⟨cellCenter v, ?_, mem_cell_cellCenter v⟩
    rw [hF, LatticeProb.mem_ballFinset_iff]
    have h1 := abs_norm_sub_euclidNorm_le (mem_cell_cellCenter v)
    have h2 := mem_ball_zero_iff.mp hv
    linarith [(abs_le.mp h1).1]
  have hmono : ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (s - 1), ‖v‖ ≤
      ∫ v in ⋃ x ∈ F, cell x, ‖v‖ :=
    setIntegral_mono_set (integrableOn_norm_biUnion_cell F)
      (Filter.Eventually.of_forall fun v => norm_nonneg v) (Filter.Eventually.of_forall hsub)
  rw [integral_norm_ball_two (by linarith), setIntegral_norm_biUnion_cell] at hmono
  have hsum : (∑ x ∈ F, ∫ v in cell x, ‖v‖) ≤ ∑ x ∈ F, euclidNorm x + (F.card : ℝ) := by
    calc ∑ x ∈ F, ∫ v in cell x, ‖v‖ ≤ ∑ x ∈ F, (euclidNorm x + 1) :=
          Finset.sum_le_sum fun x _ => setIntegral_norm_cell_le x
      _ = ∑ x ∈ F, euclidNorm x + (F.card : ℝ) := by
          rw [Finset.sum_add_distrib]; simp
  have hcard := card_ballFinset_le_nine s hs
  have hω := unitBallVolume_pos 2
  have hcube : s ^ 3 - 3 * s ^ 2 ≤ (s - 1) ^ 3 := by nlinarith
  have h3 : 2 * unitBallVolume 2 / 3 * (s ^ 3 - 3 * s ^ 2) ≤
      2 * unitBallVolume 2 / 3 * (s - 1) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  nlinarith

/-- An upper bound for the sum of `|x|` over a lattice ball of radius `s ≥ 1`. -/
private lemma sum_norm_ballFinset_le (s : ℝ) (hs : 1 ≤ s) :
    ∑ x ∈ LatticeProb.ballFinset 2 s, euclidNorm x ≤
      2 * unitBallVolume 2 / 3 * s ^ 3 + (52 * unitBallVolume 2 / 3 + 9) * s ^ 2 := by
  set F := LatticeProb.ballFinset 2 s with hF
  have hsub : (⋃ x ∈ F, cell x) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (s + 2) := by
    intro v hv
    obtain ⟨x, hx, hvx⟩ := Set.mem_iUnion₂.mp hv
    rw [mem_ball_zero_iff]
    have h1 := abs_norm_sub_euclidNorm_le hvx
    have h2 : euclidNorm x ≤ s := LatticeProb.mem_ballFinset_iff.mp hx
    linarith [(abs_le.mp h1).2]
  have hmono : ∫ v in ⋃ x ∈ F, cell x, ‖v‖ ≤
      ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (s + 2), ‖v‖ :=
    setIntegral_mono_set
      ((integrableOn_norm_closedBall (s + 2)).mono_set Metric.ball_subset_closedBall)
      (Filter.Eventually.of_forall fun v => norm_nonneg v) (Filter.Eventually.of_forall hsub)
  rw [integral_norm_ball_two (by linarith), setIntegral_norm_biUnion_cell] at hmono
  have hsum : ∑ x ∈ F, euclidNorm x ≤ (∑ x ∈ F, ∫ v in cell x, ‖v‖) + (F.card : ℝ) := by
    calc ∑ x ∈ F, euclidNorm x ≤ ∑ x ∈ F, ((∫ v in cell x, ‖v‖) + 1) :=
          Finset.sum_le_sum fun x _ => by linarith [le_setIntegral_norm_cell x]
      _ = (∑ x ∈ F, ∫ v in cell x, ‖v‖) + (F.card : ℝ) := by
          rw [Finset.sum_add_distrib]; simp
  have hcard := card_ballFinset_le_nine s hs
  have hω := unitBallVolume_pos 2
  have hcube : (s + 2) ^ 3 ≤ s ^ 3 + 26 * s ^ 2 := by nlinarith
  have h3 : 2 * unitBallVolume 2 / 3 * (s + 2) ^ 3 ≤
      2 * unitBallVolume 2 / 3 * (s ^ 3 + 26 * s ^ 2) :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  nlinarith

end LatticeSums

section RadiiComparison

open CERW CERW.Support.Occupation

/-- The cube of a real power `x ^ (1/3)`, in the form `((2 : ℕ) + 1)` used by the radii. -/
private lemma rpow_third_pow {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))) ^ 3 = x := by
  have h : (1 : ℝ) / (((2 : ℕ) : ℝ) + 1) = ((3 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [h]
  exact Real.rpow_inv_natCast_pow hx (by norm_num)

/-- The moment radius is nonnegative. -/
private lemma momentRadius_nonneg (Y : ℕ → Site 2) (n : ℕ) : 0 ≤ momentRadius Y n :=
  Real.rpow_nonneg (mul_nonneg (by have := unitBallVolume_pos 2; positivity)
    (Finset.sum_nonneg fun x _ => LatticeProb.euclidNorm_nonneg x)) _

/-- The cube of the moment radius in the plane is `3/(2 ω₂)` times the sum of `|x|` over the
departure range. -/
private lemma momentRadius_pow_three (Y : ℕ → Site 2) (n : ℕ) :
    momentRadius Y n ^ 3 =
      3 / (2 * unitBallVolume 2) * ∑ x ∈ departureRange Y n, euclidNorm x := by
  have hω := unitBallVolume_pos 2
  have hnn : 0 ≤ (((2 : ℕ) : ℝ) + 1) / (((2 : ℕ) : ℝ) * unitBallVolume 2) *
      ∑ x ∈ departureRange Y n, euclidNorm x :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => LatticeProb.euclidNorm_nonneg x)
  rw [momentRadius, rpow_third_pow hnn]
  norm_num

/-- The outer radius is nonnegative. -/
private lemma maxRadius_nonneg (Y : ℕ → Site 2) (n : ℕ) : 0 ≤ maxRadius Y n :=
  (LatticeProb.euclidNorm_nonneg (Y 0)).trans (euclidNorm_le_maxRadius Y (Nat.zero_le n))

/-- A cubic comparison: if `s³ ≤ m³ + K s²`, then `s ≤ m + K`. -/
private lemma le_add_of_cube_le {m s K : ℝ} (hm : 0 ≤ m) (hs : 0 < s) (hK : 0 ≤ K)
    (h : s ^ 3 ≤ m ^ 3 + K * s ^ 2) : s ≤ m + K := by
  by_contra hlt
  rw [not_le] at hlt
  have hms : m < s := by linarith
  have h1 : s ^ 3 - m ^ 3 - (s - m) * s ^ 2 = (s - m) * m * (s + m) := by ring
  have h2 : 0 ≤ (s - m) * m * (s + m) :=
    mul_nonneg (mul_nonneg (by linarith) hm) (by linarith)
  have h3 : K * s ^ 2 < (s - m) * s ^ 2 :=
    mul_lt_mul_of_pos_right (by linarith) (by positivity)
  linarith

/-- A cubic comparison: if `m³ ≤ s³ + K s²`, then `m ≤ s + K`. -/
private lemma le_add_of_cube_le' {m s K : ℝ} (hm : 0 ≤ m) (hs : 0 < s) (hK : 0 ≤ K)
    (h : m ^ 3 ≤ s ^ 3 + K * s ^ 2) : m ≤ s + K := by
  by_contra hlt
  rw [not_le] at hlt
  have hsm : s < m := by linarith
  have h1 : m ^ 3 - s ^ 3 - (m - s) * s ^ 2 = (m - s) * m * (m + s) := by ring
  have h2 : 0 ≤ (m - s) * m * (m + s) :=
    mul_nonneg (mul_nonneg (by linarith) hm) (by linarith)
  have h3 : K * s ^ 2 < (m - s) * s ^ 2 :=
    mul_lt_mul_of_pos_right (by linarith) (by positivity)
  linarith

/-- The moment radius in the plane exceeds the outer radius by at most a constant. -/
private lemma exists_momentRadius_le_maxRadius_add :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℕ → Site 2) (n : ℕ), momentRadius Y n ≤ maxRadius Y n + C := by
  have hω := unitBallVolume_pos 2
  set K : ℝ := 3 / (2 * unitBallVolume 2) * (52 * unitBallVolume 2 / 3 + 9) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨1 + K, by linarith, fun Y n => ?_⟩
  set s : ℝ := max (maxRadius Y n) 1 with hs
  have hs1 : 1 ≤ s := le_max_right _ _
  have hsub : departureRange Y n ⊆ LatticeProb.ballFinset 2 s := by
    intro x hx
    have := departureRange_subset_ballFinset Y n hx
    rw [LatticeProb.mem_ballFinset_iff] at this ⊢
    exact this.trans (le_max_left _ _)
  have hsum : ∑ x ∈ departureRange Y n, euclidNorm x ≤
      ∑ x ∈ LatticeProb.ballFinset 2 s, euclidNorm x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => LatticeProb.euclidNorm_nonneg x
  have hup := sum_norm_ballFinset_le s hs1
  have hcube : momentRadius Y n ^ 3 ≤ s ^ 3 + K * s ^ 2 := by
    rw [momentRadius_pow_three]
    have h0 : 0 < 3 / (2 * unitBallVolume 2) := by positivity
    calc 3 / (2 * unitBallVolume 2) * ∑ x ∈ departureRange Y n, euclidNorm x
        ≤ 3 / (2 * unitBallVolume 2) *
          (2 * unitBallVolume 2 / 3 * s ^ 3 + (52 * unitBallVolume 2 / 3 + 9) * s ^ 2) :=
          mul_le_mul_of_nonneg_left (hsum.trans hup) h0.le
      _ = s ^ 3 + K * s ^ 2 := by rw [hK]; field_simp
  have := le_add_of_cube_le' (momentRadius_nonneg Y n) (by linarith) hK0 hcube
  have hsle : s ≤ maxRadius Y n + 1 := by
    rw [hs]; exact max_le (by linarith) (by linarith [maxRadius_nonneg Y n])
  linarith

/-- Every lattice site of norm below the inner radius lies in the departure range. -/
private lemma mem_departureRange_of_lt_innerRadius (Y : ℕ → Site 2) (n : ℕ) {x : Site 2}
    (hx : euclidNorm x < innerRadius Y n) : x ∈ departureRange Y n := by
  by_contra hxA
  have hmem : toSpace x ∈ (cellSet Y n)ᶜ := fun h => hxA ((toSpace_mem_cellSet_iff Y n x).mp h)
  have hbdd : BddBelow ((fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖) '' (cellSet Y n)ᶜ) :=
    ⟨0, by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg y⟩
  have h : innerRadius Y n ≤ ‖toSpace x‖ := csInf_le hbdd ⟨toSpace x, hmem, rfl⟩
  rw [norm_toSpace] at h
  exact absurd hx (not_lt.mpr h)

/-- The inner radius in the plane exceeds the moment radius by at most a constant. -/
private lemma exists_innerRadius_le_momentRadius_add :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Y : ℕ → Site 2) (n : ℕ), innerRadius Y n ≤ momentRadius Y n + C := by
  have hω := unitBallVolume_pos 2
  set K : ℝ := 3 / (2 * unitBallVolume 2) * (2 * unitBallVolume 2 + 9) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨2 + K, by linarith, fun Y n => ?_⟩
  have hm0 := momentRadius_nonneg Y n
  by_cases hI : innerRadius Y n < 2
  · linarith
  · rw [not_lt] at hI
    set s : ℝ := innerRadius Y n - 1 with hs
    have hs1 : 1 ≤ s := by rw [hs]; linarith
    have hsub : LatticeProb.ballFinset 2 s ⊆ departureRange Y n := by
      intro x hx
      rw [LatticeProb.mem_ballFinset_iff] at hx
      exact mem_departureRange_of_lt_innerRadius Y n (by rw [hs] at hx; linarith)
    have hsum : ∑ x ∈ LatticeProb.ballFinset 2 s, euclidNorm x ≤
        ∑ x ∈ departureRange Y n, euclidNorm x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => LatticeProb.euclidNorm_nonneg x
    have hlow := sum_norm_ballFinset_ge s hs1
    have hcube : s ^ 3 ≤ momentRadius Y n ^ 3 + K * s ^ 2 := by
      rw [momentRadius_pow_three]
      have h0 : 0 < 3 / (2 * unitBallVolume 2) := by positivity
      have h1 : 2 * unitBallVolume 2 / 3 * s ^ 3 - (2 * unitBallVolume 2 + 9) * s ^ 2 ≤
          ∑ x ∈ departureRange Y n, euclidNorm x := hlow.trans hsum
      have h2 := mul_le_mul_of_nonneg_left h1 h0.le
      calc s ^ 3 = 3 / (2 * unitBallVolume 2) * (2 * unitBallVolume 2 / 3 * s ^ 3) := by
            field_simp
        _ ≤ 3 / (2 * unitBallVolume 2) * ∑ x ∈ departureRange Y n, euclidNorm x +
              K * s ^ 2 := by
            rw [hK]
            have : 3 / (2 * unitBallVolume 2) *
                (2 * unitBallVolume 2 / 3 * s ^ 3 - (2 * unitBallVolume 2 + 9) * s ^ 2) =
                s ^ 3 - 3 / (2 * unitBallVolume 2) * (2 * unitBallVolume 2 + 9) * s ^ 2 := by
              field_simp
            nlinarith
    have := le_add_of_cube_le hm0 (by linarith) hK0 hcube
    rw [hs] at this
    linarith

/-- Arithmetic of an upward deviation of the quadratic martingale: the moment radius exceeds `r`
by at least `3 q / (104 ε ω r²)`. -/
private lemma moment_sub_ge {ε ω r m E n y Q q : ℝ} (hε : 0 < ε) (hω : 0 < ω) (hr : 0 < r)
    (hm0 : 0 ≤ m) (hm3 : m ≤ 3 * r) (hmE : m ^ 3 = 3 / (2 * ω) * E)
    (hrn : r ^ 3 = 3 * n / (4 * ε * ω)) (hQ : Q = 2 * ε * E - n + y) (hy : y ≤ 4 * r ^ 2)
    (hq : 8 * r ^ 2 ≤ q) (hQq : q ≤ Q) : 3 * q / (104 * ε * ω * r ^ 2) ≤ m - r := by
  have hD : (m ^ 3 - r ^ 3) * (8 * ε * ω) ≥ 3 * q := by
    have h1 : (m ^ 3 - r ^ 3) * (4 * ε * ω) = 3 * (2 * ε * E - n) := by
      rw [hmE, hrn]
      field_simp
      ring
    nlinarith
  have hmr : r < m := by
    by_contra hle
    rw [not_lt] at hle
    have : m ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hm0 hle 3
    have hpos : 0 < 8 * ε * ω := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr this) hpos.le]
  have hfac : m ^ 3 - r ^ 3 = (m - r) * (m ^ 2 + m * r + r ^ 2) := by ring
  have hb : m ^ 2 + m * r + r ^ 2 ≤ 13 * r ^ 2 := by nlinarith
  have hD2 : m ^ 3 - r ^ 3 ≤ (m - r) * (13 * r ^ 2) := by
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hb (by linarith)
  rw [div_le_iff₀ (by positivity)]
  have hpos : 0 < 8 * ε * ω := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hD2 hpos.le]

/-- Arithmetic of a downward deviation of the quadratic martingale: the moment radius falls short
of `r` by at least `q / (4 ε ω r²)`. -/
private lemma sub_moment_ge {ε ω r m E n y Q q : ℝ} (hε : 0 < ε) (hω : 0 < ω) (hr : 0 < r)
    (hm0 : 0 ≤ m) (hmE : m ^ 3 = 3 / (2 * ω) * E)
    (hrn : r ^ 3 = 3 * n / (4 * ε * ω)) (hQ : Q = 2 * ε * E - n + y) (hy : 0 ≤ y)
    (hq : 0 ≤ q) (hQq : Q ≤ -q) : q / (4 * ε * ω * r ^ 2) ≤ r - m := by
  have hpos : 0 < 4 * ε * ω := by positivity
  have hD : (r ^ 3 - m ^ 3) * (4 * ε * ω) ≥ 3 * q := by
    have h1 : (m ^ 3 - r ^ 3) * (4 * ε * ω) = 3 * (2 * ε * E - n) := by
      rw [hmE, hrn]
      field_simp
      ring
    nlinarith
  have hmr : m ≤ r := by
    by_contra hle
    rw [not_le] at hle
    have : r ^ 3 < m ^ 3 := pow_lt_pow_left₀ hle hr.le (by norm_num)
    nlinarith [mul_pos (sub_pos.mpr this) hpos]
  have hfac : r ^ 3 - m ^ 3 = (r - m) * (r ^ 2 + r * m + m ^ 2) := by ring
  have hb : r ^ 2 + r * m + m ^ 2 ≤ 3 * r ^ 2 := by nlinarith
  have hD2 : r ^ 3 - m ^ 3 ≤ (r - m) * (3 * r ^ 2) := by
    rw [hfac]
    exact mul_le_mul_of_nonneg_left hb (by linarith)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hD2 hpos.le]

end RadiiComparison

section Martingales

open CERW CERW.Support.Law CERW.Support.Occupation CERW.Support.Contact Finset
open LatticeProb (unit walkOp nbrSum)

variable {d : ℕ}

/-- A unit step changes the squared norm by at most `2|x| + 1`. -/
private lemma abs_sq_norm_add_sub_le (x : Site d) {e : Site d} (he : e ∈ unitSteps d) :
    |euclidNorm (x + e) ^ 2 - euclidNorm x ^ 2| ≤ 2 * euclidNorm x + 1 := by
  have hcoord : ∀ i : Fin d, ∀ s : ℝ, |s| = 1 →
      |2 * (s * ((x i : ℤ) : ℝ)) + 1| ≤ 2 * euclidNorm x + 1 := by
    intro i s hs
    have h1 := abs_coord_le_euclidNorm x i
    calc |2 * (s * ((x i : ℤ) : ℝ)) + 1| ≤ |2 * (s * ((x i : ℤ) : ℝ))| + |(1 : ℝ)| :=
          abs_add_le _ _
      _ = 2 * |((x i : ℤ) : ℝ)| + 1 := by rw [abs_mul, abs_mul, hs]; simp
      _ ≤ 2 * euclidNorm x + 1 := by linarith
  obtain ⟨i, rfl | rfl⟩ := mem_unitSteps.mp he
  · have h : euclidNorm (x + unit i) ^ 2 - euclidNorm x ^ 2 =
        2 * (1 * ((x i : ℤ) : ℝ)) + 1 := by
      rw [euclidNorm_add_unit_sq]; ring
    rw [h]
    exact hcoord i 1 (by simp)
  · have h : euclidNorm (x + -unit i) ^ 2 - euclidNorm x ^ 2 =
        2 * ((-1) * ((x i : ℤ) : ℝ)) + 1 := by
      rw [← sub_eq_add_neg, euclidNorm_sub_unit_sq]; ring
    rw [h]
    exact hcoord i (-1) (by simp)

/-- The mean square oscillation of `|·|²` over a step is at most `(2|x| + 1)²`. -/
private lemma sum_stepProb_mul_sq_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (x : ℕ → Site d) (t : ℕ) :
    ∑ e ∈ unitSteps d, stepProb d ε x t e *
        (euclidNorm (x t + e) ^ 2 - euclidNorm (x t) ^ 2) ^ 2 ≤
      (2 * euclidNorm (x t) + 1) ^ 2 := by
  have hp1 : ∑ e ∈ unitSteps d, stepProb d ε x t e = 1 := sum_stepProb hd ε x t
  calc ∑ e ∈ unitSteps d, stepProb d ε x t e *
        (euclidNorm (x t + e) ^ 2 - euclidNorm (x t) ^ 2) ^ 2
      ≤ ∑ e ∈ unitSteps d, stepProb d ε x t e * (2 * euclidNorm (x t) + 1) ^ 2 := by
        refine Finset.sum_le_sum fun e he => ?_
        refine mul_le_mul_of_nonneg_left ?_ (stepProb_nonneg hε hεd x t e)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_sq_norm_add_sub_le (x t) he) 2
    _ = (2 * euclidNorm (x t) + 1) ^ 2 := by rw [← Finset.sum_mul, hp1, one_mul]

/-- At a time that is not a first departure from a nonzero site, the next-step mean of `|·|²` is
`|x|² + 1`. -/
private lemma nextMean_sq_of_srw (hd : 1 ≤ d) (ε : ℝ) (x : ℕ → Site d) (t : ℕ)
    (h : ¬(x t ≠ 0 ∧ x t ∉ (range t).image x)) :
    nextMean ε (fun z : Site d => euclidNorm z ^ 2) x t = euclidNorm (x t) ^ 2 + 1 := by
  have h1 := sum_stepProb_mul ε x t (fun z : Site d => euclidNorm z ^ 2)
  rw [if_neg h, sub_zero] at h1
  exact h1.trans (walkOp_sq_euclidNorm hd (x t))

/-- At a time that is not a first departure from a nonzero site, the mean square of the
increment of `|·|²` about its mean is `4|x|²/d`. -/
private lemma sum_stepProb_mul_sq_of_srw (hd : 1 ≤ d) (ε : ℝ) (x : ℕ → Site d) (t : ℕ)
    (h : ¬(x t ≠ 0 ∧ x t ∉ (range t).image x)) :
    ∑ e ∈ unitSteps d, stepProb d ε x t e *
        (euclidNorm (x t + e) ^ 2 -
          nextMean ε (fun z : Site d => euclidNorm z ^ 2) x t) ^ 2 =
      4 * euclidNorm (x t) ^ 2 / d := by
  rw [nextMean_sq_of_srw hd ε x t h]
  have hsrw : ∀ e, stepProb d ε x t e = srwStep d e := by
    intro e
    rw [stepProb, if_neg h]
  simp_rw [hsrw]
  rw [sum_srwStep_mul (fun z : Site d => (euclidNorm z ^ 2 - (euclidNorm (x t) ^ 2 + 1)) ^ 2)
    (x t), walkOp, nbrSum]
  have hpair : ∀ i : Fin d,
      (euclidNorm (x t + unit i) ^ 2 - (euclidNorm (x t) ^ 2 + 1)) ^ 2 +
        (euclidNorm (x t - unit i) ^ 2 - (euclidNorm (x t) ^ 2 + 1)) ^ 2 =
        8 * ((x t i : ℤ) : ℝ) ^ 2 := by
    intro i
    rw [euclidNorm_add_unit_sq, euclidNorm_sub_unit_sq]
    ring
  simp_rw [hpair]
  rw [← Finset.mul_sum, ← euclidNorm_sq_eq_sum]
  have hd' : (d : ℝ) ≠ 0 := by
    have : 0 < d := Nat.pos_of_ne_zero (by omega)
    exact_mod_cast ne_of_gt this
  field_simp
  ring

/-- The mean square of the next value of `|·|²` about its predicted mean is at most
`(2|x| + 1)²`. -/
private lemma sum_stepProb_mul_sq_nextMean_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) (x : ℕ → Site d) (t : ℕ) :
    ∑ e ∈ unitSteps d, stepProb d ε x t e *
        (euclidNorm (x t + e) ^ 2 -
          nextMean ε (fun z : Site d => euclidNorm z ^ 2) x t) ^ 2 ≤
      (2 * euclidNorm (x t) + 1) ^ 2 := by
  have hvar := sum_mul_sub_mean_sq (unitSteps d) (fun e => stepProb d ε x t e)
    (fun e => euclidNorm (x t + e) ^ 2) (sum_stepProb hd ε x t) (euclidNorm (x t) ^ 2)
  simp only [nextMean]
  rw [hvar]
  linarith [sq_nonneg (∑ j ∈ unitSteps d, stepProb d ε x t j * euclidNorm (x t + j) ^ 2 -
      euclidNorm (x t) ^ 2), sum_stepProb_mul_sq_le hd hε hεd x t]

/-- The mean square of the next value about its predicted mean is nonnegative. -/
private lemma sum_stepProb_mul_sq_nonneg {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (x : ℕ → Site d) (t : ℕ) (a : ℝ) :
    0 ≤ ∑ e ∈ unitSteps d, stepProb d ε x t e * (euclidNorm (x t + e) ^ 2 - a) ^ 2 :=
  Finset.sum_nonneg fun e _ => mul_nonneg (stepProb_nonneg hε hεd x t e) (sq_nonneg _)

section Weighted

variable {Ω : Type*} [MeasurableSpace Ω] {ε : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → Site d}

/-- The weighted increments `Σ_{s<t} ξ(X_s) (D_{s+1} - D_s)` of the Dynkin martingale of `f`,
for a weight `ξ` of sites with values in `[0, R]`, form a martingale. -/
private theorem martingale_weighted (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) (ξ : Site d → ℝ) {R : ℝ} (hξ0 : ∀ z, 0 ≤ ξ z) (hξR : ∀ z, ξ z ≤ R)
    (f : Site d → ℝ) :
    Martingale (fun t ω => ∑ s ∈ range t,
      ξ (X s ω) * (dynkin ε f X (s + 1) ω - dynkin ε f X s ω))
      (pathFiltration hX.measurable) μ := by
  have hD := martingale_dynkin hd hε hεd hX f
  have hadp : StronglyAdapted (pathFiltration hX.measurable) (fun s ω => ξ (X s ω)) :=
    fun s => stronglyMeasurable_comp_pastPath hX.measurable s
      (fun p => ξ (p ⟨s, Finset.mem_Iic.mpr le_rfl⟩))
  have h1 := hD.submartingale.sum_mul_sub hadp (fun n ω => hξR _) (fun n ω => hξ0 _)
  have h2 := (hD.neg.submartingale.sum_mul_sub hadp (fun n ω => hξR _) (fun n ω => hξ0 _)).neg
  have hfun : (fun t ω => ∑ s ∈ range t,
      ξ (X s ω) * (dynkin ε f X (s + 1) ω - dynkin ε f X s ω)) =
      fun n => ∑ k ∈ range n,
        (fun s ω => ξ (X s ω)) k * (dynkin ε f X (k + 1) - dynkin ε f X k) := by
    funext n ω
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
  have hfun2 : (fun t ω => ∑ s ∈ range t,
      ξ (X s ω) * (dynkin ε f X (s + 1) ω - dynkin ε f X s ω)) =
      -fun n => ∑ k ∈ range n, (fun s ω => ξ (X s ω)) k *
        ((-dynkin ε f X) (k + 1) - (-dynkin ε f X) k) := by
    funext n ω
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  refine martingale_iff.mpr ⟨?_, ?_⟩
  · rw [hfun2]; exact h2
  · rw [hfun]; exact h1

/-- The square of an increment of the Dynkin martingale is integrable, and its conditional
expectation is the mean square of the next value about its predicted mean. -/
private theorem condExp_sq_dynkin_succ_sub_eq (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) (hX : IsCERW μ ε X) (f : Site d → ℝ) (t : ℕ) :
    Integrable (fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2) μ ∧
    μ[fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2 |
        pathFiltration hX.measurable t] =ᵐ[μ]
      fun ω => ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e *
        (f (X t ω + e) - nextMean ε f (fun j => X j ω) t) ^ 2 := by
  set h : ((i : Iic t) → Site d) → Site d → ℝ :=
    fun p z => (f z - nextMean ε f (extendPath p) t) ^ 2 with hh
  have hsq : (fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2) =
      fun ω => h (pastPath X t ω) (X (t + 1) ω) := by
    funext ω
    rw [dynkin_succ_sub, nextMean_pastPath]
  have hint := integrable_path_next hd hε hεd hX t h
  rw [hsq]
  refine ⟨hint, ?_⟩
  filter_upwards [condExp_path_next hd hε hεd hX t h hint] with ω hω
  rw [hω]
  simp only [hh, ← nextMean_pastPath]

/-- The conditional second moment of a weighted increment of the Dynkin martingale is the
squared weight times the mean square of the next value about its predicted mean. -/
private theorem condExp_weighted_sq (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) (f : Site d → ℝ) (ξ : Site d → ℝ) {R : ℝ} (hξR : ∀ z, |ξ z| ≤ R)
    (t : ℕ) :
    μ[fun ω => (ξ (X t ω) * (dynkin ε f X (t + 1) ω - dynkin ε f X t ω)) ^ 2 |
        pathFiltration hX.measurable t] =ᵐ[μ]
      fun ω => ξ (X t ω) ^ 2 * ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e *
        (f (X t ω + e) - nextMean ε f (fun j => X j ω) t) ^ 2 := by
  obtain ⟨hint, hce⟩ := condExp_sq_dynkin_succ_sub_eq hd hε hεd hX f t
  have hξm : StronglyMeasurable[pathFiltration hX.measurable t] (fun ω => ξ (X t ω) ^ 2) :=
    stronglyMeasurable_comp_pastPath hX.measurable t
      (fun p => ξ (p ⟨t, Finset.mem_Iic.mpr le_rfl⟩) ^ 2)
  have hmeas : Measurable (fun ω => ξ (X t ω) ^ 2) :=
    ((measurable_of_countable (fun z : Site d => ξ z ^ 2)).comp (hX.measurable t))
  have hfg : Integrable ((fun ω => ξ (X t ω) ^ 2) *
      fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2) μ := by
    refine hint.bdd_mul (c := R ^ 2) hmeas.aestronglyMeasurable (Filter.Eventually.of_forall
      fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ξ (X t ω) ^ 2 = |ξ (X t ω)| ^ 2 := (sq_abs _).symm
      _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hξR _) 2
  have hmul := condExp_mul_of_stronglyMeasurable_left hξm hfg hint
  have hrw : (fun ω => (ξ (X t ω) * (dynkin ε f X (t + 1) ω - dynkin ε f X t ω)) ^ 2) =
      (fun ω => ξ (X t ω) ^ 2) *
        fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2 := by
    funext ω
    simp only [Pi.mul_apply, mul_pow]
  rw [hrw]
  filter_upwards [hmul, hce] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]

omit [MeasurableSpace Ω] in
/-- Two processes that agree almost surely at all times have almost surely equal brackets. -/
private theorem predBracket_congr_ae {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0} {S S' : ℕ → Ω → ℝ} (h : ∀ᵐ ω ∂μ, ∀ t, S t ω = S' t ω) (n : ℕ) :
    predBracket μ ℱ S S n =ᵐ[μ] predBracket μ ℱ S' S' n := by
  have hsq : ∀ t, (fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω)) =ᵐ[μ]
      fun ω => (S' (t + 1) ω - S' t ω) * (S' (t + 1) ω - S' t ω) := fun t =>
    h.mono fun ω hω => by simp only [hω (t + 1), hω t]
  have hall : ∀ᵐ ω ∂μ, ∀ t ∈ range n,
      μ[fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω) | ℱ t] ω =
        μ[fun ω => (S' (t + 1) ω - S' t ω) * (S' (t + 1) ω - S' t ω) | ℱ t] ω :=
    (ae_ball_iff (Finset.countable_toSet _)).mpr fun t _ => condExp_congr_ae (hsq t)
  filter_upwards [hall] with ω hω
  simp only [predBracket, Finset.sum_apply]
  exact Finset.sum_congr rfl hω

/-- The bracket of a scaled weighted increment process is, almost surely, the sum of the squared
scale and weight times the mean square of the next value about its predicted mean. -/
private theorem predBracket_weighted (hd : 1 ≤ d) (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    (hX : IsCERW μ ε X) (f : Site d → ℝ) (ξ : Site d → ℝ) {R : ℝ} (hξR : ∀ z, |ξ z| ≤ R)
    (κ : ℝ) (S : ℕ → Ω → ℝ)
    (hS : ∀ t ω, S (t + 1) ω - S t ω =
      κ * (ξ (X t ω) * (dynkin ε f X (t + 1) ω - dynkin ε f X t ω))) (n : ℕ) :
    predBracket μ (pathFiltration hX.measurable) S S n =ᵐ[μ] fun ω => ∑ t ∈ range n,
      κ ^ 2 * (ξ (X t ω) ^ 2 * ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e *
        (f (X t ω + e) - nextMean ε f (fun j => X j ω) t) ^ 2) := by
  have hone : ∀ t, μ[fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω) |
      pathFiltration hX.measurable t] =ᵐ[μ]
      fun ω => κ ^ 2 * (ξ (X t ω) ^ 2 * ∑ e ∈ unitSteps d,
        stepProb d ε (fun j => X j ω) t e *
          (f (X t ω + e) - nextMean ε f (fun j => X j ω) t) ^ 2) := by
    intro t
    have hfun : (fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω)) =
        κ ^ 2 • fun ω => (ξ (X t ω) * (dynkin ε f X (t + 1) ω - dynkin ε f X t ω)) ^ 2 := by
      funext ω
      simp only [hS, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    refine (condExp_smul (κ ^ 2) _ _).trans ?_
    filter_upwards [condExp_weighted_sq hd hε hεd hX f ξ hξR t] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul, hω]
  have hall : ∀ᵐ ω ∂μ, ∀ t ∈ range n,
      μ[fun ω => (S (t + 1) ω - S t ω) * (S (t + 1) ω - S t ω) |
        pathFiltration hX.measurable t] ω =
        κ ^ 2 * (ξ (X t ω) ^ 2 * ∑ e ∈ unitSteps d, stepProb d ε (fun j => X j ω) t e *
          (f (X t ω + e) - nextMean ε f (fun j => X j ω) t) ^ 2) :=
    (ae_ball_iff (Finset.countable_toSet _)).mpr fun t _ => hone t
  filter_upwards [hall] with ω hω
  simp only [predBracket, Finset.sum_apply]
  exact Finset.sum_congr rfl hω

/-- A martingale of the walk with surely bounded increments that agrees, almost surely up to time
`n`, with the scaled quadratic martingale `κ 𝒬` while the walk stays in `B(0, L)`, and whose
bracket at time `n` is sandwiched there. -/
private theorem exists_truncated_martingale (hd : 1 ≤ d) (hε : 0 ≤ ε)
    (hεd : ε < 1 / (d : ℝ)) (hX : IsCERW μ ε X) {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 < κ) (n : ℕ) :
    ∃ S : ℕ → Ω → ℝ, Martingale S (pathFiltration hX.measurable) μ ∧ (∀ ω, S 0 ω = 0) ∧
      (∀ t ω, |S (t + 1) ω - S t ω| ≤ κ * (2 * (2 * L + 1))) ∧
      (∀ᵐ ω ∂μ, (∀ t < n, euclidNorm (X t ω) ≤ L) →
        S n ω = κ * quadraticMart ε (fun j => X j ω) n) ∧
      (∀ᵐ ω ∂μ, (∀ t < n, euclidNorm (X t ω) ≤ L) →
        predBracket μ (pathFiltration hX.measurable) S S n ω ≤ κ ^ 2 * n * (2 * L + 1) ^ 2) ∧
      (∀ᵐ ω ∂μ, (∀ t < n, euclidNorm (X t ω) ≤ L) →
        κ ^ 2 * (4 / d) * ∑ t ∈ range n,
            (if X t ω ≠ 0 ∧ X t ω ∉ (range t).image (fun i => X i ω) then 0
              else euclidNorm (X t ω) ^ 2) ≤
          predBracket μ (pathFiltration hX.measurable) S S n ω) := by
  classical
  set f : Site d → ℝ := fun z => euclidNorm z ^ 2 with hf
  set ξ : Site d → ℝ := fun z => if euclidNorm z ≤ L then 1 else 0 with hξ
  have hξ0 : ∀ z, 0 ≤ ξ z := fun z => by simp only [hξ]; split_ifs <;> norm_num
  have hξ1 : ∀ z, ξ z ≤ 1 := fun z => by simp only [hξ]; split_ifs <;> norm_num
  have hξabs : ∀ z, |ξ z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (hξ0 z)]; exact hξ1 z
  have hξone : ∀ z, euclidNorm z ≤ L → ξ z = 1 := fun z hz => by simp [hξ, hz]
  set M : ℕ → Ω → ℝ := fun t ω => ∑ s ∈ range t,
    ξ (X s ω) * (dynkin ε f X (s + 1) ω - dynkin ε f X s ω) with hM
  have hMart : Martingale M (pathFiltration hX.measurable) μ :=
    martingale_weighted hd hε hεd hX ξ hξ0 hξ1 f
  set S0 : ℕ → Ω → ℝ := fun t ω => κ * M t ω with hS0
  have hS0mart : Martingale S0 (pathFiltration hX.measurable) μ := hMart.smul κ
  have hincr : ∀ t ω, S0 (t + 1) ω - S0 t ω =
      κ * (ξ (X t ω) * (dynkin ε f X (t + 1) ω - dynkin ε f X t ω)) := by
    intro t ω
    simp only [hS0, hM, Finset.sum_range_succ]
    ring
  have hb : 0 ≤ κ * (2 * (2 * L + 1)) := by positivity
  have hinc_ae : ∀ t, ∀ᵐ ω ∂μ, |S0 (t + 1) ω - S0 t ω| ≤ κ * (2 * (2 * L + 1)) := by
    intro t
    filter_upwards [ae_abs_dynkin_succ_sub_le hd hε hεd hX f] with ω hω
    rw [hincr, abs_mul, abs_mul, abs_of_pos hκ]
    by_cases hx : euclidNorm (X t ω) ≤ L
    · rw [hξone _ hx, abs_one, one_mul]
      have h2 := hω t (2 * euclidNorm (X t ω) + 1)
        (fun e he => abs_sq_norm_add_sub_le (X t ω) he)
      exact mul_le_mul_of_nonneg_left (by linarith) hκ.le
    · have h0 : ξ (X t ω) = 0 := by simp [hξ, hx]
      rw [h0]
      simpa using hb
  obtain ⟨S, hSmart, hSinc, hS00, hSae⟩ := CERW.Generic.Martingale.exists_martingale_clamp
    hS0mart hb hinc_ae
  have hcongr := predBracket_congr_ae (μ := μ) (ℱ := pathFiltration hX.measurable) hSae n
  have hbrack := predBracket_weighted hd hε hεd hX f ξ hξabs κ S0 hincr n
  have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  refine ⟨S, hSmart, fun ω => ?_, hSinc, ?_, ?_, ?_⟩
  · rw [hS00]
    simp [hS0, hM]
  · filter_upwards [hSae, h0] with ω hS hX0 hLt
    rw [hS n]
    have hsum : M n ω = dynkin ε f X n ω := by
      simp only [hM]
      rw [Finset.sum_congr rfl fun s hs => by
        rw [hξone _ (hLt s (Finset.mem_range.mp hs)), one_mul]]
      rw [Finset.sum_range_sub (fun s => dynkin ε f X s ω), dynkin_zero, sub_zero]
    have hq := sq_euclidNorm_eq hd ε X ω hX0 n
    simp only [hS0, hsum, quadraticMart]
    congr 1
    simp only [hf]
    linarith
  · filter_upwards [hcongr, hbrack] with ω h1 h2 hLt
    rw [h1, h2]
    calc ∑ t ∈ range n, κ ^ 2 * (ξ (X t ω) ^ 2 * ∑ e ∈ unitSteps d,
          stepProb d ε (fun j => X j ω) t e *
            (f (X t ω + e) - nextMean ε f (fun j => X j ω) t) ^ 2)
        ≤ ∑ _t ∈ range n, κ ^ 2 * (2 * L + 1) ^ 2 := by
          refine Finset.sum_le_sum fun t ht => ?_
          have hLt' := hLt t (Finset.mem_range.mp ht)
          rw [hξone _ hLt', one_pow, one_mul]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          refine (sum_stepProb_mul_sq_nextMean_le hd hε hεd (fun j => X j ω) t).trans ?_
          exact pow_le_pow_left₀ (by linarith [LatticeProb.euclidNorm_nonneg (X t ω)])
            (by linarith) 2
      _ = κ ^ 2 * n * (2 * L + 1) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  · filter_upwards [hcongr, hbrack] with ω h1 h2 hLt
    rw [h1, h2, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    have hLt' := hLt t (Finset.mem_range.mp ht)
    rw [hξone _ hLt', one_pow, one_mul]
    by_cases hfresh : X t ω ≠ 0 ∧ X t ω ∉ (range t).image (fun i => X i ω)
    · rw [if_pos hfresh]
      have := sum_stepProb_mul_sq_nonneg hε hεd (fun j => X j ω) t
        (nextMean ε f (fun j => X j ω) t)
      simp only [mul_zero]
      exact mul_nonneg (sq_nonneg _) this
    · rw [if_neg hfresh]
      have h4 := sum_stepProb_mul_sq_of_srw hd ε (fun j => X j ω) t hfresh
      simp only [hf]
      rw [h4]
      apply le_of_eq
      ring

end Weighted

end Martingales

section Sums

open CERW CERW.Support.Occupation Finset
open LatticeProb (ballFinset mem_ballFinset_iff)

variable {d : ℕ}

/-- The sum over the times `t < n` of a function of the position is the sum over the departure
range weighted by the local times. -/
private lemma sum_range_eq_sum_localTime (Y : ℕ → Site d) (n : ℕ) (g : Site d → ℝ) :
    ∑ t ∈ range n, g (Y t) = ∑ z ∈ departureRange Y n, (localTime Y n z : ℝ) * g z := by
  classical
  rw [departureRange, Finset.sum_comp]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [localTime, nsmul_eq_mul]

/-- The sum of `|Y_t|²` over the times that are not first departures from nonzero sites is the
sum over the departure range of `(ℓ_n(z) - 1)|z|²`. -/
private lemma sum_srw_times_eq (Y : ℕ → Site d) (n : ℕ) :
    ∑ t ∈ range n, (if Y t ≠ 0 ∧ Y t ∉ (range t).image Y then 0 else euclidNorm (Y t) ^ 2) =
      ∑ z ∈ departureRange Y n, ((localTime Y n z : ℝ) - 1) * euclidNorm z ^ 2 := by
  have h1 := sum_range_eq_sum_localTime Y n (fun z => euclidNorm z ^ 2)
  have h2 := sum_fresh_ne_zero_eq_sum_departureRange Y n (fun z => euclidNorm z ^ 2)
  have h3 : ∑ z ∈ departureRange Y n, (if z ≠ 0 then euclidNorm z ^ 2 else 0) =
      ∑ z ∈ departureRange Y n, euclidNorm z ^ 2 := by
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : z = 0 <;> simp [hz]
  have h4 : ∀ t ∈ range n, (if Y t ≠ 0 ∧ Y t ∉ (range t).image Y then 0 else euclidNorm (Y t) ^ 2) =
      euclidNorm (Y t) ^ 2 - (if Y t ≠ 0 ∧ Y t ∉ (range t).image Y then euclidNorm (Y t) ^ 2
        else 0) := fun t _ => by split_ifs <;> ring
  rw [Finset.sum_congr rfl h4, Finset.sum_sub_distrib, h1, h2, h3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

/-- The sites visited before time `n` lie in the lattice ball of radius `ρ` when the outer radius
is at most `ρ`. -/
private lemma departureRange_subset_ballFinset_of_le (Y : ℕ → Site d) (n : ℕ) {ρ : ℝ}
    (h : maxRadius Y n ≤ ρ) : departureRange Y n ⊆ ballFinset d ρ := by
  intro z hz
  have := departureRange_subset_ballFinset Y n hz
  rw [mem_ballFinset_iff] at this ⊢
  exact this.trans h

/-- If no site carries local time above `Λ` and the outer radius is at most `2r`, the weighted
sum `Σ (ℓ_n(z) - 1)|z|²` over the departure range is at least `θ² r² n / 2 - 4 r² (4r+1)²`,
provided the sites within `θ r` of the origin carry at most half of the time `n`. -/
private lemma lower_sum_localTime {Y : ℕ → Site 2} {n : ℕ} {r θ Λ : ℝ} (hθ : 0 < θ)
    (hr : 0 < r) (hΛ0 : 0 ≤ Λ) (hloc : ∀ z, (localTime Y n z : ℝ) ≤ Λ)
    (hout : maxRadius Y n ≤ 2 * r) (hΛ : Λ * (2 * θ * r + 1) ^ 2 ≤ n / 2) :
    θ ^ 2 * r ^ 2 * (n / 2) - 4 * r ^ 2 * (4 * r + 1) ^ 2 ≤
      ∑ z ∈ departureRange Y n, ((localTime Y n z : ℝ) - 1) * euclidNorm z ^ 2 := by
  classical
  set A := departureRange Y n with hA
  have hsubA : A ⊆ ballFinset 2 (2 * r) := departureRange_subset_ballFinset_of_le Y n hout
  have hAnorm : ∀ z ∈ A, euclidNorm z ≤ 2 * r := fun z hz => mem_ballFinset_iff.mp (hsubA hz)
  have hcardA : (A.card : ℝ) ≤ (4 * r + 1) ^ 2 := by
    have h1 : (A.card : ℝ) ≤ ((ballFinset 2 (2 * r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubA
    have h2 := LatticeProb.card_ballFinset_le 2 (by linarith : 0 ≤ 2 * r)
    refine h1.trans (h2.trans (le_of_eq ?_))
    ring
  -- the upper bound for the sum of squares
  have hsq : ∑ z ∈ A, euclidNorm z ^ 2 ≤ 4 * r ^ 2 * (4 * r + 1) ^ 2 := by
    calc ∑ z ∈ A, euclidNorm z ^ 2 ≤ ∑ _z ∈ A, (2 * r) ^ 2 :=
          Finset.sum_le_sum fun z hz =>
            pow_le_pow_left₀ (LatticeProb.euclidNorm_nonneg z) (hAnorm z hz) 2
      _ = (A.card : ℝ) * (2 * r) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 * r + 1) ^ 2 * (2 * r) ^ 2 :=
          mul_le_mul_of_nonneg_right hcardA (sq_nonneg _)
      _ = 4 * r ^ 2 * (4 * r + 1) ^ 2 := by ring
  -- the time spent near the origin
  set B := A.filter (fun z => ¬ θ * r < euclidNorm z) with hB
  have hBsub : B ⊆ ballFinset 2 (θ * r) := by
    intro z hz
    rw [hB, Finset.mem_filter] at hz
    exact mem_ballFinset_iff.mpr (not_lt.mp hz.2)
  have hcardB : (B.card : ℝ) ≤ (2 * θ * r + 1) ^ 2 := by
    have h1 : (B.card : ℝ) ≤ ((ballFinset 2 (θ * r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hBsub
    have h2 := LatticeProb.card_ballFinset_le 2 (by positivity : 0 ≤ θ * r)
    refine h1.trans (h2.trans (le_of_eq ?_))
    ring
  have hBtime : ∑ z ∈ B, (localTime Y n z : ℝ) ≤ n / 2 := by
    calc ∑ z ∈ B, (localTime Y n z : ℝ) ≤ ∑ _z ∈ B, Λ := Finset.sum_le_sum fun z _ => hloc z
      _ = (B.card : ℝ) * Λ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * θ * r + 1) ^ 2 * Λ := mul_le_mul_of_nonneg_right hcardB hΛ0
      _ ≤ n / 2 := by linarith
  have htotal : ∑ z ∈ A, (localTime Y n z : ℝ) = n := by
    have := sum_localTime_eq Y n
    exact_mod_cast this
  have hsplit := Finset.sum_filter_add_sum_filter_not A (fun z => θ * r < euclidNorm z)
    (fun z => (localTime Y n z : ℝ))
  have hfar : (n : ℝ) / 2 ≤ ∑ z ∈ A.filter (fun z => θ * r < euclidNorm z),
      (localTime Y n z : ℝ) := by
    rw [htotal] at hsplit
    have : ∑ z ∈ A.filter (fun z => ¬ θ * r < euclidNorm z), (localTime Y n z : ℝ) =
        ∑ z ∈ B, (localTime Y n z : ℝ) := rfl
    linarith
  -- the weighted sum
  have hweighted : θ ^ 2 * r ^ 2 * (n / 2) ≤ ∑ z ∈ A, (localTime Y n z : ℝ) * euclidNorm z ^ 2 := by
    calc θ ^ 2 * r ^ 2 * (n / 2)
        ≤ θ ^ 2 * r ^ 2 * ∑ z ∈ A.filter (fun z => θ * r < euclidNorm z),
            (localTime Y n z : ℝ) :=
          mul_le_mul_of_nonneg_left hfar (by positivity)
      _ = ∑ z ∈ A.filter (fun z => θ * r < euclidNorm z),
            (localTime Y n z : ℝ) * (θ * r) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          ring
      _ ≤ ∑ z ∈ A.filter (fun z => θ * r < euclidNorm z),
            (localTime Y n z : ℝ) * euclidNorm z ^ 2 := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [Finset.mem_filter] at hz
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact pow_le_pow_left₀ (by positivity) hz.2.le 2
      _ ≤ ∑ z ∈ A, (localTime Y n z : ℝ) * euclidNorm z ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun z _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hexp : ∑ z ∈ A, ((localTime Y n z : ℝ) - 1) * euclidNorm z ^ 2 =
      ∑ z ∈ A, (localTime Y n z : ℝ) * euclidNorm z ^ 2 - ∑ z ∈ A, euclidNorm z ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hexp]
  linarith

end Sums

section Measurability

open CERW CERW.Support.Law CERW.Support.Occupation Finset

variable {d : ℕ}

/-- The departure range depends only on the positions before time `n`. -/
private lemma departureRange_congr {Y Y' : ℕ → Site d} {n : ℕ} (h : ∀ i < n, Y i = Y' i) :
    departureRange Y n = departureRange Y' n :=
  Finset.image_congr fun i hi => h i (Finset.mem_range.mp hi)

/-- The local time depends only on the positions before time `n`. -/
private lemma localTime_congr {Y Y' : ℕ → Site d} {n : ℕ} (h : ∀ i < n, Y i = Y' i) (z : Site d) :
    localTime Y n z = localTime Y' n z := by
  classical
  unfold localTime
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  rw [h i (Finset.mem_range.mp hi)]

/-- The inner radius depends only on the positions before time `n`. -/
private lemma innerRadius_congr {Y Y' : ℕ → Site d} {n : ℕ} (h : ∀ i < n, Y i = Y' i) :
    innerRadius Y n = innerRadius Y' n := by
  have hc : cellSet Y n = cellSet Y' n := by
    unfold cellSet
    rw [departureRange_congr h]
  unfold innerRadius
  rw [hc]

/-- The outer radius depends only on the positions up to time `n`. -/
private lemma maxRadius_congr {Y Y' : ℕ → Site d} {n : ℕ} (h : ∀ i ≤ n, Y i = Y' i) :
    maxRadius Y n = maxRadius Y' n := by
  unfold maxRadius
  refine Finset.sup'_congr _ rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

/-- A property of the path that depends only on the positions up to time `n` defines a
measurable event. -/
private lemma measurableSet_path {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site d}
    (hX : ∀ n, Measurable (X n)) (n : ℕ) (P : (ℕ → Site d) → Prop)
    (hP : ∀ Y Y' : ℕ → Site d, (∀ i ≤ n, Y i = Y' i) → (P Y ↔ P Y')) :
    MeasurableSet {ω | P (fun j => X j ω)} := by
  have hset : {ω | P (fun j => X j ω)} = pastPath X n ⁻¹' {p | P (extendPath p)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact hP _ _ fun i hi => (extendPath_pastPath X hi ω).symm
  rw [hset]
  exact measurable_pastPath hX n (Set.to_countable _).measurableSet

end Measurability

section Asymptotics

/-- For a sequence `r` with `r_n³ = k n`, every real power of `log n` is eventually below any
positive multiple of any positive power of `r_n`. -/
private lemma eventually_mul_log_rpow_le {k : ℝ} (hk : 0 < k) {r : ℕ → ℝ} (hr0 : ∀ n, 0 ≤ r n)
    (hr : ∀ n : ℕ, r n ^ 3 = k * n) (s A B t : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, A * Real.log n ^ s ≤ B * r n ^ t := by
  have hpow : ∀ n : ℕ, r n ^ t = k ^ (t / 3) * (n : ℝ) ^ (t / 3) := by
    intro n
    have h1 : r n ^ t = ((r n) ^ (3 : ℝ)) ^ (t / 3) := by
      rw [← Real.rpow_mul (hr0 n)]
      congr 1
      ring
    rw [h1, show (r n) ^ (3 : ℝ) = r n ^ 3 by exact_mod_cast Real.rpow_natCast (r n) 3, hr n,
      Real.mul_rpow hk.le (Nat.cast_nonneg n)]
  have hlittle := isLittleO_log_rpow_rpow_atTop s (show 0 < t / 3 by positivity)
  have hcomp : (fun n : ℕ => Real.log (n : ℝ) ^ s) =o[atTop] fun n : ℕ => (n : ℝ) ^ (t / 3) :=
    hlittle.comp_tendsto tendsto_natCast_atTop_atTop
  have hc : 0 < B * k ^ (t / 3) / (A + 1) := by positivity
  filter_upwards [hcomp.def hc, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : 0 ≤ Real.log (n : ℝ) ^ s :=
    Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) s
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn0 _)] at hn
  rw [hpow n]
  have hA1 : 0 < A + 1 := by linarith
  calc A * Real.log (n : ℝ) ^ s ≤ (A + 1) * Real.log (n : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right (by linarith) hlog
    _ ≤ (A + 1) * (B * k ^ (t / 3) / (A + 1) * (n : ℝ) ^ (t / 3)) :=
        mul_le_mul_of_nonneg_left hn hA1.le
    _ = B * (k ^ (t / 3) * (n : ℝ) ^ (t / 3)) := by field_simp

/-- The sequence `r` with `r_n³ = k n` tends to infinity. -/
private lemma eventually_ge_of_cube {k : ℝ} (hk : 0 < k) {r : ℕ → ℝ} (hr0 : ∀ n, 0 ≤ r n)
    (hr : ∀ n : ℕ, r n ^ 3 = k * n) (M : ℝ) : ∀ᶠ n : ℕ in atTop, M ≤ r n := by
  filter_upwards [eventually_ge_atTop ⌈|M| ^ 3 / k⌉₊] with n hn
  have h1 : |M| ^ 3 / k ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have h2 : |M| ^ 3 ≤ r n ^ 3 := by
    rw [hr n]
    calc |M| ^ 3 = (|M| ^ 3 / k) * k := by field_simp
      _ ≤ n * k := mul_le_mul_of_nonneg_right h1 hk.le
      _ = k * n := by ring
  have h3 : |M| ≤ r n := le_of_pow_le_pow_left₀ (by norm_num) (hr0 n) h2
  exact (le_abs_self M).trans h3

/-- `log n` eventually exceeds any bound. -/
private lemma eventually_ge_log (M : ℝ) : ∀ᶠ n : ℕ in atTop, M ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop M

/-- A negative power of `n` is eventually below any positive bound. -/
private lemma eventually_rpow_neg_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-s) ≤ δ := by
  have h := (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
  exact ((tendsto_order.1 h).2 δ hδ).mono fun n hn => hn.le

end Asymptotics

section Bookkeeping

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- If `A ∩ E` lies almost surely in `T`, then `μ A ≤ μ T + μ Eᶜ`, in real numbers. -/
private lemma measureReal_le_of_ae_inter {A E T : Set Ω} (hE : MeasurableSet E)
    (hAT : ∀ᵐ ω ∂μ, ω ∈ A → ω ∈ E → ω ∈ T) : μ.real A ≤ μ.real T + μ.real Eᶜ := by
  have h1 : μ (A ∩ E) ≤ μ T := measure_mono_ae (by
    filter_upwards [hAT] with ω h hω using h hω.1 hω.2)
  have h2 : μ (A \ E) ≤ μ Eᶜ := measure_mono fun ω hω => hω.2
  have h3 : μ A ≤ μ T + μ Eᶜ := by
    rw [← measure_inter_add_sdiff A hE]
    exact add_le_add h1 h2
  have := ENNReal.toReal_mono (by finiteness) h3
  rwa [ENNReal.toReal_add (by finiteness) (by finiteness)] at this

/-- The real measure of a measurable set is at least `1 - α` when its complement has measure at
most `α`. -/
private lemma one_sub_le_measureReal {E : Set Ω} {α : ℝ} (hα : 0 ≤ α) (hE : MeasurableSet E)
    (h : μ Eᶜ ≤ ENNReal.ofReal α) : 1 - α ≤ μ.real E := by
  have h1 : μ.real Eᶜ ≤ α := ENNReal.toReal_le_of_le_ofReal hα h
  rw [probReal_compl_eq_one_sub hE] at h1
  linarith

end Bookkeeping

section Deviation

variable {Ω : Type u} [m0 : MeasurableSpace Ω]

/-- The conclusion of the exponential-deviation lemma for one martingale with bracket between
`c₀` and `C₀`, at time `n`, for the constants `c₁` and `C₁`. -/
private def DeviationBound (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (n : ℕ) (c₀ C₀ c₁ C₁ : ℝ) : Prop :=
  ∀ (b α : ℝ) (S : ℕ → Ω → ℝ) (E : Set Ω), 0 < b → 0 ≤ α → α ≤ 1 →
    Martingale S ℱ μ → (∀ ω, S 0 ω = 0) → (∀ t < n, ∀ ω, |S (t + 1) ω - S t ω| ≤ b) →
    MeasurableSet E → 1 - α ≤ μ.real E →
    (∀ᵐ ω ∂μ, ω ∈ E → c₀ ≤ predBracket μ ℱ S S n ω ∧ predBracket μ ℱ S S n ω ≤ C₀) →
    ∀ β : ℝ, C₁ ≤ β → β * b ≤ c₁ →
      Real.exp (-(C₁ * β ^ 2)) / 4 - α ≤ μ.real {ω | c₁ * β ≤ S n ω} ∧
      Real.exp (-(C₁ * β ^ 2)) / 4 - α ≤ μ.real {ω | S n ω ≤ -(c₁ * β)}

end Deviation

section Core

open CERW CERW.Support.Law CERW.Support.Occupation Finset

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → Site 2}

/-- Lower bounds for the radii at one time `n`, from a deviation of the truncated quadratic
martingale. Suppose the exponential-deviation estimate holds for one martingale, and the event
that the walk stays in `B(0, 2r)` with local times at most `Λ` has probability at least `1 - α`.
Then the outer radius exceeds `r` by at least the first threshold with probability at least
`e^{-C₁ β²}/4 - 2α`, and so does `r` exceed the inner radius by at least the second threshold. -/
private theorem radii_deviation {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    (hX : IsCERW μ ε X) {n : ℕ} {r θ Λ α β κ c₀ C₀ c₁ C₁ CS CI : ℝ}
    (hr : 1 ≤ r) (hrn : r ^ 3 = 3 * n / (4 * ε * unitBallVolume 2))
    (hκ : 0 < κ) (hθ : 0 < θ) (hΛ0 : 0 ≤ Λ) (hΛ : Λ * (2 * θ * r + 1) ^ 2 ≤ n / 2)
    (hc₀ : c₀ ≤ κ ^ 2 * (4 / ((2 : ℕ) : ℝ)) *
      (θ ^ 2 * r ^ 2 * (n / 2) - 4 * r ^ 2 * (4 * r + 1) ^ 2))
    (hC₀ : κ ^ 2 * n * (2 * (2 * r) + 1) ^ 2 ≤ C₀)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hEc : μ {ω | ¬ (maxRadius (fun j => X j ω) n ≤ 2 * r ∧
      ∀ z, (localTime (fun j => X j ω) n z : ℝ) ≤ Λ)} ≤ ENNReal.ofReal α)
    (hβb : β * (κ * (2 * (2 * (2 * r) + 1))) ≤ c₁) (hβ : C₁ ≤ β)
    (hq : 8 * r ^ 2 ≤ c₁ * β / κ) (hCS : CS ≤ r)
    (hCSr : ∀ (Y : ℕ → Site 2) (m : ℕ), momentRadius Y m ≤ maxRadius Y m + CS)
    (hCIr : ∀ (Y : ℕ → Site 2) (m : ℕ), innerRadius Y m ≤ momentRadius Y m + CI)
    (hdev : DeviationBound μ (pathFiltration hX.measurable) n c₀ C₀ c₁ C₁) :
    Real.exp (-(C₁ * β ^ 2)) / 4 - 2 * α ≤ μ.real {ω |
      3 * (c₁ * β / κ) / (104 * ε * unitBallVolume 2 * r ^ 2) - CS ≤
        maxRadius (fun j => X j ω) n - r} ∧
    Real.exp (-(C₁ * β ^ 2)) / 4 - 2 * α ≤ μ.real {ω |
      (c₁ * β / κ) / (4 * ε * unitBallVolume 2 * r ^ 2) - CI ≤
        r - innerRadius (fun j => X j ω) n} := by
  classical
  have hωpos := unitBallVolume_pos 2
  have hr0 : 0 < r := by linarith
  obtain ⟨S, hSmart, hS0, hSinc, hSQ, hSup, hSlow⟩ :=
    exists_truncated_martingale (d := 2) (by norm_num) hε.le hεd hX (L := 2 * r) (κ := κ)
      (by linarith) hκ n
  set Eset : Set Ω := {ω | maxRadius (fun j => X j ω) n ≤ 2 * r ∧
      ∀ z, (localTime (fun j => X j ω) n z : ℝ) ≤ Λ} with hEset
  have hEmeas : MeasurableSet Eset := by
    refine measurableSet_path hX.measurable n (fun Y => maxRadius Y n ≤ 2 * r ∧
      ∀ z, (localTime Y n z : ℝ) ≤ Λ) ?_
    intro Y Y' h
    have h1 := maxRadius_congr h
    have h2 := fun z => localTime_congr (n := n) (fun i hi => h i hi.le) z
    simp only [h1, h2]
  have hEprob : 1 - α ≤ μ.real Eset := one_sub_le_measureReal hα0 hEmeas hEc
  have hEc' : μ.real Esetᶜ ≤ α := by
    rw [probReal_compl_eq_one_sub hEmeas]
    linarith
  have hbr : ∀ᵐ ω ∂μ, ω ∈ Eset → c₀ ≤ predBracket μ (pathFiltration hX.measurable) S S n ω ∧
      predBracket μ (pathFiltration hX.measurable) S S n ω ≤ C₀ := by
    filter_upwards [hSup, hSlow] with ω hup hlow hωE
    have hLt : ∀ t < n, euclidNorm (X t ω) ≤ 2 * r := fun t ht =>
      (euclidNorm_le_maxRadius (fun j => X j ω) ht.le).trans hωE.1
    refine ⟨?_, (hup hLt).trans hC₀⟩
    have h1 := hlow hLt
    have hsum := sum_srw_times_eq (fun j => X j ω) n
    have hbound := lower_sum_localTime (Y := fun j => X j ω) (n := n) (r := r) hθ hr0 hΛ0
      hωE.2 hωE.1 hΛ
    have hpos : 0 ≤ κ ^ 2 * (4 / ((2 : ℕ) : ℝ)) := by positivity
    have hfinal : c₀ ≤ κ ^ 2 * (4 / ((2 : ℕ) : ℝ)) * ∑ t ∈ range n,
        (if X t ω ≠ 0 ∧ X t ω ∉ (range t).image (fun i => X i ω) then 0
          else euclidNorm (X t ω) ^ 2) := by
      rw [hsum]
      exact hc₀.trans (mul_le_mul_of_nonneg_left hbound hpos)
    exact hfinal.trans h1
  have hb : 0 < κ * (2 * (2 * (2 * r) + 1)) := by positivity
  obtain ⟨hA, hA'⟩ := hdev (κ * (2 * (2 * (2 * r) + 1))) α S Eset hb hα0 hα1 hSmart hS0
    (fun t _ ω => hSinc t ω) hEmeas hEprob hbr β hβ hβb
  have hq0 : 0 ≤ c₁ * β / κ := by
    have : 0 ≤ 8 * r ^ 2 := by positivity
    linarith
  refine ⟨?_, ?_⟩
  · have hout : ∀ᵐ ω ∂μ, ω ∈ {ω | c₁ * β ≤ S n ω} → ω ∈ Eset → ω ∈ {ω |
        3 * (c₁ * β / κ) / (104 * ε * unitBallVolume 2 * r ^ 2) - CS ≤
          maxRadius (fun j => X j ω) n - r} := by
      filter_upwards [hSQ] with ω hω hωA hωE
      have hLt : ∀ t < n, euclidNorm (X t ω) ≤ 2 * r := fun t ht =>
        (euclidNorm_le_maxRadius (fun j => X j ω) ht.le).trans hωE.1
      have hSn := hω hLt
      have hQq : c₁ * β / κ ≤ quadraticMart ε (fun j => X j ω) n := by
        rw [div_le_iff₀ hκ]
        have hh : c₁ * β ≤ S n ω := hωA
        rw [hSn] at hh
        linarith
      have hyn : euclidNorm (X n ω) ^ 2 ≤ 4 * r ^ 2 := by
        have h1 := (euclidNorm_le_maxRadius (fun j => X j ω) (le_refl n)).trans hωE.1
        have h2 : euclidNorm (X n ω) ^ 2 ≤ (2 * r) ^ 2 :=
          pow_le_pow_left₀ (LatticeProb.euclidNorm_nonneg _) h1 2
        nlinarith
      have hm := hCSr (fun j => X j ω) n
      have hm3 : momentRadius (fun j => X j ω) n ≤ 3 * r := by linarith [hωE.1]
      have key := moment_sub_ge (ε := ε) (ω := unitBallVolume 2) (r := r)
        (m := momentRadius (fun j => X j ω) n)
        (E := ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (n := (n : ℝ))
        (y := euclidNorm (X n ω) ^ 2) (Q := quadraticMart ε (fun j => X j ω) n)
        (q := c₁ * β / κ) hε hωpos hr0 (momentRadius_nonneg _ n) hm3
        (momentRadius_pow_three _ n) hrn rfl hyn hq hQq
      show _ ≤ _
      linarith
    have h1 := measureReal_le_of_ae_inter hEmeas hout
    linarith [hA]
  · have hin : ∀ᵐ ω ∂μ, ω ∈ {ω | S n ω ≤ -(c₁ * β)} → ω ∈ Eset → ω ∈ {ω |
        (c₁ * β / κ) / (4 * ε * unitBallVolume 2 * r ^ 2) - CI ≤
          r - innerRadius (fun j => X j ω) n} := by
      filter_upwards [hSQ] with ω hω hωA hωE
      have hLt : ∀ t < n, euclidNorm (X t ω) ≤ 2 * r := fun t ht =>
        (euclidNorm_le_maxRadius (fun j => X j ω) ht.le).trans hωE.1
      have hSn := hω hLt
      have hQq : quadraticMart ε (fun j => X j ω) n ≤ -(c₁ * β / κ) := by
        have hh : S n ω ≤ -(c₁ * β) := hωA
        rw [hSn] at hh
        have : κ * quadraticMart ε (fun j => X j ω) n ≤ κ * (-(c₁ * β / κ)) := by
          rw [mul_neg, mul_div_cancel₀ _ hκ.ne']
          exact hh
        exact le_of_mul_le_mul_left this hκ
      have key := sub_moment_ge (ε := ε) (ω := unitBallVolume 2) (r := r)
        (m := momentRadius (fun j => X j ω) n)
        (E := ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x) (n := (n : ℝ))
        (y := euclidNorm (X n ω) ^ 2) (Q := quadraticMart ε (fun j => X j ω) n)
        (q := c₁ * β / κ) hε hωpos hr0 (momentRadius_nonneg _ n)
        (momentRadius_pow_three _ n) hrn rfl (sq_nonneg _) hq0 hQq
      have hi := hCIr (fun j => X j ω) n
      show _ ≤ _
      linarith
    have h1 := measureReal_le_of_ae_inter hEmeas hin
    linarith [hA']

end Core

section Arithmetic

/-- The scale `κ = (√(r⁵))⁻¹` has `κ² r⁵ = 1`. -/
private lemma scale_sq_mul {r : ℝ} (hr : 0 < r) :
    ((Real.sqrt (r ^ 5))⁻¹) ^ 2 * r ^ 5 = 1 := by
  have h : 0 < r ^ 5 := pow_pos hr 5
  rw [inv_pow, Real.sq_sqrt h.le]
  exact inv_mul_cancel₀ h.ne'

/-- `√(r⁵) = r² √r`. -/
private lemma sqrt_pow_five (r : ℝ) : Real.sqrt (r ^ 5) = r ^ 2 * Real.sqrt r := by
  have h : r ^ 5 = (r ^ 2) ^ 2 * r := by ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _)]

/-- The sites within `θ r` of the origin carry at most half of the time, when `θ² = ω/108`,
`n = (4 ε ω / 3) r³`, the local times are at most `8 ε r`, and `θ r ≥ 1`. -/
private lemma local_time_half {ε ω r θ n : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hθ2 : θ ^ 2 = ω / 108) (hθr : 1 ≤ θ * r) (hn : n = 4 * ε * ω / 3 * r ^ 3) :
    8 * ε * r * (2 * θ * r + 1) ^ 2 ≤ n / 2 := by
  have h1 : (2 * θ * r + 1) ^ 2 ≤ 9 * (θ * r) ^ 2 := by nlinarith
  have h2 : 8 * ε * r * (2 * θ * r + 1) ^ 2 ≤ 8 * ε * r * (9 * (θ * r) ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg (by norm_num) hε.le) hr.le)
  have h3 : 8 * ε * r * (9 * (θ * r) ^ 2) = n / 2 := by
    rw [hn, mul_pow, hθ2]
    ring
  linarith

/-- The lower bracket bound: `c₀ ≤ κ² · 2 · (θ² r² n/2 - 4 r² (4r+1)²)`. -/
private lemma bracket_lower {ε ω r θ n κ : ℝ} (hε : 0 < ε) (hω : 0 < ω) (hθ : 0 < θ)
    (hr : 1 ≤ r) (hrθ : 400 / (θ ^ 2 * (4 * ε * ω / 3)) ≤ r)
    (hn : n = 4 * ε * ω / 3 * r ^ 3) (hκ : κ ^ 2 * r ^ 5 = 1) :
    θ ^ 2 * (4 * ε * ω / 3) / 2 ≤
      κ ^ 2 * (4 / ((2 : ℕ) : ℝ)) * (θ ^ 2 * r ^ 2 * (n / 2) - 4 * r ^ 2 * (4 * r + 1) ^ 2) := by
  have hr0 : 0 < r := by linarith
  set k : ℝ := θ ^ 2 * (4 * ε * ω / 3) with hk
  have hkpos : 0 < k := mul_pos (pow_pos hθ 2) (by positivity)
  have h1 : 400 ≤ k * r := by
    rw [div_le_iff₀ hkpos] at hrθ
    linarith
  have h2 : 4 * r ^ 2 * (4 * r + 1) ^ 2 ≤ 100 * r ^ 4 := by
    have hh : (4 * r + 1) ^ 2 ≤ 25 * r ^ 2 := by nlinarith
    calc 4 * r ^ 2 * (4 * r + 1) ^ 2 ≤ 4 * r ^ 2 * (25 * r ^ 2) :=
          mul_le_mul_of_nonneg_left hh (by positivity)
      _ = 100 * r ^ 4 := by ring
  have h3 : 100 * r ^ 4 ≤ k * r ^ 5 / 4 := by
    have : 100 * r ^ 4 = (400 * r ^ 4) / 4 := by ring
    rw [this]
    have : k * r ^ 5 = (k * r) * r ^ 4 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity))
      (by norm_num)
  have h4 : θ ^ 2 * r ^ 2 * (n / 2) = k * r ^ 5 / 2 := by
    rw [hn, hk]; ring
  have h5 : k * r ^ 5 / 4 ≤ θ ^ 2 * r ^ 2 * (n / 2) - 4 * r ^ 2 * (4 * r + 1) ^ 2 := by
    rw [h4]; linarith
  have h6 : (4 / ((2 : ℕ) : ℝ)) = 2 := by norm_num
  rw [h6]
  calc k / 2 = κ ^ 2 * 2 * (k * r ^ 5 / 4) := by
        have : κ ^ 2 * 2 * (k * r ^ 5 / 4) = (κ ^ 2 * r ^ 5) * (k / 2) := by ring
        rw [this, hκ, one_mul]
    _ ≤ κ ^ 2 * 2 * (θ ^ 2 * r ^ 2 * (n / 2) - 4 * r ^ 2 * (4 * r + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)

/-- The upper bracket bound: `κ² n (2 (2 r) + 1)² ≤ 25 · (4 ε ω / 3)`. -/
private lemma bracket_upper {ε ω r n κ : ℝ} (hε : 0 < ε) (hω : 0 < ω) (hr : 1 ≤ r)
    (hn : n = 4 * ε * ω / 3 * r ^ 3) (hκ : κ ^ 2 * r ^ 5 = 1) :
    κ ^ 2 * n * (2 * (2 * r) + 1) ^ 2 ≤ 25 * (4 * ε * ω / 3) := by
  have hr0 : 0 < r := by linarith
  have h1 : (2 * (2 * r) + 1) ^ 2 ≤ 25 * r ^ 2 := by nlinarith
  calc κ ^ 2 * n * (2 * (2 * r) + 1) ^ 2 ≤ κ ^ 2 * n * (25 * r ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by rw [hn]; positivity)
    _ = 25 * (4 * ε * ω / 3) * (κ ^ 2 * r ^ 5) := by rw [hn]; ring
    _ = 25 * (4 * ε * ω / 3) := by rw [hκ, mul_one]

/-- The two thresholds of a deviation of the quadratic martingale are at least
`(3 c₁ a / (104 ε ω) / 2) √(r L)` once `CS` and `CI` are at most that quantity. -/
private lemma thresholds {ε ω c₁ a L r CS CI : ℝ} (hε : 0 < ε) (hω : 0 < ω) (hc₁ : 0 < c₁)
    (ha : 0 < a) (hr : 1 ≤ r)
    (hCS : CS ≤ 3 * c₁ * a / (104 * ε * ω) / 2 * Real.sqrt (r * L))
    (hCI : CI ≤ 3 * c₁ * a / (104 * ε * ω) / 2 * Real.sqrt (r * L)) :
    3 * c₁ * a / (104 * ε * ω) / 2 * Real.sqrt (r * L) ≤
        3 * (c₁ * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹) / (104 * ε * ω * r ^ 2) - CS ∧
      3 * c₁ * a / (104 * ε * ω) / 2 * Real.sqrt (r * L) ≤
        (c₁ * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹) / (4 * ε * ω * r ^ 2) - CI := by
  have hr0 : 0 < r := by linarith
  have hA : c₁ * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹ =
      c₁ * a * Real.sqrt L * (r ^ 2 * Real.sqrt r) := by
    rw [sqrt_pow_five r, div_inv_eq_mul]
    ring
  have hs : Real.sqrt (r * L) = Real.sqrt r * Real.sqrt L := Real.sqrt_mul hr0.le L
  have hsn : 0 ≤ Real.sqrt (r * L) := Real.sqrt_nonneg _
  have e1 : 3 * (c₁ * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹) / (104 * ε * ω * r ^ 2) =
      3 * c₁ * a / (104 * ε * ω) * Real.sqrt (r * L) := by
    rw [hA, hs]
    field_simp
  have e2 : (c₁ * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹) / (4 * ε * ω * r ^ 2) =
      c₁ * a / (4 * ε * ω) * Real.sqrt (r * L) := by
    rw [hA, hs]
    field_simp
  have hcA : 0 ≤ 3 * c₁ * a / (104 * ε * ω) := by positivity
  have hcB : 3 * c₁ * a / (104 * ε * ω) ≤ c₁ * a / (4 * ε * ω) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < c₁ * a * (ε * ω) := by positivity
    nlinarith
  rw [e1, e2]
  refine ⟨by linarith, ?_⟩
  have := mul_le_mul_of_nonneg_right hcB hsn
  linarith

/-- The lower bound for the first-departure scale: `8 r² ≤ c₁ (a √L) √(r⁵)`. -/
private lemma scale_lower {c₁ a L r : ℝ} (hr : 1 ≤ r) (h : 8 ≤ c₁ * a * Real.sqrt L) :
    8 * r ^ 2 ≤ c₁ * (a * Real.sqrt L) / (Real.sqrt (r ^ 5))⁻¹ := by
  have hr0 : 0 < r := by linarith
  rw [div_inv_eq_mul, sqrt_pow_five r]
  have h1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
  have h2 : 0 ≤ r ^ 2 := sq_nonneg r
  calc 8 * r ^ 2 = 8 * (r ^ 2 * 1) := by ring
    _ ≤ (c₁ * a * Real.sqrt L) * (r ^ 2 * Real.sqrt r) :=
        mul_le_mul h (mul_le_mul_of_nonneg_left h1 h2) (by positivity) (by linarith)
    _ = c₁ * (a * Real.sqrt L) * (r ^ 2 * Real.sqrt r) := by ring

/-- The increment bound times `β` is at most `c₁`. -/
private lemma increment_scale {c₁ a L r : ℝ} (hr : 1 ≤ r) (ha : 0 < a)
    (h : 10 * a * Real.sqrt L ≤ c₁ * (r * Real.sqrt r)) :
    a * Real.sqrt L * ((Real.sqrt (r ^ 5))⁻¹ * (2 * (2 * (2 * r) + 1))) ≤ c₁ := by
  have hr0 : 0 < r := by linarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  rw [sqrt_pow_five r]
  have hpos : 0 < r ^ 2 * Real.sqrt r := by positivity
  have hL : 0 ≤ a * Real.sqrt L := mul_nonneg ha.le (Real.sqrt_nonneg _)
  have h1 : a * Real.sqrt L * (2 * (2 * (2 * r) + 1)) ≤ a * Real.sqrt L * (10 * r) :=
    mul_le_mul_of_nonneg_left (by linarith) hL
  have h2 : a * Real.sqrt L * (10 * r) ≤ c₁ * (r ^ 2 * Real.sqrt r) := by
    have := mul_le_mul_of_nonneg_left h hr0.le
    calc a * Real.sqrt L * (10 * r) = r * (10 * a * Real.sqrt L) := by ring
      _ ≤ r * (c₁ * (r * Real.sqrt r)) := this
      _ = c₁ * (r ^ 2 * Real.sqrt r) := by ring
  have : a * Real.sqrt L * ((r ^ 2 * Real.sqrt r)⁻¹ * (2 * (2 * (2 * r) + 1))) =
      a * Real.sqrt L * (2 * (2 * (2 * r) + 1)) / (r ^ 2 * Real.sqrt r) := by
    field_simp
  rw [this, div_le_iff₀ hpos]
  linarith

/-- The exponential lower bound beats the target polynomial bound. -/
private lemma prob_ineq {p C₁ a Cf : ℝ} {n : ℕ} (ha : C₁ * a ^ 2 = p / 2)
    (hCf : 0 < Cf) (hn : 1 ≤ n)
    (hu : (n : ℝ) ^ (-(p / 2)) ≤ 1 / (4 * (1 + 2 * Cf))) :
    (n : ℝ) ^ (-p) ≤
      Real.exp (-(C₁ * (a * Real.sqrt (Real.log n)) ^ 2)) / 4 -
        2 * (Cf * (n : ℝ) ^ (-(p + 1))) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  set u : ℝ := (n : ℝ) ^ (-(p / 2)) with hudef
  have hupos : 0 < u := Real.rpow_pos_of_pos hn0 _
  have hexp : Real.exp (-(C₁ * (a * Real.sqrt (Real.log n)) ^ 2)) = u := by
    rw [hudef, Real.rpow_def_of_pos hn0, mul_pow, Real.sq_sqrt hL]
    congr 1
    have : C₁ * (a ^ 2 * Real.log n) = (C₁ * a ^ 2) * Real.log n := by ring
    rw [this, ha]
    ring
  have hpow : (n : ℝ) ^ (-p) = u ^ 2 := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    ring
  have hpow1 : (n : ℝ) ^ (-(p + 1)) ≤ u ^ 2 := by
    have h1 : (n : ℝ) ^ (-(p + 1)) = (n : ℝ) ^ (-p) * (n : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    have h2 : (n : ℝ) ^ (-1 : ℝ) ≤ 1 := by
      rw [Real.rpow_neg_one]
      exact inv_le_one_of_one_le₀ hn1
    rw [h1, hpow]
    calc u ^ 2 * (n : ℝ) ^ (-1 : ℝ) ≤ u ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg u)
      _ = u ^ 2 := mul_one _
  have hcoef : (1 + 2 * Cf) * u ≤ 1 / 4 := by
    have h4 : 0 < 4 * (1 + 2 * Cf) := by positivity
    have := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 1 + 2 * Cf)
    calc (1 + 2 * Cf) * u ≤ (1 + 2 * Cf) * (1 / (4 * (1 + 2 * Cf))) := this
      _ = 1 / 4 := by field_simp
  rw [hexp, hpow]
  have h5 : u ^ 2 * (1 + 2 * Cf) ≤ u / 4 := by
    calc u ^ 2 * (1 + 2 * Cf) = u * ((1 + 2 * Cf) * u) := by ring
      _ ≤ u * (1 / 4) := mul_le_mul_of_nonneg_left hcoef hupos.le
      _ = u / 4 := by ring
  have h6 : Cf * (n : ℝ) ^ (-(p + 1)) ≤ Cf * u ^ 2 := mul_le_mul_of_nonneg_left hpow1 hCf.le
  nlinarith

end Arithmetic

section Consequences

open CERW CERW.Support.Law CERW.Support.Occupation Finset

/-- The part of `fluctuation_rates` used for the lower bounds: with probability at least
`1 - C n^{-p}`, the outer radius and the local times are within the stated error of their
limits. -/
private theorem fluct_consequence (hfluct : fluctuation_rates.{u}) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε < 1 / ((2 : ℕ) : ℝ)) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, r n = ((((2 : ℕ) : ℝ) + 1) * n /
      (2 * ((2 : ℕ) : ℝ) * ε * unitBallVolume 2)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)))
    {p : ℝ} (hp : 0 < p) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site 2), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
      μ {ω | ¬ (maxRadius (fun j => X j ω) n - r n ≤
          Cf * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) ∧
        ∀ z : Site 2, |(localTime (fun j => X j ω) n z : ℝ) -
          2 * ((2 : ℕ) : ℝ) * ε * max (r n - euclidNorm z) 0| ≤
            Cf * (Real.sqrt (r n) * Real.log n ^ ((3 : ℝ) / 2)))} ≤
        ENNReal.ofReal (Cf * (n : ℝ) ^ (-p)) := by
  obtain ⟨Cf, hCf, hprob, -⟩ := @hfluct 2 (le_refl 2) ε hε hεd p hp
  refine ⟨Cf, hCf, fun {Ω} _ μ _ X hX n hn => ?_⟩
  refine le_trans (measure_mono ?_) (hprob μ X hX n hn)
  intro ω hω hgood
  apply hω
  simp only [if_true] at hgood
  obtain ⟨⟨-, hmax⟩, -, hloc⟩ := hgood
  rw [hr n]
  exact ⟨hmax, hloc⟩

/-- On the fluctuation event, for large `n`, the walk stays in `B(0, 2r)` and the local times are
at most `8 ε r`. -/
private theorem event_of_good {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → Site 2} {ε Cf α r : ℝ} {n : ℕ} (hε : 0 < ε) (hr : 0 < r)
    (hc6 : Cf * Real.log n ^ ((5 : ℝ) / 2) ≤ 1 * r ^ ((1 : ℝ) / 2))
    (hc7 : Cf * Real.log n ^ ((3 : ℝ) / 2) ≤ 4 * ε * r ^ ((1 : ℝ) / 2))
    (hG : μ {ω | ¬ (maxRadius (fun j => X j ω) n - r ≤
          Cf * Real.sqrt r * Real.log n ^ ((5 : ℝ) / 2) ∧
        ∀ z : Site 2, |(localTime (fun j => X j ω) n z : ℝ) -
          2 * ((2 : ℕ) : ℝ) * ε * max (r - euclidNorm z) 0| ≤
            Cf * (Real.sqrt r * Real.log n ^ ((3 : ℝ) / 2)))} ≤ ENNReal.ofReal α) :
    μ {ω | ¬ (maxRadius (fun j => X j ω) n ≤ 2 * r ∧
      ∀ z, (localTime (fun j => X j ω) n z : ℝ) ≤ 8 * ε * r)} ≤ ENNReal.ofReal α := by
  refine le_trans (measure_mono ?_) hG
  intro ω hω hgood
  apply hω
  obtain ⟨hmax, hloc⟩ := hgood
  have hsqrt : Real.sqrt r = r ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hsqsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  refine ⟨?_, fun z => ?_⟩
  · have h1 : Cf * Real.sqrt r * Real.log n ^ ((5 : ℝ) / 2) ≤ r := by
      calc Cf * Real.sqrt r * Real.log n ^ ((5 : ℝ) / 2)
          = Real.sqrt r * (Cf * Real.log n ^ ((5 : ℝ) / 2)) := by ring
        _ ≤ Real.sqrt r * (1 * r ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hc6 (Real.sqrt_nonneg _)
        _ = r := by rw [one_mul, ← hsqrt, hsqsq]
    linarith
  · have hl := abs_le.mp (hloc z)
    have h2 : Cf * (Real.sqrt r * Real.log n ^ ((3 : ℝ) / 2)) ≤ 4 * ε * r := by
      calc Cf * (Real.sqrt r * Real.log n ^ ((3 : ℝ) / 2))
          = Real.sqrt r * (Cf * Real.log n ^ ((3 : ℝ) / 2)) := by ring
        _ ≤ Real.sqrt r * (4 * ε * r ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hc7 (Real.sqrt_nonneg _)
        _ = 4 * ε * (Real.sqrt r * Real.sqrt r) := by rw [← hsqrt]; ring
        _ = 4 * ε * r := by rw [hsqsq]
    have h3 : max (r - euclidNorm z) 0 ≤ r :=
      max_le (by linarith [LatticeProb.euclidNorm_nonneg z]) hr.le
    have h4 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    have h5 : 2 * ((2 : ℕ) : ℝ) * ε * max (r - euclidNorm z) 0 ≤ 2 * ((2 : ℕ) : ℝ) * ε * r := by
      rw [h4]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    rw [h4] at h5 hl
    linarith [hl.2]

/-- The exponential-deviation lemma for one martingale. -/
private theorem deviation_single (hexp : exp_deviation.{u}) {c₀ C₀ : ℝ} (hc₀ : 0 < c₀)
    (hcC : c₀ ≤ C₀) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (n : ℕ), 0 < n →
        DeviationBound μ ℱ n c₀ C₀ c₁ C₁ := by
  obtain ⟨c₁, C₁, hc₁, hC₁, H⟩ := hexp c₀ C₀ hc₀ hcC
  refine ⟨c₁, C₁, hc₁, hC₁, fun {Ω} _ μ _ ℱ n hn b α S E hb hα0 hα1 hmart hS0 hinc hE hEα hbr
    β hβ hβb => ?_⟩
  have h := H μ ℱ 1 n one_pos hn b 0 α hb le_rfl hα0 hα1 (fun _ => S) (fun _ => hmart)
    (fun _ => hS0) (fun _ => hinc) E hE hEα (fun _ => hbr) β hβ hβb
  exact ⟨(h.1 0).1, (h.1 0).2⟩

/-- Two bounds on the probabilities of deviation events give the conclusions of `sharp_radii`
at one `n`. -/
private theorem radii_events {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site 2} (hX : ∀ m, Measurable (X m)) {n : ℕ}
    {r c P T₁ T₂ : ℝ}
    (hP₁ : P ≤ μ.real {ω | T₁ ≤ maxRadius (fun j => X j ω) n - r})
    (hP₂ : P ≤ μ.real {ω | T₂ ≤ r - innerRadius (fun j => X j ω) n})
    (hT₁ : c * Real.sqrt (r * Real.log n) ≤ T₁) (hT₂ : c * Real.sqrt (r * Real.log n) ≤ T₂) :
    MeasurableSet {ω | c * Real.sqrt (r * Real.log n) ≤ r - innerRadius (fun j => X j ω) n} ∧
      ENNReal.ofReal P ≤ μ {ω | c * Real.sqrt (r * Real.log n) ≤
        r - innerRadius (fun j => X j ω) n} ∧
      MeasurableSet {ω | c * Real.sqrt (r * Real.log n) ≤
        maxRadius (fun j => X j ω) n - r} ∧
      ENNReal.ofReal P ≤ μ {ω | c * Real.sqrt (r * Real.log n) ≤
        maxRadius (fun j => X j ω) n - r} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine measurableSet_path hX n (fun Y => c * Real.sqrt (r * Real.log n) ≤
      r - innerRadius Y n) ?_
    intro Y Y' h
    rw [innerRadius_congr (fun i hi => h i hi.le)]
  · refine ENNReal.ofReal_le_of_le_toReal (hP₂.trans ?_)
    exact measureReal_mono (fun ω hω => le_trans hT₂ hω)
  · refine measurableSet_path hX n (fun Y => c * Real.sqrt (r * Real.log n) ≤
      maxRadius Y n - r) ?_
    intro Y Y' h
    rw [maxRadius_congr h]
  · refine ENNReal.ofReal_le_of_le_toReal (hP₁.trans ?_)
    exact measureReal_mono (fun ω hω => le_trans hT₁ hω)

/-- The conclusions of `sharp_radii` at one `n`, from the estimates valid for `n` large. -/
private theorem sharp_radii_at {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site 2} {ε θ c₁ C₁ CS CI Cf a cA p r : ℝ} {n : ℕ}
    (hε : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ)) (hX : IsCERW μ ε X) (hn2 : 2 ≤ n)
    (hr1 : 1 ≤ r) (hrn3 : r ^ 3 = 3 * n / (4 * ε * unitBallVolume 2))
    (hθ : 0 < θ) (hθ2 : θ ^ 2 = unitBallVolume 2 / 108) (hrθ : 1 / θ ≤ r)
    (hr400 : 400 / (θ ^ 2 * (4 * ε * unitBallVolume 2 / 3)) ≤ r) (hCSr' : CS ≤ r)
    (hCS0 : 0 ≤ CS) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hCf : 0 < Cf) (ha : 0 < a)
    (ha2 : C₁ * a ^ 2 = p / 2)
    (hcA : cA = 3 * c₁ * a / (104 * ε * unitBallVolume 2)) (hcApos : 0 < cA)
    (hc6 : Cf * Real.log n ^ ((5 : ℝ) / 2) ≤ 1 * r ^ ((1 : ℝ) / 2))
    (hc7 : Cf * Real.log n ^ ((3 : ℝ) / 2) ≤ 4 * ε * r ^ ((1 : ℝ) / 2))
    (hc8 : (n : ℝ) ^ (-(p + 1)) ≤ 1 / Cf)
    (hc9 : (n : ℝ) ^ (-(p / 2)) ≤ 1 / (4 * (1 + 2 * Cf)))
    (hc10 : (C₁ / a) ^ 2 ≤ Real.log n)
    (hc11 : 10 * a * Real.log n ^ ((1 : ℝ) / 2) ≤ c₁ * r ^ ((3 : ℝ) / 2))
    (hc12 : (8 / (c₁ * a)) ^ 2 ≤ Real.log n) (hc13 : (2 * max CS CI / cA) ^ 2 ≤ Real.log n)
    (hG : μ {ω | ¬ (maxRadius (fun j => X j ω) n - r ≤
          Cf * Real.sqrt r * Real.log n ^ ((5 : ℝ) / 2) ∧
        ∀ z : Site 2, |(localTime (fun j => X j ω) n z : ℝ) -
          2 * ((2 : ℕ) : ℝ) * ε * max (r - euclidNorm z) 0| ≤
            Cf * (Real.sqrt r * Real.log n ^ ((3 : ℝ) / 2)))} ≤
        ENNReal.ofReal (Cf * (n : ℝ) ^ (-(p + 1))))
    (hCSr : ∀ (Y : ℕ → Site 2) (m : ℕ), momentRadius Y m ≤ maxRadius Y m + CS)
    (hCIr : ∀ (Y : ℕ → Site 2) (m : ℕ), innerRadius Y m ≤ momentRadius Y m + CI)
    (hdev : DeviationBound μ (pathFiltration hX.measurable) n
      (θ ^ 2 * (4 * ε * unitBallVolume 2 / 3) / 2)
      (max (θ ^ 2 * (4 * ε * unitBallVolume 2 / 3) / 2) (25 * (4 * ε * unitBallVolume 2 / 3)))
      c₁ C₁) :
    MeasurableSet {ω | cA / 2 * Real.sqrt (r * Real.log n) ≤
        r - innerRadius (fun j => X j ω) n} ∧
      ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ {ω | cA / 2 * Real.sqrt (r * Real.log n) ≤
        r - innerRadius (fun j => X j ω) n} ∧
      MeasurableSet {ω | cA / 2 * Real.sqrt (r * Real.log n) ≤
        maxRadius (fun j => X j ω) n - r} ∧
      ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ {ω | cA / 2 * Real.sqrt (r * Real.log n) ≤
        maxRadius (fun j => X j ω) n - r} := by
  have hω₂ := unitBallVolume_pos 2
  have hr0 : 0 < r := by linarith
  have hn1 : 1 ≤ n := by omega
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hn_eq : (n : ℝ) = 4 * ε * unitBallVolume 2 / 3 * r ^ 3 := by
    rw [hrn3]; field_simp
  have hθr : 1 ≤ θ * r := by
    have := (div_le_iff₀ hθ).mp hrθ
    linarith
  have hκ : 0 < (Real.sqrt (r ^ 5))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (pow_pos hr0 5))
  have hκ2 := scale_sq_mul hr0
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = Cf * (n : ℝ) ^ (-(p + 1)) := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hαdef]; positivity
  have hα1 : α ≤ 1 := by
    rw [hαdef]
    calc Cf * (n : ℝ) ^ (-(p + 1)) ≤ Cf * (1 / Cf) := mul_le_mul_of_nonneg_left hc8 hCf.le
      _ = 1 := by field_simp
  rw [← hαdef] at hG
  have hEc := event_of_good hε hr0 hc6 hc7 hG
  have hcl := bracket_lower hε hω₂ hθ hr1 hr400 hn_eq hκ2
  have hcu := bracket_upper hε hω₂ hr1 hn_eq hκ2
  have hβC : C₁ ≤ a * Real.sqrt (Real.log n) := by
    have h1 : C₁ / a ≤ Real.sqrt (Real.log n) := by
      calc C₁ / a = Real.sqrt ((C₁ / a) ^ 2) := (Real.sqrt_sq (div_nonneg hC₁.le ha.le)).symm
        _ ≤ Real.sqrt (Real.log n) := Real.sqrt_le_sqrt hc10
    have := (div_le_iff₀ ha).mp h1
    linarith
  have hq8 : 8 ≤ c₁ * a * Real.sqrt (Real.log n) := by
    have h1 : 8 / (c₁ * a) ≤ Real.sqrt (Real.log n) := by
      calc 8 / (c₁ * a) = Real.sqrt ((8 / (c₁ * a)) ^ 2) :=
            (Real.sqrt_sq (div_nonneg (by norm_num) (mul_pos hc₁ ha).le)).symm
        _ ≤ Real.sqrt (Real.log n) := Real.sqrt_le_sqrt hc12
    have := (div_le_iff₀ (mul_pos hc₁ ha)).mp h1
    linarith
  have hr32 : r ^ ((3 : ℝ) / 2) = r * Real.sqrt r := by
    have h : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
    rw [h, Real.rpow_add hr0, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hinc : 10 * a * Real.sqrt (Real.log n) ≤ c₁ * (r * Real.sqrt r) := by
    rw [← hr32, Real.sqrt_eq_rpow]
    exact hc11
  have hβb := increment_scale hr1 ha hinc
  have hq := scale_lower hr1 hq8
  have hcore := radii_deviation hε hεd hX hr1 hrn3 hκ hθ
    (mul_nonneg (mul_nonneg (by norm_num) hε.le) hr0.le)
    (local_time_half hε hr0 hθ2 hθr hn_eq) hcl (hcu.trans (le_max_right _ _)) hα0 hα1 hEc hβb
    hβC hq hCSr' hCSr hCIr hdev
  have hpi := prob_ineq ha2 hCf hn1 hc9
  rw [← hαdef] at hpi
  have hM : max CS CI ≤ cA / 2 * Real.sqrt (Real.log n) := by
    have h1 : 2 * max CS CI / cA ≤ Real.sqrt (Real.log n) := by
      calc 2 * max CS CI / cA
          = Real.sqrt ((2 * max CS CI / cA) ^ 2) :=
            (Real.sqrt_sq (div_nonneg (mul_nonneg (by norm_num)
              ((hCS0.trans (le_max_left _ _)))) hcApos.le)).symm
        _ ≤ Real.sqrt (Real.log n) := Real.sqrt_le_sqrt hc13
    have := (div_le_iff₀ hcApos).mp h1
    linarith
  have hsr : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr1
  have hsrL : Real.sqrt (Real.log n) ≤ Real.sqrt (r * Real.log n) := by
    rw [Real.sqrt_mul hr0.le]
    exact le_mul_of_one_le_left (Real.sqrt_nonneg _) hsr
  have hM' : max CS CI ≤ 3 * c₁ * a / (104 * ε * unitBallVolume 2) / 2 *
      Real.sqrt (r * Real.log n) := by
    rw [← hcA]
    calc max CS CI ≤ cA / 2 * Real.sqrt (Real.log n) := hM
      _ ≤ cA / 2 * Real.sqrt (r * Real.log n) :=
          mul_le_mul_of_nonneg_left hsrL (by positivity)
  have hth := thresholds hε hω₂ hc₁ ha hr1 ((le_max_left _ _).trans hM')
    ((le_max_right _ _).trans hM')
  rw [← hcA] at hth
  exact radii_events hX.measurable (hpi.trans hcore.1) (hpi.trans hcore.2) hth.1 hth.2

end Consequences

section Main

open CERW CERW.Support.Law CERW.Support.Occupation Finset

/-- Theorem 1.3(i): polynomial lower bounds for the inner and outer radii in the plane. -/
theorem sharp_radii_of (hfluct : fluctuation_rates.{u})
    (hexp : exp_deviation.{u}) : sharp_radii.{u} := by
  intro d hd
  subst hd
  intro ωd ε hε hεd r p hp
  have hω₂ : 0 < unitBallVolume 2 := unitBallVolume_pos 2
  have hrdef : ∀ n : ℕ, r n = ((((2 : ℕ) : ℝ) + 1) * n /
      (2 * ((2 : ℕ) : ℝ) * ε * unitBallVolume 2)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) :=
    fun n => rfl
  have hr0 : ∀ n : ℕ, 0 ≤ r n := fun n => by
    rw [hrdef n]
    exact Real.rpow_nonneg (by positivity) _
  have hr3 : ∀ n : ℕ, r n ^ 3 = 3 * n / (4 * ε * unitBallVolume 2) := by
    intro n
    have hnn : 0 ≤ (((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε * unitBallVolume 2) := by
      positivity
    rw [hrdef n, rpow_third_pow hnn]
    push_cast
    ring
  obtain ⟨Cf, hCf, hprob⟩ := fluct_consequence hfluct hε hεd r hrdef (by linarith : 0 < p + 1)
  have hκ₃ : 0 < 4 * ε * unitBallVolume 2 / 3 := by positivity
  obtain ⟨θ, hθ, hθ2⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ^ 2 = unitBallVolume 2 / 108 :=
    ⟨Real.sqrt (unitBallVolume 2 / 108), Real.sqrt_pos.mpr (by positivity),
      Real.sq_sqrt (by positivity)⟩
  have hc₀pos : 0 < θ ^ 2 * (4 * ε * unitBallVolume 2 / 3) / 2 := by positivity
  obtain ⟨c₁, C₁, hc₁, hC₁, Hs⟩ := deviation_single hexp hc₀pos
    (le_max_left (θ ^ 2 * (4 * ε * unitBallVolume 2 / 3) / 2) (25 * (4 * ε * unitBallVolume 2 / 3)))
  obtain ⟨CS, hCS0, hCSr⟩ := exists_momentRadius_le_maxRadius_add
  obtain ⟨CI, hCI0, hCIr⟩ := exists_innerRadius_le_momentRadius_add
  obtain ⟨a, ha, ha2⟩ : ∃ a : ℝ, 0 < a ∧ C₁ * a ^ 2 = p / 2 :=
    ⟨Real.sqrt (p / (2 * C₁)), Real.sqrt_pos.mpr (by positivity), by
      rw [Real.sq_sqrt (by positivity)]
      field_simp⟩
  obtain ⟨cA, hcA⟩ : ∃ cA : ℝ, cA = 3 * c₁ * a / (104 * ε * unitBallVolume 2) := ⟨_, rfl⟩
  have hcApos : 0 < cA := by rw [hcA]; positivity
  have hev : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ r n ∧ 1 / θ ≤ r n ∧
      400 / (θ ^ 2 * (4 * ε * unitBallVolume 2 / 3)) ≤ r n ∧ CS ≤ r n ∧
      Cf * Real.log n ^ ((5 : ℝ) / 2) ≤ 1 * r n ^ ((1 : ℝ) / 2) ∧
      Cf * Real.log n ^ ((3 : ℝ) / 2) ≤ 4 * ε * r n ^ ((1 : ℝ) / 2) ∧
      (n : ℝ) ^ (-(p + 1)) ≤ 1 / Cf ∧ (n : ℝ) ^ (-(p / 2)) ≤ 1 / (4 * (1 + 2 * Cf)) ∧
      (C₁ / a) ^ 2 ≤ Real.log n ∧
      10 * a * Real.log n ^ ((1 : ℝ) / 2) ≤ c₁ * r n ^ ((3 : ℝ) / 2) ∧
      (8 / (c₁ * a)) ^ 2 ≤ Real.log n ∧ (2 * max CS CI / cA) ^ 2 ≤ Real.log n := by
    have hk : 0 < 3 / (4 * ε * unitBallVolume 2) := by positivity
    have hr3' : ∀ n : ℕ, r n ^ 3 = 3 / (4 * ε * unitBallVolume 2) * n := fun n => by
      rw [hr3 n]; ring
    filter_upwards [eventually_ge_atTop 2, eventually_ge_of_cube hk hr0 hr3' 1,
      eventually_ge_of_cube hk hr0 hr3' (1 / θ),
      eventually_ge_of_cube hk hr0 hr3' (400 / (θ ^ 2 * (4 * ε * unitBallVolume 2 / 3))),
      eventually_ge_of_cube hk hr0 hr3' CS,
      eventually_mul_log_rpow_le hk hr0 hr3' (5 / 2) Cf 1 (1 / 2) hCf.le one_pos
        (by norm_num),
      eventually_mul_log_rpow_le hk hr0 hr3' (3 / 2) Cf (4 * ε) (1 / 2) hCf.le
        (by positivity) (by norm_num),
      eventually_rpow_neg_le (by linarith : 0 < p + 1) (by positivity : 0 < 1 / Cf),
      eventually_rpow_neg_le (by positivity : 0 < p / 2)
        (by positivity : 0 < 1 / (4 * (1 + 2 * Cf))),
      eventually_ge_log ((C₁ / a) ^ 2),
      eventually_mul_log_rpow_le hk hr0 hr3' (1 / 2) (10 * a) c₁ (3 / 2) (by positivity) hc₁
        (by norm_num),
      eventually_ge_log ((8 / (c₁ * a)) ^ 2),
      eventually_ge_log ((2 * max CS CI / cA) ^ 2)] with n h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
        h13 h14
    exact ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨cA / 2, by positivity, n₀, ?_⟩
  intro Ω _ μ _ X hX n hn
  obtain ⟨hn2, hr1, hrθ, hr400, hCSr', hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13⟩ :=
    hn₀ n hn
  dsimp only
  exact sharp_radii_at hε hεd hX hn2 hr1 (hr3 n) hθ hθ2 hrθ hr400 hCSr' hCS0 hc₁ hC₁ hCf ha ha2
    hcA hcApos hc6 hc7 hc8 hc9 hc10 hc11 hc12 hc13 (hprob μ X hX n hn2) hCSr hCIr
    (Hs μ (pathFiltration hX.measurable) n (by omega))

end Main

section IteratedLogarithm

open CERW CERW.Support.Law CERW.Support.Occupation Finset

/-- The law of the iterated logarithm for the moment radius in the plane, in the form it takes
for the radii: almost surely, for every `δ > 0` and each sign `σ`, the quantity
`σ (R_mom(n) - r_n) / √r_n` exceeds `(√v₂ - δ) √(2 log log n)` infinitely often, where `v₂` is the
limiting variance of the central limit theorem of `moment_fluctuations`. -/
def moment_radius_lil : Prop :=
  ∀ {d : ℕ} (_ : d = 2) (_ : StoutLIL.{u}),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      let v₂ : ℝ := 2 / (ε * d * ωd * (d + 2) * (d + 3))
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        let R : ℕ → Ω → ℝ := fun n ω =>
          (CERW.momentRadius (X · ω) n - r n) / r n ^ ((3 - (d : ℝ)) / 2)
        ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
          ∃ᶠ n : ℕ in atTop,
            (Real.sqrt v₂ - δ) * Real.sqrt (2 * Real.log (Real.log n)) ≤ σ * R n ω

/-- The exponent `(3 - 2)/2` of the normalization of the moment radius in the plane is `1/2`. -/
private lemma rpow_three_sub_two (r : ℝ) :
    r ^ (((3 : ℝ) - ((2 : ℕ) : ℝ)) / 2) = Real.sqrt r := by
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- From a large deviation of the moment radius downward, a large deviation of the inner radius,
for the threshold `(√(2 v₂) - δ) √(r L)`. -/
private lemma inner_of_deviation {r m Rin L v₂ δ C : ℝ} (hr : 0 < r)
    (hH : (Real.sqrt v₂ - δ / (2 * Real.sqrt 2)) * Real.sqrt (2 * L) ≤
      -1 * ((m - r) / r ^ (((3 : ℝ) - ((2 : ℕ) : ℝ)) / 2)))
    (hIn : Rin ≤ m + C) (hC : C ≤ δ / 2 * Real.sqrt (r * L)) :
    (Real.sqrt (2 * v₂) - δ) * Real.sqrt (r * L) ≤ r - Rin := by
  rw [rpow_three_sub_two r] at hH
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 := mul_le_mul_of_nonneg_right hH hs.le
  have e1 : -1 * ((m - r) / Real.sqrt r) * Real.sqrt r = r - m := by
    field_simp
    ring
  have e2 : Real.sqrt (2 * L) * Real.sqrt r = Real.sqrt 2 * Real.sqrt (r * L) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul hr.le]
    ring
  have e3 : Real.sqrt (2 * v₂) = Real.sqrt 2 * Real.sqrt v₂ :=
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) v₂
  rw [e1] at h1
  have e4 : (Real.sqrt v₂ - δ / (2 * Real.sqrt 2)) * Real.sqrt (2 * L) * Real.sqrt r =
      (Real.sqrt (2 * v₂) - δ / 2) * Real.sqrt (r * L) := by
    rw [mul_assoc, e2, e3]
    field_simp
  rw [e4] at h1
  nlinarith

/-- From a large deviation of the moment radius upward, a large deviation of the outer radius,
for the threshold `(√(2 v₂) - δ) √(r L)`. -/
private lemma outer_of_deviation {r m Rout L v₂ δ C : ℝ} (hr : 0 < r)
    (hH : (Real.sqrt v₂ - δ / (2 * Real.sqrt 2)) * Real.sqrt (2 * L) ≤
      1 * ((m - r) / r ^ (((3 : ℝ) - ((2 : ℕ) : ℝ)) / 2)))
    (hOut : m ≤ Rout + C) (hC : C ≤ δ / 2 * Real.sqrt (r * L)) :
    (Real.sqrt (2 * v₂) - δ) * Real.sqrt (r * L) ≤ Rout - r := by
  rw [rpow_three_sub_two r] at hH
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 := mul_le_mul_of_nonneg_right hH hs.le
  have e1 : 1 * ((m - r) / Real.sqrt r) * Real.sqrt r = m - r := by
    field_simp
  have e2 : Real.sqrt (2 * L) * Real.sqrt r = Real.sqrt 2 * Real.sqrt (r * L) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul hr.le]
    ring
  have e3 : Real.sqrt (2 * v₂) = Real.sqrt 2 * Real.sqrt v₂ :=
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) v₂
  rw [e1] at h1
  have e4 : (Real.sqrt v₂ - δ / (2 * Real.sqrt 2)) * Real.sqrt (2 * L) * Real.sqrt r =
      (Real.sqrt (2 * v₂) - δ / 2) * Real.sqrt (r * L) := by
    rw [mul_assoc, e2, e3]
    field_simp
  rw [e4] at h1
  nlinarith

/-- If `r ≥ 1` and `(2 C / δ)² ≤ L`, then `C ≤ (δ/2) √(r L)`. -/
private lemma error_le_sqrt {r L C δ : ℝ} (hr : 1 ≤ r) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hL : (2 * C / δ) ^ 2 ≤ L) : C ≤ δ / 2 * Real.sqrt (r * L) := by
  have hr0 : 0 < r := by linarith
  have h1 : 2 * C / δ ≤ Real.sqrt L := by
    calc 2 * C / δ = Real.sqrt ((2 * C / δ) ^ 2) :=
          (Real.sqrt_sq (div_nonneg (by linarith) hδ.le)).symm
      _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
  have h2 := (div_le_iff₀ hδ).mp h1
  have h3 : Real.sqrt L ≤ Real.sqrt (r * L) := by
    rw [Real.sqrt_mul hr0.le]
    exact le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr hr)
  nlinarith [Real.sqrt_nonneg L]

/-- Monotonicity of `A ↦ (2 A / δ)²` on the nonnegative reals. -/
private lemma sq_div_le_of_le {A B δ : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hδ : 0 < δ) :
    (2 * A / δ) ^ 2 ≤ (2 * B / δ) ^ 2 :=
  pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (by linarith) hδ.le) 2

/-- Theorem 1.3(ii): the iterated logarithm law for the radii in the plane follows from the
iterated logarithm law for the moment radius and the comparison of the radii with it. -/
theorem sharp_radii_lil_of_moment_lil (hlil : moment_radius_lil.{u}) :
    sharp_radii_lil.{u} := by
  intro d hd hStout
  subst hd
  intro ωd ε hε hεd r Ω _ μ _ X hX
  have h := @hlil 2 rfl hStout ε hε hεd Ω _ μ _ X hX
  simp only [] at h
  have hω₂ : 0 < unitBallVolume 2 := unitBallVolume_pos 2
  have hrdef : ∀ n : ℕ, r n = ((((2 : ℕ) : ℝ) + 1) * n /
      (2 * ((2 : ℕ) : ℝ) * ε * unitBallVolume 2)) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) :=
    fun n => rfl
  have hr0 : ∀ n : ℕ, 0 ≤ r n := fun n => by
    rw [hrdef n]
    exact Real.rpow_nonneg (by positivity) _
  have hr3 : ∀ n : ℕ, r n ^ 3 = 3 / (4 * ε * unitBallVolume 2) * n := by
    intro n
    have hnn : 0 ≤ (((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε * unitBallVolume 2) := by
      positivity
    rw [hrdef n, rpow_third_pow hnn]
    push_cast
    ring
  have hπ : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal = Real.pi := by
    rw [EuclideanSpace.volume_ball_fin_two]
    simp [Real.pi_nonneg]
  have hcI : Real.sqrt (2 * (2 / (ε * ((2 : ℕ) : ℝ) *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal *
      (((2 : ℕ) : ℝ) + 2) * (((2 : ℕ) : ℝ) + 3)))) = 1 / Real.sqrt (10 * Real.pi * ε) := by
    rw [hπ, one_div, ← Real.sqrt_inv]
    congr 1
    push_cast
    field_simp
    ring
  obtain ⟨CS, hCS0, hCSr⟩ := exists_momentRadius_le_maxRadius_add
  obtain ⟨CI, hCI0, hCIr⟩ := exists_innerRadius_le_momentRadius_add
  filter_upwards [h] with ω hω
  intro δ hδ
  have hδ1 : 0 < δ / (2 * Real.sqrt 2) := by positivity
  have hk : 0 < 3 / (4 * ε * unitBallVolume 2) := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ r n ∧ (2 * max CS CI / δ) ^ 2 ≤ Real.log (Real.log n) := by
    filter_upwards [eventually_ge_of_cube hk hr0 hr3 1,
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)).eventually_ge_atTop ((2 * max CS CI / δ) ^ 2)] with n h1 h2
    exact ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · refine ((hω _ hδ1 (-1) (Or.inr rfl)).and_eventually hev).mono fun n ⟨hn, hr1, hL⟩ => ?_
    have hrpos : 0 < r n := by linarith
    have hC : CI ≤ δ / 2 * Real.sqrt (r n * Real.log (Real.log n)) :=
      error_le_sqrt hr1 hδ hCI0 ((sq_div_le_of_le hCI0 (le_max_right CS CI) hδ).trans hL)
    have key := inner_of_deviation hrpos hn (hCIr (fun x => X x ω) n) hC
    rw [hcI] at key
    exact key
  · refine ((hω _ hδ1 1 (Or.inl rfl)).and_eventually hev).mono fun n ⟨hn, hr1, hL⟩ => ?_
    have hrpos : 0 < r n := by linarith
    have hC : CS ≤ δ / 2 * Real.sqrt (r n * Real.log (Real.log n)) :=
      error_le_sqrt hr1 hδ hCS0 ((sq_div_le_of_le hCS0 (le_max_left CS CI) hδ).trans hL)
    have key := outer_of_deviation hrpos hn (hCSr (fun x => X x ω) n) hC
    rw [hcI] at key
    exact key

/-- The iterated logarithm law for the moment radius, extracted from `moment_fluctuations` once
the martingale central limit theorem is available. -/
theorem moment_radius_lil_of (hclt : MartingaleCLT.{u}) (hmom : moment_fluctuations.{u}) :
    moment_radius_lil.{u} := by
  intro d hd hStout
  subst hd
  intro ωd ε hε hεd r v₂ Ω _ μ _ X hX R
  have h := @hmom 2 (le_refl 2) hclt hStout ε hε hεd Ω _ μ _ X hX
  simp only [] at h
  exact h.2.2.mono fun ω hω δ hδ σ hσ => (hω δ hδ σ hσ).2.2.2

/-- Theorem 1.3(ii), from `moment_fluctuations` and the martingale central limit theorem. -/
theorem sharp_radii_lil_of_clt (hclt : MartingaleCLT.{u}) (hmom : moment_fluctuations.{u}) :
    sharp_radii_lil.{u} :=
  sharp_radii_lil_of_moment_lil (moment_radius_lil_of hclt hmom)

end IteratedLogarithm

end CERW.Support.Lower
