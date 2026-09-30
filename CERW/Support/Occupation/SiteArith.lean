import CERW.Support.Occupation.CellVolume
import CERW.Support.Occupation.Facts
import CERW.Generic.Lattice.SummableSums

/-!
# Elementary facts about lattice sites, cells and unit directions

Small identities and inequalities used throughout the Support layer: the embedding `toSpace` of
lattice sites is additive, the lattice norm is subadditive, a unit step changes the squared norm by
`±2x_i + 1`, the Euclidean norm is at most the sum of the coordinate moduli, `unitDir` is a unit
vector in the direction of its argument, and a finite union of cells has volume equal to the number
of its sites.
-/

namespace CERW.Support.Occupation

open MeasureTheory LatticeProb CERW

open scoped ENNReal

variable {d : ℕ}

/-- The square of the Euclidean norm is the sum of the squared coordinates. -/
theorem euclidNorm_sq_eq_sum (x : Site d) :
    euclidNorm x ^ 2 = ∑ i : Fin d, ((x i : ℤ) : ℝ) ^ 2 := by
  rw [euclidNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The origin of the lattice embeds as the origin of Euclidean space. -/
theorem toSpace_zero : toSpace (0 : Site d) = 0 := by
  ext i
  simp [toSpace]

/-- The embedding of lattice sites is additive: `toSpace (x - y) = toSpace x - toSpace y`. -/
theorem toSpace_sub (x y : Site d) : toSpace (x - y) = toSpace x - toSpace y := by
  ext i
  simp [toSpace, Pi.sub_apply, Int.cast_sub]

/-- The Euclidean norm of a lattice difference is at most the sum of the two norms. -/
theorem euclidNorm_sub_le (x y : Site d) :
    euclidNorm (x - y) ≤ euclidNorm x + euclidNorm y := by
  calc euclidNorm (x - y) = euclidNorm (x + -y) := by rw [sub_eq_add_neg]
    _ ≤ euclidNorm x + euclidNorm (-y) := euclidNorm_add_le _ _
    _ = euclidNorm x + euclidNorm y := by rw [CERW.Generic.Lattice.euclidNorm_neg]

/-- Shifting by `+unit i` changes only the `i`-th coordinate by `+1`. -/
theorem euclidNorm_add_unit_sq (x : Site d) (i : Fin d) :
    euclidNorm (x + unit i) ^ 2 = euclidNorm x ^ 2 + 2 * ((x i : ℤ) : ℝ) + 1 := by
  rw [euclidNorm_sq_eq_sum, euclidNorm_sq_eq_sum]
  have hpoint : ∀ j : Fin d,
      (((x + unit i) j : ℤ) : ℝ) ^ 2 =
        (((x j : ℤ) : ℝ)) ^ 2 +
          (if j = i then 2 * ((x i : ℤ) : ℝ) + 1 else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [Pi.add_apply, unit, Pi.single_eq_same]
      simp only [if_true]
      push_cast
      ring
    · rw [Pi.add_apply, unit, Pi.single_eq_of_ne hji, add_zero]
      simp [hji]
  rw [Finset.sum_congr rfl fun j _ => hpoint j, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Shifting by `-unit i` changes only the `i`-th coordinate by `-1`. -/
theorem euclidNorm_sub_unit_sq (x : Site d) (i : Fin d) :
    euclidNorm (x - unit i) ^ 2 = euclidNorm x ^ 2 - 2 * ((x i : ℤ) : ℝ) + 1 := by
  rw [euclidNorm_sq_eq_sum, euclidNorm_sq_eq_sum]
  have hpoint : ∀ j : Fin d,
      (((x - unit i) j : ℤ) : ℝ) ^ 2 =
        (((x j : ℤ) : ℝ)) ^ 2 +
          (if j = i then -2 * ((x i : ℤ) : ℝ) + 1 else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [Pi.sub_apply, unit, Pi.single_eq_same]
      simp only [if_true]
      push_cast
      ring
    · rw [Pi.sub_apply, unit, Pi.single_eq_of_ne hji, sub_zero]
      simp [hji]
  rw [Finset.sum_congr rfl fun j _ => hpoint j, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The Euclidean norm is at most the sum of the absolute values of the coordinates. -/
theorem norm_le_sum_abs (w : EuclideanSpace ℝ (Fin d)) :
    ‖w‖ ≤ ∑ i : Fin d, |w i| := by
  rw [EuclideanSpace.norm_eq]
  have hsq : ∑ i : Fin d, ‖w i‖ ^ 2 ≤ (∑ i : Fin d, |w i|) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |w i|)
        (fun i _ => abs_nonneg _)
  calc Real.sqrt (∑ i : Fin d, ‖w i‖ ^ 2)
      ≤ Real.sqrt ((∑ i : Fin d, |w i|) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i : Fin d, |w i| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

/-- The direction of a nonzero vector has norm one. -/
theorem norm_unitDir_eq_one {x : EuclideanSpace ℝ (Fin d)} (hx : x ≠ 0) :
    ‖unitDir x‖ = 1 := by
  rw [unitDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- The inner product of the direction of `x` with `x` is the norm of `x`. -/
theorem inner_unitDir_self (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (unitDir x) x = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [unitDir, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    field_simp

/-- The projection on a unit vector is at most the Euclidean norm of a site. -/
theorem inner_toSpace_le_euclidNorm {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ = 1)
    (x : Site d) : inner ℝ v (toSpace x) ≤ euclidNorm x := by
  have h := real_inner_le_norm v (toSpace x)
  rwa [hv, one_mul, norm_toSpace] at h

/-- A finite disjoint union of cells has volume equal to the number of its sites. -/
theorem volume_biUnion_cell (S : Finset (Site d)) :
    volume (⋃ x ∈ S, cell x) = (S.card : ℝ≥0∞) := by
  rw [measure_biUnion_finset (fun x _ y _ hxy => cell_disjoint hxy)
        (fun x _ => measurableSet_cell x)]
  simp_rw [volume_cell]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A constant `c` that is a pointwise lower bound on a finite disjoint union of unit cells
is at most the integral of the bounded function over that union. -/
theorem const_mul_card_le_integral_biUnion_cell (S : Finset (Site d))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {c : ℝ}
    (hfint : IntegrableOn f (⋃ x ∈ S, cell x))
    (hbound : ∀ v ∈ (⋃ x ∈ S, cell x), c ≤ f v) :
    c * (S.card : ℝ) ≤ ∫ v in (⋃ x ∈ S, cell x), f v := by
  have hAmeas : MeasurableSet (⋃ x ∈ S, cell x) :=
    Finset.measurableSet_biUnion S fun x _ => measurableSet_cell x
  have hvolA : (volume (⋃ x ∈ S, cell x)).toReal = (S.card : ℝ) := by
    rw [volume_biUnion_cell S, ENNReal.toReal_natCast]
  have hfine : volume (⋃ x ∈ S, cell x) ≠ ∞ := by
    rw [volume_biUnion_cell S]
    exact ENNReal.natCast_ne_top S.card
  have hIntAc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => c)
      (⋃ x ∈ S, cell x) := integrableOn_const hfine
  have hmono : ∫ v in (⋃ x ∈ S, cell x), c ≤ ∫ v in (⋃ x ∈ S, cell x), f v :=
    setIntegral_mono_on hIntAc hfint hAmeas hbound
  have hAc_eq : ∫ v in (⋃ x ∈ S, cell x), c = (S.card : ℝ) * c := by
    rw [setIntegral_const, smul_eq_mul, Measure.real_def, hvolA]
  calc c * (S.card : ℝ) = (S.card : ℝ) * c := by ring
    _ = ∫ v in (⋃ x ∈ S, cell x), c := hAc_eq.symm
    _ ≤ ∫ v in (⋃ x ∈ S, cell x), f v := hmono

end CERW.Support.Occupation
