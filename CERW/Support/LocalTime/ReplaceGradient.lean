import CERW.Support.Law.StepMean
import CERW.Generic.Kernel.NewtonField
import CERW.Generic.Lattice.Centered
import CERW.Model.Potential
import CERW.Support.Occupation.SiteArith

/-!
# Replacing the lattice gradient by the Newtonian field

The first replacement in the proof of `eq:approx`: summed over a finite set of sites within
distance `R'` of `y`, the errors `|Db(x - y) - (2/ω_d) K(x - y)|` total `O(log(R' + 2))`. Beyond a
fixed radius `R`, the gradient asymptotics `eq:gradient` give `O(|x - y|^{-d})`. The finitely many
nearer sites contribute `O(1)` by the one-step bound. Both are `O((1 + |x - y|)^{-d})`, and the
centred sum of `(1 + |x - y|)^{-d}` is logarithmic.
-/

namespace CERW.Support.LocalTime

open LatticeProb CERW CERW.Support.Law CERW.Generic.Kernel
open CERW.Support.Occupation

variable {d : ℕ}

/-- A Euclidean norm of a lattice site is either zero or at least one. -/
private lemma euclidNorm_eq_zero_or_one_le (z : Site d) :
    euclidNorm z = 0 ∨ 1 ≤ euclidNorm z := by
  by_cases hz : z = 0
  · exact Or.inl (by simp [hz])
  · refine Or.inr ?_
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    have hz1 : (1 : ℤ) ≤ |z i| := by
      have hpos : 0 < |z i| := abs_pos.mpr hi
      omega
    have hcast : (1 : ℝ) ≤ |((z i : ℤ) : ℝ)| := by exact_mod_cast hz1
    exact hcast.trans (abs_coord_le_euclidNorm z i)

/-- The Newtonian field of an embedded site is the scaled embedding. -/
private lemma smul_newtonField_toSpace (z : Site d) :
    (2 / unitBallVolume d) • newtonField (toSpace z)
      = (2 / unitBallVolume d / euclidNorm z ^ d) • toSpace z := by
  simp only [newtonField, norm_toSpace, smul_smul, div_eq_mul_inv]

/-- The central difference under the one-step bound obeys the same power law. -/
private lemma norm_centralDiff_le {b : Site d → ℝ} {Cg : ℝ}
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (z : Site d) :
    ‖centralDiff b z‖ ≤ (d : ℝ) * max Cg 0 * (1 + euclidNorm z) ^ (1 - (d : ℝ)) := by
  set A : ℝ := (1 + euclidNorm z) ^ (1 - (d : ℝ))
  have hAnonneg : 0 ≤ A := Real.rpow_nonneg (by linarith [euclidNorm_nonneg z]) _
  have hcoord : ∀ i : Fin d, |(centralDiff b z) i| ≤ max Cg 0 * A := by
    intro i
    have hm1 : unit i ∈ unitSteps d := mem_unitSteps.mpr ⟨i, Or.inl rfl⟩
    have hm2 : -unit i ∈ unitSteps d := mem_unitSteps.mpr ⟨i, Or.inr rfl⟩
    have h1 : |b (z + unit i) - b z| ≤ max Cg 0 * A :=
      (hgrad z (unit i) hm1).trans (mul_le_mul_of_nonneg_right (le_max_left Cg 0) hAnonneg)
    have h2 : |b (z - unit i) - b z| ≤ max Cg 0 * A := by
      have h := (hgrad z (-unit i) hm2).trans
        (mul_le_mul_of_nonneg_right (le_max_left Cg 0) hAnonneg)
      rw [sub_eq_add_neg]
      exact h
    have h3 : |b (z + unit i) - b (z - unit i)| ≤ 2 * (max Cg 0 * A) := by
      calc |b (z + unit i) - b (z - unit i)|
          = |(b (z + unit i) - b z) + (b z - b (z - unit i))| := by
              congr 1
              ring
        _ ≤ |b (z + unit i) - b z| + |b z - b (z - unit i)| := abs_add_le _ _
        _ = |b (z + unit i) - b z| + |b (z - unit i) - b z| := by
              rw [abs_sub_comm (b z) (b (z - unit i))]
        _ ≤ max Cg 0 * A + max Cg 0 * A := add_le_add h1 h2
        _ = 2 * (max Cg 0 * A) := by ring
    have h4 : |(b (z + unit i) - b (z - unit i)) / 2| ≤ max Cg 0 * A := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    simpa only [centralDiff, PiLp.toLp_apply] using h4
  calc ‖centralDiff b z‖ ≤ ∑ i : Fin d, |(centralDiff b z) i| := norm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, max Cg 0 * A := Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * (max Cg 0 * A) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (d : ℝ) * max Cg 0 * A := by ring

/-- The scaled Newtonian field of an embedded site is bounded by the scaling factor. -/
private lemma norm_smul_newtonField_le (hd : 2 ≤ d) (z : Site d) :
    ‖(2 / unitBallVolume d) • newtonField (toSpace z)‖ ≤ 2 / unitBallVolume d := by
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hcoef : 0 ≤ 2 / unitBallVolume d := le_of_lt (div_pos (by norm_num) hω)
  rw [norm_smul, Real.norm_eq_abs, norm_newtonField hd, norm_toSpace, abs_of_nonneg hcoef]
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : euclidNorm z ^ (1 - (d : ℝ)) ≤ 1 := by
    rcases euclidNorm_eq_zero_or_one_le z with h0 | h1
    · rw [h0, Real.zero_rpow (by intro h; linarith)]
      norm_num
    · exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  calc (2 / unitBallVolume d) * euclidNorm z ^ (1 - (d : ℝ))
      ≤ (2 / unitBallVolume d) * 1 := mul_le_mul_of_nonneg_left hpow hcoef
    _ = 2 / unitBallVolume d := mul_one _

/-- For `ρ ≥ 1`, `ρ^{-d}` is bounded by `2^d (1 + ρ)^{-d}`. -/
private lemma rpow_neg_le_two_pow_mul {ρ : ℝ} (hρ : 1 ≤ ρ) (d : ℕ) :
    ρ ^ (-(d : ℝ)) ≤ (2 : ℝ) ^ d * (1 + ρ) ^ (-(d : ℝ)) := by
  have hρpos : 0 < ρ := by linarith
  have hle : 1 + ρ ≤ 2 * ρ := by linarith
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < 1 + ρ) hle
    (neg_nonpos.mpr (Nat.cast_nonneg d))
  have hexp : (2 * ρ) ^ (-(d : ℝ)) = ((2 : ℝ) ^ d)⁻¹ * ρ ^ (-(d : ℝ)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hρpos.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  calc ρ ^ (-(d : ℝ))
      = (2 : ℝ) ^ d * (2 * ρ) ^ (-(d : ℝ)) := by
        rw [hexp, ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero d (by norm_num : (2 : ℝ) ≠ 0)), one_mul]
    _ ≤ (2 : ℝ) ^ d * (1 + ρ) ^ (-(d : ℝ)) :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- For `0 < a ≤ b`, `1 ≤ b^n a^{-n}`. -/
private lemma one_le_pow_mul_rpow_neg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ) :
    1 ≤ b ^ n * a ^ (-(n : ℝ)) := by
  have hpow : a ^ n ≤ b ^ n := pow_le_pow_left₀ ha.le hab n
  have hone : a ^ n * a ^ (-(n : ℝ)) = 1 := by
    rw [← Real.rpow_natCast a n, ← Real.rpow_add ha (n : ℝ) (-(n : ℝ)), add_neg_cancel,
      Real.rpow_zero]
  calc (1 : ℝ) = a ^ n * a ^ (-(n : ℝ)) := hone.symm
    _ ≤ b ^ n * a ^ (-(n : ℝ)) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg ha.le _)

/-- For `0 ≤ ρ ≤ R` and `1 ≤ d`, `(1 + ρ)^{1-d} ≤ (1 + R)^d (1 + ρ)^{-d}`. -/
private lemma rpow_one_sub_le_pow_mul {ρ R : ℝ} {d : ℕ} (hρ : 0 ≤ ρ) (hd : 1 ≤ d)
    (hρR : ρ ≤ R) :
    (1 + ρ) ^ (1 - (d : ℝ)) ≤ (1 + R) ^ d * (1 + ρ) ^ (-(d : ℝ)) := by
  have hbase : (1 + ρ) ≤ (1 + R) ^ d := by
    calc (1 + ρ) ≤ 1 + R := by linarith
      _ = (1 + R) ^ 1 := (pow_one _).symm
      _ ≤ (1 + R) ^ d := pow_le_pow_right₀ (by linarith) hd
  have hsplit : (1 + ρ) ^ (1 - (d : ℝ)) = (1 + ρ) * (1 + ρ) ^ (-(d : ℝ)) := by
    rw [show (1 : ℝ) - (d : ℝ) = 1 + (-(d : ℝ)) by ring,
      Real.rpow_add (by positivity : (0 : ℝ) < 1 + ρ), Real.rpow_one]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (by positivity) _)

/-- The termwise replacement error is bounded by the maximum of the far-field and near-field
constants times `(1 + |z|)^{-d}`. -/
private lemma term_bound (hd : 2 ≤ d) {b : Site d → ℝ} {Ca R Cg : ℝ} (hR : 1 ≤ R)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d →
      |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ)))
    (z : Site d) :
    ‖centralDiff b z - (2 / unitBallVolume d) • newtonField (toSpace z)‖
      ≤ max (max Ca 0 * (2 : ℝ) ^ d)
          ((d * max Cg 0 + 2 / unitBallVolume d) * (1 + R) ^ d)
        * (1 + euclidNorm z) ^ (-(d : ℝ)) := by
  have hρ0 : 0 ≤ euclidNorm z := euclidNorm_nonneg z
  have hA0 : 0 ≤ (1 + euclidNorm z) ^ (-(d : ℝ)) := Real.rpow_nonneg (by linarith) _
  by_cases hρR : R ≤ euclidNorm z
  · have hA' : ‖centralDiff b z - (2 / unitBallVolume d) • newtonField (toSpace z)‖
        ≤ Ca * euclidNorm z ^ (-(d : ℝ)) := by
      rw [smul_newtonField_toSpace z]
      exact hgradA z hρR
    have hstep : Ca * euclidNorm z ^ (-(d : ℝ))
        ≤ max (max Ca 0 * (2 : ℝ) ^ d)
            ((d * max Cg 0 + 2 / unitBallVolume d) * (1 + R) ^ d)
          * (1 + euclidNorm z) ^ (-(d : ℝ)) := by
      have hCa : Ca ≤ max Ca 0 := le_max_left _ _
      have hpow : euclidNorm z ^ (-(d : ℝ))
          ≤ (2 : ℝ) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ)) :=
        rpow_neg_le_two_pow_mul (le_trans hR hρR) d
      calc Ca * euclidNorm z ^ (-(d : ℝ))
          ≤ max Ca 0 * euclidNorm z ^ (-(d : ℝ)) :=
              mul_le_mul_of_nonneg_right hCa (Real.rpow_nonneg hρ0 _)
        _ ≤ max Ca 0 * ((2 : ℝ) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ))) :=
              mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
        _ = (max Ca 0 * (2 : ℝ) ^ d) * (1 + euclidNorm z) ^ (-(d : ℝ)) := by ring
        _ ≤ max (max Ca 0 * (2 : ℝ) ^ d)
              ((d * max Cg 0 + 2 / unitBallVolume d) * (1 + R) ^ d)
            * (1 + euclidNorm z) ^ (-(d : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hA0
    exact hA'.trans hstep
  · have hρlt : euclidNorm z < R := lt_of_not_ge hρR
    have hcentral := norm_centralDiff_le hgrad z
    have hfield := norm_smul_newtonField_le hd z
    have hdiff : ‖centralDiff b z - (2 / unitBallVolume d) • newtonField (toSpace z)‖
        ≤ (d : ℝ) * max Cg 0 * (1 + euclidNorm z) ^ (1 - (d : ℝ))
          + 2 / unitBallVolume d := by
      calc ‖centralDiff b z - (2 / unitBallVolume d) • newtonField (toSpace z)‖
          ≤ ‖centralDiff b z‖ + ‖(2 / unitBallVolume d) • newtonField (toSpace z)‖ :=
              norm_sub_le _ _
        _ ≤ (d : ℝ) * max Cg 0 * (1 + euclidNorm z) ^ (1 - (d : ℝ))
              + 2 / unitBallVolume d := add_le_add hcentral hfield
    have hbase : (1 + euclidNorm z) ^ (1 - (d : ℝ))
        ≤ (1 + R) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ)) :=
      rpow_one_sub_le_pow_mul hρ0 (by omega) (le_of_lt hρlt)
    have hratio : 1 ≤ (1 + R) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ)) :=
      one_le_pow_mul_rpow_neg (by linarith) (by linarith) d
    have hterm1 : (d : ℝ) * max Cg 0 * (1 + euclidNorm z) ^ (1 - (d : ℝ))
        ≤ (d : ℝ) * max Cg 0
            * ((1 + R) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ))) :=
      mul_le_mul_of_nonneg_left hbase
        (mul_nonneg (Nat.cast_nonneg d) (le_max_right _ _))
    have hterm2 : 2 / unitBallVolume d
        ≤ (2 / unitBallVolume d)
            * ((1 + R) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ))) := by
      have hcoe : 0 ≤ 2 / unitBallVolume d :=
        le_of_lt (div_pos (by norm_num) (unitBallVolume_pos d))
      have h := mul_le_mul_of_nonneg_left hratio hcoe
      rwa [mul_one] at h
    have hcombine : (d : ℝ) * max Cg 0 * (1 + euclidNorm z) ^ (1 - (d : ℝ))
          + 2 / unitBallVolume d
        ≤ ((d : ℝ) * max Cg 0 + 2 / unitBallVolume d)
          * ((1 + R) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ))) := by
      calc (d : ℝ) * max Cg 0 * (1 + euclidNorm z) ^ (1 - (d : ℝ))
            + 2 / unitBallVolume d
          ≤ (d : ℝ) * max Cg 0
              * ((1 + R) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ)))
            + (2 / unitBallVolume d)
              * ((1 + R) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ))) :=
              add_le_add hterm1 hterm2
        _ = ((d : ℝ) * max Cg 0 + 2 / unitBallVolume d)
              * ((1 + R) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ))) := by ring
    have hfinal : (d : ℝ) * max Cg 0 * (1 + euclidNorm z) ^ (1 - (d : ℝ))
          + 2 / unitBallVolume d
        ≤ max (max Ca 0 * (2 : ℝ) ^ d)
            ((d * max Cg 0 + 2 / unitBallVolume d) * (1 + R) ^ d)
          * (1 + euclidNorm z) ^ (-(d : ℝ)) := by
      calc (d : ℝ) * max Cg 0 * (1 + euclidNorm z) ^ (1 - (d : ℝ))
            + 2 / unitBallVolume d
          ≤ ((d : ℝ) * max Cg 0 + 2 / unitBallVolume d)
              * ((1 + R) ^ d * (1 + euclidNorm z) ^ (-(d : ℝ))) := hcombine
        _ = ((d : ℝ) * max Cg 0 + 2 / unitBallVolume d) * (1 + R) ^ d
              * (1 + euclidNorm z) ^ (-(d : ℝ)) := by ring
        _ ≤ max (max Ca 0 * (2 : ℝ) ^ d)
                ((d * max Cg 0 + 2 / unitBallVolume d) * (1 + R) ^ d)
              * (1 + euclidNorm z) ^ (-(d : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hA0
    exact hdiff.trans hfinal

/-- The gradient replacement: under `eq:gradient` and the one-step bound, the errors
`|Db(x - y) - (2/ω_d) K(x - y)|` over any finite set of sites within distance `R'` of `y` sum to
at most `C log(R' + 2)`. -/
theorem exists_sum_norm_centralDiff_sub_newtonField_le (hd : 2 ≤ d) {b : Site d → ℝ}
    {Ca R Cg : ℝ} (hR : 1 ≤ R)
    (hgradA : ∀ x, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        Ca * euclidNorm x ^ (-(d : ℝ)))
    (hgrad : ∀ x e, e ∈ unitSteps d → |b (x + e) - b x| ≤ Cg * (1 + euclidNorm x) ^ (1 - (d : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Finset (Site d)) (y : Site d) (R' : ℝ), 1 ≤ R' →
      (∀ x ∈ E, euclidNorm (x - y) ≤ R') →
        ∑ x ∈ E, ‖centralDiff b (x - y) - (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖
          ≤ C * Real.log (R' + 2) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C', hC'pos, hC'⟩ := CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := d) hd1
  set K : ℝ := max (max Ca 0 * (2 : ℝ) ^ d)
      ((d * max Cg 0 + 2 / unitBallVolume d) * (1 + R) ^ d) with hK
  have hKpos : 0 < K := by
    have hω : 0 < unitBallVolume d := unitBallVolume_pos d
    have h1 : 0 ≤ (d : ℝ) * max Cg 0 :=
      mul_nonneg (Nat.cast_nonneg d) (le_max_right _ _)
    have h2 : 0 < (d : ℝ) * max Cg 0 + 2 / unitBallVolume d := by
      have h3 : 0 < 2 / unitBallVolume d := div_pos (by norm_num) hω
      linarith
    have h4 : 0 < (1 + R) ^ d := pow_pos (by linarith) d
    rw [hK]
    exact lt_of_lt_of_le (mul_pos h2 h4) (le_max_right _ _)
  refine ⟨K * C', mul_nonneg hKpos.le hC'pos.le, ?_⟩
  intro E y R' hR' hE
  have hbound : ∀ x ∈ E,
      ‖centralDiff b (x - y) - (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖
        ≤ K * (1 + euclidNorm (x - y)) ^ (-(d : ℝ)) := by
    intro x _
    have h := term_bound hd hR hgradA hgrad (x - y)
    simpa only [hK] using h
  calc ∑ x ∈ E,
        ‖centralDiff b (x - y) - (2 / unitBallVolume d) • newtonField (toSpace (x - y))‖
      ≤ ∑ x ∈ E, K * (1 + euclidNorm (x - y)) ^ (-(d : ℝ)) := Finset.sum_le_sum hbound
    _ = K * ∑ x ∈ E, (1 + euclidNorm (x - y)) ^ (-(d : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ K * (C' * Real.log (R' + 2)) :=
        mul_le_mul_of_nonneg_left (hC' E y R' hR' hE) hKpos.le
    _ = K * C' * Real.log (R' + 2) := by ring

end CERW.Support.LocalTime
