import CERW.Support.Statements
import CERW.Support.Norm.VectorBound
import CERW.Generic.Norm
import CERW.Support.Occupation.Facts

/-!
# The outer radius from the crossing lemma in the Euclidean farthest direction

For every norm `Ψ` and every real `a ≥ 0`, the farthest visited point `x_*` of the walk, in the
Euclidean sense, gives the direction `q = Λ_Ψ u_{x_*}` of a half-space that the crossing lemma
`outer_crossing` can use. With `θ = c_Ψ² / (8 Λ_Ψ²)`, every visited site `y` with
`q · y > (1 - θ) Λ_Ψ |x_*|` makes a Euclidean angle at most `arccos (1 - θ)` with `x_*`, so Euler's
relation and `|ξ| ≤ Λ_Ψ` give `q · ξ(y) ≥ Λ_Ψ c_Ψ / 2`. Any site with `q · x ≥ Λ_Ψ a / c_Ψ` has
`Ψ(x) ≥ a`. The crossing lemma then gives, for every real threshold `a ≥ 0`,

`max_{j ≤ n} |X_j| ≤ a / c_Ψ + C (1 + max_{Ψ(x) ≥ a} ℓ_n(x)) log n`.

This module proves that deterministic statement for a path that satisfies the vector bound and the
half-space martingale bounds for the finite family `{Λ_Ψ u_z : |z| ≤ n}` of directions, in the form
produced by `VectorBound.exists_driftCompensated_bound` and by the finite-family martingale
theorem. It uses neither the local time potential, the radial test, the Moreau envelope nor any
coarse bound: the only input about the walk is the crossing lemma, carried as a hypothesis in the
form of its statement proposition.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm.CoarseCrossing

open CERW CERW.Support.Statements CERW.Generic.Norm
open scoped Classical

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The family of directions -/

/-- The direction `Λ_Ψ u_z` of a site `z`, where `u_z = z / |z|` and `u_0 = 0`. -/
noncomputable def capDirection (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (z : Site d) :
    EuclideanSpace ℝ (Fin d) :=
  normMax Ψ • (‖toSpace z‖⁻¹ • toSpace z)

/-- The finite deterministic family `{Λ_Ψ u_z : |z| ≤ n}` of directions of the half-space
martingales. -/
noncomputable def capDirections (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  (LatticeProb.ballFinset d (n : ℝ)).image (capDirection Ψ)

/-- The least value of a norm on the Euclidean unit sphere is at most its largest value. -/
private lemma normMin_le_normMax (hd : 1 ≤ d) (hΨ : IsNorm Ψ) : normMin Ψ ≤ normMax Ψ := by
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h1 := (normMin_pos_mul_le hΨ hd).2 (coordVec (⟨0, by omega⟩ : Fin d))
  have h2 := le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h1 h2
  linarith

/-- A subgradient of a norm has Euclidean length at most `Λ_Ψ`. -/
private lemma norm_subgradient_le (hd : 1 ≤ d) (hΨ : IsNorm Ψ)
    {x ξ : EuclideanSpace ℝ (Fin d)} (h : IsSubgradient Ψ x ξ) : ‖ξ‖ ≤ normMax Ψ := by
  have hΛ : 0 ≤ normMax Ψ :=
    le_trans (normMin_pos_mul_le hΨ hd).1.le (normMin_le_normMax hd hΨ)
  have h1 : ‖ξ‖ ^ 2 ≤ normMax Ψ * ‖ξ‖ :=
    calc ‖ξ‖ ^ 2 = inner ℝ ξ ξ := (real_inner_self_eq_norm_sq ξ).symm
      _ ≤ Ψ ξ := (subgradient_euler hΨ h).2 ξ
      _ ≤ normMax Ψ * ‖ξ‖ := le_normMax_mul hΨ ξ
  rcases eq_or_lt_of_le (norm_nonneg ξ) with h0 | hpos
  · rw [← h0]
    exact hΛ
  · have h2 : ‖ξ‖ * ‖ξ‖ ≤ normMax Ψ * ‖ξ‖ := by rw [← sq]; exact h1
    exact le_of_mul_le_mul_right h2 hpos

/-- Every direction of the family has length at most `Λ_Ψ`. -/
theorem norm_capDirection_le (hΛ : 0 ≤ normMax Ψ) (z : Site d) :
    ‖capDirection Ψ z‖ ≤ normMax Ψ := by
  unfold capDirection
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΛ,
    abs_inv, abs_of_nonneg (norm_nonneg _)]
  rcases eq_or_ne ‖toSpace z‖ 0 with h0 | h0
  · rw [h0]
    simpa using hΛ
  · rw [inv_mul_cancel₀ h0, mul_one]

/-- Every vector of the family `capDirections Ψ n` has length at most `Λ_Ψ`. -/
theorem norm_le_of_mem_capDirections (hΛ : 0 ≤ normMax Ψ) {n : ℕ}
    {q : EuclideanSpace ℝ (Fin d)} (hq : q ∈ capDirections Ψ n) : ‖q‖ ≤ normMax Ψ := by
  obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
  exact norm_capDirection_le hΛ z

/-- The direction of a site of Euclidean norm at most `n` belongs to the family. -/
theorem capDirection_mem_capDirections {n : ℕ} {z : Site d} (hz : euclidNorm z ≤ n) :
    capDirection Ψ z ∈ capDirections Ψ n :=
  Finset.mem_image_of_mem _ (LatticeProb.mem_ballFinset_iff.mpr hz)

/-- The family has at most `(2n + 1)^d` vectors. -/
theorem card_capDirections_le (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) (n : ℕ) :
    ((capDirections Ψ n).card : ℝ) ≤ (2 * (n : ℝ) + 1) ^ d :=
  (Nat.cast_le.mpr Finset.card_image_le).trans
    (LatticeProb.card_ballFinset_le d (Nat.cast_nonneg n))


/-! ## The cap drift alignment -/

/-- The lattice embedding of the origin is the origin. -/
private lemma toSpace_zero_eq : toSpace (0 : Site d) = 0 := by
  ext i
  simp [toSpace]

/-- **The drift in a cap about the farthest direction.** Let `w ≠ 0` have Euclidean norm `R`, let
`q = Λ w / R`, and let `θ = c² / (8 Λ²)`. If `y` has Euclidean norm at most `R` and
`q · y > (1 - θ) Λ R`, then every subgradient `ξ` of the norm `Ψ` at `y` satisfies
`q · ξ ≥ Λ c / 2`: by Euler's relation `ξ · y = Ψ(y) ≥ c |y|`, the unit vectors `w / R` and
`y / |y|` differ by less than `c / (2 Λ)`, and `|ξ| ≤ Λ`. -/
private theorem cap_drift_alignment (hd : 1 ≤ d) (hΨ : IsNorm Ψ)
    {w y ξ : EuclideanSpace ℝ (Fin d)} (hR : 0 < ‖w‖) (hy : ‖y‖ ≤ ‖w‖)
    (hξ : IsSubgradient Ψ y ξ)
    (hcap : (1 - normMin Ψ ^ 2 / (8 * normMax Ψ ^ 2)) * (normMax Ψ * ‖w‖) <
      inner ℝ (normMax Ψ • (‖w‖⁻¹ • w)) y) :
    normMax Ψ * normMin Ψ / 2 ≤ inner ℝ (normMax Ψ • (‖w‖⁻¹ • w)) ξ := by
  obtain ⟨hc0, hcle⟩ := normMin_pos_mul_le hΨ hd
  have hcΛ : normMin Ψ ≤ normMax Ψ := normMin_le_normMax hd hΨ
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 hcΛ
  set c := normMin Ψ with hc
  set Λ := normMax Ψ with hΛdef
  set R := ‖w‖ with hRdef
  set θ : ℝ := c ^ 2 / (8 * Λ ^ 2) with hθ
  set u : EuclideanSpace ℝ (Fin d) := R⁻¹ • w with hu
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 8 := by
    rw [hθ, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : c ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hc0.le hcΛ 2
    linarith
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w)]
    exact inv_mul_cancel₀ hR.ne'
  have hnξ : ‖ξ‖ ≤ Λ := norm_subgradient_le hd hΨ hξ
  -- the cap hypothesis for `u`
  have hcap' : (1 - θ) * R < inner ℝ u y := by
    have h1 : inner ℝ (Λ • u) y = Λ * inner ℝ u y := real_inner_smul_left _ _ _
    rw [h1] at hcap
    have h2 : Λ * ((1 - θ) * R) < Λ * inner ℝ u y := by linarith
    exact lt_of_mul_lt_mul_left h2 hΛ.le
  have hy0 : 0 < ‖y‖ := by
    rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
    · exfalso
      have hy' : y = 0 := norm_eq_zero.mp h0.symm
      rw [hy', inner_zero_right] at hcap'
      have : 0 < (1 - θ) * R := mul_pos (by linarith) hR
      linarith
    · exact h0
  set v : EuclideanSpace ℝ (Fin d) := ‖y‖⁻¹ • y with hv
  have hnv : ‖v‖ = 1 := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg y)]
    exact inv_mul_cancel₀ hy0.ne'
  have huv : 1 - θ < inner ℝ u v := by
    have h1 : inner ℝ u v = ‖y‖⁻¹ * inner ℝ u y := real_inner_smul_right _ _ _
    rw [h1]
    have h2 : (1 - θ) * ‖y‖ < inner ℝ u y := by
      have : (1 - θ) * ‖y‖ ≤ (1 - θ) * R :=
        mul_le_mul_of_nonneg_left hy (by linarith)
      linarith
    rw [← div_eq_inv_mul, lt_div_iff₀ hy0]
    exact h2
  have hdist : ‖u - v‖ ^ 2 < 2 * θ := by
    rw [norm_sub_sq_real, hnu, hnv]
    linarith
  have hΛd : Λ * ‖u - v‖ < c / 2 := by
    by_contra hcon
    have hcon' : c / 2 ≤ Λ * ‖u - v‖ := not_lt.mp hcon
    have h1 : (c / 2) ^ 2 ≤ (Λ * ‖u - v‖) ^ 2 := pow_le_pow_left₀ (by positivity) hcon' 2
    have h2 : (Λ * ‖u - v‖) ^ 2 = Λ ^ 2 * ‖u - v‖ ^ 2 := by ring
    have h3 : Λ ^ 2 * ‖u - v‖ ^ 2 < Λ ^ 2 * (2 * θ) :=
      mul_lt_mul_of_pos_left hdist (by positivity)
    have h4 : Λ ^ 2 * (2 * θ) = (c / 2) ^ 2 := by
      rw [hθ]
      field_simp
      ring
    linarith
  -- Euler's relation at `y`
  obtain ⟨heuler, -⟩ := subgradient_euler hΨ hξ
  have hvξ : c ≤ inner ℝ v ξ := by
    have h1 : inner ℝ v ξ = ‖y‖⁻¹ * inner ℝ y ξ := real_inner_smul_left _ _ _
    have h2 : inner ℝ y ξ = Ψ y := by rw [real_inner_comm]; exact heuler
    have h3 : c * ‖y‖ ≤ Ψ y := hcle y
    rw [h1, h2, ← div_eq_inv_mul, le_div_iff₀ hy0]
    exact h3
  have hdiff : -(‖u - v‖ * Λ) ≤ inner ℝ (u - v) ξ := by
    have h1 : |inner ℝ (u - v) ξ| ≤ ‖u - v‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
    have h2 : ‖u - v‖ * ‖ξ‖ ≤ ‖u - v‖ * Λ := mul_le_mul_of_nonneg_left hnξ (norm_nonneg _)
    have h3 := neg_abs_le (inner ℝ (u - v) ξ)
    linarith
  have huξ : c / 2 < inner ℝ u ξ := by
    have h1 : inner ℝ u ξ = inner ℝ v ξ + inner ℝ (u - v) ξ := by
      rw [← inner_add_left]
      congr 1
      abel
    have h2 : ‖u - v‖ * Λ = Λ * ‖u - v‖ := by ring
    linarith
  have h5 : inner ℝ (Λ • u) ξ = Λ * inner ℝ u ξ := real_inner_smul_left _ _ _
  rw [h5]
  have h6 : Λ * (c / 2) ≤ Λ * inner ℝ u ξ := mul_le_mul_of_nonneg_left huξ.le hΛ.le
  linarith


/-! ## The rough outer bound -/

/-- A site whose pairing with a vector `q` of length at most `Λ_Ψ` is at least `Λ_Ψ a / c_Ψ` has
`Ψ ≥ a`. -/
private theorem le_norm_of_cap_level (hd : 1 ≤ d) (hΨ : IsNorm Ψ)
    {q z : EuclideanSpace ℝ (Fin d)} (hq : ‖q‖ ≤ normMax Ψ) {a : ℝ}
    (hz : normMax Ψ * a / normMin Ψ ≤ inner ℝ q z) : a ≤ Ψ z := by
  obtain ⟨hc0, hcle⟩ := normMin_pos_mul_le hΨ hd
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 (normMin_le_normMax hd hΨ)
  have h1 : inner ℝ q z ≤ normMax Ψ * ‖z‖ :=
    (real_inner_le_norm q z).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg z))
  have h2 : normMax Ψ * a / normMin Ψ ≤ normMax Ψ * ‖z‖ := hz.trans h1
  rw [div_le_iff₀ hc0] at h2
  have h3 : normMax Ψ * a ≤ normMax Ψ * (normMin Ψ * ‖z‖) := by linarith
  have h4 : a ≤ normMin Ψ * ‖z‖ := le_of_mul_le_mul_left h3 hΛ
  exact h4.trans (hcle z)

/-- **The rough outer bound for every norm and every real level.** There is a constant `C`, chosen
from the norm, the drift strength and the constants of the two martingale bounds, such that for
every choice of subgradients `ξ`, every `n ≥ 2` and every nearest-neighbour path from the origin
that satisfies the vector bound with constant `C_V` and the half-space martingale bounds with
constant `C_M` for the finite family `capDirections Ψ n`, every real `a ≥ 0` satisfies
`max_{j ≤ n} |x_j| ≤ a / c_Ψ + C (1 + max_{Ψ(z) ≥ a} ℓ_n(z)) log n`. The crossing lemma is applied
in the direction `Λ_Ψ u_{x_*}` of a Euclidean farthest point `x_*` of the path, with
`θ = c_Ψ² / (8 Λ_Ψ²)`, drift bound `α = Λ_Ψ c_Ψ / 2` and level `Λ_Ψ a / c_Ψ`. -/
theorem rough_outer_bound (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    (houter : CERW.Support.Statements.outer_crossing) {C_V C_M : ℝ} (hC_V : 0 < C_V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (n : ℕ), 2 ≤ n → ∀ (x : ℕ → Site d), x 0 = 0 →
      (∀ j, x (j + 1) - x j ∈ unitSteps d) →
      (∀ s t : ℕ, s < t → t ≤ n →
        ‖VectorBound.driftCompensated ε ξ x t - VectorBound.driftCompensated ε ξ x s‖ ≤
          C_V * Real.sqrt (((t : ℝ) - s) * Real.log n)) →
      (∀ q ∈ capDirections Ψ n, ∀ k : ℕ, k ≤ n →
        |dynkinMart (driftStepProb d ε ξ)
            (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) x n| ≤
          C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
              (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
            (localTime x n z : ℝ)) + Real.log n)) →
      ∀ a : ℝ, 0 ≤ a →
        maxRadius x n ≤ a / normMin Ψ + C * (1 + ((((departureRange x n).filter
          (fun z => a ≤ Ψ (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) * Real.log n := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc0, hcle⟩ := normMin_pos_mul_le hΨ hd1
  have hcΛ : normMin Ψ ≤ normMax Ψ := normMin_le_normMax hd1 hΨ
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 hcΛ
  set θ : ℝ := normMin Ψ ^ 2 / (8 * normMax Ψ ^ 2) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 / 8 := by
    rw [hθdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : normMin Ψ ^ 2 ≤ normMax Ψ ^ 2 := pow_le_pow_left₀ hc0.le hcΛ 2
    linarith
  set α : ℝ := normMax Ψ * normMin Ψ / 2 with hαdef
  have hα : 0 < α := by positivity
  have hC₁ : 0 < max C_V C_M := lt_max_of_lt_left hC_V
  obtain ⟨C, hCpos, hC⟩ := houter hd Ψ hΨ ε hε hell α hα (max C_V C_M) hC₁
  refine ⟨C * (1 + θ⁻¹) / normMax Ψ, by positivity, ?_⟩
  intro ξ hξ hξ0 n hn x hx0 hstep hvec hmart a ha
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  set S : ℝ := ((((departureRange x n).filter (fun z => a ≤ Ψ (toSpace z))).sup
    (localTime x n) : ℕ) : ℝ) with hSdef
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  set F : ℝ := C * (1 + S) * Real.log n with hFdef
  have hF0 : 0 ≤ F := by positivity
  have hrhs : C * (1 + θ⁻¹) / normMax Ψ * (1 + S) * Real.log n = (1 + θ⁻¹) * F / normMax Ψ := by
    rw [hFdef]
    ring
  rw [hrhs]
  have hκ0 : 0 ≤ (1 + θ⁻¹) * F / normMax Ψ := by positivity
  by_cases hR : maxRadius x n = 0
  · rw [hR]
    exact add_nonneg (div_nonneg ha hc0.le) hκ0
  have hRpos : 0 < maxRadius x n := by
    have h0 : 0 ≤ maxRadius x n :=
      (by rw [← norm_toSpace]; exact norm_nonneg _ : 0 ≤ euclidNorm (x 0)).trans
        (euclidNorm_le_maxRadius x (Nat.zero_le n))
    exact lt_of_le_of_ne h0 (Ne.symm hR)
  -- a farthest point of the path
  obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun j => euclidNorm (x j)) ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
  have hj₀n : j₀ ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj₀mem)
  have hmax : ∀ j ≤ n, euclidNorm (x j) ≤ euclidNorm (x j₀) :=
    fun j hj => hj₀max j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hRj : maxRadius x n = euclidNorm (x j₀) :=
    le_antisymm
      (Finset.sup'_le _ _ fun j hj => hmax j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
      (euclidNorm_le_maxRadius x hj₀n)
  set w : EuclideanSpace ℝ (Fin d) := toSpace (x j₀) with hw
  have hwR : ‖w‖ = maxRadius x n := by rw [hw, norm_toSpace, hRj]
  have hnorm_le : ∀ j ≤ n, ‖toSpace (x j)‖ ≤ ‖w‖ := fun j hj => by
    rw [norm_toSpace, hwR, hRj]
    exact hmax j hj
  -- the direction `q = Λ u_{x_*}`
  set q : EuclideanSpace ℝ (Fin d) := capDirection Ψ (x j₀) with hqdef
  have hqeq : q = normMax Ψ • (‖w‖⁻¹ • w) := rfl
  have hqn : ‖q‖ ≤ normMax Ψ := norm_capDirection_le hΛ.le _
  have hqmem : q ∈ capDirections Ψ n :=
    capDirection_mem_capDirections
      ((CERW.Support.Occupation.euclidNorm_le_of_steps x hx0 hstep j₀).trans
        (by exact_mod_cast hj₀n))
  have hqw : inner ℝ q w = normMax Ψ * ‖w‖ := by
    rw [hqeq, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  set T : ℝ := inner ℝ q w with hTdef
  have hT : T = normMax Ψ * ‖w‖ := hqw
  have hlin : ∀ j ≤ n, inner ℝ q (toSpace (x j)) ≤ T := by
    intro j hj
    calc inner ℝ q (toSpace (x j)) ≤ ‖q‖ * ‖toSpace (x j)‖ := real_inner_le_norm _ _
      _ ≤ normMax Ψ * ‖w‖ :=
          mul_le_mul hqn (hnorm_le j hj) (norm_nonneg _) hΛ.le
      _ = T := hT.symm
  have hTpos : 0 < T := by rw [hT]; exact mul_pos hΛ (hwR ▸ hRpos)
  set h : ℝ := θ * T with hhdef
  have hh : 0 < h := mul_pos hθ0 hTpos
  have hThm : T - h = (1 - θ) * (normMax Ψ * ‖w‖) := by rw [hhdef, hT]; ring
  have hcap : ∀ j ≤ n, T - h < inner ℝ q (toSpace (x j)) → α ≤ inner ℝ q (ξ (x j)) := by
    intro j hj hlt
    have hxj : x j ≠ 0 := by
      intro h0
      rw [h0, toSpace_zero_eq, inner_zero_right] at hlt
      have : 0 < T - h := by rw [hThm]; exact mul_pos (by linarith) (mul_pos hΛ (hwR ▸ hRpos))
      linarith
    rw [hThm, hqeq] at hlt
    rw [hqeq]
    exact cap_drift_alignment hd1 hΨ (hwR ▸ hRpos) (hnorm_le j hj) (hξ (x j) hxj) hlt
  -- the crossing lemma, for the vector and martingale bounds with the common constant
  have hvec' : ∀ s t : ℕ, s < t → t ≤ n →
      ‖(toSpace (x t) + ε • ∑ j ∈ Finset.range t,
          if x j ∉ departureRange x j then ξ (x j) else 0) -
        (toSpace (x s) + ε • ∑ j ∈ Finset.range s,
          if x j ∉ departureRange x j then ξ (x j) else 0)‖ ≤
        max C_V C_M * Real.sqrt (((t : ℝ) - s) * Real.log n) := fun s t hst htn =>
    (hvec s t hst htn).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have hmart' : ∀ k : ℕ, k ≤ n →
      |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) x n| ≤
        max C_V C_M * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
            (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
          (localTime x n z : ℝ)) + Real.log n) := fun k hk =>
    (hmart q hqmem k hk).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (add_nonneg (Real.sqrt_nonneg _) hlog))
  have hb : 0 ≤ normMax Ψ * a / normMin Ψ := by positivity
  have hcross := hC ξ hξ hξ0 n hn q hqn x hx0 hstep hvec' hmart' j₀ hj₀n hlin h hh hcap
    (normMax Ψ * a / normMin Ψ) hb
  -- compare the two suprema of local times
  have hsub : ((departureRange x n).filter
      (fun z => normMax Ψ * a / normMin Ψ ≤ inner ℝ q (toSpace z))) ⊆
        (departureRange x n).filter (fun z => a ≤ Ψ (toSpace z)) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, le_norm_of_cap_level hd1 hΨ hqn hz.2⟩
  have hsup : ((((departureRange x n).filter
      (fun z => normMax Ψ * a / normMin Ψ ≤ inner ℝ q (toSpace z))).sup
        (localTime x n) : ℕ) : ℝ) ≤ S := Nat.cast_le.mpr (Finset.sup_mono hsub)
  have hcross' : T ≤ max (T - h) (normMax Ψ * a / normMin Ψ) + F := by
    refine hcross.trans (add_le_add le_rfl ?_)
    rw [hFdef]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsup) hCpos.le) hlog
  rw [← hwR]
  rcases max_cases (T - h) (normMax Ψ * a / normMin Ψ) with ⟨hm, -⟩ | ⟨hm, -⟩
  · -- the maximum is `T - h`: `θ Λ R ≤ F`
    rw [hm] at hcross'
    have h1 : θ * (normMax Ψ * ‖w‖) ≤ F := by
      have : h ≤ F := by linarith
      rw [hhdef, hT] at this
      exact this
    have h2 : normMax Ψ * ‖w‖ ≤ θ⁻¹ * F := by
      have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hθ0.le)
      rwa [← mul_assoc, inv_mul_cancel₀ hθ0.ne', one_mul] at this
    have h3 : ‖w‖ ≤ (1 + θ⁻¹) * F / normMax Ψ := by
      rw [le_div_iff₀ hΛ]
      have : (1 + θ⁻¹) * F = F + θ⁻¹ * F := by ring
      linarith
    have h4 : 0 ≤ a / normMin Ψ := div_nonneg ha hc0.le
    linarith
  · -- the maximum is the level: `Λ R ≤ Λ a / c + F`
    rw [hm] at hcross'
    have h1 : normMax Ψ * ‖w‖ ≤ normMax Ψ * a / normMin Ψ + F := by
      rw [← hT]
      exact hcross'
    have h2 : ‖w‖ ≤ a / normMin Ψ + F / normMax Ψ := by
      have h3 : normMax Ψ * a / normMin Ψ = normMax Ψ * (a / normMin Ψ) := by ring
      rw [h3] at h1
      have h4 : normMax Ψ * ‖w‖ ≤ normMax Ψ * (a / normMin Ψ + F / normMax Ψ) := by
        calc normMax Ψ * ‖w‖ ≤ normMax Ψ * (a / normMin Ψ) + F := h1
          _ = normMax Ψ * (a / normMin Ψ + F / normMax Ψ) := by field_simp
      exact le_of_mul_le_mul_left h4 hΛ
    have h5 : F / normMax Ψ ≤ (1 + θ⁻¹) * F / normMax Ψ := by
      apply div_le_div_of_nonneg_right _ hΛ.le
      have h6 : 0 ≤ θ⁻¹ * F := mul_nonneg (inv_nonneg.mpr hθ0.le) hF0
      have h7 : (1 + θ⁻¹) * F = F + θ⁻¹ * F := by ring
      linarith
    linarith


/-- The finite supremum of the local times over the sites of the departure range with `Ψ ≥ a` is at
most `L` as soon as every site with `Ψ ≥ a` has local time at most `L`. -/
theorem sup_localTime_filter_le {a L : ℝ} (hL : 0 ≤ L) (x : ℕ → Site d) (n : ℕ)
    (h : ∀ z : Site d, a ≤ Ψ (toSpace z) → (localTime x n z : ℝ) ≤ L) :
    ((((departureRange x n).filter (fun z => a ≤ Ψ (toSpace z))).sup (localTime x n) : ℕ) : ℝ) ≤
      L := by
  have h1 : ((departureRange x n).filter (fun z => a ≤ Ψ (toSpace z))).sup (localTime x n) ≤
      ⌊L⌋₊ :=
    Finset.sup_le fun z hz => Nat.le_floor (h z (Finset.mem_filter.1 hz).2)
  exact (Nat.cast_le.2 h1).trans (Nat.floor_le hL)

/-- Every site with `Ψ ≥ a` has local time at most the finite supremum over the departure range:
off the departure range the local time vanishes. With `sup_localTime_filter_le`, the supremum is
the maximum of `ℓ_n` over the lattice sites with `Ψ ≥ a`, as in the paper. -/
theorem localTime_le_sup_filter (x : ℕ → Site d) (n : ℕ) {a : ℝ} {z : Site d}
    (hz : a ≤ Ψ (toSpace z)) :
    localTime x n z ≤
      ((departureRange x n).filter (fun z => a ≤ Ψ (toSpace z))).sup (localTime x n) := by
  by_cases hmem : z ∈ departureRange x n
  · exact Finset.le_sup (f := localTime x n) (Finset.mem_filter.2 ⟨hmem, hz⟩)
  · rw [mem_departureRange_iff, not_lt] at hmem
    exact hmem.trans (Nat.zero_le _)

end CERW.Support.Norm.CoarseCrossing
