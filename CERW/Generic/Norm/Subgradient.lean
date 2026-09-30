import CERW.Model.Norm

/-!
# Subgradients of a norm

A subgradient `ξ` of a norm `Ψ` at `x` satisfies Euler's relation `ξ · x = Ψ(x)` and the
bound `ξ · y ≤ Ψ(y)` for every `y` (`eq:convexity`); so each coordinate satisfies
`|ξ_i| ≤ Ψ(e_i)`. The zero vector is a subgradient at the origin, which is the paper's
convention `ξ(0) = 0`.
-/

namespace CERW.Generic.Norm

open CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A norm vanishes at the origin. -/
private lemma norm_apply_zero (hΨ : IsNorm Ψ) : Ψ 0 = 0 := by
  simpa using hΨ.smul 0 (0 : EuclideanSpace ℝ (Fin d))

/-- A norm is even: `Ψ (-x) = Ψ x`. -/
private lemma norm_apply_neg (hΨ : IsNorm Ψ) (x : EuclideanSpace ℝ (Fin d)) :
    Ψ (-x) = Ψ x := by
  simpa using hΨ.smul (-1) x

/-- A norm is nonnegative. -/
private lemma norm_apply_nonneg (hΨ : IsNorm Ψ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ Ψ x := by
  have h := hΨ.add_le x (-x)
  rw [add_neg_cancel, norm_apply_zero hΨ, norm_apply_neg hΨ x] at h
  linarith

/-- The inner product with a basis vector is the corresponding coordinate. -/
private lemma inner_coordVec (ξ : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    inner ℝ ξ (coordVec i) = ξ i := by
  simp [coordVec, EuclideanSpace.inner_single_right]

/-- Euler's relation `ξ · x = Ψ(x)` and the bound `ξ · y ≤ Ψ(y)` for a subgradient `ξ` at
`x`. -/
theorem subgradient_euler (hΨ : IsNorm Ψ) {x ξ : EuclideanSpace ℝ (Fin d)}
    (h : IsSubgradient Ψ x ξ) : inner ℝ ξ x = Ψ x ∧ ∀ y, inner ℝ ξ y ≤ Ψ y := by
  have key : ∀ y, Ψ x + inner ℝ ξ y - inner ℝ ξ x ≤ Ψ y := by
    intro y
    have hh := h y
    rw [inner_sub_right] at hh
    linarith
  have hlow : Ψ x ≤ inner ℝ ξ x := by
    have h0 := key 0
    rw [inner_zero_right, norm_apply_zero hΨ] at h0
    linarith
  have hhigh : inner ℝ ξ x ≤ Ψ x := by
    have h2 := key ((2 : ℝ) • x)
    rw [real_inner_smul_right, hΨ.smul 2 x] at h2
    norm_num at h2
    linarith
  have heuler : inner ℝ ξ x = Ψ x := le_antisymm hhigh hlow
  refine ⟨heuler, fun y => ?_⟩
  have hy := key y
  rw [heuler] at hy
  linarith

/-- Each coordinate of a subgradient satisfies `|ξ_i| ≤ Ψ(e_i)`. -/
theorem subgradient_abs_coord_le (hΨ : IsNorm Ψ) {x ξ : EuclideanSpace ℝ (Fin d)}
    (h : IsSubgradient Ψ x ξ) (i : Fin d) : |ξ i| ≤ Ψ (coordVec i) := by
  have hb := (subgradient_euler hΨ h).2
  have hpos := hb (coordVec i)
  have hneg := hb (-coordVec i)
  rw [inner_coordVec] at hpos
  rw [inner_neg_right, inner_coordVec, norm_apply_neg hΨ] at hneg
  rw [abs_le]
  constructor <;> linarith

/-- The zero vector is a subgradient of a norm at the origin. -/
theorem subgradient_zero (hΨ : IsNorm Ψ) : IsSubgradient Ψ 0 0 := by
  intro y
  rw [norm_apply_zero hΨ, sub_zero, inner_zero_left, zero_add]
  exact norm_apply_nonneg hΨ y

end CERW.Generic.Norm
