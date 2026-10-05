import CERW.Model
import CERW.Generic.Norm
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Euclidean projection onto a sublevel set of a norm

For a norm `Ψ` on `ℝ^d` and `r ≥ 0` let `K = {Ψ ≤ r}`, a closed convex set containing the
origin. This module proves the deterministic geometry of the Euclidean projection onto `K`
that replaces the Moreau envelope in the outer-radius argument.

* Every point has a nearest point in `K`, characterized by the variational inequality
  `⟨y - z, v - z⟩ ≤ 0` for `v ∈ K` (`exists_nearest`); a selection of nearest points for all
  points at once is obtained without any uniqueness statement (`exists_nearestSelection`).
* The support and threshold geometry: a linear functional that is bounded by `β` on `K`
  stays strictly below `β` on `{Ψ < r}` (`inner_lt_of_lt`), and `Ψ y ≤ r + Λ ‖y - z‖` for
  `z ∈ K` (`le_add_normMax_mul_dist`).
* The cap drift lemma (`cap_drift`): if `y ∉ K`, `z ∈ K` is a nearest point to `y`, and the
  offset `y - z` makes a small angle with a direction `q` of length `Λ_Ψ`, then every
  subgradient `ξ` of `Ψ` at `y` satisfies `⟨q, ξ⟩ ≥ Λ_Ψ c_Ψ / 2`. The proof uses the
  subgradient inequality at the nearest point and the radial competitor `(r / Ψ y) y ∈ K`, and
  it holds for every subgradient, including those at corners of the unit ball.

The nearest points enter only through their minimization and variational properties, so no
projection function is introduced and no uniqueness is used.
-/

namespace CERW.Support.Norm.ProjectionGeometry

open CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## Constants of a norm -/

/-- The least value of a norm on the unit sphere is at most its largest value. -/
theorem normMin_le_normMax (hΨ : IsNorm Ψ) (hd : 1 ≤ d) : normMin Ψ ≤ normMax Ψ := by
  have hd0 : 0 < d := by omega
  set u : EuclideanSpace ℝ (Fin d) := coordVec (⟨0, hd0⟩ : Fin d) with hu
  have hnorm : ‖u‖ = 1 := by simp [hu, coordVec]
  have h1 := (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd).2 u
  have h2 := CERW.Generic.Norm.le_normMax_mul hΨ u
  rw [hnorm, mul_one] at h1 h2
  exact h1.trans h2

/-- A subgradient of a norm `Ψ` has Euclidean norm at most `Λ_Ψ`. -/
theorem norm_subgradient_le_normMax (hΨ : IsNorm Ψ) {x ξ : EuclideanSpace ℝ (Fin d)}
    (h : IsSubgradient Ψ x ξ) : ‖ξ‖ ≤ normMax Ψ := by
  have h0 : 0 ≤ normMax Ψ := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨u, -, rfl⟩
    exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 u
  have h1 := (CERW.Generic.Norm.subgradient_euler hΨ h).2 ξ
  have h2 := CERW.Generic.Norm.le_normMax_mul hΨ ξ
  rw [real_inner_self_eq_norm_sq] at h1
  by_contra hnot
  have hlt := not_le.mp hnot
  have h3 := mul_lt_mul_of_pos_right hlt (lt_of_le_of_lt h0 hlt)
  have h4 : ‖ξ‖ * ‖ξ‖ = ‖ξ‖ ^ 2 := (sq ‖ξ‖).symm
  linarith

/-! ## Nearest points of a sublevel set -/

/-- The sublevel set `{Ψ ≤ r}` of a norm is convex. -/
theorem convex_sublevel (hΨ : IsNorm Ψ) (r : ℝ) :
    Convex ℝ {z : EuclideanSpace ℝ (Fin d) | Ψ z ≤ r} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  calc Ψ (a • x + b • y) ≤ Ψ (a • x) + Ψ (b • y) := hΨ.add_le _ _
    _ = a * Ψ x + b * Ψ y := by
        rw [hΨ.smul, hΨ.smul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * r + b * r := add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
    _ = r := by rw [← add_mul, hab, one_mul]

/-- The sublevel set `{Ψ ≤ r}` of a norm is closed. -/
theorem isClosed_sublevel (hΨ : IsNorm Ψ) (r : ℝ) :
    IsClosed {z : EuclideanSpace ℝ (Fin d) | Ψ z ≤ r} :=
  isClosed_le (CERW.Generic.Norm.norm_continuous hΨ) continuous_const

/-- Every point `y` has a nearest point `z` in `{Ψ ≤ r}` for `0 ≤ r`: it minimizes the Euclidean
distance to `y` over the set, and it satisfies the variational inequality
`⟨y - z, v - z⟩ ≤ 0` for every `v` in the set. -/
theorem exists_nearest (hΨ : IsNorm Ψ) {r : ℝ} (hr : 0 ≤ r) (y : EuclideanSpace ℝ (Fin d)) :
    ∃ z : EuclideanSpace ℝ (Fin d), Ψ z ≤ r ∧
      (∀ v : EuclideanSpace ℝ (Fin d), Ψ v ≤ r → ‖y - z‖ ≤ ‖y - v‖) ∧
      ∀ v : EuclideanSpace ℝ (Fin d), Ψ v ≤ r → inner ℝ (y - z) (v - z) ≤ 0 := by
  have hne : ({z : EuclideanSpace ℝ (Fin d) | Ψ z ≤ r}).Nonempty :=
    ⟨0, by simpa [(CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1] using hr⟩
  have hcv := convex_sublevel hΨ r
  obtain ⟨z, hzK, hz⟩ := exists_norm_eq_iInf_of_complete_convex hne
    (isClosed_sublevel hΨ r).isComplete hcv y
  refine ⟨z, hzK, fun v hv => ?_, (norm_eq_iInf_iff_real_inner_le_zero hcv hzK).1 hz⟩
  rw [hz]
  exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
    (⟨v, hv⟩ : {z : EuclideanSpace ℝ (Fin d) | Ψ z ≤ r})

/-- A choice of a nearest point of `{Ψ ≤ r}` for every point of `ℝ^d`, with the minimization and
variational properties of `exists_nearest`. It is made once, before any probabilistic
event; no uniqueness of the nearest point is used. -/
theorem exists_nearestSelection (hΨ : IsNorm Ψ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ y, Ψ (P y) ≤ r) ∧
      (∀ y v, Ψ v ≤ r → ‖y - P y‖ ≤ ‖y - v‖) ∧
      ∀ y v, Ψ v ≤ r → inner ℝ (y - P y) (v - P y) ≤ 0 := by
  choose P hP1 hP2 hP3 using exists_nearest hΨ hr
  exact ⟨P, hP1, hP2, hP3⟩

/-! ## Support and threshold geometry -/

/-- `Ψ y ≤ r + Λ_Ψ ‖y - z‖` whenever `Ψ z ≤ r`. -/
theorem le_add_normMax_mul_dist (hΨ : IsNorm Ψ) {r : ℝ} {y z : EuclideanSpace ℝ (Fin d)}
    (hz : Ψ z ≤ r) : Ψ y ≤ r + normMax Ψ * ‖y - z‖ := by
  have h1 := hΨ.add_le z (y - z)
  rw [add_sub_cancel] at h1
  have h2 := CERW.Generic.Norm.le_normMax_mul hΨ (y - z)
  linarith

/-- A linear functional `⟨q, ·⟩`, with `‖q‖ = Λ_Ψ > 0`, that is at most `β` on `{Ψ ≤ r}` is
strictly below `β` on `{Ψ < r}`: from `x` one can move by a positive multiple of `q` and stay in
the set. -/
theorem inner_lt_of_lt (hΨ : IsNorm Ψ) {r β : ℝ} {q x : EuclideanSpace ℝ (Fin d)}
    (hΛ : 0 < normMax Ψ) (hq : ‖q‖ = normMax Ψ)
    (hsup : ∀ v : EuclideanSpace ℝ (Fin d), Ψ v ≤ r → inner ℝ q v ≤ β) (hx : Ψ x < r) :
    inner ℝ q x < β := by
  set s : ℝ := (r - Ψ x) / normMax Ψ ^ 2 with hs
  have hs0 : 0 < s := div_pos (sub_pos.2 hx) (pow_pos hΛ 2)
  have hsΛ : s * normMax Ψ ^ 2 = r - Ψ x := by
    rw [hs]
    field_simp
  have hΨq : Ψ q ≤ normMax Ψ ^ 2 := by
    have := CERW.Generic.Norm.le_normMax_mul hΨ q
    rw [hq] at this
    linarith [sq (normMax Ψ)]
  have hv : Ψ (x + s • q) ≤ r := by
    have h1 := hΨ.add_le x (s • q)
    rw [hΨ.smul, abs_of_pos hs0] at h1
    have h2 : s * Ψ q ≤ s * normMax Ψ ^ 2 := mul_le_mul_of_nonneg_left hΨq hs0.le
    linarith
  have h3 := hsup _ hv
  rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hq] at h3
  linarith

/-- If `⟨q, ·⟩` is at most `β` on `{Ψ ≤ r}` and `‖q‖ = Λ_Ψ > 0`, every point with
`β ≤ ⟨q, x⟩` has `r ≤ Ψ x`. -/
theorem le_of_support_le_inner (hΨ : IsNorm Ψ) {r β : ℝ} {q x : EuclideanSpace ℝ (Fin d)}
    (hΛ : 0 < normMax Ψ) (hq : ‖q‖ = normMax Ψ)
    (hsup : ∀ v : EuclideanSpace ℝ (Fin d), Ψ v ≤ r → inner ℝ q v ≤ β)
    (hx : β ≤ inner ℝ q x) : r ≤ Ψ x := by
  by_contra h
  exact absurd (inner_lt_of_lt hΨ hΛ hq hsup (not_le.1 h)) (not_lt.2 hx)

/-- The direction of the offset from a nearest point: for `a ≠ 0`, `(Λ / ‖a‖) • a` has
norm `Λ`, and it vanishes for `a = 0`; in both cases its norm is at most `Λ ≥ 0`. -/
theorem norm_scaledDirection_le {Λ : ℝ} (hΛ : 0 ≤ Λ) (a : EuclideanSpace ℝ (Fin d)) :
    ‖(Λ / ‖a‖) • a‖ ≤ Λ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using hΛ
  · have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hΛ ha0.le)]
    exact (div_mul_cancel₀ Λ ha0.ne').le

/-- For `a ≠ 0`, the vector `(Λ / ‖a‖) • a` has norm exactly `Λ`. -/
theorem norm_scaledDirection {Λ : ℝ} (hΛ : 0 ≤ Λ) {a : EuclideanSpace ℝ (Fin d)}
    (ha : a ≠ 0) : ‖(Λ / ‖a‖) • a‖ = Λ := by
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hΛ ha0.le)]
  exact div_mul_cancel₀ Λ ha0.ne'

/-- The pairing of `(Λ / ‖a‖) • a` with `a` is `Λ ‖a‖`. -/
theorem inner_scaledDirection_self {Λ : ℝ} {a : EuclideanSpace ℝ (Fin d)} (ha : a ≠ 0) :
    inner ℝ ((Λ / ‖a‖) • a) a = Λ * ‖a‖ := by
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

/-! ## The cap drift lemma -/

/-- **The subgradient inequality at the nearest point.** If `Ψ z ≤ r` and `ξ` is a subgradient of
`Ψ` at `y`, then `Ψ y - r ≤ ⟨ξ, y - z⟩`. This holds for every subgradient, including those at
corners of the unit ball. -/
theorem sub_le_inner_of_subgradient {r : ℝ} {y z ξ : EuclideanSpace ℝ (Fin d)}
    (hz : Ψ z ≤ r) (hξ : IsSubgradient Ψ y ξ) : Ψ y - r ≤ inner ℝ ξ (y - z) := by
  have h1 := hξ z
  have h2 : inner ℝ ξ (z - y) = -inner ℝ ξ (y - z) := by
    rw [← inner_neg_right, neg_sub]
  linarith

/-- **The radial competitor.** If `z` is a nearest point of `{Ψ ≤ r}` to a point `y` with
`r < Ψ y`, then `c_Ψ ‖y - z‖ ≤ Ψ y - r`. The point `(r / Ψ y) y` lies in the set, and its distance
to `y` is `(1 - r/Ψ y) ‖y‖ ≤ (Ψ y - r) / c_Ψ`. -/
theorem normMin_mul_dist_le (hΨ : IsNorm Ψ) (hd : 1 ≤ d) {r : ℝ} (hr : 0 ≤ r)
    {y z : EuclideanSpace ℝ (Fin d)}
    (hmin : ∀ v : EuclideanSpace ℝ (Fin d), Ψ v ≤ r → ‖y - z‖ ≤ ‖y - v‖) (hy : r < Ψ y) :
    normMin Ψ * ‖y - z‖ ≤ Ψ y - r := by
  obtain ⟨hc, hcmul⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hΨy : 0 < Ψ y := lt_of_le_of_lt hr hy
  have ht0 : 0 ≤ r / Ψ y := div_nonneg hr hΨy.le
  have ht1 : r / Ψ y ≤ 1 := (div_le_one hΨy).2 hy.le
  have htΨ : r / Ψ y * Ψ y = r := div_mul_cancel₀ r hΨy.ne'
  have hv : Ψ ((r / Ψ y) • y) ≤ r := by
    rw [hΨ.smul, abs_of_nonneg ht0, htΨ]
  have h1 : ‖y - z‖ ≤ (1 - r / Ψ y) * ‖y‖ := by
    have h2 := hmin _ hv
    have h3 : y - (r / Ψ y) • y = (1 - r / Ψ y) • y := by rw [sub_smul, one_smul]
    rw [h3, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht1)] at h2
    exact h2
  calc normMin Ψ * ‖y - z‖ ≤ normMin Ψ * ((1 - r / Ψ y) * ‖y‖) :=
        mul_le_mul_of_nonneg_left h1 hc.le
    _ = (1 - r / Ψ y) * (normMin Ψ * ‖y‖) := by ring
    _ ≤ (1 - r / Ψ y) * Ψ y := mul_le_mul_of_nonneg_left (hcmul y) (sub_nonneg.2 ht1)
    _ = Ψ y - r := by rw [sub_mul, one_mul, htΨ]

/-- **Cap drift.** Let `z` be a nearest point of `{Ψ ≤ r}` to a point `y` outside it, let `q` have
length `Λ_Ψ`, and let `w ≥ ‖y - z‖` be such that the offset `y - z` has pairing at least
`(1 - c_Ψ²/(8 Λ_Ψ²)) Λ_Ψ w` with `q`. Then every subgradient `ξ` of `Ψ` at `y` satisfies
`Λ_Ψ c_Ψ / 2 ≤ ⟨q, ξ⟩`.

The subgradient inequality at the nearest point gives `⟨ξ, y - z⟩ ≥ Ψ y - r`, and the radial
competitor `(r/Ψ y) y` gives `c_Ψ ‖y - z‖ ≤ Ψ y - r`; the small angle between `q` and `y - z`
transfers the resulting positive pairing of `ξ` with `y - z` to `q`. -/
theorem cap_drift (hΨ : IsNorm Ψ) (hd : 1 ≤ d) {r : ℝ} (hr : 0 ≤ r)
    {y z q ξ : EuclideanSpace ℝ (Fin d)} {w : ℝ}
    (hz : Ψ z ≤ r) (hmin : ∀ v : EuclideanSpace ℝ (Fin d), Ψ v ≤ r → ‖y - z‖ ≤ ‖y - v‖)
    (hy : r < Ψ y) (hq : ‖q‖ = normMax Ψ) (hw : ‖y - z‖ ≤ w)
    (hcap : (1 - normMin Ψ ^ 2 / (8 * normMax Ψ ^ 2)) * (normMax Ψ * w) ≤ inner ℝ q (y - z))
    (hξ : IsSubgradient Ψ y ξ) :
    normMax Ψ * normMin Ψ / 2 ≤ inner ℝ q ξ := by
  obtain ⟨hc, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hcΛ := normMin_le_normMax hΨ hd
  have hξΛ := norm_subgradient_le_normMax hΨ hξ
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc hcΛ
  -- the offset from the nearest point is nonzero
  have hwy : 0 < ‖y - z‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    have h1 : y = z := sub_eq_zero.1 h0
    rw [h1] at hy
    linarith
  have hξa := sub_le_inner_of_subgradient hz hξ
  have hrad := normMin_mul_dist_le hΨ hd hr hmin hy
  have hξa' : normMin Ψ * ‖y - z‖ ≤ inner ℝ ξ (y - z) := le_trans hrad hξa
  -- the small angle between `q` and the offset
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = normMin Ψ ^ 2 / (8 * normMax Ψ ^ 2) := ⟨_, rfl⟩
  rw [← hθdef] at hcap
  have hθΛ : θ * normMax Ψ ^ 2 = normMin Ψ ^ 2 / 8 := by
    rw [hθdef]
    field_simp
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by positivity)]
    have h1 : normMin Ψ ^ 2 ≤ normMax Ψ ^ 2 := pow_le_pow_left₀ hc.le hcΛ 2
    nlinarith [pow_pos hΛ 2]
  have hI : (1 - θ) * (normMax Ψ * ‖y - z‖) ≤ inner ℝ q (y - z) :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hΛ.le)
      (sub_nonneg.2 hθ1)) hcap
  have hsq : ‖‖y - z‖ • q - normMax Ψ • (y - z)‖ ^ 2 ≤ (normMin Ψ * ‖y - z‖ / 2) ^ 2 := by
    have h1 : ‖‖y - z‖ • q - normMax Ψ • (y - z)‖ ^ 2 =
        2 * (‖y - z‖ ^ 2 * normMax Ψ ^ 2) -
          2 * (‖y - z‖ * normMax Ψ * inner ℝ q (y - z)) := by
      rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), abs_of_nonneg hΛ.le, real_inner_smul_left,
        real_inner_smul_right, hq]
      ring
    have h2 : ‖y - z‖ * normMax Ψ * ((1 - θ) * (normMax Ψ * ‖y - z‖)) ≤
        ‖y - z‖ * normMax Ψ * inner ℝ q (y - z) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    have h3 : ‖y - z‖ * normMax Ψ * ((1 - θ) * (normMax Ψ * ‖y - z‖)) =
        ‖y - z‖ ^ 2 * normMax Ψ ^ 2 - ‖y - z‖ ^ 2 * (θ * normMax Ψ ^ 2) := by ring
    have h4 : ‖y - z‖ ^ 2 * (θ * normMax Ψ ^ 2) = ‖y - z‖ ^ 2 * (normMin Ψ ^ 2 / 8) := by
      rw [hθΛ]
    have h5 : (normMin Ψ * ‖y - z‖ / 2) ^ 2 = 2 * (‖y - z‖ ^ 2 * (normMin Ψ ^ 2 / 8)) := by
      ring
    rw [h1, h5]
    linarith
  have hnorm : ‖‖y - z‖ • q - normMax Ψ • (y - z)‖ ≤ normMin Ψ * ‖y - z‖ / 2 :=
    le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  -- transfer the pairing of `ξ` with the offset to `q`
  have hD : -(‖‖y - z‖ • q - normMax Ψ • (y - z)‖ * ‖ξ‖) ≤
      inner ℝ (‖y - z‖ • q - normMax Ψ • (y - z)) ξ :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hprod : ‖‖y - z‖ • q - normMax Ψ • (y - z)‖ * ‖ξ‖ ≤
      normMin Ψ * ‖y - z‖ / 2 * normMax Ψ :=
    mul_le_mul hnorm hξΛ (norm_nonneg _) (by positivity)
  have hdecomp : ‖y - z‖ * inner ℝ q ξ =
      normMax Ψ * inner ℝ ξ (y - z) +
        inner ℝ (‖y - z‖ • q - normMax Ψ • (y - z)) ξ := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm ξ (y - z)]
    ring
  have hmain : ‖y - z‖ * (normMax Ψ * normMin Ψ / 2) ≤ ‖y - z‖ * inner ℝ q ξ := by
    have h1 : normMax Ψ * (normMin Ψ * ‖y - z‖) ≤ normMax Ψ * inner ℝ ξ (y - z) :=
      mul_le_mul_of_nonneg_left hξa' hΛ.le
    linarith
  exact le_of_mul_le_mul_left hmain hwy

end CERW.Support.Norm.ProjectionGeometry
