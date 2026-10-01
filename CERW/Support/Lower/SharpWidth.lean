import CERW.Support.Statements
import CERW.Frozen.CoarseBounds
import CERW.Support.Law.CoordinateDrift
import CERW.Support.Occupation.Facts
import CERW.Support.Occupation.Cells
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.FreshSum
import CERW.Support.Occupation.CellSetVolume
import CERW.Generic.Martingale.Clamp

/-!
# Sharpness of the width of the range in the plane

Theorem 1.3 (iv) of the paper: for `d = 2` the difference `R_out(n) - R_in(n)` of the radii is at
least `c √(r_n log n)` with probability at least `n^{-p}`, and at least
`√(π/(3ε)) √(r_n log log n)` infinitely often almost surely.

The first coordinate `Y_n = (X_n)_1 + ε V_n` of the compensated position, where
`V_n = Σ_{x ∈ A_n} (u_x)_1`, is a martingale with increments at most `2` and bracket between
`n/2 - ε²|A_n|` and `n/2`. The sum `V_n` over the range is controlled by the radii alone: the
sites of the inner disk cancel by the reflection `x ↦ (-x₁, x₂)`, and the sites between the radii
are counted row by row. The polynomial bound follows from `exp_deviation` and the coarse bounds
on the outer radius, and the iterated logarithm from Stout's law and `limit_shape`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower

open CERW.Support.Statements CERW CERW.Support.Law
open LatticeProb (unit)

/-! ### The sum of first coordinates of directions over the range -/

/-- The planar row function `a ↦ √(a² + b²)` increases with `a ≥ 0`, and the ratio `a / φ(a)`
is at most the increment `φ(a+1) - φ(a)`. -/
private lemma div_sqrt_le_sub (b : ℝ) (a : ℕ) :
    (a : ℝ) / Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) ≤
      Real.sqrt (((a + 1 : ℕ) : ℝ) ^ 2 + b ^ 2) - Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) := by
  set φ := Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) with hφ
  set ψ := Real.sqrt (((a + 1 : ℕ) : ℝ) ^ 2 + b ^ 2) with hψ
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hP : 0 ≤ (a : ℝ) ^ 2 + b ^ 2 := by positivity
  have hQ : 0 ≤ ((a + 1 : ℕ) : ℝ) ^ 2 + b ^ 2 := by positivity
  have hφ0 : 0 ≤ φ := Real.sqrt_nonneg _
  have hφψ : φ ≤ ψ := Real.sqrt_le_sqrt (by push_cast; nlinarith)
  rcases hφ0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]
    linarith
  · rw [div_le_iff₀ hpos]
    have hφ2 : φ * φ = (a : ℝ) ^ 2 + b ^ 2 := Real.mul_self_sqrt hP
    have hprod : φ * ψ = Real.sqrt (((a : ℝ) ^ 2 + b ^ 2) * (((a + 1 : ℕ) : ℝ) ^ 2 + b ^ 2)) :=
      (Real.sqrt_mul hP _).symm
    have hle : (a : ℝ) ^ 2 + a + b ^ 2 ≤ φ * ψ := by
      rw [hprod]
      apply Real.le_sqrt_of_sq_le
      push_cast
      nlinarith [sq_nonneg b]
    nlinarith

/-- The row function `φ(a) = √(a² + b²)` is at least `a`. -/
private lemma le_sqrt_sq_add (b : ℝ) (a : ℕ) : (a : ℝ) ≤ Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg b]

/-- The row function `φ(a) = √(a² + b²)` is at least `|b|`. -/
private lemma abs_le_sqrt_sq_add (b : ℝ) (a : ℕ) :
    |b| ≤ Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a : ℝ)])

/-- The row function increases by at most one: `φ(a+1) ≤ φ(a) + 1`. -/
private lemma sqrt_succ_le (b : ℝ) (a : ℕ) :
    Real.sqrt (((a + 1 : ℕ) : ℝ) ^ 2 + b ^ 2) ≤ Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) + 1 := by
  have hP : 0 ≤ (a : ℝ) ^ 2 + b ^ 2 := by positivity
  have h1 := Real.sq_sqrt hP
  have h2 := le_sqrt_sq_add b a
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  push_cast
  nlinarith

/-- One row of the lattice annulus: the sum of `a / √(a² + b²)` over positive integers `a`
with `ρ ≤ √(a² + b²) ≤ R` is at most `R + 1 - max ρ |b|`, by telescoping. -/
private lemma row_sum_le (b ρ R : ℝ) (T : Finset ℕ)
    (hT : ∀ a ∈ T, ρ ≤ Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) ∧ Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) ≤ R)
    (hnn : 0 ≤ R + 1 - max ρ |b|) :
    ∑ a ∈ T, (a : ℝ) / Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) ≤ R + 1 - max ρ |b| := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simpa using hnn
  set f : ℕ → ℝ := fun a => Real.sqrt ((a : ℝ) ^ 2 + b ^ 2) with hf
  have hmono : ∀ a : ℕ, f a ≤ f (a + 1) := fun a =>
    Real.sqrt_le_sqrt (by push_cast; nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)])
  have hterm : ∀ a ∈ T, (a : ℝ) / f a ≤ f (a + 1) - f a := fun a _ => div_sqrt_le_sub b a
  have hsub : T ⊆ Finset.Icc (T.min' hne) (T.max' hne) := fun a ha =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le T a ha, Finset.le_max' T a ha⟩
  have hM : f (T.max' hne + 1) ≤ R + 1 := by
    have := (hT _ (Finset.max'_mem T hne)).2
    have h2 := sqrt_succ_le b (T.max' hne)
    simp only [hf] at this ⊢
    linarith
  have hm : max ρ |b| ≤ f (T.min' hne) :=
    max_le (hT _ (Finset.min'_mem T hne)).1 (abs_le_sqrt_sq_add b _)
  calc ∑ a ∈ T, (a : ℝ) / f a ≤ ∑ a ∈ T, (f (a + 1) - f a) := Finset.sum_le_sum hterm
    _ ≤ ∑ a ∈ Finset.Icc (T.min' hne) (T.max' hne), (f (a + 1) - f a) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => sub_nonneg.mpr (hmono a)
    _ = f (T.max' hne + 1) - f (T.min' hne) :=
        Finset.sum_Icc_sub (Finset.min'_le_max' T hne) f
    _ ≤ R + 1 - max ρ |b| := by linarith

/-- The arithmetic of the row sum: `((y+1)₊)² ≤ (y₊)² + 2 (y+1)₊`. -/
private lemma sq_max_succ_le (y : ℝ) :
    (max (y + 1) 0) ^ 2 ≤ (max y 0) ^ 2 + 2 * max (y + 1) 0 := by
  rcases le_or_gt 0 y with hy | hy
  · rw [max_eq_left hy, max_eq_left (by linarith)]
    nlinarith
  · rw [max_eq_right hy.le]
    have h0 : 0 ≤ max (y + 1) 0 := le_max_right _ _
    have h1 : max (y + 1) 0 ≤ 1 := max_le (by linarith) zero_le_one
    nlinarith

/-- The sum over the rows `|b| ≤ N` of `R + 1 - max ρ |b|`, by induction on `N`. -/
private lemma outer_sum_le (ρ R : ℝ) (hρ : 0 ≤ ρ) (N : ℕ) :
    ∑ b ∈ Finset.Icc (-(N : ℤ)) N, (R + 1 - max ρ |((b : ℤ) : ℝ)|) ≤
      (2 * N + 1) * (R + 1 - ρ) - (max ((N : ℝ) - ρ) 0) ^ 2 := by
  induction N with
  | zero =>
    simp [hρ]
  | succ N ih =>
    have hset : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
      ext b
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hn1 : (-((N + 1 : ℕ) : ℤ)) ∉ insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N) := by
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hn2 : ((N + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(N : ℤ)) N := by
      simp only [Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert hn1, Finset.sum_insert hn2]
    have habs : |(((-((N + 1 : ℕ) : ℤ) : ℤ)) : ℝ)| = (N : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    have habs2 : |((((N + 1 : ℕ) : ℤ)) : ℝ)| = (N : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
    rw [habs, habs2]
    have hstep := sq_max_succ_le ((N : ℝ) - ρ)
    have hmax : max ρ ((N : ℝ) + 1) = ρ + max ((N : ℝ) + 1 - ρ) 0 := by
      rcases le_total ρ ((N : ℝ) + 1) with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]
        ring
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
    rw [hmax]
    push_cast
    have e1 : (N : ℝ) - ρ + 1 = (N : ℝ) + 1 - ρ := by ring
    rw [e1] at hstep
    nlinarith

/-- The final arithmetic of the annulus count. -/
private lemma final_arith (ρ R : ℝ) (hR : 0 ≤ R) (hρR : ρ ≤ R + 1) :
    (2 * (⌊R⌋₊ : ℝ) + 1) * (R + 1 - ρ) - (max ((⌊R⌋₊ : ℝ) - ρ) 0) ^ 2 ≤
      (R - ρ + 1) * (R + ρ + 6) := by
  have hN1 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR
  have hN2 : R < (⌊R⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one R
  have hN0 : (0 : ℝ) ≤ ⌊R⌋₊ := Nat.cast_nonneg _
  have hc : 0 ≤ R + 1 - ρ := by linarith
  rcases le_or_gt ρ (⌊R⌋₊ : ℝ) with h | h
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (1 + (R - (⌊R⌋₊ : ℝ)))]
  · rw [max_eq_right (by linarith)]
    nlinarith [mul_nonneg hc (by linarith : (0 : ℝ) ≤ R + ρ + 6 - (2 * (⌊R⌋₊ : ℝ) + 1))]

/-- The first coordinate of the direction of a planar site. -/
private lemma dir_apply (x : Site 2) :
    (unitDir (toSpace x)) 0 = ((x 0 : ℤ) : ℝ) / euclidNorm x := by
  simp [unitDir, norm_toSpace, div_eq_inv_mul]

/-- The Euclidean norm of a planar site in coordinates. -/
private lemma euclidNorm_two (x : Site 2) :
    euclidNorm x = Real.sqrt (((x 0 : ℤ) : ℝ) ^ 2 + ((x 1 : ℤ) : ℝ) ^ 2) := by
  simp [LatticeProb.euclidNorm, Fin.sum_univ_two]

/-- The reflection `x ↦ (-x₁, x₂)` of the plane lattice. -/
private def reflect (x : Site 2) : Site 2 := ![-(x 0), x 1]

/-- The reflection is an involution. -/
private lemma reflect_reflect (x : Site 2) : reflect (reflect x) = x := by
  ext i
  fin_cases i <;> simp [reflect]

/-- The reflection preserves the Euclidean norm. -/
private lemma euclidNorm_reflect (x : Site 2) : euclidNorm (reflect x) = euclidNorm x := by
  rw [euclidNorm_two, euclidNorm_two]
  simp [reflect]

/-- The reflection negates the first coordinate of the direction. -/
private lemma dir_reflect (x : Site 2) :
    (unitDir (toSpace (reflect x))) 0 = -(unitDir (toSpace x)) 0 := by
  rw [dir_apply, dir_apply, euclidNorm_reflect]
  simp [reflect, neg_div]

/-- A finite set of sites invariant under the reflection has zero sum of first coordinates of
directions. -/
private lemma sum_dir_reflect_invariant (L : Finset (Site 2)) (hL : ∀ x ∈ L, reflect x ∈ L) :
    ∑ x ∈ L, (unitDir (toSpace x)) 0 = 0 := by
  have h : ∑ x ∈ L, (unitDir (toSpace x)) 0 = ∑ x ∈ L, (unitDir (toSpace (reflect x))) 0 :=
    Finset.sum_nbij' reflect reflect (fun x hx => hL x hx) (fun x hx => hL x hx)
      (fun x _ => reflect_reflect x) (fun x _ => reflect_reflect x)
      (fun x _ => by rw [reflect_reflect])
  simp only [dir_reflect, Finset.sum_neg_distrib] at h
  linarith

/-- The sum over a row of the half annulus `x₁ > 0` of `x₁ / |x|`. -/
private lemma row_sum_site (b : ℤ) (ρ R : ℝ) (S : Finset (Site 2))
    (hS : ∀ x ∈ S, 0 < x 0 ∧ x 1 = b ∧ ρ ≤ euclidNorm x ∧ euclidNorm x ≤ R)
    (hnn : 0 ≤ R + 1 - max ρ |(b : ℝ)|) :
    ∑ x ∈ S, ((x 0 : ℤ) : ℝ) / euclidNorm x ≤ R + 1 - max ρ |(b : ℝ)| := by
  have hg : ∀ x ∈ S, (((x 0).toNat : ℕ) : ℝ) = ((x 0 : ℤ) : ℝ) := fun x hx => by
    have : ((((x 0).toNat : ℕ) : ℤ)) = x 0 := Int.toNat_of_nonneg (hS x hx).1.le
    exact_mod_cast this
  have hnorm : ∀ x ∈ S, euclidNorm x =
      Real.sqrt ((((x 0).toNat : ℕ) : ℝ) ^ 2 + (b : ℝ) ^ 2) := fun x hx => by
    rw [euclidNorm_two, hg x hx, (hS x hx).2.1]
  have hinj : Set.InjOn (fun x : Site 2 => (x 0).toNat) S := by
    intro x hx y hy hxy
    have h0 : x 0 = y 0 := by
      have h1 := Int.toNat_of_nonneg (hS x hx).1.le
      have h2 := Int.toNat_of_nonneg (hS y hy).1.le
      simp only at hxy
      omega
    ext i
    fin_cases i
    · exact h0
    · simp [(hS x hx).2.1, (hS y hy).2.1]
  have hsum : ∑ x ∈ S, ((x 0 : ℤ) : ℝ) / euclidNorm x =
      ∑ a ∈ S.image (fun x : Site 2 => (x 0).toNat),
        (a : ℝ) / Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hnorm x hx, hg x hx]
  rw [hsum]
  refine row_sum_le (b : ℝ) ρ R _ ?_ hnn
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  rw [← hnorm x hx]
  exact ⟨(hS x hx).2.2.1, (hS x hx).2.2.2⟩

/-- The sum of `x₁ / |x|` over the lattice points of the half annulus `ρ ≤ |x| ≤ R`, `x₁ > 0`. -/
private lemma half_annulus_sum_le (ρ R : ℝ) (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (hρR : ρ ≤ R + 1) :
    ∑ x ∈ (LatticeProb.ballFinset 2 R).filter (fun x => ρ ≤ euclidNorm x ∧ 0 < x 0),
        ((x 0 : ℤ) : ℝ) / euclidNorm x ≤ (R - ρ + 1) * (R + ρ + 6) := by
  classical
  set H := (LatticeProb.ballFinset 2 R).filter (fun x => ρ ≤ euclidNorm x ∧ 0 < x 0) with hH
  set N := ⌊R⌋₊ with hN
  have hmaps : ∀ x ∈ H, x 1 ∈ Finset.Icc (-(N : ℤ)) N := by
    intro x hx
    rw [hH, Finset.mem_filter, LatticeProb.mem_ballFinset_iff] at hx
    have h1 : |((x 1 : ℤ) : ℝ)| ≤ R := by
      refine le_trans ?_ hx.1
      rw [euclidNorm_two, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((x 0 : ℤ) : ℝ)])
    have h2 : (|x 1| : ℤ) ≤ N := by
      have h3 : ((|x 1| : ℤ) : ℝ) ≤ R := by rwa [Int.cast_abs]
      have h4 : (|x 1|).toNat ≤ N := Nat.le_floor (by
        have : (((|x 1|).toNat : ℕ) : ℝ) = ((|x 1| : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (abs_nonneg (x 1))
        rw [this]
        exact h3)
      have h5 := Int.toNat_of_nonneg (abs_nonneg (x 1))
      omega
    rw [Finset.mem_Icc]
    have := abs_le.mp h2
    constructor <;> omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hrow : ∀ b ∈ Finset.Icc (-(N : ℤ)) N,
      ∑ x ∈ H.filter (fun x => x 1 = b), ((x 0 : ℤ) : ℝ) / euclidNorm x ≤
        R + 1 - max ρ |((b : ℤ) : ℝ)| := by
    intro b hb
    have hbR : |((b : ℤ) : ℝ)| ≤ R := by
      have h1 : |b| ≤ (N : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hb)
      have h2 : ((|b| : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
      rw [Int.cast_abs] at h2
      exact h2.trans (Nat.floor_le hR)
    refine row_sum_site b ρ R _ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter, hH, Finset.mem_filter, LatticeProb.mem_ballFinset_iff] at hx
      exact ⟨hx.1.2.2, hx.2, hx.1.2.1, hx.1.1⟩
    · have : 0 ≤ R + 1 - ρ := by linarith
      rcases le_total ρ |((b : ℤ) : ℝ)| with h | h
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left h]
        exact this
  calc ∑ b ∈ Finset.Icc (-(N : ℤ)) N, ∑ x ∈ H.filter (fun x => x 1 = b),
        ((x 0 : ℤ) : ℝ) / euclidNorm x
      ≤ ∑ b ∈ Finset.Icc (-(N : ℤ)) N, (R + 1 - max ρ |((b : ℤ) : ℝ)|) :=
        Finset.sum_le_sum hrow
    _ ≤ (2 * N + 1) * (R + 1 - ρ) - (max ((N : ℝ) - ρ) 0) ^ 2 := outer_sum_le ρ R hρ N
    _ ≤ (R - ρ + 1) * (R + ρ + 6) := final_arith ρ R hR hρR

/-- The positive part of the first coordinate of the direction is the direction on the
half plane `x₁ > 0` and vanishes elsewhere. -/
private lemma max_dir_eq (x : Site 2) :
    max ((unitDir (toSpace x)) 0) 0 = if 0 < x 0 then ((x 0 : ℤ) : ℝ) / euclidNorm x else 0 := by
  rw [dir_apply]
  have hn := LatticeProb.euclidNorm_nonneg x
  split_ifs with h
  · exact max_eq_left (div_nonneg (Int.cast_nonneg h.le) hn)
  · exact max_eq_right (div_nonpos_of_nonpos_of_nonneg
      (by simpa using (Int.cast_le (R := ℝ)).mpr (not_lt.mp h : x 0 ≤ 0)) hn)

/-- The sum of the first coordinates of the directions over a finite set of sites that contains
the lattice disk of radius `ρ` and lies in the disk of radius `R`. -/
private theorem abs_sum_dir_le (A : Finset (Site 2)) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R)
    (hin : ∀ x : Site 2, euclidNorm x < ρ → x ∈ A) (hout : ∀ x ∈ A, euclidNorm x ≤ R) :
    |∑ x ∈ A, (unitDir (toSpace x)) 0| ≤ (R - ρ + 1) * (R + ρ + 6) := by
  classical
  set w : Site 2 → ℝ := fun x => (unitDir (toSpace x)) 0 with hw
  have hρR : ρ ≤ R + 1 := by
    by_contra hlt
    rw [not_le] at hlt
    set s : Site 2 := ![((⌊R⌋₊ : ℕ) : ℤ) + 1, 0] with hs
    have hsn : euclidNorm s = (⌊R⌋₊ : ℝ) + 1 := by
      rw [euclidNorm_two]
      simp only [hs, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      rw [show (((⌊R⌋₊ : ℕ) : ℝ) + 1) ^ 2 + (0 : ℝ) ^ 2 = (((⌊R⌋₊ : ℕ) : ℝ) + 1) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    have h1 : euclidNorm s < ρ := by linarith [Nat.floor_le hR]
    have h2 := hout s (hin s h1)
    linarith [Nat.lt_floor_add_one R]
  -- split the range at the radius `ρ`
  have hsplit := Finset.sum_filter_add_sum_filter_not A (fun x => euclidNorm x < ρ) w
  have hlow : ∑ x ∈ A.filter (fun x => euclidNorm x < ρ), w x = 0 := by
    refine sum_dir_reflect_invariant _ fun x hx => ?_
    rw [Finset.mem_filter] at hx ⊢
    have : euclidNorm (reflect x) < ρ := by rw [euclidNorm_reflect]; exact hx.2
    exact ⟨hin _ this, this⟩
  set H := (LatticeProb.ballFinset 2 R).filter (fun x => ρ ≤ euclidNorm x) with hH
  have hsub : A.filter (fun x => ¬ euclidNorm x < ρ) ⊆ H := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hH, Finset.mem_filter, LatticeProb.mem_ballFinset_iff]
    exact ⟨hout x hx.1, not_lt.mp hx.2⟩
  have hP : ∑ x ∈ H, max (w x) 0 ≤ (R - ρ + 1) * (R + ρ + 6) := by
    have hmax : ∀ x ∈ H, max (w x) 0 = if 0 < x 0 then ((x 0 : ℤ) : ℝ) / euclidNorm x else 0 :=
      fun x _ => max_dir_eq x
    rw [Finset.sum_congr rfl hmax, ← Finset.sum_filter, hH, Finset.filter_filter]
    exact half_annulus_sum_le ρ R hρ hR hρR
  have hHreflect : ∀ x ∈ H, reflect x ∈ H := by
    intro x hx
    rw [hH, Finset.mem_filter, LatticeProb.mem_ballFinset_iff] at hx ⊢
    rw [euclidNorm_reflect]
    exact hx
  have hP' : ∑ x ∈ H, max (-(w x)) 0 = ∑ x ∈ H, max (w x) 0 := by
    have h := Finset.sum_nbij' (s := H) (t := H) reflect reflect hHreflect hHreflect
      (fun x _ => reflect_reflect x) (fun x _ => reflect_reflect x)
      (f := fun x => max (w x) 0) (g := fun x => max (-(w x)) 0) (fun x _ => by
        simp only [hw, dir_reflect, neg_neg])
    exact h.symm
  have hup : ∑ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ), w x ≤
      (R - ρ + 1) * (R + ρ + 6) := by
    calc ∑ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ), w x
        ≤ ∑ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ), max (w x) 0 :=
          Finset.sum_le_sum fun x _ => le_max_left _ _
      _ ≤ ∑ x ∈ H, max (w x) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => le_max_right _ _
      _ ≤ _ := hP
  have hdown : -∑ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ), w x ≤
      (R - ρ + 1) * (R + ρ + 6) := by
    calc -∑ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ), w x
        = ∑ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ), -(w x) := by
          rw [Finset.sum_neg_distrib]
      _ ≤ ∑ x ∈ A.filter (fun x => ¬ euclidNorm x < ρ), max (-(w x)) 0 :=
          Finset.sum_le_sum fun x _ => le_max_left _ _
      _ ≤ ∑ x ∈ H, max (-(w x)) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => le_max_right _ _
      _ ≤ _ := by rw [hP']; exact hP
  rw [← hsplit, hlow, zero_add, abs_le]
  exact ⟨by linarith, hup⟩

/-! ### Interface R: radii and the departure range -/

/-- The inner radius is nonnegative. -/
private theorem innerRadius_nonneg {d : ℕ} (X : ℕ → Site d) (n : ℕ) :
    0 ≤ innerRadius X n := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨y, -, rfl⟩
  exact norm_nonneg y

/-- The outer radius is nonnegative. -/
private theorem maxRadius_nonneg {d : ℕ} (X : ℕ → Site d) (n : ℕ) : 0 ≤ maxRadius X n :=
  (LatticeProb.euclidNorm_nonneg (X 0)).trans (euclidNorm_le_maxRadius X (Nat.zero_le n))

/-- A site in the open ball of radius the inner radius belongs to the departure range. -/
private theorem mem_departureRange_of_lt_innerRadius {d : ℕ} {X : ℕ → Site d} {n : ℕ}
    {x : Site d} (h : euclidNorm x < innerRadius X n) : x ∈ departureRange X n := by
  by_contra hx
  have hmem : toSpace x ∈ (cellSet X n)ᶜ := fun hc =>
    hx ((CERW.Support.Occupation.toSpace_mem_cellSet_iff X n x).mp hc)
  have hle : innerRadius X n ≤ ‖toSpace x‖ := by
    refine csInf_le ⟨0, ?_⟩ ⟨toSpace x, hmem, rfl⟩
    rintro _ ⟨y, -, rfl⟩
    exact norm_nonneg y
  rw [norm_toSpace] at hle
  exact absurd h (not_lt.mpr hle)

/-- A site of the departure range is within the outer radius. -/
private theorem euclidNorm_le_maxRadius_of_mem {d : ℕ} {X : ℕ → Site d} {n : ℕ} {x : Site d}
    (hx : x ∈ departureRange X n) : euclidNorm x ≤ maxRadius X n :=
  LatticeProb.mem_ballFinset_iff.mp
    (CERW.Support.Occupation.departureRange_subset_ballFinset X n hx)

/-- If all lattice sites of norm below `s` are in the departure range, the inner radius is at
least `s - 1` (in the plane the cell of a site has radius `√2/2 < 1`). -/
private theorem sub_one_le_innerRadius {X : ℕ → Site 2} {n : ℕ} {s : ℝ}
    (h : ∀ x : Site 2, euclidNorm x < s → x ∈ departureRange X n) :
    s - 1 ≤ innerRadius X n := by
  have hne : ((fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖) '' (cellSet X n)ᶜ).Nonempty := by
    have hsub := CERW.Support.Occupation.cellSet_subset_ball (d := 2) (by norm_num) X n
    obtain ⟨y, hy⟩ : ∃ y : EuclideanSpace ℝ (Fin 2),
        y ∉ Metric.ball 0 (maxRadius X n + Real.sqrt 2) := by
      refine ⟨EuclideanSpace.single 0 (maxRadius X n + Real.sqrt 2 + 1), ?_⟩
      rw [mem_ball_zero_iff, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs, not_lt,
        abs_of_nonneg (by linarith [maxRadius_nonneg X n, Real.sqrt_nonneg 2])]
      linarith
    exact ⟨‖y‖, y, fun hc => hy (hsub hc), rfl⟩
  refine le_csInf hne ?_
  rintro _ ⟨y, hy, rfl⟩
  have hc : cellCenter y ∉ departureRange X n := fun hc =>
    hy ((CERW.Support.Occupation.mem_cellSet_iff X n y).mpr hc)
  have h1 : s ≤ euclidNorm (cellCenter y) := not_lt.mp fun hlt => hc (h _ hlt)
  have h2 := CERW.Support.Occupation.norm_sub_toSpace_le_of_mem_cell (mem_cell_cellCenter y)
  have h3 : Real.sqrt 2 / 2 < 1 := by
    have : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  have h4 : ‖toSpace (cellCenter y)‖ ≤ ‖y‖ + ‖y - toSpace (cellCenter y)‖ := by
    calc ‖toSpace (cellCenter y)‖ = ‖y - (y - toSpace (cellCenter y))‖ := by
          rw [sub_sub_cancel]
      _ ≤ ‖y‖ + ‖y - toSpace (cellCenter y)‖ := norm_sub_le _ _
  rw [norm_toSpace] at h4
  push_cast at h2
  linarith

/-- If the departure range lies in the ball of radius `s` and the walk makes unit steps, then
the outer radius at a time `n ≥ 1` is at most `s + 1`. -/
private theorem maxRadius_le_add_one {d : ℕ} {X : ℕ → Site d} {n : ℕ} {s : ℝ} (hn : 1 ≤ n)
    (hA : ∀ x ∈ departureRange X n, euclidNorm x ≤ s)
    (hstep : ∀ j < n, X (j + 1) - X j ∈ unitSteps d) : maxRadius X n ≤ s + 1 := by
  apply Finset.sup'_le
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rcases Nat.lt_or_ge j n with hlt | hge
  · have hmem : X j ∈ departureRange X n := Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hlt, rfl⟩
    linarith [hA _ hmem]
  · have hjn' : j = n := le_antisymm hjn hge
    subst hjn'
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    have hmem : X m ∈ departureRange X (m + 1) :=
      Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), rfl⟩
    have hnorm : euclidNorm (X (m + 1) - X m) = 1 :=
      euclidNorm_of_mem_unitSteps (hstep m (Nat.lt_succ_self m))
    calc euclidNorm (X (m + 1)) = euclidNorm (X m + (X (m + 1) - X m)) := by
          rw [add_sub_cancel]
      _ ≤ euclidNorm (X m) + euclidNorm (X (m + 1) - X m) :=
          CERW.Support.Occupation.euclidNorm_add_le _ _
      _ ≤ s + 1 := by rw [hnorm]; linarith [hA _ hmem]


/-- A unit step changes a coordinate of a site by at most one in absolute value, and the square
of the change is `1` exactly when the step is along that coordinate. -/
private lemma coord_add_sub_unit {d : ℕ} (k i : Fin d) (x : Site d) :
    ((((x + unit i) k : ℤ) : ℝ)) - ((x k : ℤ) : ℝ) = if i = k then 1 else 0 := by
  simp only [Pi.add_apply, unit_apply_coord]
  split_ifs <;> push_cast <;> ring

/-- The change of a coordinate under the step `-e_i`. -/
private lemma coord_add_sub_neg_unit {d : ℕ} (k i : Fin d) (x : Site d) :
    ((((x + -unit i) k : ℤ) : ℝ)) - ((x k : ℤ) : ℝ) = if i = k then -1 else 0 := by
  simp only [Pi.add_apply, Pi.neg_apply, unit_apply_coord]
  split_ifs <;> push_cast <;> ring

/-- The probabilities of the steps `e_k` and `-e_k` add up to `1/d`, at every time and along
every path. -/
private lemma stepProb_unit_add_neg {d : ℕ} (ε : ℝ) (x : ℕ → Site d) (t : ℕ) (k : Fin d) :
    stepProb d ε x t (unit k) + stepProb d ε x t (-unit k) = 1 / (d : ℝ) := by
  unfold stepProb
  split_ifs
  · rw [firstStep_unit, firstStep_neg_unit]
    ring
  · rw [srwStep_unit, srwStep_neg_unit]
    ring

/-- The mean square oscillation of the `k`-th coordinate at the next step is `1/d`. -/
private lemma sum_stepProb_coord_sq {d : ℕ} (ε : ℝ) (x : ℕ → Site d) (t : ℕ) (k : Fin d) :
    ∑ e ∈ unitSteps d, stepProb d ε x t e *
        ((((x t + e) k : ℤ) : ℝ) - ((x t k : ℤ) : ℝ)) ^ 2 = 1 / (d : ℝ) := by
  rw [sum_unitSteps]
  have hpair : ∀ i : Fin d,
      stepProb d ε x t (unit i) * ((((x t + unit i) k : ℤ) : ℝ) - ((x t k : ℤ) : ℝ)) ^ 2 +
        stepProb d ε x t (-unit i) *
          ((((x t + -unit i) k : ℤ) : ℝ) - ((x t k : ℤ) : ℝ)) ^ 2 =
      (stepProb d ε x t (unit i) + stepProb d ε x t (-unit i)) * (if i = k then 1 else 0) := by
    intro i
    rw [coord_add_sub_unit, coord_add_sub_neg_unit]
    split_ifs <;> ring
  simp_rw [hpair]
  rw [Finset.sum_eq_single k]
  · rw [stepProb_unit_add_neg]
    simp
  · intro i _ hik
    rw [if_neg hik, mul_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- The conditional variance of an increment of the Dynkin martingale is exactly the mean square
oscillation `Σ_e p_t(e) (f(X_t + e) - f(X_t))²` minus the square of the drift
`Σ_e p_t(e) (f(X_t + e) - f(X_t))`. -/
private theorem condExp_sq_dynkin_succ_sub_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ)) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (f : Site d → ℝ)
    (t : ℕ) :
    μ[fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2 |
        pathFiltration hX.measurable t] =ᵐ[μ]
      fun ω => ∑ e ∈ unitSteps d,
        stepProb d ε (fun j => X j ω) t e * (f (X t ω + e) - f (X t ω)) ^ 2 -
          (nextMean ε f (fun j => X j ω) t - f (X t ω)) ^ 2 := by
  set h : ((i : Finset.Iic t) → Site d) → Site d → ℝ :=
    fun p z => (f z - nextMean ε f (extendPath p) t) ^ 2 with hh
  have hsq : (fun ω => (dynkin ε f X (t + 1) ω - dynkin ε f X t ω) ^ 2) =
      fun ω => h (pastPath X t ω) (X (t + 1) ω) := by
    funext ω
    rw [dynkin_succ_sub, nextMean_pastPath]
  have hint := integrable_path_next hd hε hεd hX t h
  rw [hsq]
  filter_upwards [condExp_path_next hd hε hεd hX t h hint] with ω hω
  rw [hω]
  simp only [hh, ← nextMean_pastPath]
  have hvar := sum_mul_sub_mean_sq (unitSteps d)
    (fun e => stepProb d ε (fun j => X j ω) t e) (fun e => f (X t ω + e))
    (sum_stepProb hd ε _ t) (f (X t ω))
  simp only [nextMean]
  exact hvar

/-- The first coordinate of a direction has absolute value at most one. -/
private lemma abs_unitDir_apply_le {d : ℕ} (x : Site d) (k : Fin d) :
    |unitDir (toSpace x) k| ≤ 1 :=
  (PiLp.norm_apply_le (unitDir (toSpace x)) k).trans (norm_unitDir_le _)

/-- A process with increments at most `2` that starts at `0` is at most `2 n` at time `n`. -/
private lemma abs_le_two_mul_of_increments {Ω : Type*} {Y : ℕ → Ω → ℝ} (h0 : ∀ ω, Y 0 ω = 0)
    (hbd : ∀ i ω, |Y (i + 1) ω - Y i ω| ≤ 2) (n : ℕ) (ω : Ω) : |Y n ω| ≤ 2 * n := by
  induction n with
  | zero => simp [h0 ω]
  | succ n ih =>
    have h1 := hbd n ω
    have h2 : |Y (n + 1) ω| ≤ |Y (n + 1) ω - Y n ω| + |Y n ω| := by
      calc |Y (n + 1) ω| = |(Y (n + 1) ω - Y n ω) + Y n ω| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    push_cast
    linarith


/-- The conditional variance of an increment of a process that almost surely agrees with the
Dynkin martingale of the `k`-th coordinate is `1/d` minus the square of the drift
`ε I_t (u_{X_t})_k`, where `I_t` indicates a first departure from a nonzero site. -/
private theorem condExp_sq_coord_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ)) {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site d} (hX : IsCERW μ ε X) (k : Fin d) {Y : ℕ → Ω → ℝ}
    (hae : ∀ᵐ ω ∂μ, ∀ i, Y i ω = dynkin ε (fun z : Site d => ((z k : ℤ) : ℝ)) X i ω) (t : ℕ) :
    μ[fun ω => (Y (t + 1) ω - Y t ω) * (Y (t + 1) ω - Y t ω) | pathFiltration hX.measurable t]
      =ᵐ[μ] fun ω => 1 / (d : ℝ) -
        (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω) then
          ε * unitDir (toSpace (X t ω)) k else 0) ^ 2 := by
  have hsq : (fun ω => (Y (t + 1) ω - Y t ω) * (Y (t + 1) ω - Y t ω)) =ᵐ[μ]
      fun ω => (dynkin ε (fun z : Site d => ((z k : ℤ) : ℝ)) X (t + 1) ω -
        dynkin ε (fun z : Site d => ((z k : ℤ) : ℝ)) X t ω) ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω (t + 1), hω t, sq]
  refine (condExp_congr_ae hsq).trans ?_
  filter_upwards [condExp_sq_dynkin_succ_sub_eq hd hε hεd hX
    (fun z : Site d => ((z k : ℤ) : ℝ)) t] with ω hω
  rw [hω, sum_stepProb_coord_sq, nextMean_coord hd]
  ring


/-- The embedding of the origin is the origin of Euclidean space. -/
private lemma toSpace_zero' {d : ℕ} : toSpace (0 : Site d) = 0 := by
  apply PiLp.ext
  intro i
  simp [toSpace_apply]

/-- The sum over first departures from nonzero sites of the `k`-th coordinate of the direction
is the sum of that coordinate over the departure range. -/
private lemma sum_fresh_dir {d : ℕ} (x : ℕ → Site d) (n : ℕ) (k : Fin d) :
    ∑ j ∈ Finset.range n, (if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then
      unitDir (toSpace (x j)) k else 0) = ∑ z ∈ departureRange x n, unitDir (toSpace z) k := by
  rw [CERW.Support.Occupation.sum_fresh_ne_zero_eq_sum_departureRange x n
    (fun z => unitDir (toSpace z) k)]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z = 0
  · subst hz
    simp [toSpace_zero']
  · simp [hz]

/-- The number of first departures from nonzero sites before time `n` is at most the size of
the departure range. -/
private lemma sum_fresh_indicator_le {d : ℕ} (x : ℕ → Site d) (n : ℕ) :
    ∑ j ∈ Finset.range n, (if x j ≠ 0 ∧ x j ∉ (Finset.range j).image x then (1 : ℝ) else 0) ≤
      ((departureRange x n).card : ℝ) := by
  rw [CERW.Support.Occupation.sum_fresh_ne_zero_eq_sum_departureRange x n (fun _ => (1 : ℝ))]
  calc ∑ z ∈ departureRange x n, (if z ≠ 0 then (1 : ℝ) else 0)
      ≤ ∑ _z ∈ departureRange x n, (1 : ℝ) :=
        Finset.sum_le_sum fun z _ => by split_ifs <;> norm_num
    _ = ((departureRange x n).card : ℝ) := by simp

/-- The Dynkin martingale of the `k`-th coordinate of a walk started at the origin is the
coordinate plus `ε` times the sum of the `k`-th coordinates of the directions over the
departure range. -/
private lemma dynkin_coord_eq {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} (ε : ℝ) (X : ℕ → Ω → Site d)
    (k : Fin d) (ω : Ω) (h0 : X 0 ω = 0) (n : ℕ) :
    dynkin ε (fun z : Site d => ((z k : ℤ) : ℝ)) X n ω = ((X n ω k : ℤ) : ℝ) +
      ε * ∑ x ∈ departureRange (fun j => X j ω) n, unitDir (toSpace x) k := by
  have hterm : ∀ j, nextMean ε (fun z : Site d => ((z k : ℤ) : ℝ)) (fun i => X i ω) j -
      ((X j ω k : ℤ) : ℝ) = -(ε * (if X j ω ≠ 0 ∧ X j ω ∉ (Finset.range j).image (fun i => X i ω)
        then unitDir (toSpace (X j ω)) k else 0)) := by
    intro j
    rw [nextMean_coord hd ε _ j k]
    split_ifs <;> ring
  rw [dynkin, h0, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_neg_distrib,
    ← Finset.mul_sum, sum_fresh_dir (fun j => X j ω) n k]
  simp


/-- The first coordinate of the compensated position `Z_t = X_t + ε Σ_{j<t} I_j u_{X_j}` is,
up to a null set, a martingale `Y` for the natural filtration with `Y_0 = 0`, increments at most
`2` everywhere, and bracket between `n/2 - ε²|A_n|` and `n/2`. -/
private theorem exists_coord_martingale {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) :
    ∃ Y : ℕ → Ω → ℝ, Martingale Y (pathFiltration hX.measurable) μ ∧
      (∀ ω, Y 0 ω = 0) ∧ (∀ i ω, |Y (i + 1) ω - Y i ω| ≤ 2) ∧ (∀ n, MemLp (Y n) 2 μ) ∧
      (∀ᵐ ω ∂μ, ∀ n, Y n ω = ((X n ω 0 : ℤ) : ℝ) +
          ε * ∑ x ∈ departureRange (fun j => X j ω) n, (unitDir (toSpace x)) 0) ∧
      (∀ᵐ ω ∂μ, ∀ n,
        predBracket μ (pathFiltration hX.measurable) Y Y n ω ≤ (n : ℝ) / 2 ∧
          (n : ℝ) / 2 - ε ^ 2 * ((departureRange (fun j => X j ω) n).card : ℝ) ≤
            predBracket μ (pathFiltration hX.measurable) Y Y n ω) := by
  have hd : 1 ≤ 2 := by norm_num
  have hε : 0 ≤ ε := hε0.le
  have hmart := martingale_dynkin (d := 2) hd hε hεd hX (fun z : Site 2 => ((z 0 : ℤ) : ℝ))
  have hinc : ∀ i, ∀ᵐ ω ∂μ, |dynkin ε (fun z : Site 2 => ((z 0 : ℤ) : ℝ)) X (i + 1) ω -
      dynkin ε (fun z : Site 2 => ((z 0 : ℤ) : ℝ)) X i ω| ≤ 2 := fun i =>
    (ae_abs_dynkin_succ_sub_le hd hε hεd hX (fun z : Site 2 => ((z 0 : ℤ) : ℝ))).mono
      fun ω hω => by
        simpa using hω i 1 fun e he => by
          obtain ⟨j, rfl | rfl⟩ := mem_unitSteps.mp he
          · rw [coord_add_sub_unit]
            split_ifs <;> simp
          · rw [coord_add_sub_neg_unit]
            split_ifs <;> simp
  obtain ⟨Y, hY, hbd, h0, hae⟩ := CERW.Generic.Martingale.exists_martingale_clamp hmart
    (b := 2) (by norm_num) hinc
  have hY0 : ∀ ω, Y 0 ω = 0 := fun ω => by rw [h0 ω, dynkin_zero]
  have hX0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    rw [ae_iff]
    exact hX.start
  refine ⟨Y, hY, hY0, hbd, fun n => ?_, ?_, ?_⟩
  · refine MemLp.of_bound
      ((hY.stronglyMeasurable n).mono ((pathFiltration hX.measurable).le n)).aestronglyMeasurable
      (2 * n) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le_two_mul_of_increments hY0 hbd n ω
  · filter_upwards [hae, hX0] with ω hω hω0 n
    rw [hω n]
    exact dynkin_coord_eq hd ε X 0 ω hω0 n
  · have hvar := fun t => condExp_sq_coord_eq hd hε hεd hX (0 : Fin 2) hae t
    filter_upwards [ae_all_iff.mpr hvar] with ω hω n
    have hsum : predBracket μ (pathFiltration hX.measurable) Y Y n ω = ∑ t ∈ Finset.range n,
        (1 / ((2 : ℕ) : ℝ) - (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω)
          then ε * unitDir (toSpace (X t ω)) 0 else 0) ^ 2) := by
      rw [predBracket, Finset.sum_apply]
      exact Finset.sum_congr rfl fun t _ => hω t
    rw [hsum]
    refine ⟨?_, ?_⟩
    · calc _ ≤ ∑ _t ∈ Finset.range n, (1 / ((2 : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun t _ => sub_le_self _ (sq_nonneg _)
        _ = (n : ℝ) / 2 := by simp [div_eq_mul_inv]
    · have hterm : ∀ t ∈ Finset.range n,
          1 / ((2 : ℕ) : ℝ) - ε ^ 2 * (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image
            (fun i => X i ω) then (1 : ℝ) else 0) ≤
          1 / ((2 : ℕ) : ℝ) - (if X t ω ≠ 0 ∧ X t ω ∉ (Finset.range t).image (fun i => X i ω)
            then ε * unitDir (toSpace (X t ω)) 0 else 0) ^ 2 := by
        intro t _
        refine sub_le_sub_left ?_ _
        split_ifs
        · rw [mul_pow, mul_one]
          exact mul_le_of_le_one_right (sq_nonneg _)
            ((sq_le_one_iff_abs_le_one _).mpr (abs_unitDir_apply_le (X t ω) 0))
        · simp
      refine le_trans ?_ (Finset.sum_le_sum hterm)
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hcount := sum_fresh_indicator_le (fun j => X j ω) n
      have h2 : (0 : ℝ) ≤ ε ^ 2 := sq_nonneg ε
      have h3 := mul_le_mul_of_nonneg_left hcount h2
      have hc : ∑ _t ∈ Finset.range n, (1 / ((2 : ℕ) : ℝ)) = (n : ℝ) / 2 := by
        simp [div_eq_mul_inv]
      rw [hc]
      linarith


/-! ### Measurability of the width -/

/-- The outer radius up to time `n` depends only on the path up to time `n`. -/
private lemma maxRadius_congr {d : ℕ} {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    maxRadius x n = maxRadius y n := by
  unfold maxRadius
  refine Finset.sup'_congr _ rfl fun j hj => ?_
  rw [h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

/-- The inner radius at time `n` depends only on the path up to time `n`. -/
private lemma innerRadius_congr {d : ℕ} {x y : ℕ → Site d} {n : ℕ} (h : ∀ j ≤ n, x j = y j) :
    innerRadius x n = innerRadius y n := by
  have himage : departureRange x n = departureRange y n :=
    Finset.image_congr fun j hj => h j (Finset.mem_range.mp hj).le
  simp only [innerRadius, cellSet, himage]

/-- The difference of the two radii is a measurable function of the sample point. -/
private lemma measurable_width {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → Site 2}
    (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (fun ω => maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n) := by
  have hG : (fun ω => maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n) =
      fun ω => (fun p : (i : Finset.Iic n) → Site 2 =>
        maxRadius (extendPath p) n - innerRadius (extendPath p) n) (pastPath X n ω) := by
    funext ω
    have h : ∀ j ≤ n, (fun j => X j ω) j = extendPath (pastPath X n ω) j := fun j hj =>
      (extendPath_pastPath X hj ω).symm
    simp only [maxRadius_congr h, innerRadius_congr h]
  rw [hG]
  exact (measurable_of_countable (fun p : (i : Finset.Iic n) → Site 2 =>
    maxRadius (extendPath p) n - innerRadius (extendPath p) n)).comp (measurable_pastPath hX n)

/-! ### The bracket of a rescaled martingale -/

/-- Rescaling a process by `c` rescales its predictable bracket by `c ^ 2`, almost surely. -/
private lemma predBracket_smul {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) :
    predBracket μ ℱ (c • Y) (c • Y) n =ᵐ[μ] fun ω => c ^ 2 * predBracket μ ℱ Y Y n ω := by
  have h : ∀ t, μ[fun ω => ((c • Y) (t + 1) ω - (c • Y) t ω) *
        ((c • Y) (t + 1) ω - (c • Y) t ω) | ℱ t] =ᵐ[μ]
      fun ω => c ^ 2 * μ[fun ω => (Y (t + 1) ω - Y t ω) * (Y (t + 1) ω - Y t ω) | ℱ t] ω := by
    intro t
    have hfun : (fun ω => ((c • Y) (t + 1) ω - (c • Y) t ω) *
        ((c • Y) (t + 1) ω - (c • Y) t ω)) =
        (c ^ 2) • (fun ω => (Y (t + 1) ω - Y t ω) * (Y (t + 1) ω - Y t ω)) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    exact condExp_smul (c ^ 2) _ _
  filter_upwards [ae_all_iff.mpr h] with ω hω
  simp only [predBracket, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => hω t

/-! ### The deviation of the first coordinate -/

/-- The rescaled martingale has bracket between `1/2 - ε²` and `1/2`, almost surely. -/
private lemma bracket_rescaled_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ε : ℝ} {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X)
    {Y : ℕ → Ω → ℝ} (hYbr : ∀ᵐ ω ∂μ, ∀ n,
        predBracket μ (pathFiltration hX.measurable) Y Y n ω ≤ (n : ℝ) / 2 ∧
          (n : ℝ) / 2 - ε ^ 2 * ((departureRange (fun j => X j ω) n).card : ℝ) ≤
            predBracket μ (pathFiltration hX.measurable) Y Y n ω)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, 1 / 2 - ε ^ 2 ≤ predBracket μ (pathFiltration hX.measurable)
        ((Real.sqrt n)⁻¹ • Y) ((Real.sqrt n)⁻¹ • Y) n ω ∧
      predBracket μ (pathFiltration hX.measurable)
        ((Real.sqrt n)⁻¹ • Y) ((Real.sqrt n)⁻¹ • Y) n ω ≤ 1 / 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  filter_upwards [predBracket_smul μ (pathFiltration hX.measurable) Y (Real.sqrt n)⁻¹ n,
    hYbr] with ω h1 h2
  obtain ⟨h2a, h2b⟩ := h2 n
  have hcard : ((departureRange (fun j => X j ω) n).card : ℝ) ≤ n := by
    exact_mod_cast CERW.Support.Occupation.card_departureRange_le (fun j => X j ω) n
  have hsq : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hnpos.le]
  rw [h1, hsq]
  have hlow : (n : ℝ) * (1 / 2 - ε ^ 2) ≤
      predBracket μ (pathFiltration hX.measurable) Y Y n ω := by
    have : ε ^ 2 * ((departureRange (fun j => X j ω) n).card : ℝ) ≤ ε ^ 2 * n :=
      mul_le_mul_of_nonneg_left hcard (sq_nonneg ε)
    linarith
  constructor
  · calc 1 / 2 - ε ^ 2 = (n : ℝ)⁻¹ * ((n : ℝ) * (1 / 2 - ε ^ 2)) := by
          field_simp
      _ ≤ (n : ℝ)⁻¹ * predBracket μ (pathFiltration hX.measurable) Y Y n ω :=
          mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hnpos.le)
  · calc (n : ℝ)⁻¹ * predBracket μ (pathFiltration hX.measurable) Y Y n ω
        ≤ (n : ℝ)⁻¹ * ((n : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left h2a (inv_nonneg.mpr hnpos.le)
      _ = 1 / 2 := by field_simp

/-- With probability at least `exp (-C₁ β²) / 4`, the first coordinate of the compensated position
`X_n + ε Σ_{x ∈ A_n} u_x` exceeds `c₁ β √n`: Lemma 9.1 (i) for the martingale `Y / √n`, whose
bracket lies between two positive constants on the whole probability space. -/
private lemma coord_deviation (hexp : exp_deviation.{u}) {ε : ℝ} (hε0 : 0 < ε)
    (hεd : ε < 1 / ((2 : ℕ) : ℝ)) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site 2), IsCERW μ ε X → ∀ n : ℕ, 1 ≤ n → ∀ β : ℝ, C₁ ≤ β →
        β * (2 / Real.sqrt n) ≤ c₁ →
        ENNReal.ofReal (Real.exp (-(C₁ * β ^ 2)) / 4) ≤
          μ {ω | c₁ * β * Real.sqrt n ≤ ((X n ω 0 : ℤ) : ℝ) +
            ε * ∑ x ∈ departureRange (fun j => X j ω) n, (unitDir (toSpace x)) 0} := by
  have hεhalf : ε < 1 / 2 := by simpa using hεd
  have hc0 : 0 < 1 / 2 - ε ^ 2 := by nlinarith
  obtain ⟨c₁, C₁, hc₁, hC₁, H⟩ :=
    hexp (1 / 2 - ε ^ 2) (1 / 2) hc0 (by nlinarith [sq_nonneg ε])
  refine ⟨c₁, C₁, hc₁, hC₁, ?_⟩
  intro Ω _ μ _ X hX n hn β hβ hβb
  obtain ⟨Y, hYm, hY0, hYinc, -, hYform, hYbr⟩ := exists_coord_martingale hε0 hεd hX
  have hn0 : 0 < n := hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  have hinc : ∀ t ω, |((Real.sqrt n)⁻¹ • Y) (t + 1) ω - ((Real.sqrt n)⁻¹ • Y) t ω| ≤
      2 / Real.sqrt n := by
    intro t ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hs), ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (hYinc t ω) hs.le
  have hbr := bracket_rescaled_bounds hX hYbr hn
  have hmain := (H μ (pathFiltration hX.measurable) 1 n one_pos hn0 (2 / Real.sqrt n) 0 0
    (div_pos two_pos hs) le_rfl le_rfl zero_le_one (fun _ => (Real.sqrt n)⁻¹ • Y)
    (fun _ => hYm.smul _) (fun _ ω => by simp [hY0]) (fun _ t _ ω => hinc t ω)
    Set.univ MeasurableSet.univ (by simp)
    (fun _ => by filter_upwards [hbr] with ω hω _ using hω) β hβ hβb).1 0
  have hF := hmain.1
  rw [sub_zero] at hF
  have hle : ENNReal.ofReal (Real.exp (-(C₁ * β ^ 2)) / 4) ≤
      μ {ω | c₁ * β ≤ ((fun _ : Fin 1 => (Real.sqrt n)⁻¹ • Y) 0) n ω} :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hF
  refine hle.trans (measure_mono_ae ?_)
  filter_upwards [hYform] with ω hω hmem
  have hmem' : c₁ * β ≤ (Real.sqrt n)⁻¹ * Y n ω := hmem
  have h2 : c₁ * β * Real.sqrt n ≤ Y n ω := by
    calc c₁ * β * Real.sqrt n ≤ ((Real.sqrt n)⁻¹ * Y n ω) * Real.sqrt n :=
          mul_le_mul_of_nonneg_right hmem' hs.le
      _ = Y n ω := by field_simp
  rw [hω n] at h2
  exact h2

/-! ### The pathwise lower bound on the width -/

/-- In the plane the inner radius exceeds the outer radius by at most one: the lattice site
`(⌊R⌋ + 1, 0)` has norm at most `R + 1` and norm above `R`. -/
private lemma innerRadius_le_maxRadius_add_one (x : ℕ → Site 2) (n : ℕ) :
    innerRadius x n ≤ maxRadius x n + 1 := by
  by_contra hcon
  have hlt : maxRadius x n + 1 < innerRadius x n := not_le.mp hcon
  have hR0 : 0 ≤ maxRadius x n := maxRadius_nonneg x n
  set k : ℕ := ⌊maxRadius x n⌋₊ + 1 with hk
  set s : Site 2 := Pi.single (0 : Fin 2) ((k : ℕ) : ℤ) with hs
  have hnorm : euclidNorm s = k := by
    simp only [euclidNorm, hs, Fin.sum_univ_two, Pi.single_apply]
    simp
  have hk1 : (k : ℝ) ≤ maxRadius x n + 1 := by
    rw [hk]
    push_cast
    linarith [Nat.floor_le hR0]
  have hk2 : maxRadius x n < k := by
    rw [hk]
    push_cast
    exact Nat.lt_floor_add_one _
  have hmem : s ∈ departureRange x n :=
    mem_departureRange_of_lt_innerRadius (by rw [hnorm]; linarith)
  have := euclidNorm_le_maxRadius_of_mem hmem
  rw [hnorm] at this
  linarith

/-- If the first coordinate of the compensated position exceeds `T + M` and the outer radius is at
most `M`, then the difference of the radii is at least `T / (ε (2 M + 7)) - 1`: the sum of the
directions over the range is bounded by the width of the annulus. -/
private lemma width_ge_of_dev {x : ℕ → Site 2} {n : ℕ} {ε T M : ℝ} (hε : 0 < ε)
    (hM : maxRadius x n ≤ M)
    (hdev : T + M ≤ ((x n 0 : ℤ) : ℝ) +
      ε * ∑ z ∈ departureRange x n, (unitDir (toSpace z)) 0) :
    T / (ε * (2 * M + 7)) - 1 ≤ maxRadius x n - innerRadius x n := by
  have hR0 : 0 ≤ maxRadius x n := maxRadius_nonneg x n
  have hρ0 : 0 ≤ innerRadius x n := innerRadius_nonneg x n
  have hρR := innerRadius_le_maxRadius_add_one x n
  have hG := abs_sum_dir_le (departureRange x n) hρ0 hR0
    (fun z hz => mem_departureRange_of_lt_innerRadius hz)
    (fun z hz => euclidNorm_le_maxRadius_of_mem hz)
  have hx0 : ((x n 0 : ℤ) : ℝ) ≤ maxRadius x n :=
    (le_abs_self _).trans ((abs_coord_le_euclidNorm (x n) 0).trans
      (euclidNorm_le_maxRadius x le_rfl))
  set V := ∑ z ∈ departureRange x n, (unitDir (toSpace z)) 0 with hV
  have hεV : T ≤ ε * V := by linarith
  have hw : 0 ≤ maxRadius x n - innerRadius x n + 1 := by linarith
  have h1 : (maxRadius x n - innerRadius x n + 1) * (maxRadius x n + innerRadius x n + 6) ≤
      (maxRadius x n - innerRadius x n + 1) * (2 * M + 7) :=
    mul_le_mul_of_nonneg_left (by linarith) hw
  have h2 : T ≤ (maxRadius x n - innerRadius x n + 1) * (ε * (2 * M + 7)) := by
    calc T ≤ ε * V := hεV
      _ ≤ ε * ((maxRadius x n - innerRadius x n + 1) * (2 * M + 7)) :=
          mul_le_mul_of_nonneg_left ((le_abs_self V).trans (hG.trans h1)) hε.le
      _ = (maxRadius x n - innerRadius x n + 1) * (ε * (2 * M + 7)) := by ring
  have hpos : 0 < ε * (2 * M + 7) := mul_pos hε (by linarith)
  have h3 : T / (ε * (2 * M + 7)) ≤ maxRadius x n - innerRadius x n + 1 := by
    rw [div_le_iff₀ hpos]
    exact h2
  linarith

/-- The arithmetic of the width bound: with `q = n^(1/6)`, `ℓ = log n`, `r_n = K q²`, a path with
`max_j |X_j| ≤ C_b q²` and first coordinate of the compensated position at least `c₁ a √ℓ q³`
has width at least `c √(r_n log n)` for the explicit constant `c` below, once `q √ℓ` is large. -/
private lemma width_ge_of_large {x : ℕ → Site 2} {n : ℕ} {ε c₁ a C_b K q ℓ : ℝ}
    (hε : 0 < ε) (hc₁ : 0 < c₁) (ha : 0 < a) (hCb : 0 < C_b) (hK : 0 < K)
    (hq1 : 1 ≤ q) (hℓ1 : 1 ≤ ℓ)
    (h5 : 2 * C_b ≤ c₁ * a * (Real.sqrt ℓ * q))
    (h6 : 2 ≤ c₁ * a / (2 * ε * (2 * C_b + 7)) * (Real.sqrt ℓ * q))
    (hM : maxRadius x n ≤ C_b * q ^ 2)
    (hdev : c₁ * (a * Real.sqrt ℓ) * q ^ 3 ≤ ((x n 0 : ℤ) : ℝ) +
      ε * ∑ z ∈ departureRange x n, (unitDir (toSpace z)) 0) :
    c₁ * a / (2 * ε * (2 * C_b + 7)) / (2 * Real.sqrt K) * Real.sqrt (K * q ^ 2 * ℓ) ≤
      maxRadius x n - innerRadius x n := by
  set L := Real.sqrt ℓ with hL
  have hq0 : 0 < q := by linarith
  have hD : 0 < 2 * C_b + 7 := by linarith
  set κ := c₁ * a / (2 * ε * (2 * C_b + 7)) with hκ
  have hκpos : 0 < κ := div_pos (mul_pos hc₁ ha) (by positivity)
  set T := c₁ * a * L * q ^ 3 / 2 with hT
  have hdev' : T + C_b * q ^ 2 ≤ ((x n 0 : ℤ) : ℝ) +
      ε * ∑ z ∈ departureRange x n, (unitDir (toSpace z)) 0 := by
    have e1 : 2 * C_b * q ^ 2 ≤ c₁ * a * (L * q) * q ^ 2 :=
      mul_le_mul_of_nonneg_right h5 (sq_nonneg q)
    have e2 : c₁ * (a * L) * q ^ 3 = c₁ * a * (L * q) * q ^ 2 := by ring
    have e3 : T = c₁ * a * (L * q) * q ^ 2 / 2 := by rw [hT]; ring
    linarith
  have hpath := width_ge_of_dev hε hM hdev'
  have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq1
  have hpos : 0 < ε * (2 * (C_b * q ^ 2) + 7) := mul_pos hε (by positivity)
  have hmain : κ * (L * q) ≤ T / (ε * (2 * (C_b * q ^ 2) + 7)) := by
    rw [le_div_iff₀ hpos]
    have e3 : 2 * (C_b * q ^ 2) + 7 ≤ (2 * C_b + 7) * q ^ 2 := by nlinarith
    have e4 : κ * ε * (2 * C_b + 7) = c₁ * a / 2 := by rw [hκ]; field_simp
    have hcoef : 0 ≤ κ * (L * q) * ε := by
      have : 0 ≤ L := Real.sqrt_nonneg ℓ
      positivity
    calc κ * (L * q) * (ε * (2 * (C_b * q ^ 2) + 7))
        = (κ * (L * q) * ε) * (2 * (C_b * q ^ 2) + 7) := by ring
      _ ≤ (κ * (L * q) * ε) * ((2 * C_b + 7) * q ^ 2) := mul_le_mul_of_nonneg_left e3 hcoef
      _ = (κ * ε * (2 * C_b + 7)) * (L * q) * q ^ 2 := by ring
      _ = T := by rw [e4, hT]; ring
  have hsqrt : Real.sqrt (K * q ^ 2 * ℓ) = Real.sqrt K * q * L := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK.le, Real.sqrt_sq hq0.le]
  have hKs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  calc κ / (2 * Real.sqrt K) * Real.sqrt (K * q ^ 2 * ℓ)
      = κ * (L * q) / 2 := by rw [hsqrt]; field_simp
    _ ≤ T / (ε * (2 * (C_b * q ^ 2) + 7)) - 1 := by linarith
    _ ≤ maxRadius x n - innerRadius x n := hpath

/-! ### Arithmetic of the planar radius -/

/-- For `x ≥ 0`, the cube of `x^(1/6)` is `√x`, and its square is `x^(1/3)`. -/
private lemma rpow_sixth_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 6)) ^ 2 = x ^ ((1 : ℝ) / 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- For `x ≥ 0`, the cube of `x^(1/6)` is `√x`. -/
private lemma rpow_sixth_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 6)) ^ 3 = Real.sqrt x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]
  norm_num

/-- The radius `r_n` of the statement in the plane is `K (n^(1/6))²` with `K` a positive
constant: the volume of the unit disk is `π`. -/
private lemma planar_radius_eq {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) =
      (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := by
  have hvol : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal = Real.pi := by
    simp [EuclideanSpace.volume_ball_fin_two, Real.pi_pos.le]
  rw [hvol, rpow_sixth_sq (Nat.cast_nonneg n)]
  have h : (((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε * Real.pi) =
      3 / (4 * ε * Real.pi) * n := by
    push_cast
    field_simp
    ring
  have h3 : ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) = (1 : ℝ) / 3 := by norm_num
  rw [h, h3, Real.mul_rpow (by positivity) (Nat.cast_nonneg n)]

/-! ### The outer radius and asymptotics in `n` -/

/-- The proved coarse bounds give `max_{j ≤ n} |X_j| ≤ C n^(1/3)` with probability at least
`1 - C n^(-p)`, for every `n ≥ 2`; here `n^(1/3)` is written `(n^(1/6))²`. -/
private lemma coarse_radius_bound {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ)) {p : ℝ}
    (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : ℕ → Ω → Site 2), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | C * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 < maxRadius (fun j => X j ω) n} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  obtain ⟨c, C, -, hC, h⟩ := CERW.Frozen.coarse_bounds.{u} (d := 2) le_rfl ε hε0 hεd p hp
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ _ X hX n hn
  have h' := h μ X hX n hn
  dsimp only at h'
  refine le_trans (measure_mono ?_) h'
  intro ω hω hcon
  have h6 := hcon.2.2.2.2.2
  have hN : (n : ℝ) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) = ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := by
    rw [rpow_sixth_sq (Nat.cast_nonneg n)]
    norm_num
  rw [hN] at h6
  exact absurd h6 (not_le.mpr hω)

/-- `√(log n)` is eventually at least any given bound. -/
private lemma eventually_sqrt_log_ge (Λ : ℝ) :
    ∀ᶠ n : ℕ in atTop, Λ ≤ Real.sqrt (Real.log n) := by
  have h : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually_ge_atTop (Λ ^ 2)] with n hn
  exact (le_abs_self Λ).trans (Real.abs_le_sqrt hn)

/-- `√(log n) / √n` is eventually at most any positive bound. -/
private lemma eventually_sqrt_log_div_sqrt_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Real.sqrt (Real.log n) / Real.sqrt n ≤ η := by
  have h := Real.isLittleO_log_id_atTop.def (c := η ^ 2) (by positivity)
  have h' : ∀ᶠ n : ℕ in atTop, ‖Real.log (n : ℝ)‖ ≤ η ^ 2 * ‖(n : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1'
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hnpos.le] at hn
  rw [← Real.sqrt_div hlog, Real.sqrt_le_iff]
  refine ⟨hη.le, ?_⟩
  rw [div_le_iff₀ hnpos]
  exact hn

/-- `n ^ s` is eventually at least any given bound, for `s > 0`. -/
private lemma eventually_rpow_ge {s : ℝ} (hs : 0 < s) (Λ : ℝ) :
    ∀ᶠ n : ℕ in atTop, Λ ≤ (n : ℝ) ^ s :=
  ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop Λ

/-- `n^(1/6) √(log n)` is eventually at least any given bound. -/
private lemma eventually_q_mul_sqrt_log_ge (Λ : ℝ) :
    ∀ᶠ n : ℕ in atTop, Λ ≤ (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt (Real.log n) := by
  filter_upwards [eventually_rpow_ge (s := (1 : ℝ) / 6) (by norm_num) Λ,
    eventually_sqrt_log_ge 1] with n h1 h2
  have hq : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  exact h1.trans (le_mul_of_one_le_right hq h2)

/-! ### The probability arithmetic -/

/-- If `F ⊆ E ∪ B` and `μ F` and `μ B` are controlled, then `μ E` is at least `w`. -/
private lemma measure_ge_of_subset_union {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E F B : Set Ω} {A Bv w : ℝ} (hsub : F ⊆ E ∪ B)
    (hF : ENNReal.ofReal A ≤ μ F) (hB : μ B ≤ ENNReal.ofReal Bv) (hA : 0 ≤ A) (hBv : 0 ≤ Bv)
    (hw : w ≤ A - Bv) : ENNReal.ofReal w ≤ μ E := by
  have hchain : ENNReal.ofReal A ≤ μ E + ENNReal.ofReal Bv :=
    hF.trans ((measure_mono hsub).trans ((measure_union_le E B).trans (add_le_add le_rfl hB)))
  have hne : μ E + ENNReal.ofReal Bv ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
  have h1 := ENNReal.toReal_mono hne hchain
  rw [ENNReal.toReal_ofReal hA, ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hBv] at h1
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr (by linarith)

/-- With `C₁ a² = p/2`, the exponential `exp (-(C₁ β²))` at `β = a √(log x)` is `x^(-(p/2))`. -/
private lemma exp_eq_rpow {C₁ a p x : ℝ} (haC : C₁ * a ^ 2 = p / 2) (hx : 1 ≤ x) :
    Real.exp (-(C₁ * (a * Real.sqrt (Real.log x)) ^ 2)) = x ^ (-(p / 2)) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : C₁ * (a * Real.sqrt (Real.log x)) ^ 2 = p / 2 * Real.log x := by
    rw [mul_pow, Real.sq_sqrt hlog, ← haC]
    ring
  rw [h1, Real.rpow_def_of_pos (by linarith)]
  congr 1
  ring

/-- The last inequality of the probability bound: `x^(-p) ≤ x^(-p/2)/4 - C x^(-p)` once
`x^(p/2) ≥ 4 (C + 1)`. -/
private lemma rpow_arith {x p C : ℝ} (hx : 0 < x) (h : 4 * (C + 1) ≤ x ^ (p / 2)) :
    x ^ (-p) ≤ x ^ (-(p / 2)) / 4 - C * x ^ (-p) := by
  have hadd : x ^ (-(p / 2)) = x ^ (-p) * x ^ (p / 2) := by
    rw [← Real.rpow_add hx]
    ring_nf
  have hw : 0 < x ^ (-p) := Real.rpow_pos_of_pos hx _
  have h2 : x ^ (-p) * (4 * (C + 1)) ≤ x ^ (-p) * x ^ (p / 2) :=
    mul_le_mul_of_nonneg_left h hw.le
  rw [hadd]
  linarith

/-! ### The polynomial lower bound -/

/-- Theorem 1.3 (iv) (a): the polynomial lower bound for the difference of the radii. -/
theorem sharp_width_poly_of (hexp : exp_deviation.{u}) :
    ∀ {d : ℕ} (_ : d = 2),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      (∀ p : ℝ, 0 < p → ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
        ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, n₀ ≤ n →
          let E : Set Ω := {ω | c * Real.sqrt (r n * Real.log n)
            ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n}
          MeasurableSet E ∧ ENNReal.ofReal ((n : ℝ) ^ (-p)) ≤ μ E) := by
  intro d hd
  subst hd
  intro ωd ε hε0 hε1 r p hp
  obtain ⟨c₁, C₁, hc₁, hC₁, hdev⟩ := coord_deviation hexp hε0 hε1
  obtain ⟨C_b, hCb, hcoarse⟩ := coarse_radius_bound.{u} hε0 hε1 hp
  set a : ℝ := Real.sqrt (p / (2 * C₁)) with ha_def
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have haC : C₁ * a ^ 2 = p / 2 := by
    rw [ha_def, Real.sq_sqrt (by positivity)]
    field_simp
  set K : ℝ := (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) with hK_def
  have hK : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  have hr : ∀ n : ℕ, r n = K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := fun n => planar_radius_eq hε0 n
  set κ : ℝ := c₁ * a / (2 * ε * (2 * C_b + 7)) with hκ_def
  have hκ : 0 < κ := div_pos (mul_pos hc₁ ha) (by positivity)
  set c : ℝ := κ / (2 * Real.sqrt K) with hc_def
  have hc : 0 < c := div_pos hκ (mul_pos two_pos (Real.sqrt_pos.mpr hK))
  have hev := (eventually_ge_atTop 3).and ((eventually_sqrt_log_ge (C₁ / a)).and
    ((eventually_sqrt_log_div_sqrt_le (η := c₁ / (2 * a)) (by positivity)).and
      ((eventually_rpow_ge (s := p / 2) (by positivity) (4 * (C_b + 1))).and
        ((eventually_q_mul_sqrt_log_ge (max (2 * C_b / (c₁ * a)) (2 / κ))).and
          (eventually_sqrt_log_ge 1)))))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨c, hc, n₀, ?_⟩
  intro Ω _ μ _ X hX n hn E
  refine ⟨measurableSet_le measurable_const (measurable_width hX.measurable n), ?_⟩
  obtain ⟨h3, hLge, hdiv, hpow, hqL, hL1⟩ := hn₀ n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  have hq1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := Real.one_le_rpow hn1 (by norm_num)
  have hℓ1 : 1 ≤ Real.log n := by
    have := Real.sq_sqrt (Real.log_nonneg hn1)
    nlinarith
  have hsqrtn : Real.sqrt n = ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 :=
    (rpow_sixth_cube (Nat.cast_nonneg n)).symm
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hβ1 : C₁ ≤ a * Real.sqrt (Real.log n) := by
    have := (div_le_iff₀ ha).mp hLge
    linarith
  have hβ2 : a * Real.sqrt (Real.log n) * (2 / Real.sqrt n) ≤ c₁ := by
    calc a * Real.sqrt (Real.log n) * (2 / Real.sqrt n)
        = 2 * a * (Real.sqrt (Real.log n) / Real.sqrt n) := by ring
      _ ≤ 2 * a * (c₁ / (2 * a)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = c₁ := by field_simp
  have hF := hdev μ X hX n (by omega) _ hβ1 hβ2
  rw [exp_eq_rpow haC hn1] at hF
  have hBad := hcoarse μ X hX n (by omega)
  have h5 : 2 * C_b ≤ c₁ * a * (Real.sqrt (Real.log n) * (n : ℝ) ^ ((1 : ℝ) / 6)) := by
    have h := (le_max_left _ _).trans hqL
    rw [div_le_iff₀ (mul_pos hc₁ ha)] at h
    calc 2 * C_b ≤ (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt (Real.log n) * (c₁ * a) := h
      _ = _ := by ring
  have h6 : 2 ≤ κ * (Real.sqrt (Real.log n) * (n : ℝ) ^ ((1 : ℝ) / 6)) := by
    have h := (le_max_right _ _).trans hqL
    rw [div_le_iff₀ hκ] at h
    calc 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 6) * Real.sqrt (Real.log n) * κ := h
      _ = _ := by ring
  have hsub : {ω | c₁ * (a * Real.sqrt (Real.log n)) * Real.sqrt n ≤ ((X n ω 0 : ℤ) : ℝ) +
        ε * ∑ x ∈ departureRange (fun j => X j ω) n, (unitDir (toSpace x)) 0} ⊆
      E ∪ {ω | C_b * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 < maxRadius (fun j => X j ω) n} := by
    intro ω hω
    by_cases hB : C_b * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 < maxRadius (fun j => X j ω) n
    · exact Or.inr hB
    · left
      have hM := not_lt.mp hB
      have hdev' : c₁ * (a * Real.sqrt (Real.log n)) * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 ≤
          ((X n ω 0 : ℤ) : ℝ) +
            ε * ∑ x ∈ departureRange (fun j => X j ω) n, (unitDir (toSpace x)) 0 := by
        have h := hω
        rw [hsqrtn] at h
        exact h
      have hw := width_ge_of_large (x := fun j => X j ω) (n := n) hε0 hc₁ ha hCb hK hq1
        hℓ1 h5 h6 hM hdev'
      show c * Real.sqrt (r n * Real.log n) ≤
        maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n
      rw [hr n]
      exact hw
  exact measure_ge_of_subset_union hsub hF hBad (by positivity) (by positivity)
    (rpow_arith hnpos hpow)


/-! ### Interface L: the law of the iterated logarithm -/

/-- If `B ≥ (1-s)n/2` with `s ≤ 1/4` and `n` is large, then `2 B log log B ≥ (1-s)² n log log n`. -/
private lemma two_mul_loglog_ge {s n B L : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hn0 : 0 < n)
    (hL : L = Real.log (Real.log n)) (T1 : 2 * Real.log 4 ≤ Real.log n)
    (T2 : Real.log 2 ≤ s * L) (T3 : 1 ≤ L) (hB : (1 - s) / 2 * n ≤ B) :
    (1 - s) ^ 2 * (n * L) ≤ 2 * B * Real.log (Real.log B) := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogn : 0 < Real.log n := by linarith
  have hBn : n / 4 ≤ B := by
    have h1 : n / 4 ≤ (1 - s) / 2 * n := by nlinarith
    linarith
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) hBn
  have hlogB : Real.log n / 2 ≤ Real.log B := by
    have h1 : Real.log (n / 4) ≤ Real.log B := Real.log_le_log (by positivity) hBn
    rw [Real.log_div hn0.ne' (by norm_num)] at h1
    linarith
  have hll : L - Real.log 2 ≤ Real.log (Real.log B) := by
    have h1 : Real.log (Real.log n / 2) ≤ Real.log (Real.log B) :=
      Real.log_le_log (by positivity) hlogB
    rw [Real.log_div hlogn.ne' (by norm_num), ← hL] at h1
    exact h1
  have hll' : (1 - s) * L ≤ Real.log (Real.log B) := by nlinarith
  have hL0 : 0 ≤ (1 - s) * L := by
    have : 0 ≤ 1 - s := by linarith
    exact mul_nonneg this (by linarith)
  have hBnn : 0 ≤ (1 - s) / 2 * n := by
    have : 0 ≤ 1 - s := by linarith
    positivity
  calc (1 - s) ^ 2 * (n * L) = 2 * ((1 - s) / 2 * n) * ((1 - s) * L) := by ring
    _ ≤ 2 * B * Real.log (Real.log B) :=
        mul_le_mul (by linarith) hll' hL0 (by linarith)

/-- For `n = q² r³`, `√(n L) = q r √(r L)`. -/
private lemma sqrt_mul_eq {q r n L : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hn : n = q ^ 2 * r ^ 3) :
    Real.sqrt (n * L) = q * r * Real.sqrt (r * L) := by
  have h : n * L = (q * r) ^ 2 * (r * L) := by rw [hn]; ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hq hr)]


/-- The lower bound for the bracket from the bound on the cardinality of the range. -/
private lemma bracket_lower {ε s q n rn a B : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hn : n = q ^ 2 * rn ^ 3) (h1 : 1 ≤ rn) (h2 : 50 * ε ^ 2 ≤ s * q ^ 2 * rn)
    (hBa : n / 2 - ε ^ 2 * a ≤ B) (ha : a ≤ (2 * ((1 + s) * rn) + 1) ^ 2) :
    (1 - s) / 2 * n ≤ B := by
  have hrn0 : 0 < rn := lt_of_lt_of_le one_pos h1
  have hsr : s * rn ≤ 1 / 4 * rn := mul_le_mul_of_nonneg_right hs hrn0.le
  have h25 : 2 * ((1 + s) * rn) + 1 ≤ 5 * rn := by nlinarith
  have hsq : (2 * ((1 + s) * rn) + 1) ^ 2 ≤ (5 * rn) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h25 2
  have hεa : ε ^ 2 * a ≤ ε ^ 2 * (5 * rn) ^ 2 :=
    mul_le_mul_of_nonneg_left (ha.trans hsq) (sq_nonneg ε)
  have hfin : ε ^ 2 * (5 * rn) ^ 2 ≤ s * n / 2 := by
    calc ε ^ 2 * (5 * rn) ^ 2 = rn ^ 2 * (50 * ε ^ 2) / 2 := by ring
      _ ≤ rn ^ 2 * (s * q ^ 2 * rn) / 2 := by
          have := mul_le_mul_of_nonneg_left h2 (sq_nonneg rn)
          linarith
      _ = s * n / 2 := by rw [hn]; ring
  linarith


/-- The real arithmetic behind the planar width bound: from the lower bound of the law of the
iterated logarithm for `Y_n = X_n,1 + ε V_n`, the bound `|V_n| ≤ (R-ρ+1)(R+ρ+6)` and the
bounds on the two radii, the width `R - ρ` is at least `(κ - δ) √(r log log n)`. -/
private lemma width_core {ε κ δ s q n rn L y B a x0 R ρ V : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hδ : 0 < δ) (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hsκ : 5 * s * κ ≤ δ / 2) (hq : q = 2 * ε * κ) (hn : n = q ^ 2 * rn ^ 3) (hn0 : 0 < n)
    (hL : L = Real.log (Real.log n))
    (T1 : 2 * Real.log 4 ≤ Real.log n) (T2 : Real.log 2 ≤ s * L) (T3 : 1 ≤ L)
    (h1 : 1 ≤ rn) (h2 : 50 * ε ^ 2 ≤ s * q ^ 2 * rn) (h3 : 9 ≤ s ^ 2 * q ^ 2 * rn)
    (h4 : 9 ≤ 2 * s * rn) (h5 : 4 ≤ δ ^ 2 * rn)
    (hBa : n / 2 - ε ^ 2 * a ≤ B) (ha : a ≤ (2 * ((1 + s) * rn) + 1) ^ 2)
    (hy : y = x0 + ε * V) (hx0 : |x0| ≤ R) (hV : |V| ≤ (R - ρ + 1) * (R + ρ + 6))
    (hR : R ≤ (1 + s) * rn + 1) (hρ0 : 0 ≤ ρ)
    (hyB : (1 - s) * Real.sqrt (2 * B * Real.log (Real.log B)) ≤ y) :
    (κ - δ) * Real.sqrt (rn * L) ≤ R - ρ := by
  have hq0 : 0 < q := by rw [hq]; positivity
  have hrn0 : 0 < rn := lt_of_lt_of_le one_pos h1
  have hL0 : 0 < L := lt_of_lt_of_le one_pos T3
  have hs1 : 0 ≤ 1 - s := by linarith
  set W := Real.sqrt (rn * L) with hW
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hT : Real.sqrt (n * L) = q * rn * W := sqrt_mul_eq hq0.le hrn0.le hn
  -- the lower bound for the bracket and the iterated logarithm
  have hB : (1 - s) / 2 * n ≤ B := bracket_lower hs0 hs hn h1 h2 hBa ha
  have hbig := two_mul_loglog_ge hs0 hs hn0 hL T1 T2 T3 hB
  have hsqrt : (1 - s) * Real.sqrt (n * L) ≤ Real.sqrt (2 * B * Real.log (Real.log B)) := by
    have h : (1 - s) * Real.sqrt (n * L) = Real.sqrt ((1 - s) ^ 2 * (n * L)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs1]
    rw [h]
    exact Real.sqrt_le_sqrt hbig
  have hyT : (1 - s) * ((1 - s) * (q * rn * W)) ≤ y := by
    have := mul_le_mul_of_nonneg_left hsqrt hs1
    rw [hT] at this
    exact this.trans hyB
  -- the outer radius is small compared with the scale
  have hsqW : 3 ≤ s * q * W := by
    have hsq0 : 0 ≤ s * q * W := by positivity
    have hsq2 : (s * q * W) ^ 2 = s ^ 2 * q ^ 2 * (rn * L) := by
      rw [mul_pow, hW, Real.sq_sqrt (by positivity)]
      ring
    have h9 : (3 : ℝ) ^ 2 ≤ (s * q * W) ^ 2 := by
      rw [hsq2]
      have : s ^ 2 * q ^ 2 * rn ≤ s ^ 2 * q ^ 2 * (rn * L) := by
        have h0 : 0 ≤ s ^ 2 * q ^ 2 * rn := by positivity
        calc s ^ 2 * q ^ 2 * rn = s ^ 2 * q ^ 2 * rn * 1 := by ring
          _ ≤ s ^ 2 * q ^ 2 * rn * L := mul_le_mul_of_nonneg_left T3 h0
          _ = s ^ 2 * q ^ 2 * (rn * L) := by ring
      norm_num
      linarith
    exact (pow_le_pow_iff_left₀ (by norm_num) hsq0 two_ne_zero).mp h9
  have hsr : s * rn ≤ 1 / 4 * rn := mul_le_mul_of_nonneg_right hs hrn0.le
  have hR3 : R ≤ 3 * rn := by linarith only [hR, hsr, h1]
  have hRT : R ≤ s * (q * rn * W) := by
    calc R ≤ 3 * rn := hR3
      _ ≤ (s * q * W) * rn := mul_le_mul_of_nonneg_right hsqW hrn0.le
      _ = s * (q * rn * W) := by ring
  -- the width
  have hρR : 0 ≤ R - ρ + 1 := by
    by_contra hneg
    have hneg := not_le.mp hneg
    have hR0 : 0 ≤ R := (abs_nonneg x0).trans hx0
    have : (R - ρ + 1) * (R + ρ + 6) < 0 := mul_neg_of_neg_of_pos hneg (by linarith only [hR0, hρ0])
    linarith [abs_nonneg V]
  have hD : R + ρ + 6 ≤ 2 * (1 + s) ^ 2 * rn := by
    have hρR' : ρ ≤ R + 1 := by linarith
    have h9 : 9 ≤ 2 * s * (1 + s) * rn := by
      have : 2 * s * rn ≤ 2 * s * (1 + s) * rn := by
        have h0 : 0 ≤ 2 * s * rn := by positivity
        calc 2 * s * rn = 2 * s * rn * 1 := by ring
          _ ≤ 2 * s * rn * (1 + s) := mul_le_mul_of_nonneg_left (by linarith) h0
          _ = 2 * s * (1 + s) * rn := by ring
      linarith
    have hid : 2 * (1 + s) * rn + 2 * s * (1 + s) * rn = 2 * (1 + s) ^ 2 * rn := by ring
    have hid2 : 2 * ((1 + s) * rn) = 2 * (1 + s) * rn := by ring
    linarith
  have hεV : (1 - s) * ((1 - s) * (q * rn * W)) - s * (q * rn * W) ≤ ε * |V| := by
    have h1 : ε * V ≤ ε * |V| := mul_le_mul_of_nonneg_left (le_abs_self V) hε.le
    have h2 : x0 ≤ R := (le_abs_self x0).trans hx0
    linarith only [h1, h2, hy, hyT, hRT]
  have hup : ε * |V| ≤ ε * ((R - ρ + 1) * (2 * (1 + s) ^ 2 * rn)) := by
    refine mul_le_mul_of_nonneg_left (hV.trans ?_) hε.le
    exact mul_le_mul_of_nonneg_left hD hρR
  have hkey : ((1 - s) * (1 - s) - s) * (2 * ε * rn) * (κ * W) ≤
      ((1 + s) ^ 2 * (R - ρ + 1)) * (2 * ε * rn) := by
    have h := hεV.trans hup
    rw [hq] at h
    linarith only [h]
  have hpos : 0 < 2 * ε * rn := by positivity
  have hkey' : ((1 - s) * (1 - s) - s) * (κ * W) ≤ (1 + s) ^ 2 * (R - ρ + 1) := by
    have := hkey
    rw [mul_comm ((1 + s) ^ 2 * (R - ρ + 1)) (2 * ε * rn),
      show ((1 - s) * (1 - s) - s) * (2 * ε * rn) * (κ * W) =
        (2 * ε * rn) * (((1 - s) * (1 - s) - s) * (κ * W)) by ring] at this
    exact le_of_mul_le_mul_left this hpos
  have hcoef : (1 - 5 * s) * (1 + s) ^ 2 ≤ (1 - s) * (1 - s) - s := by
    have hd : (1 - s) * (1 - s) - s - (1 - 5 * s) * (1 + s) ^ 2 = 10 * s ^ 2 + 5 * s ^ 3 := by
      ring
    have : 0 ≤ 10 * s ^ 2 + 5 * s ^ 3 := by positivity
    linarith only [hd, this]
  have hκW : 0 ≤ κ * W := by positivity
  have hfin : (1 - 5 * s) * (κ * W) ≤ R - ρ + 1 := by
    have h1 : (1 + s) ^ 2 * ((1 - 5 * s) * (κ * W)) ≤ (1 + s) ^ 2 * (R - ρ + 1) := by
      calc (1 + s) ^ 2 * ((1 - 5 * s) * (κ * W)) = ((1 - 5 * s) * (1 + s) ^ 2) * (κ * W) := by ring
        _ ≤ ((1 - s) * (1 - s) - s) * (κ * W) := mul_le_mul_of_nonneg_right hcoef hκW
        _ ≤ _ := hkey'
    exact le_of_mul_le_mul_left h1 (by positivity)
  have hδW : 1 ≤ δ / 2 * W := by
    have hW2 : W ^ 2 = rn * L := by rw [hW, Real.sq_sqrt (by positivity)]
    have hd0 : 0 ≤ δ / 2 * W := by positivity
    have h4' : (1 : ℝ) ^ 2 ≤ (δ / 2 * W) ^ 2 := by
      rw [mul_pow, hW2]
      have : δ ^ 2 * rn ≤ δ ^ 2 * (rn * L) := by
        calc δ ^ 2 * rn = δ ^ 2 * (rn * 1) := by ring
          _ ≤ δ ^ 2 * (rn * L) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left T3 hrn0.le)
            (sq_nonneg δ)
      linarith only [this, h5]
    exact (pow_le_pow_iff_left₀ (by norm_num) hd0 two_ne_zero).mp h4'
  have h5s : 5 * s * κ * W ≤ δ / 2 * W := mul_le_mul_of_nonneg_right hsκ hW0
  linarith only [hfin, hδW, h5s]


/-- The planar radius `r_n = (3n/(4 ε π))^{1/3}`. -/
private noncomputable def planarRadius (ε : ℝ) (n : ℕ) : ℝ :=
  (3 / (4 * ε * Real.pi) * n) ^ ((1 : ℝ) / 3)

/-- The volume of the planar unit disk is `π`. -/
private lemma volume_unit_ball_two :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal = Real.pi := by
  simp [EuclideanSpace.volume_ball_fin_two, Real.pi_pos.le]

/-- The radius of the statement, in the plane, is `planarRadius`. -/
private lemma radius_eq_planarRadius (ε : ℝ) (n : ℕ) :
    ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
      ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) = planarRadius ε n := by
  rw [volume_unit_ball_two, planarRadius]
  norm_num
  congr 1
  ring

/-- The planar radius is nonnegative. -/
private lemma planarRadius_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℕ) : 0 ≤ planarRadius ε n :=
  Real.rpow_nonneg (by positivity) _

/-- The cube of the planar radius is `3 n / (4 ε π)`. -/
private lemma planarRadius_cube {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    planarRadius ε n ^ 3 = 3 / (4 * ε * Real.pi) * n := by
  unfold planarRadius
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- The planar radius tends to infinity. -/
private lemma tendsto_planarRadius {ε : ℝ} (hε : 0 < ε) :
    Tendsto (planarRadius ε) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => 3 / (4 * ε * Real.pi) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp h1

/-- Eventually the planar radius exceeds any bound. -/
private lemma eventually_planarRadius_ge {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K ≤ planarRadius ε n :=
  (tendsto_planarRadius hε).eventually_ge_atTop K

/-- Eventually `log log n` exceeds any bound. -/
private lemma eventually_loglog_ge (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K ≤ Real.log (Real.log n) :=
  (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop)).eventually_ge_atTop K

/-- Eventually `log n` exceeds any bound. -/
private lemma eventually_log_ge (K : ℝ) : ∀ᶠ n : ℕ in atTop, K ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K


/-- The square of `κ = √(π/(3ε))` is `π/(3ε)`, so `q = 2εκ` satisfies `n = q² r_n³`. -/
private lemma nat_eq_sq_mul_cube {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (n : ℝ) = (2 * ε * Real.sqrt (Real.pi / (3 * ε))) ^ 2 * planarRadius ε n ^ 3 := by
  rw [planarRadius_cube hε, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- The deterministic width bound, valid for all large `n`, with constants depending only on
`ε`, `δ` and the slack `s`. -/
private lemma eventually_width {ε δ s : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hs0 : 0 < s)
    (hs : s ≤ 1 / 4) (hsκ : 5 * s * Real.sqrt (Real.pi / (3 * ε)) ≤ δ / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ y B a x0 R ρ V : ℝ,
      (n : ℝ) / 2 - ε ^ 2 * a ≤ B → a ≤ (2 * ((1 + s) * planarRadius ε n) + 1) ^ 2 →
      y = x0 + ε * V → |x0| ≤ R → |V| ≤ (R - ρ + 1) * (R + ρ + 6) →
      R ≤ (1 + s) * planarRadius ε n + 1 → 0 ≤ ρ →
      (1 - s) * Real.sqrt (2 * B * Real.log (Real.log B)) ≤ y →
      (Real.sqrt (Real.pi / (3 * ε)) - δ) *
        Real.sqrt (planarRadius ε n * Real.log (Real.log n)) ≤ R - ρ := by
  set κ : ℝ := Real.sqrt (Real.pi / (3 * ε)) with hκdef
  have hκ : 0 < κ := Real.sqrt_pos.mpr (by positivity)
  set q : ℝ := 2 * ε * κ with hqdef
  have hq0 : 0 < q := by positivity
  filter_upwards [eventually_ge_atTop 1, eventually_log_ge (2 * Real.log 4),
    eventually_loglog_ge (Real.log 2 / s), eventually_loglog_ge 1,
    eventually_planarRadius_ge hε 1,
    eventually_planarRadius_ge hε (50 * ε ^ 2 / (s * q ^ 2)),
    eventually_planarRadius_ge hε (9 / (s ^ 2 * q ^ 2)),
    eventually_planarRadius_ge hε (9 / (2 * s)),
    eventually_planarRadius_ge hε (4 / δ ^ 2)] with n hn1 T1 T2 T3 h1 h2 h3 h4 h5
  intro y B a x0 R ρ V hBa ha hy hx0 hV hR hρ0 hyB
  have hn0 : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  refine width_core hε hκ hδ hs0 hs hsκ rfl (nat_eq_sq_mul_cube hε n) hn0 rfl T1 ?_ T3 h1 ?_ ?_
    ?_ ?_ hBa ha hy hx0 hV hR hρ0 hyB
  · have := (div_le_iff₀ hs0).mp T2
    linarith only [this]
  · have := (div_le_iff₀ (by positivity)).mp h2
    linarith only [this]
  · have := (div_le_iff₀ (by positivity)).mp h3
    linarith only [this]
  · have := (div_le_iff₀ (by positivity)).mp h4
    linarith only [this]
  · have := (div_le_iff₀ (by positivity)).mp h5
    linarith only [this]


/-- `log log x / x → 0` as `x → ∞`. -/
private lemma tendsto_loglog_div :
    Tendsto (fun x : ℝ => Real.log (Real.log x) / x) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
    have h1 : 1 ≤ Real.log x := by
      have := Real.log_le_log (Real.exp_pos 1) hx
      rwa [Real.log_exp] at this
    exact div_nonneg (Real.log_nonneg h1) hx0.le
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos hx
    have h1 := Real.log_le_sub_one_of_pos hlog
    exact div_le_div_of_nonneg_right (by linarith) hx0.le

/-- The ratio hypothesis of Stout's law of the iterated logarithm holds for a bounded
increment bound whenever the bracket tends to infinity. -/
private lemma tendsto_bracket_ratio {x : ℕ → ℝ} (hx : Tendsto x atTop atTop) :
    Tendsto (fun n => 2 * Real.sqrt (Real.log (Real.log (max (x n) (Real.exp (Real.exp 1))))) /
      Real.sqrt (x n)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.log (Real.log (max t (Real.exp (Real.exp 1)))) / t)
      atTop (𝓝 0) := by
    refine tendsto_loglog_div.congr' ?_
    filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1))] with t ht
    rw [max_eq_left ht]
  have h1 := (h0.comp hx).sqrt.const_mul 2
  rw [Real.sqrt_zero, mul_zero] at h1
  refine h1.congr' ?_
  filter_upwards [hx.eventually_ge_atTop (Real.exp (Real.exp 1))] with n hn
  have h1e : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hlog : 1 ≤ Real.log (x n) := by
    have := Real.log_le_log (Real.exp_pos _) hn
    rw [Real.log_exp] at this
    linarith
  have hnn : 0 ≤ Real.log (Real.log (max (x n) (Real.exp (Real.exp 1)))) := by
    rw [max_eq_left hn]
    exact Real.log_nonneg hlog
  simp only [Function.comp]
  rw [Real.sqrt_div hnn, mul_div_assoc]


/-- Theorem 1.3 (iv) (b): the iterated logarithm for the difference of the radii. -/
private theorem width_lil (hshape : limit_shape.{u}) :
    ∀ {d : ℕ} (_ : d = 2) (_ : StoutLIL.{u}),
      let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
          (Real.sqrt (Real.pi / (3 * ε)) - δ) * Real.sqrt (r n * Real.log (Real.log n))
            ≤ CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n) := by
  intro d hd hS
  subst hd
  intro ωd ε hε0 hε1 r Ω _ μ _ X hX
  have hr : ∀ n : ℕ, r n = planarRadius ε n := fun n => radius_eq_planarRadius ε n
  have hε2 : ε < 1 / 2 := by simpa using hε1
  have hc : 0 < 1 / 2 - ε ^ 2 := by nlinarith
  obtain ⟨Y, hmart, hY0, hYinc, hYL2, hYform, hYbr⟩ := exists_coord_martingale hε0 hε1 hX
  -- the bracket tends to infinity, almost surely
  have hbr_inf : ∀ᵐ ω ∂μ, Tendsto
      (fun n => predBracket μ (pathFiltration hX.measurable) Y Y n ω) atTop atTop := by
    filter_upwards [hYbr] with ω hω
    refine tendsto_atTop_mono (fun n => ?_)
      ((tendsto_natCast_atTop_atTop.const_mul_atTop hc))
    have h1 := (hω n).2
    have h2 : ((departureRange (fun j => X j ω) n).card : ℝ) ≤ n := by
      exact_mod_cast CERW.Support.Occupation.card_departureRange_le (fun j => X j ω) n
    have h3 : ε ^ 2 * ((departureRange (fun j => X j ω) n).card : ℝ) ≤ ε ^ 2 * n :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg ε)
    linarith only [h1, h3]
  have hratio : ∀ᵐ ω ∂μ, Tendsto (fun n => (fun (_ : ℕ) (_ : Ω) => (2 : ℝ)) n ω *
      Real.sqrt (Real.log (Real.log (max
        (predBracket μ (pathFiltration hX.measurable) Y Y n ω) (Real.exp (Real.exp 1))))) /
      Real.sqrt (predBracket μ (pathFiltration hX.measurable) Y Y n ω)) atTop (𝓝 0) := by
    filter_upwards [hbr_inf] with ω hω
    exact tendsto_bracket_ratio hω
  have hStout := hS μ (pathFiltration hX.measurable) Y hmart hYL2 hY0 (fun _ _ => 2)
    (fun n => stronglyMeasurable_const) (ae_of_all _ fun ω n => hYinc n ω) hbr_inf hratio
  have hsteps : ∀ᵐ ω ∂μ, ∀ n, X (n + 1) ω - X n ω ∈ unitSteps 2 :=
    ae_all_iff.mpr (ae_sub_mem_unitSteps (by norm_num) hε0.le hε1 hX)
  have hsh : ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
      (↑(departureRange (fun j => X j ω) n) : Set (Site 2)) ⊆
        {x | euclidNorm x < (1 + η) * planarRadius ε n} := by
    have h := hshape (le_refl 2) hε0 hε1 μ X hX
    simp only [radius_eq_planarRadius] at h
    filter_upwards [h] with ω hω η hη0 hη1
    exact (hω.1 η hη0 hη1).mono fun n hn => hn.2
  filter_upwards [hStout, hsteps, hYform, hYbr, hsh] with ω hSω hst hform hbr hshω δ hδ
  simp only [hr]
  set κ : ℝ := Real.sqrt (Real.pi / (3 * ε)) with hκdef
  have hκ : 0 < κ := Real.sqrt_pos.mpr (by positivity)
  set s : ℝ := min (1 / 4) (δ / (10 * κ)) with hsdef
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 / 4 := min_le_left _ _
  have hsκ : 5 * s * κ ≤ δ / 2 := by
    have h1 : s ≤ δ / (10 * κ) := min_le_right _ _
    calc 5 * s * κ ≤ 5 * (δ / (10 * κ)) * κ := by gcongr
      _ = δ / 2 := by field_simp; ring
  have hfreq := (hSω s hs0).2
  have hsub := hshω s hs0 (by linarith)
  have hev := eventually_width hε0 hδ hs0 hs1 hsκ
  refine (hfreq.and_eventually ((hsub.and hev).and (eventually_ge_atTop 1))).mono ?_
  rintro n ⟨hyB, ⟨hsubn, hevn⟩, hn1⟩
  set A := departureRange (fun j => X j ω) n with hA
  have hrn0 := planarRadius_nonneg hε0 n
  have hAball : ∀ x ∈ A, euclidNorm x ≤ (1 + s) * planarRadius ε n := fun x hx =>
    (Set.mem_setOf_eq.mp (hsubn (Finset.mem_coe.mpr hx))).le
  have hcard : (A.card : ℝ) ≤ (2 * ((1 + s) * planarRadius ε n) + 1) ^ 2 := by
    have hsubset : A ⊆ LatticeProb.ballFinset 2 ((1 + s) * planarRadius ε n) := fun x hx =>
      LatticeProb.mem_ballFinset_iff.mpr (hAball x hx)
    have h1 : (A.card : ℝ) ≤ ((LatticeProb.ballFinset 2 ((1 + s) * planarRadius ε n)).card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hsubset
    exact h1.trans (LatticeProb.card_ballFinset_le 2 (by positivity))
  have hx0 : |((X n ω 0 : ℤ) : ℝ)| ≤ CERW.maxRadius (fun j => X j ω) n :=
    (abs_coord_le_euclidNorm (X n ω) 0).trans
      (CERW.euclidNorm_le_maxRadius (fun j => X j ω) le_rfl)
  have hV := abs_sum_dir_le A (innerRadius_nonneg _ n) (maxRadius_nonneg _ n)
    (fun x hx => mem_departureRange_of_lt_innerRadius hx)
    (fun x hx => euclidNorm_le_maxRadius_of_mem hx)
  have hR := maxRadius_le_add_one hn1 hAball (fun j _ => hst j)
  exact hevn _ _ _ _ _ _ _ (hbr n).2 hcard (hform n) hx0 hV hR (innerRadius_nonneg _ n) hyB


/-- The width of the range in the plane is at least `c √(r_n log n)` with polynomial probability,
and at least `√(π/(3ε)) √(r_n log log n)` infinitely often. -/
theorem sharp_width_of (hshape : limit_shape.{u})
    (hexp : exp_deviation.{u}) : sharp_width.{u} := by
  intro d hd hS ωd ε hε0 hε1 r
  exact ⟨sharp_width_poly_of hexp hd ε hε0 hε1, width_lil hshape hd hS ε hε0 hε1⟩

end CERW.Support.Lower
