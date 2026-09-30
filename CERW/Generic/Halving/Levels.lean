import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Dyadic halving of a nonincreasing tail on a grid

A nonincreasing, nonnegative function `F` is sampled on the grid `r₁ + 2bj`. Suppose that at
each grid point with `F(r - b) ≤ A`, either `F(r + b) ≤ A/2` or `F` drops by at least `A/K`
across the grid cell. Then `F` is halved within `⌈K⌉ + 1` grid steps. Iterating over dyadic
levels drives `F` below a floor `Λ` (`eq:halving-K`, `eq:halving-cost`, and the tail halving
of the outer bound). The per-level budget `K` may depend on the level.
-/

namespace CERW.Generic.Halving

/-- One halving: if at every grid point `r + 2bj` (`j ≤ ⌈K⌉`) with `F(r + 2bj - b) ≤ A` either
`F(r + 2bj + b) ≤ A/2` or the drop `F(r + 2bj - b) - F(r + 2bj + b)` is at least `A/K`, and
`F(r - b) ≤ A`, then `F(r + 2b⌈K⌉ + b) ≤ A/2`. -/
theorem halving_level {F : ℝ → ℝ} (hF : Antitone F) (hF0 : ∀ t, 0 ≤ F t) {b A K r : ℝ}
    (hb : 0 < b) (hA : 0 < A) (hK : 1 ≤ K)
    (hstep : ∀ j : ℕ, j ≤ ⌈K⌉₊ → F (r + 2 * b * j - b) ≤ A →
      F (r + 2 * b * j + b) ≤ A / 2 ∨ A / K ≤ F (r + 2 * b * j - b) - F (r + 2 * b * j + b))
    (hstart : F (r - b) ≤ A) :
    F (r + 2 * b * ⌈K⌉₊ + b) ≤ A / 2 := by
  by_contra hcon
  simp only [not_le] at hcon
  have hfail : ∀ j : ℕ, j ≤ ⌈K⌉₊ → ¬ F (r + 2 * b * (j : ℝ) + b) ≤ A / 2 := by
    intro j hj hle
    have hjle : (j : ℝ) ≤ (⌈K⌉₊ : ℝ) := by exact_mod_cast hj
    have hmono : r + 2 * b * (j : ℝ) + b ≤ r + 2 * b * (⌈K⌉₊ : ℝ) + b := by
      nlinarith [hb]
    have := hF hmono
    linarith
  have hmain : ∀ j : ℕ, j ≤ ⌈K⌉₊ →
      F (r + 2 * b * (j : ℝ) + b) ≤ F (r - b) - ((j : ℝ) + 1) * (A / K) := by
    intro j
    induction j with
    | zero =>
        intro _
        have h0 := hstep 0 (Nat.zero_le _) (by simpa using hstart)
        rcases h0 with h | h
        · exact absurd h (hfail 0 (Nat.zero_le _))
        · simp only [Nat.cast_zero, mul_zero, zero_add, add_zero, one_mul] at h ⊢
          linarith
    | succ j ih =>
        intro hj
        have hj' : j ≤ ⌈K⌉₊ := Nat.le_of_succ_le hj
        have ih' := ih hj'
        have hleA : F (r + 2 * b * ((j + 1 : ℕ) : ℝ) - b) ≤ A := by
          push_cast
          rw [show r + 2 * b * ((j : ℝ) + 1) - b = r + 2 * b * (j : ℝ) + b by ring]
          have hAK : 0 ≤ ((j : ℝ) + 1) * (A / K) := by positivity
          linarith
        have hs := hstep (j + 1) hj hleA
        push_cast
        rcases hs with h | h
        · exact absurd h (hfail (j + 1) hj)
        · push_cast at h
          rw [show r + 2 * b * ((j : ℝ) + 1) - b = r + 2 * b * (j : ℝ) + b by ring] at h
          linarith
  have hN := hmain ⌈K⌉₊ (le_refl _)
  have hKN : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
  have hAKpos : 0 < A / K := by positivity
  have hbig : (K + 1) * (A / K) ≤ ((⌈K⌉₊ : ℝ) + 1) * (A / K) :=
    mul_le_mul_of_nonneg_right (by linarith [hKN]) (le_of_lt hAKpos)
  have hK1 : (K + 1) * (A / K) = A + A / K := by
    field_simp
  have hneg : F (r + 2 * b * (⌈K⌉₊ : ℝ) + b) < 0 := by
    nlinarith [hN, hstart, hbig, hK1, hAKpos]
  have hFnonneg : 0 ≤ F (r + 2 * b * (⌈K⌉₊ : ℝ) + b) := hF0 _
  linarith [hFnonneg]

/-- Iterated halving: under the halving alternative at every grid point `r₁ + 2bj` with
`j ≤ J` and every level `A ≥ Λ` (budget `K A ≥ 1`), a start `F(r₁ - b) ≤ A₀`, and `M` levels
with `A₀/2^M ≤ Λ` whose total budget fits in the grid, `F` falls below `Λ` at the end. -/
theorem halving_iterate {F : ℝ → ℝ} (hF : Antitone F) (hF0 : ∀ t, 0 ≤ F t)
    {b Λ r₁ A₀ : ℝ} (hb : 0 < b) (hΛ : 0 < Λ) (K : ℝ → ℝ) (hK : ∀ A, 1 ≤ K A) (J : ℕ)
    (hstep : ∀ j : ℕ, j ≤ J → ∀ A : ℝ, Λ ≤ A → F (r₁ + 2 * b * j - b) ≤ A →
      F (r₁ + 2 * b * j + b) ≤ A / 2 ∨
        A / K A ≤ F (r₁ + 2 * b * j - b) - F (r₁ + 2 * b * j + b))
    (M : ℕ) (hM : A₀ / 2 ^ M ≤ Λ) (hstart : F (r₁ - b) ≤ A₀)
    (hJ : ∑ k ∈ Finset.range M, (⌈K (A₀ / 2 ^ k)⌉₊ + 1) ≤ J + 1) :
    F (r₁ + 2 * b * ((∑ k ∈ Finset.range M, (⌈K (A₀ / 2 ^ k)⌉₊ + 1) : ℕ) : ℝ) - b) ≤ Λ := by
  let n : ℕ → ℕ := fun k => ⌈K (A₀ / 2 ^ k)⌉₊ + 1
  let i : ℕ → ℕ := fun k => ∑ k' ∈ Finset.range k, n k'
  have hisucc : ∀ k, i (k + 1) = i k + n k := by
    intro k
    simp only [i, Finset.sum_range_succ]
  have himono : Monotone i := by
    intro a b hab
    simp only [i]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hab) (fun x _ _ => Nat.zero_le _)
  have hmain : ∀ k : ℕ, k ≤ M →
      F (r₁ + 2 * b * (i k : ℝ) - b) ≤ max (A₀ / 2 ^ k) Λ := by
    intro k
    induction k with
    | zero =>
        intro _
        have h0 : i 0 = 0 := by simp only [i, Finset.sum_range_zero]
        simp only [h0, Nat.cast_zero, mul_zero, add_zero, pow_zero, div_one]
        exact le_trans hstart (le_max_left _ _)
    | succ k ih =>
        intro hk
        have hkM : k < M := Nat.lt_of_succ_le hk
        have ihk := ih (Nat.le_of_lt hkM)
        let A : ℝ := A₀ / 2 ^ k
        let r : ℝ := r₁ + 2 * b * (i k : ℝ)
        by_cases hcase : A < Λ
        · have hmax : max A Λ = Λ := max_eq_right (le_of_lt hcase)
          have hilek : (i k : ℝ) ≤ (i (k + 1) : ℝ) := by
            exact_mod_cast himono (Nat.le_succ k)
          have hmono : r₁ + 2 * b * (i k : ℝ) - b ≤ r₁ + 2 * b * (i (k+1) : ℝ) - b := by
            nlinarith [hb]
          have h1 : F (r₁ + 2 * b * (i (k+1) : ℝ) - b) ≤ max A Λ :=
            le_trans (hF hmono) ihk
          rw [hmax] at h1
          exact le_trans h1 (le_max_right (A₀ / 2 ^ (k+1)) Λ)
        · have hAle : Λ ≤ A := le_of_not_gt hcase
          have hApos : 0 < A := lt_of_lt_of_le hΛ hAle
          have hAmax : max A Λ = A := max_eq_left hAle
          have hstep' : ∀ j : ℕ, j ≤ ⌈K A⌉₊ → F (r + 2 * b * j - b) ≤ A →
              F (r + 2 * b * j + b) ≤ A / 2 ∨
                A / K A ≤ F (r + 2 * b * j - b) - F (r + 2 * b * j + b) := by
            intro j hj hjA
            have h2 : i k + ⌈K A⌉₊ < i (k+1) := by
              rw [hisucc]
              simp only [n, A]
              omega
            have h3 : i (k+1) ≤ J + 1 :=
              le_trans (himono (Nat.succ_le_of_lt hkM)) (by simpa only [i, n] using hJ)
            have hjJ : i k + j ≤ J := by
              have h1 : i k + j ≤ i k + ⌈K A⌉₊ := Nat.add_le_add_left hj (i k)
              omega
            have hargm : r₁ + 2 * b * ((i k + j : ℕ) : ℝ) - b = r + 2 * b * j - b := by
              simp only [r]
              push_cast
              ring
            have hargp : r₁ + 2 * b * ((i k + j : ℕ) : ℝ) + b = r + 2 * b * j + b := by
              simp only [r]
              push_cast
              ring
            have h := hstep (i k + j) hjJ A hAle (by rw [hargm]; exact hjA)
            rw [hargm, hargp] at h
            exact h
          have hAmax' : max (A₀ / 2 ^ k) Λ = A := by simpa only [A] using hAmax
          have hstart' : F (r - b) ≤ A := by
            have := ihk
            rw [hAmax'] at this
            simpa only [r] using this
          have hlevel := halving_level hF hF0 hb hApos (hK A) hstep' hstart'
          have hA2 : A / 2 = A₀ / 2 ^ (k+1) := by
            rw [pow_succ]
            simp only [A]
            rw [div_div]
          have heq : r₁ + 2 * b * (i (k+1) : ℝ) - b = r + 2 * b * ⌈K A⌉₊ + b := by
            rw [hisucc]
            simp only [r, n, A]
            push_cast
            ring
          rw [heq, ← hA2]
          exact le_trans hlevel (le_max_left _ _)
  have hMbound := hmain M le_rfl
  rw [max_eq_right hM] at hMbound
  simpa only [i, n] using hMbound

end CERW.Generic.Halving
