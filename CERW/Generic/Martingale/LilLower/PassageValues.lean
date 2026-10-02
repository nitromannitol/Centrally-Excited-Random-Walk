import CERW.Generic.Martingale.LilLower.BracketTimes

/-!
# The bracket at a passage time

For a nondecreasing process `V` from `0` whose jump after time `N` is at most `max 1` of
`g² V(t+1) / log log (V(t+1) ∨ e^e)`, the value of `V` just before its first passage over a level
`x ≥ e^e` lies in `[x - max 1 (2 g² x / log log x), x)`, provided the passage index is at least `N`
and `2 g² ≤ log log x`. The solve for the jump uses only `V(t+1) ≥ x`.
-/

namespace CERW.Generic.Martingale.LilLower

open Filter

/-- If a jump from `y₀ < x` to `y₁ ≥ x` is at most `max 1 (g² y₁ / log log (y₁ ∨ e^e))`, with
`x ≥ e^e` and `g² ≤ log log x / 2`, then it is at most `max 1 (2 g² x / log log x)`. -/
theorem jump_solve {x y₀ y₁ g : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) (hy₀ : y₀ < x)
    (hy₁ : x ≤ y₁) (hg : g ^ 2 ≤ Real.log (Real.log x) / 2)
    (hjump : y₁ - y₀ ≤
      max 1 (g ^ 2 * y₁ / Real.log (Real.log (max y₁ (Real.exp (Real.exp 1)))))) :
    y₁ - y₀ ≤ max 1 (2 * g ^ 2 * x / Real.log (Real.log x)) := by
  have hexp1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
    linarith
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hx
  have hlogxpos : 0 < Real.log x := by linarith
  have hL : 1 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hlogxpos).2 hlogx
  have hLpos : 0 < Real.log (Real.log x) := by linarith
  have hy₁pos : 0 < y₁ := hxpos.trans_le hy₁
  have hmax : max y₁ (Real.exp (Real.exp 1)) = y₁ := max_eq_left (hx.trans hy₁)
  rw [hmax] at hjump
  have hlog1 : Real.log x ≤ Real.log y₁ := Real.log_le_log hxpos hy₁
  have hlog2 : Real.log (Real.log x) ≤ Real.log (Real.log y₁) := Real.log_le_log hlogxpos hlog1
  have hdiv : g ^ 2 * y₁ / Real.log (Real.log y₁) ≤ g ^ 2 * y₁ / Real.log (Real.log x) :=
    div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg g) hy₁pos.le) hLpos hlog2
  by_cases hc : y₁ - y₀ ≤ 1
  · exact hc.trans (le_max_left _ _)
  · have hc' : 1 < y₁ - y₀ := not_le.1 hc
    rcases le_max_iff.1 hjump with h1 | h2
    · exact absurd h1 hc
    · have h3 : y₁ - y₀ ≤ g ^ 2 * y₁ / Real.log (Real.log x) := h2.trans hdiv
      have h4 : (y₁ - y₀) * Real.log (Real.log x) ≤ g ^ 2 * y₁ := (le_div_iff₀ hLpos).1 h3
      have h5 : g ^ 2 * (y₁ - y₀) ≤ Real.log (Real.log x) / 2 * (y₁ - y₀) :=
        mul_le_mul_of_nonneg_right hg (by linarith)
      have h6 : g ^ 2 * y₁ ≤ g ^ 2 * x + g ^ 2 * (y₁ - y₀) := by
        have : g ^ 2 * y₀ ≤ g ^ 2 * x := mul_le_mul_of_nonneg_left hy₀.le (sq_nonneg g)
        linarith
      have h7 : (y₁ - y₀) * Real.log (Real.log x) ≤ 2 * g ^ 2 * x := by linarith
      exact le_max_of_le_right ((le_div_iff₀ hLpos).2 h7)

/-- The value of the process just before the passage over `x` lies in
`[x - max 1 (2 g² x / log log x), x)`. -/
theorem passage_values {Ω : Type*} (V : ℕ → Ω → ℝ) (ω : Ω) {N : ℕ} {g x : ℝ}
    (hV0 : V 0 ω = 0)
    (hjump : ∀ t, N ≤ t → V (t + 1) ω - V t ω ≤
      max 1 (g ^ 2 * V (t + 1) ω /
        Real.log (Real.log (max (V (t + 1) ω) (Real.exp (Real.exp 1))))))
    (hx : Real.exp (Real.exp 1) ≤ x) (hg : g ^ 2 ≤ Real.log (Real.log x) / 2) {n : ℕ}
    (hn : N ≤ n) (h : firstPassage V x ω = (n : WithTop ℕ)) :
    x - max 1 (2 * g ^ 2 * x / Real.log (Real.log x)) ≤ V n ω ∧ V n ω < x := by
  obtain ⟨h1, h2⟩ := firstPassage_spec h
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlt : V n ω < x := by
    rcases n with _ | m
    · rw [hV0]
      exact hxpos
    · exact h2 m (Nat.lt_succ_self m)
  refine ⟨?_, hlt⟩
  have h3 := jump_solve hx hlt h1 hg (hjump n hn)
  linarith

end CERW.Generic.Martingale.LilLower
