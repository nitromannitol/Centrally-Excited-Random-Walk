import CERW.Generic.Martingale.LilLower.BracketTimes

/-!
# The passage times of the bracket

Along one path: the passage times of the bracket over the levels `θ^k` are finite and tend to
infinity, and eventually the bracket at the passage time lies in `[e^e, θ^k)`, from the bound on
the jumps of the bracket after the start time.
-/

namespace CERW.Generic.Martingale.LilAssembly

open Filter Topology CERW.Generic.Martingale.LilLower

/-- The iterated logarithm of anything at least `exp (exp 1)` is at least one. -/
theorem one_le_loglog_max (y : ℝ) :
    1 ≤ Real.log (Real.log (max y (Real.exp (Real.exp 1)))) := by
  have hpos : 0 < Real.exp (Real.exp 1) := Real.exp_pos _
  have h1 : Real.exp (Real.exp 1) ≤ max y (Real.exp (Real.exp 1)) := le_max_right _ _
  have h2 : Real.exp 1 ≤ Real.log (max y (Real.exp (Real.exp 1))) := by
    have := Real.log_le_log hpos h1
    rwa [Real.log_exp] at this
  have h3 : 0 < Real.exp 1 := Real.exp_pos _
  have h4 := Real.log_le_log h3 h2
  rwa [Real.log_exp] at h4

/-- A bounded relative jump keeps the value just before a high level high. -/
theorem exp_exp_le_of_jump (a b x εg : ℝ) (hεg : 0 < εg) (hεg1 : εg ≤ 1 / 2)
    (hxb : x ≤ b) (hx : 2 * Real.exp (Real.exp 1) + 3 ≤ x)
    (hj : b - a ≤ max 1 (εg ^ 2 * b /
      Real.log (Real.log (max b (Real.exp (Real.exp 1)))))) :
    Real.exp (Real.exp 1) ≤ a := by
  have hE : 0 < Real.exp (Real.exp 1) := Real.exp_pos _
  have hb : 0 < b := by linarith
  have hL := one_le_loglog_max b
  have hsq : εg ^ 2 ≤ 1 / 4 := by nlinarith
  have hbq : εg ^ 2 * b ≤ b / 4 := by nlinarith
  have hdiv : εg ^ 2 * b /
      Real.log (Real.log (max b (Real.exp (Real.exp 1)))) ≤ εg ^ 2 * b :=
    div_le_self (by positivity) hL
  have hj' : b - a ≤ max 1 (b / 4) := hj.trans (max_le_max le_rfl (hdiv.trans hbq))
  rcases le_max_iff.1 hj' with h | h <;> linarith

/-- The passage times of the bracket are finite, tend to infinity, and land in a window. -/
theorem passage_window {Ω : Type*} (V : ℕ → Ω → ℝ) (εg θ : ℝ) (N : ℕ) (ω : Ω) (hθ : 1 < θ)
    (hεg : 0 < εg) (hεg1 : εg ≤ 1 / 2)
    (hinf : Tendsto (fun n => V n ω) atTop atTop)
    (hjump : ∀ t, N ≤ t → V (t + 1) ω - V t ω ≤ max 1 (εg ^ 2 * V (t + 1) ω /
      Real.log (Real.log (max (V (t + 1) ω) (Real.exp (Real.exp 1)))))) :
    (∀ k, firstPassage V (θ ^ k) ω ≠ ⊤) ∧
      Tendsto (fun k => (firstPassage V (θ ^ k) ω).untopA) atTop atTop ∧
      ∀ᶠ k in atTop, Real.exp (Real.exp 1) ≤ V ((firstPassage V (θ ^ k) ω).untopA) ω ∧
        V ((firstPassage V (θ ^ k) ω).untopA) ω < θ ^ k := by
  have hne : ∀ k : ℕ, firstPassage V (θ ^ k) ω ≠ ⊤ :=
    fun k => firstPassage_ne_top_of_tendsto hinf
  have hxs : Tendsto (fun k : ℕ => θ ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hθ
  have hn : Tendsto (fun k => (firstPassage V (θ ^ k) ω).untopA) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_le_firstPassage (V := V) (ω := ω) hxs M)
    exact ⟨K, fun k hk => (WithTop.le_untopA_iff (hne k)).2 (hK k hk)⟩
  refine ⟨hne, hn, ?_⟩
  filter_upwards [hn.eventually_ge_atTop (max N 1),
    hxs.eventually_ge_atTop (2 * Real.exp (Real.exp 1) + 3)] with k hk1 hk2
  obtain ⟨n, hnk⟩ := WithTop.ne_top_iff_exists.1 (hne k)
  have hu : (firstPassage V (θ ^ k) ω).untopA = n := by
    rw [← hnk, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [hu] at hk1 ⊢
  obtain ⟨hs1, hs2⟩ := firstPassage_spec hnk.symm
  have hN : N ≤ n := (le_max_left _ _).trans hk1
  have h1 : 1 ≤ n := (le_max_right _ _).trans hk1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨exp_exp_le_of_jump _ _ _ εg hεg hεg1 hs1 hk2 (hjump (m + 1) hN),
    hs2 m (Nat.lt_succ_self m)⟩

end CERW.Generic.Martingale.LilAssembly
