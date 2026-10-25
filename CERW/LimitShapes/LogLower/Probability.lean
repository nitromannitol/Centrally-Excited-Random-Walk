module

public import CERW.LimitShapes.LogLower.TailBounds

@[expose] public section

/-!
# Logarithmic lower bounds by stopped quadratic Azuma

Proposition 9.4 (`prop:log-lower`) follows from the elliptic exit trials and the quadratic
Azuma bound. Borel–Cantelli supplies the almost-sure conclusions with the same constants.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory

namespace CERW.LimitShapes

open CERW.Support.Statements CERW CERW.Support.Law
open CERW.LimitShapes.LogLower
open private radius radius_nonneg radii_as_bounds exp_neg_mul_le
  from CERW.Support.Lower.LogLower

/-- **Proposition 9.4** (`prop:log-lower`): lower bounds for the radii. -/
theorem log_lower_bounds_from_azuma : log_lower_bounds.{u} := by
  intro d hd ωd ε hε hεd r
  have hr : r = radius d ε := rfl
  rw [hr]
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, C, h₀, hc, hC, hh₀, n₀, hb⟩ := radii_tail_bounds hd hε hεd
  have hdm : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcstar : 0 < ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) := by positivity
  set c' : ℝ := min c (((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2))) with hc'
  have hc'pos : 0 < c' := lt_min hc hcstar
  have hc'c : c' ≤ c := min_le_left _ _
  have hc'star : c' ≤ ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) := min_le_right _ _
  refine ⟨c', C, h₀, hc'pos, hC, hh₀, n₀, ?_⟩
  intro Ω _ μ _ X hX
  refine ⟨?_, ?_⟩
  · intro n hn h hhh hhr
    obtain ⟨b1, b2⟩ := hb μ X hX n hn h hhh hhr
    have hr0 : 0 ≤ radius d ε n := radius_nonneg hd1 hε n
    have hY : 0 ≤ radius d ε n ^ (d - 1) := pow_nonneg hr0 _
    have hE : 0 ≤ Real.exp (-(C * h)) := (Real.exp_pos _).le
    have hZ : 0 ≤ radius d ε n ^ ((d : ℝ) - 3) := Real.rpow_nonneg hr0 _
    refine ⟨b1.trans (ENNReal.ofReal_le_ofReal (exp_neg_mul_le hc'c hY hE)), ?_⟩
    refine b2.trans (ENNReal.ofReal_le_ofReal (add_le_add (exp_neg_mul_le hc'c hY hE)
      (exp_neg_mul_le hc'c hZ (sq_nonneg h))))
  · have has := radii_as_bounds hd hε hc hC (fun n hn h hhh hhr => hb μ X hX n hn h hhh hhr)
    filter_upwards [has] with ω hω
    filter_upwards [hω, Filter.eventually_ge_atTop 1] with n hn hn1
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hmono : c' * Real.log n ≤ ((d : ℝ) - 1) / (4 * C * ((d : ℝ) + 2)) * Real.log n :=
      mul_le_mul_of_nonneg_right hc'star hlog
    exact ⟨lt_of_le_of_lt hmono hn.1, fun h3 => lt_of_le_of_lt hmono (hn.2 h3)⟩


end CERW.LimitShapes
