import CERW.Generic.Martingale.LilAssembly.Statements
import CERW.Generic.Martingale.Lil.Arith

/-!
# The pathwise combination of the blocks

Along one path: the eventual lower bound `S ≥ -(1 + δ') ψ(P)` at the passage times and
infinitely many block increments at least `a_k` give `S_n ≥ (1 - δ) ψ(P_n)` infinitely often.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology

private theorem one_lt_of_exp_exp_le {y : ℝ} (h : Real.exp (Real.exp 1) ≤ y) :
    Real.exp 1 ≤ y ∧ 1 < Real.exp 1 := by
  have h1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  exact ⟨le_trans (Real.exp_le_exp.mpr h1.le) h, h1⟩

private theorem lilScale_mono {y z : ℝ} (hy : Real.exp (Real.exp 1) ≤ y) (hyz : y ≤ z) :
    lilScale y ≤ lilScale z := by
  have hy1 := (one_lt_of_exp_exp_le hy).1
  have hm := CERW.Generic.Martingale.Lil.lilArith_monotoneOn_mul_loglog
    (Set.mem_Ici.mpr hy1) (Set.mem_Ici.mpr (le_trans hy1 hyz)) hyz
  simp only at hm
  unfold lilScale
  apply Real.sqrt_le_sqrt
  linarith

private theorem sqrt_mul_lilScale_le {θ x : ℝ} (hθ : 1 ≤ θ) (hx : Real.exp (Real.exp 1) ≤ x) :
    Real.sqrt θ * lilScale x ≤ lilScale (θ * x) := by
  obtain ⟨hx1, he⟩ := one_lt_of_exp_exp_le hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hxθ : x ≤ θ * x := le_mul_of_one_le_left hx0.le hθ
  have hll : Real.log (Real.log x) ≤ Real.log (Real.log (θ * x)) :=
    Real.log_le_log hlx (Real.log_le_log hx0 hxθ)
  have hle : 2 * x * Real.log (Real.log x) ≤ 2 * x * Real.log (Real.log (θ * x)) :=
    mul_le_mul_of_nonneg_left hll (by linarith)
  have heq : 2 * (θ * x) * Real.log (Real.log (θ * x)) =
      θ * (2 * x * Real.log (Real.log (θ * x))) := by ring
  unfold lilScale
  rw [heq, Real.sqrt_mul (show 0 ≤ θ by linarith)]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _)

private theorem combine_step {s c δ δ' A B a u w v q : ℝ} (hs : 0 < s) (hδ : δ < 1) (hδ' : 0 < δ')
    (hc : 1 - δ ≤ c - (1 + δ') / s) (hsw : s * w ≤ v) (huw : u ≤ w) (hqv : q ≤ v)
    (hv : 0 ≤ v) (hcv : c * v ≤ a) (hA : -((1 + δ') * u) ≤ A) (hab : a ≤ B - A) :
    (1 - δ) * q ≤ B := by
  have h1 : (1 + δ') * w ≤ (1 + δ') / s * v := by
    have : (1 + δ') * w = (1 + δ') / s * (s * w) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hsw (by positivity)
  have h2 : (1 + δ') * u ≤ (1 + δ') * w := mul_le_mul_of_nonneg_left huw (by linarith)
  have h3 : (1 - δ) * v ≤ (c - (1 + δ') / s) * v := mul_le_mul_of_nonneg_right hc hv
  have h4 : (1 - δ) * q ≤ (1 - δ) * v := mul_le_mul_of_nonneg_left hqv (by linarith)
  linarith

/-- The pathwise combination of the blocks. -/
theorem path_combine : PathCombine := by
  intro S P τ x a θ δ δ' hθ hδ0 hδ1 hδ' hc hx hxt hτ hP ha hS hfreq
  have hP' : ∀ᶠ k in atTop, Real.exp (Real.exp 1) ≤ P (τ (k + 1)) ∧ P (τ (k + 1)) < x (k + 1) :=
    (tendsto_add_atTop_nat 1).eventually hP
  have hxe : ∀ᶠ k in atTop, Real.exp (Real.exp 1) ≤ x k := hxt.eventually_ge_atTop _
  have hall := hP.and (hP'.and (ha.and (hS.and hxe)))
  have key : ∃ᶠ k in atTop, (1 - δ) * lilScale (P (τ (k + 1))) ≤ S (τ (k + 1)) := by
    refine (hfreq.and_eventually hall).mono ?_
    rintro k ⟨hk, ⟨hP1, hP2⟩, ⟨hP3, hP4⟩, hak, hSk, hxk⟩
    have hs : 0 < Real.sqrt θ := Real.sqrt_pos.mpr (by linarith)
    have hv : 0 ≤ lilScale (x (k + 1)) := Real.sqrt_nonneg _
    have hsw : Real.sqrt θ * lilScale (x k) ≤ lilScale (x (k + 1)) := by
      rw [hx k]
      exact sqrt_mul_lilScale_le hθ.le hxk
    exact combine_step hs hδ1 hδ' hc hsw (lilScale_mono hP1 hP2.le)
      (lilScale_mono hP3 hP4.le) hv hak hSk hk
  rw [Filter.frequently_atTop] at key ⊢
  intro N
  obtain ⟨i, hi⟩ := Filter.tendsto_atTop_atTop.mp hτ N
  obtain ⟨b, hb, hbq⟩ := key i
  exact ⟨τ (b + 1), hi (b + 1) (by omega), hbq⟩

end CERW.Generic.Martingale.LilAssembly
