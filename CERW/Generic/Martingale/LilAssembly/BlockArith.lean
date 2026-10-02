import Mathlib.Analysis.PSeries
import CERW.Generic.Martingale.LilAssembly.Statements

/-!
# The parameters of the blocks

With `θ = (16/δ)²` and `η = δ/2`, the block quantities meet the conditions of the sharp lower tail
eventually, and the resulting lower bounds have divergent partial sums.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology

/-- The `θ`-condition for `θ = (16 / δ) ^ 2`. -/
theorem ba_theta_cond (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) :
    1 - δ ≤ (1 - δ / 2) * Real.sqrt (1 - 1 / (16 / δ) ^ 2) -
      (1 + δ / 4) / Real.sqrt ((16 / δ) ^ 2) := by
  have hθ : Real.sqrt ((16 / δ) ^ 2) = 16 / δ := Real.sqrt_sq (by positivity)
  have ht : 1 / (16 / δ) ^ 2 = δ ^ 2 / 256 := by field_simp; norm_num
  have h2 : δ ^ 2 ≤ δ := by nlinarith
  have hs : 1 - δ ^ 2 / 256 ≤ Real.sqrt (1 - δ ^ 2 / 256) := by
    have h3 : 0 ≤ 1 - δ ^ 2 / 256 := by nlinarith
    rw [Real.le_sqrt h3 h3]
    nlinarith [sq_nonneg δ]
  have h4 : (1 + δ / 4) / (16 / δ) = (1 + δ / 4) * δ / 16 := by field_simp
  rw [hθ, ht, h4]
  have h5 : (1 - δ / 2) * (1 - δ ^ 2 / 256) ≤ (1 - δ / 2) * Real.sqrt (1 - δ ^ 2 / 256) :=
    mul_le_mul_of_nonneg_left hs (by linarith)
  nlinarith [pow_pos h0 3]

/-- `log log` is at most doubled when the argument is multiplied by `θ`. -/
theorem ba_ll_mul_le (θ y : ℝ) (hθ : 1 < θ) (hy : Real.exp (Real.exp 1) ≤ y) (hθy : θ ≤ y) :
    Real.log (Real.log (θ * y)) ≤ 2 * Real.log (Real.log y) := by
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  have hθ0 : 0 < θ := by linarith
  have hly : Real.exp 1 ≤ Real.log y := (Real.le_log_iff_exp_le hy0).2 hy
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hll : 1 ≤ Real.log (Real.log y) := by
    have := Real.log_le_log (Real.exp_pos 1) hly
    rwa [Real.log_exp] at this
  have hlθ : Real.log θ ≤ Real.log y := Real.log_le_log hθ0 hθy
  have hθpos : 0 < Real.log θ := Real.log_pos hθ
  rw [Real.log_mul hθ0.ne' hy0.ne']
  have hle : Real.log θ + Real.log y ≤ 2 * Real.log y := by linarith
  have h1 := Real.log_le_log (by linarith) hle
  rw [Real.log_mul two_ne_zero (by linarith)] at h1
  have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

/-- `log log` is at least one past `exp (exp 1)`. -/
theorem ba_ll_ge_one (y : ℝ) (hy : Real.exp (Real.exp 1) ≤ y) : 1 ≤ Real.log (Real.log y) := by
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  have hly : Real.exp 1 ≤ Real.log y := (Real.le_log_iff_exp_le hy0).2 hy
  have := Real.log_le_log (Real.exp_pos 1) hly
  rwa [Real.log_exp] at this

/-- `log log` is monotone past `exp (exp 1)`. -/
theorem ba_ll_mono (y z : ℝ) (hy : Real.exp (Real.exp 1) ≤ y) (hyz : y ≤ z) :
    Real.log (Real.log y) ≤ Real.log (Real.log z) := by
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  have hly : Real.exp 1 ≤ Real.log y := (Real.le_log_iff_exp_le hy0).2 hy
  have h1 : 0 < Real.log y := lt_of_lt_of_le (Real.exp_pos 1) hly
  exact Real.log_le_log h1 (Real.log_le_log hy0 hyz)

/-- The bound on the level jump. -/
theorem ba_J_le (ε y Y u U : ℝ) (hu : 1 ≤ u) (hU : 0 < U) (hU2 : U ≤ 2 * u) (hy : 0 ≤ y)
    (hyY : y ≤ Y) : max 1 (ε ^ 2 * y / u) ≤ 1 + 2 * ε ^ 2 * Y / U := by
  have hu0 : 0 < u := by linarith
  have h2 : 0 ≤ ε ^ 2 * y / u := by positivity
  have h1 : ε ^ 2 * y / u ≤ 2 * ε ^ 2 * Y / U := by
    rw [div_le_div_iff₀ hu0 hU]
    have h4 : ε ^ 2 * y * U ≤ ε ^ 2 * y * (2 * u) := by gcongr
    have h5 : ε ^ 2 * y * (2 * u) ≤ ε ^ 2 * Y * (2 * u) := by gcongr
    linarith
  have h3 : 0 ≤ 2 * ε ^ 2 * Y / U := le_trans h2 h1
  exact max_le (by linarith) (by linarith)

/-- The lower bounds on the block bracket. -/
theorem ba_w_lower (θ y Y w J : ℝ) (hθ : 2 ≤ θ) (hy : 0 ≤ y) (hY : Y = θ * y) (hJ : 1 ≤ J)
    (hw : w = Y - y + J) : (1 - 1 / θ) * Y < w ∧ Y / 2 ≤ w := by
  have hθ0 : 0 < θ := by linarith
  have h1 : (1 - 1 / θ) * Y = Y - y := by rw [hY]; field_simp
  have h2 : 2 * y ≤ θ * y := mul_le_mul_of_nonneg_right hθ hy
  constructor <;> linarith

/-- The upper bound on the block bracket. -/
theorem ba_w_upper (ε Y U w y J : ℝ) (hU : 0 < U) (hY : 1 ≤ Y) (hu2 : 2 * ε ^ 2 ≤ U) (hy : 0 ≤ y)
    (hJ : J ≤ 1 + 2 * ε ^ 2 * Y / U) (hw : w = Y - y + J) : w ≤ 3 * Y := by
  have h1 : 2 * ε ^ 2 * Y / U ≤ Y := by
    rw [div_le_iff₀ hU]
    have := mul_le_mul_of_nonneg_right hu2 (show (0 : ℝ) ≤ Y by linarith)
    linarith
  linarith

/-- The deficit is at most `ρ₀`. -/
theorem ba_rho_le (ρ₀ ε Y U w J J' : ℝ) (hρ₀ : 0 < ρ₀) (hU : 0 < U) (hY : 0 < Y)
    (hw : Y / 2 ≤ w) (hJ : J ≤ 1 + 2 * ε ^ 2 * Y / U) (hJ' : J' ≤ 1 + ε ^ 2 * Y / U)
    (hu1 : 3 * ε ^ 2 ≤ ρ₀ / 4 * U) (hY3 : 8 ≤ ρ₀ * Y) : J + J' ≤ ρ₀ * w := by
  have h1 : 3 * ε ^ 2 * Y / U ≤ ρ₀ / 4 * Y := by
    rw [div_le_iff₀ hU]
    have := mul_le_mul_of_nonneg_right hu1 hY.le
    linarith
  have h2 : 2 * ε ^ 2 * Y / U + ε ^ 2 * Y / U = 3 * ε ^ 2 * Y / U := by ring
  have h3 : ρ₀ * (Y / 2) ≤ ρ₀ * w := mul_le_mul_of_nonneg_left hw hρ₀.le
  linarith

/-- The target dominates `A₀ w`. -/
theorem ba_A_le (A₀ c₀ Y U w : ℝ) (hY : 0 < Y) (hw0 : 0 < w) (hw : w ≤ 3 * Y)
    (hu : 3 * |A₀| ≤ 2 * c₀ * U) : A₀ * w ≤ c₀ * (2 * Y * U) := by
  have h1 : A₀ * w ≤ |A₀| * w := mul_le_mul_of_nonneg_right (le_abs_self _) hw0.le
  have h2 : |A₀| * w ≤ |A₀| * (3 * Y) := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  have h3 : 3 * |A₀| * Y ≤ 2 * c₀ * U * Y := mul_le_mul_of_nonneg_right hu hY.le
  linarith

/-- The product of the target and the increment bound. -/
theorem ba_ab_le (c ε ε₀ Y u U w : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hY : 0 < Y) (hu : 0 < u) (hU : 0 < U) (hU2 : U ≤ 2 * u) (h4 : 4 * ε ≤ ε₀)
    (hu4 : 8 * U ≤ ε₀ ^ 2 * Y) (hw : Y / 2 ≤ w) :
    c * Real.sqrt (2 * Y * U) * max 1 (ε * Real.sqrt (Y / u)) ≤ ε₀ * w := by
  have hS0 : 0 ≤ Real.sqrt (2 * Y * U) := Real.sqrt_nonneg _
  have hca : 0 ≤ c * Real.sqrt (2 * Y * U) := by positivity
  have hεw : ε₀ * (Y / 2) ≤ ε₀ * w := mul_le_mul_of_nonneg_left hw hε₀.le
  rw [mul_max_of_nonneg _ _ hca]
  apply max_le
  · have hS : Real.sqrt (2 * Y * U) ≤ ε₀ * Y / 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      have : 8 * U * Y ≤ ε₀ ^ 2 * Y * Y := mul_le_mul_of_nonneg_right hu4 hY.le
      nlinarith
    calc c * Real.sqrt (2 * Y * U) * 1 ≤ 1 * Real.sqrt (2 * Y * U) * 1 := by gcongr
      _ ≤ ε₀ * Y / 2 := by linarith
      _ ≤ ε₀ * w := by linarith
  · have hprod : Real.sqrt (2 * Y * U) * Real.sqrt (Y / u) ≤ 2 * Y := by
      rw [← Real.sqrt_mul (by positivity), Real.sqrt_le_left (by positivity)]
      have : U / u ≤ 2 := by rw [div_le_iff₀ hu]; linarith
      calc 2 * Y * U * (Y / u) = 2 * Y ^ 2 * (U / u) := by ring
        _ ≤ 2 * Y ^ 2 * 2 := by gcongr
        _ = (2 * Y) ^ 2 := by ring
    have h5 : 4 * ε * Y ≤ ε₀ * Y := mul_le_mul_of_nonneg_right h4 hY.le
    calc c * Real.sqrt (2 * Y * U) * (ε * Real.sqrt (Y / u))
        = c * ε * (Real.sqrt (2 * Y * U) * Real.sqrt (Y / u)) := by ring
      _ ≤ 1 * ε * (2 * Y) := by gcongr
      _ ≤ ε₀ * w := by linarith

/-- The lower bound on a term of the divergent series. -/
theorem ba_term_ge (g s q Y U w : ℝ) (hg : g * s ^ 2 ≤ 1) (hg0 : 0 ≤ g) (hq : 0 < q)
    (hY : 0 < Y) (hU : 0 ≤ U) (hw : q * Y ≤ w) (hlog : 0 < Real.log Y)
    (hUdef : U = Real.log (Real.log Y)) :
    1 / Real.log Y ≤ Real.exp (-(g * ((s ^ 2 * q) * (2 * Y * U) / (2 * w)))) := by
  have hw0 : 0 < w := lt_of_lt_of_le (mul_pos hq hY) hw
  have hP : 0 ≤ s ^ 2 * U := by positivity
  have h1 : (s ^ 2 * q) * (2 * Y * U) / (2 * w) ≤ s ^ 2 * U := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hw hP
    nlinarith
  have h2 : g * ((s ^ 2 * q) * (2 * Y * U) / (2 * w)) ≤ g * (s ^ 2 * U) :=
    mul_le_mul_of_nonneg_left h1 hg0
  have h3 : g * (s ^ 2 * U) ≤ U := by nlinarith
  have h4 : Real.exp (-U) = 1 / Real.log Y := by
    rw [Real.exp_neg, hUdef, Real.exp_log hlog, one_div]
  rw [← h4]
  exact Real.exp_le_exp.2 (by linarith)

/-- The exponent constant of the lower bound is at most one. -/
theorem ba_g_le (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1) : (1 + δ / 2) * (1 - δ / 2) ^ 2 ≤ 1 := by
  nlinarith [mul_pos (pow_pos h0 2) (sub_pos.2 h1), pow_pos h0 2]

/-- The pointwise conditions at one block, given the eventual smallness conditions. -/
theorem ba_point (δ θ ε ρ₀ ε₀ A₀ y Y J J' w ρ a b : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hθ : 256 ≤ θ) (hε : 0 < ε) (hε₀ : 0 < ε₀) (hρ₀ : 0 < ρ₀)
    (h4 : 4 * ε ≤ ε₀) (hY : Y = θ * y)
    (hJ : J = max 1 (ε ^ 2 * y / Real.log (Real.log y)))
    (hJ' : J' = max 1 (ε ^ 2 * Y / Real.log (Real.log Y)))
    (hw : w = Y - y + J) (hρ : ρ = (J + J') / w)
    (ha : a = (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale Y)
    (hb : b = max 1 (ε * Real.sqrt (Y / Real.log (Real.log y))))
    (hy1 : Real.exp (Real.exp 1) ≤ y) (hy2 : θ ≤ y)
    (hu1 : 3 * ε ^ 2 ≤ ρ₀ / 4 * Real.log (Real.log Y))
    (hu2 : 2 * ε ^ 2 ≤ Real.log (Real.log Y))
    (hu3 : 3 * |A₀| ≤ 2 * ((1 - δ / 2) ^ 2 * (1 - 1 / θ)) * Real.log (Real.log Y))
    (hu4 : 8 * Real.log (Real.log Y) ≤ ε₀ ^ 2 * Y) (hY3 : 8 ≤ ρ₀ * Y) :
    0 < w ∧ 0 < a ∧ 0 ≤ ρ ∧ ρ ≤ ρ₀ ∧ w * (1 - ρ) = Y - y - J' ∧ A₀ * w ≤ a ^ 2 ∧
      a * b ≤ ε₀ * w ∧ 1 / Real.log Y ≤ Real.exp (-((1 + δ / 2) * (a ^ 2 / (2 * w)))) := by
  have hθ1 : 1 < θ := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy1
  have hyY : y ≤ Y := by rw [hY]; exact le_mul_of_one_le_left hy0.le hθ1.le
  have hY1 : Real.exp (Real.exp 1) ≤ Y := hy1.trans hyY
  have hY0 : 0 < Y := hy0.trans_le hyY
  have hYge : 1 ≤ Y := by linarith
  have hu : 1 ≤ Real.log (Real.log y) := ba_ll_ge_one y hy1
  have hU1 : Real.log (Real.log y) ≤ Real.log (Real.log Y) := ba_ll_mono y Y hy1 hyY
  have hU2 : Real.log (Real.log Y) ≤ 2 * Real.log (Real.log y) := by
    have := ba_ll_mul_le θ y hθ1 hy1 hy2
    rwa [← hY] at this
  have hUpos : 0 < Real.log (Real.log Y) := by linarith
  have hlog : 0 < Real.log Y := lt_of_lt_of_le (Real.exp_pos 1) ((Real.le_log_iff_exp_le hY0).2 hY1)
  have hq1 : 1 / θ < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hq : 0 < 1 - 1 / θ := by linarith
  have hq' : 1 - 1 / θ ≤ 1 := by
    have : 0 < 1 / θ := by positivity
    linarith
  have hs : 0 < 1 - δ / 2 := by linarith
  have hc0 : 0 < (1 - δ / 2) * Real.sqrt (1 - 1 / θ) := mul_pos hs (Real.sqrt_pos.2 hq)
  have hc1 : (1 - δ / 2) * Real.sqrt (1 - 1 / θ) ≤ 1 :=
    mul_le_one₀ (by linarith) (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 hq')
  have hJ1 : 1 ≤ J := by rw [hJ]; exact le_max_left _ _
  have hJ'1 : 1 ≤ J' := by rw [hJ']; exact le_max_left _ _
  have hJb : J ≤ 1 + 2 * ε ^ 2 * Y / Real.log (Real.log Y) := by
    rw [hJ]; exact ba_J_le ε y Y _ _ hu hUpos hU2 hy0.le hyY
  have hJ'b : J' ≤ 1 + ε ^ 2 * Y / Real.log (Real.log Y) := by
    have : 0 ≤ ε ^ 2 * Y / Real.log (Real.log Y) := by positivity
    rw [hJ']; exact max_le (by linarith) (by linarith)
  obtain ⟨hw1, hw2⟩ := ba_w_lower θ y Y w J (by linarith) hy0.le hY hJ1 hw
  have hw0 : 0 < w := lt_trans (mul_pos hq hY0) hw1
  have hwu : w ≤ 3 * Y := ba_w_upper ε Y _ w y J hUpos hYge hu2 hy0.le hJb hw
  have hS : lilScale Y ^ 2 = 2 * Y * Real.log (Real.log Y) := Real.sq_sqrt (by positivity)
  have ha2 : a ^ 2 = ((1 - δ / 2) ^ 2 * (1 - 1 / θ)) * (2 * Y * Real.log (Real.log Y)) := by
    rw [ha, mul_pow, mul_pow, Real.sq_sqrt hq.le, hS]
  have hg : (1 + δ / 2) * (1 - δ / 2) ^ 2 ≤ 1 := ba_g_le δ hδ0 hδ1
  refine ⟨hw0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha]; exact mul_pos hc0 (Real.sqrt_pos.2 (by positivity))
  · rw [hρ]; exact div_nonneg (by linarith) hw0.le
  · rw [hρ, div_le_iff₀ hw0]
    exact ba_rho_le ρ₀ ε Y _ w J J' hρ₀ hUpos hY0 hw2 hJb hJ'b hu1 hY3
  · rw [hρ]; field_simp; rw [hw]; ring
  · rw [ha2]; exact ba_A_le A₀ _ Y _ w hY0 hw0 hwu hu3
  · rw [ha, hb]
    exact ba_ab_le _ ε ε₀ Y _ _ w hc0 hc1 hε hε₀ hY0 (by linarith) hUpos hU2 h4 hu4 hw2
  · rw [ha2]
    exact ba_term_ge (1 + δ / 2) (1 - δ / 2) (1 - 1 / θ) Y _ w hg (by linarith) hq hY0
      hUpos.le hw1.le hlog rfl

/-- `log log (θ y)` tends to infinity. -/
theorem ba_ev_ll (θ M : ℝ) (hθ : 0 < θ) :
    ∀ᶠ y : ℝ in atTop, M ≤ Real.log (Real.log (θ * y)) := by
  have h : Tendsto (fun y : ℝ => Real.log (Real.log (θ * y))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop hθ))
  exact h.eventually_ge_atTop M

/-- `log log z` is eventually at most `c z`. -/
theorem ba_ev_small (c : ℝ) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, Real.log (Real.log z) ≤ c * z := by
  filter_upwards [Real.isLittleO_log_id_atTop.def hc, eventually_ge_atTop (1 : ℝ)] with z hz h1
  have h0 : 0 ≤ Real.log z := Real.log_nonneg h1
  have h3 := Real.log_le_self h0
  have h2 : ‖Real.log z‖ ≤ c * ‖z‖ := hz
  rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (by linarith)] at h2
  linarith

/-- The eventual smallness conditions on the level `y`. -/
theorem ba_eventually (δ θ ε ρ₀ ε₀ A₀ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hθ : 256 ≤ θ)
    (hρ₀ : 0 < ρ₀) (hε₀ : 0 < ε₀) :
    ∀ᶠ y : ℝ in atTop, ∀ Y : ℝ, Y = θ * y → (Real.exp (Real.exp 1) ≤ y ∧ θ ≤ y ∧
      3 * ε ^ 2 ≤ ρ₀ / 4 * Real.log (Real.log Y) ∧ 2 * ε ^ 2 ≤ Real.log (Real.log Y) ∧
      3 * |A₀| ≤ 2 * ((1 - δ / 2) ^ 2 * (1 - 1 / θ)) * Real.log (Real.log Y) ∧
      8 * Real.log (Real.log Y) ≤ ε₀ ^ 2 * Y ∧ 8 ≤ ρ₀ * Y) := by
  have hθ0 : 0 < θ := by linarith
  have hθ1 : 1 < θ := by linarith
  have hq1 : 1 / θ < 1 := by rw [div_lt_one hθ0]; exact hθ1
  have hc₀ : 0 < (1 - δ / 2) ^ 2 * (1 - 1 / θ) :=
    mul_pos (pow_pos (by linarith) 2) (by linarith)
  have hlin : Tendsto (fun y : ℝ => θ * y) atTop atTop := tendsto_id.const_mul_atTop hθ0
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1)), eventually_ge_atTop θ,
    ba_ev_ll θ (12 * ε ^ 2 / ρ₀) hθ0, ba_ev_ll θ (2 * ε ^ 2) hθ0,
    ba_ev_ll θ (3 * |A₀| / (2 * ((1 - δ / 2) ^ 2 * (1 - 1 / θ)))) hθ0,
    hlin.eventually (ba_ev_small (ε₀ ^ 2 / 8) (by positivity)),
    hlin.eventually_ge_atTop (8 / ρ₀)] with y h1 h2 h3 h4 h5 h6 h7 Y hY
  subst hY
  refine ⟨h1, h2, ?_, h4, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hρ₀] at h3
    linarith
  · rw [div_le_iff₀ (by positivity)] at h5
    linarith
  · have h6' : Real.log (Real.log (θ * y)) ≤ ε₀ ^ 2 / 8 * (θ * y) := h6
    linarith
  · have h7' : 8 / ρ₀ ≤ θ * y := h7
    rwa [div_le_iff₀ hρ₀, mul_comm] at h7'

/-- The partial sums of a series bounded below by a multiple of the harmonic series diverge. -/
theorem ba_diverge (θ : ℝ) (k₀ : ℕ) (f : ℕ → ℝ) (hθ : 1 < θ) (hf : ∀ n, 0 ≤ f n)
    (hge : ∀ k, k₀ ≤ k → 1 / (((k + 1 : ℕ) : ℝ) * Real.log θ) ≤ f k) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, f k) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg hf]
  intro hs
  have hL : 0 < Real.log θ := Real.log_pos hθ
  have hs1 : Summable (fun n : ℕ => Real.log θ * f (n + k₀)) :=
    ((summable_nat_add_iff k₀).2 hs).mul_left _
  have hs2 : Summable (fun n : ℕ => 1 / (((n + (k₀ + 1) : ℕ) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs1
    have h1 := hge (n + k₀) (Nat.le_add_left _ _)
    have h2 : (((n + k₀ + 1 : ℕ) : ℝ)) = (((n + (k₀ + 1) : ℕ) : ℝ)) := by push_cast; ring
    rw [h2] at h1
    have h3 : 1 / (((n + (k₀ + 1) : ℕ) : ℝ)) =
        Real.log θ * (1 / (((n + (k₀ + 1) : ℕ) : ℝ) * Real.log θ)) := by
      field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_left h1 hL.le
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff (k₀ + 1)).1 hs2)

/-- The eventual conditions and the divergence, for the chosen parameters. -/
theorem ba_core (δ θ ε ρ₀ ε₀ A₀ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hθ : 256 ≤ θ)
    (hε : 0 < ε) (hρ₀ : 0 < ρ₀) (hε₀ : 0 < ε₀) (h4 : 4 * ε ≤ ε₀) : ∃ k₀ : ℕ,
      let x : ℕ → ℝ := fun k => θ ^ k
      let J : ℕ → ℝ := fun k => max 1 (ε ^ 2 * x k / Real.log (Real.log (x k)))
      let w : ℕ → ℝ := fun k => x (k + 1) - x k + J k
      let ρ : ℕ → ℝ := fun k => (J k + J (k + 1)) / w k
      let a : ℕ → ℝ := fun k => (1 - δ / 2) * Real.sqrt (1 - 1 / θ) * lilScale (x (k + 1))
      let b : ℕ → ℝ := fun k => max 1 (ε * Real.sqrt (x (k + 1) / Real.log (Real.log (x k))))
      (∀ k, k₀ ≤ k → 0 < w k ∧ 0 < a k ∧ 0 ≤ ρ k ∧ ρ k ≤ ρ₀ ∧
        w k * (1 - ρ k) = x (k + 1) - x k - J (k + 1) ∧ A₀ * w k ≤ a k ^ 2 ∧
        a k * b k ≤ ε₀ * w k ∧ Real.exp (Real.exp 1) ≤ x k) ∧
      Tendsto (fun n => ∑ k ∈ Finset.range n,
        if k₀ ≤ k then Real.exp (-((1 + δ / 2) * (a k ^ 2 / (2 * w k)))) else 0) atTop atTop := by
  have hθ1 : 1 < θ := by linarith
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_pow_atTop_atTop_of_one_lt hθ1).eventually
    (ba_eventually δ θ ε ρ₀ ε₀ A₀ hδ0 hδ1 hθ hρ₀ hε₀))
  refine ⟨k₀, ?_⟩
  intro x J w ρ a b
  have hxs : ∀ k, x (k + 1) = θ * x k := fun k => by
    show θ ^ (k + 1) = θ * θ ^ k
    ring
  have hpt : ∀ k, k₀ ≤ k → (0 < w k ∧ 0 < a k ∧ 0 ≤ ρ k ∧ ρ k ≤ ρ₀ ∧
      w k * (1 - ρ k) = x (k + 1) - x k - J (k + 1) ∧ A₀ * w k ≤ a k ^ 2 ∧
      a k * b k ≤ ε₀ * w k ∧ 1 / Real.log (x (k + 1)) ≤
        Real.exp (-((1 + δ / 2) * (a k ^ 2 / (2 * w k))))) := by
    intro k hk
    obtain ⟨h1, h2, h3, h4', h5, h6, h7⟩ := hk₀ k hk (x (k + 1)) (hxs k)
    exact ba_point δ θ ε ρ₀ ε₀ A₀ (x k) (x (k + 1)) (J k) (J (k + 1)) (w k) (ρ k) (a k) (b k)
      hδ0 hδ1 hθ hε hε₀ hρ₀ h4 (hxs k) rfl rfl rfl rfl rfl rfl h1 h2 h3 h4' h5 h6 h7
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6, p7, -⟩ := hpt k hk
    exact ⟨p1, p2, p3, p4, p5, p6, p7, (hk₀ k hk (x (k + 1)) (hxs k)).1⟩
  · refine ba_diverge θ k₀ _ hθ1 (fun n => ?_) (fun k hk => ?_)
    · split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    · rw [if_pos hk]
      have h := (hpt k hk).2.2.2.2.2.2.2
      have hl : Real.log (x (k + 1)) = ((k + 1 : ℕ) : ℝ) * Real.log θ := Real.log_pow θ (k + 1)
      rwa [hl] at h

/-- The parameters of the blocks. -/
theorem block_arith : BlockArith := by
  intro δ hδ0 hδ1
  have hθ : (256 : ℝ) ≤ (16 / δ) ^ 2 := by
    have h : 16 ≤ 16 / δ := by rw [le_div_iff₀ hδ0]; linarith
    nlinarith
  refine ⟨(16 / δ) ^ 2, δ / 2, δ / 4, by linarith, by positivity, by positivity,
    ba_theta_cond δ hδ0 hδ1, ?_⟩
  intro ρ₀ ε₀ A₀ hρ₀ hε₀
  exact ⟨ε₀ / 8, by positivity,
    ba_core δ ((16 / δ) ^ 2) (ε₀ / 8) ρ₀ ε₀ A₀ hδ0 hδ1 hθ (by positivity) hρ₀ hε₀ (by linarith)⟩

end CERW.Generic.Martingale.LilAssembly
