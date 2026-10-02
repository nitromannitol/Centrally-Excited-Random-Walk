import CERW.Generic.Martingale.Tilt.Statements

/-!
# The choice of the parameters of the tail

Real arithmetic: with `θ = min η 1 / 40`, `w = θ a`, `s = (a + w) / (v (1 - ρ))` and `l = w / v`,
the window starts at `a`, both weighted tails are at most `1/4`, and the prefactor beats
`exp (-(1 + η) a² / (2 v))`.
-/

namespace CERW.Generic.Martingale.Tilt

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.ExpMart

/-- `exp E ≤ 1/4` once `E ≤ -2`. -/
lemma ta_exp_le_quarter {E : ℝ} (h : E ≤ -2) : Real.exp E ≤ 1 / 4 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 : (4 : ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith
  have h4 : Real.exp E ≤ Real.exp (-2) := Real.exp_le_exp.2 h
  rw [Real.exp_neg 2] at h4
  refine h4.trans ?_
  rw [one_div]
  exact inv_anti₀ (by norm_num) h3

/-- `exp (-A) ≤ exp (-F) / 2` once `F + 1 ≤ A`. -/
lemma ta_exp_le_mul_half {A F : ℝ} (h : F + 1 ≤ A) :
    Real.exp (-A) ≤ Real.exp (-F) * (1 / 2) := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]; exact inv_anti₀ (by norm_num) h1
  calc Real.exp (-A) ≤ Real.exp (-F + -1) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-F) * Real.exp (-1) := Real.exp_add _ _
    _ ≤ Real.exp (-F) * (1 / 2) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

/-- Bounds on `c = (1 + θ) / (1 - ρ)`. -/
lemma ta_c_bounds {θ ρ c : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 40) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ θ) (hc : c * (1 - ρ) = 1 + θ) : 1 ≤ c ∧ c ≤ 1 + 3 * θ := by
  have h1 : 0 < 1 - ρ := by linarith
  constructor
  · by_contra hlt
    have hlt' : c < 1 := lt_of_not_ge hlt
    have : c * (1 - ρ) < 1 * (1 - ρ) := mul_lt_mul_of_pos_right hlt' h1
    linarith
  · by_contra hgt
    have hgt' : 1 + 3 * θ < c := lt_of_not_ge hgt
    have : (1 + 3 * θ) * (1 - ρ) < c * (1 - ρ) := mul_lt_mul_of_pos_right hgt' h1
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 3 * θ) (sub_nonneg.2 hρ),
      mul_nonneg hθ.le (by linarith : (0 : ℝ) ≤ 1 - 3 * θ)]

/-- The exponent of the weighted tails is at most `-2`. -/
lemma ta_E_le {x e θ K : ℝ} (hK : K ≤ 3) (he0 : 0 ≤ e) (he : e ≤ θ ^ 2 / 1600)
    (hx0 : 0 ≤ x) (hx6 : 6 ≤ θ ^ 2 * x) :
    θ ^ 2 * x / 2 - θ ^ 2 * x + 2 * K * e * x ≤ -2 := by
  have h1 : K * e ≤ 3 * (θ ^ 2 / 1600) := mul_le_mul hK he he0 (by norm_num)
  have h2 : K * e * x ≤ 3 * (θ ^ 2 / 1600) * x := mul_le_mul_of_nonneg_right h1 hx0
  linarith

/-- The bound on the prefactor exponent. -/
lemma ta_F_le {θ ρ e c : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 40) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ θ) (he : e ≤ θ ^ 2 / 1600) (hc1 : 1 ≤ c) (hc : c ≤ 1 + 3 * θ) :
    c ^ 2 * (1 + ρ) + 2 * c * θ + 4 * e * c ^ 3 ≤ 1 + 10 * θ := by
  have hc0 : 0 ≤ c := by linarith
  have h1 : c ^ 2 ≤ (1 + 3 * θ) ^ 2 := pow_le_pow_left₀ hc0 hc 2
  have h2 : c ^ 2 * (1 + ρ) ≤ (1 + 3 * θ) ^ 2 * (1 + θ) :=
    mul_le_mul h1 (by linarith) (by linarith) (by positivity)
  have h3 : c ^ 3 ≤ (11 / 10) ^ 3 := pow_le_pow_left₀ hc0 (by linarith) 3
  have h4 : e * c ^ 3 ≤ (θ ^ 2 / 1600) * (11 / 10) ^ 3 :=
    mul_le_mul he h3 (by positivity) (by positivity)
  have h5 : θ * θ ≤ θ * (1 / 40) := mul_le_mul_of_nonneg_left hθ1 hθ.le
  have h6 : θ * θ * θ ≤ θ * θ * (1 / 40) := mul_le_mul_of_nonneg_left hθ1 (by positivity)
  have h7 : c * θ ≤ (1 + 3 * θ) * θ := mul_le_mul_of_nonneg_right hc hθ.le
  norm_num at h4
  nlinarith

/-- The pure-arithmetic core, in terms of `x = a² / v`, `e = a b / v` and `c`. -/
lemma ta_pure {η θ ρ x e c : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 40) (hθη : 40 * θ ≤ η)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ θ) (he0 : 0 ≤ e) (he : e ≤ θ ^ 2 / 1600) (hx0 : 0 ≤ x)
    (hx6 : 6 ≤ θ ^ 2 * x) (hx4 : 4 ≤ η * x) (hc : c * (1 - ρ) = 1 + θ) :
    (c + θ) * e ≤ 1 / 2 ∧
    Real.exp (θ ^ 2 * x / 2 - θ ^ 2 * x + 2 * ((c + θ) ^ 3 + c ^ 3) * e * x) ≤ 1 / 4 ∧
    Real.exp (θ ^ 2 * x / 2 - θ ^ 2 * x + 2 * ((c - θ) ^ 3 + c ^ 3) * e * x) ≤ 1 / 4 ∧
    Real.exp (-((1 + η) * (x / 2))) ≤
      Real.exp (-(x * c ^ 2 * (1 + ρ) / 2 + c * θ * x + 2 * c ^ 3 * e * x)) * (1 / 2) := by
  obtain ⟨hc1, hc3⟩ := ta_c_bounds hθ hθ1 hρ0 hρ hc
  have hc0 : 0 ≤ c := by linarith
  have hcθ : c + θ ≤ 11 / 10 := by linarith
  have hc43 : c ≤ 43 / 40 := by linarith
  have hcube : c ^ 3 ≤ (43 / 40) ^ 3 := pow_le_pow_left₀ hc0 hc43 3
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (c + θ) * e ≤ (11 / 10) * (θ ^ 2 / 1600) := mul_le_mul hcθ he he0 (by norm_num)
    have h5 : θ * θ ≤ θ * (1 / 40) := mul_le_mul_of_nonneg_left hθ1 hθ.le
    nlinarith
  · refine ta_exp_le_quarter (ta_E_le ?_ he0 he hx0 hx6)
    have h1 : (c + θ) ^ 3 ≤ (11 / 10) ^ 3 := pow_le_pow_left₀ (by linarith) hcθ 3
    norm_num at h1 hcube
    linarith
  · refine ta_exp_le_quarter (ta_E_le ?_ he0 he hx0 hx6)
    have h1 : (c - θ) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    norm_num at hcube
    linarith
  · have hF := ta_F_le hθ hθ1 hρ0 hρ he hc1 hc3
    have hF2 : (c ^ 2 * (1 + ρ) + 2 * c * θ + 4 * e * c ^ 3) * (x / 2)
        ≤ (1 + 10 * θ) * (x / 2) :=
      mul_le_mul_of_nonneg_right hF (by positivity)
    have hθx : 40 * θ * x ≤ η * x := mul_le_mul_of_nonneg_right hθη hx0
    refine ta_exp_le_mul_half ?_
    nlinarith

/-- The arithmetic of `tail_arith`, with the parameters named. -/
lemma ta_main {η θ v a ρ b w s l : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 40)
    (hθη : 40 * θ ≤ η) (hv : 0 < v) (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ θ)
    (hb : 0 ≤ b)
    (hA : (6 / θ ^ 2 + 1 / (10 * θ)) * v ≤ a ^ 2) (hε : a * b ≤ θ ^ 2 / 1600 * v)
    (hw : w = θ * a) (hs : s = (a + w) / (v * (1 - ρ))) (hl : l = w / v) :
    0 ≤ s ∧ 0 ≤ l ∧ l ≤ s ∧ (s + l) * b ≤ 1 / 2 ∧ s * v * (1 - ρ) - w = a ∧
      Real.exp (l ^ 2 * v / 2 + 2 * ((s + l) ^ 3 + s ^ 3) * b * v - l * w) ≤ 1 / 4 ∧
      Real.exp (l ^ 2 * v / 2 + 2 * ((s - l) ^ 3 + s ^ 3) * b * v - l * w) ≤ 1 / 4 ∧
      Real.exp (-((1 + η) * (a ^ 2 / (2 * v)))) ≤
        Real.exp (-(s ^ 2 * v * (1 + ρ) / 2 + s * w + 2 * s ^ 3 * b * v)) * (1 / 2) := by
  obtain ⟨p, hp⟩ : ∃ p, p = a / v := ⟨_, rfl⟩
  have hpv : a = p * v := by rw [hp]; field_simp
  have hp0 : 0 < p := by rw [hp]; positivity
  obtain ⟨c, hcdef⟩ : ∃ c, c = (1 + θ) / (1 - ρ) := ⟨_, rfl⟩
  have h1ρ : 0 < 1 - ρ := by linarith
  have hc : c * (1 - ρ) = 1 + θ := by rw [hcdef]; field_simp
  have hsc : s = c * p := by
    rw [hs, hw, hcdef, hp]; field_simp
  have hlp : l = θ * p := by rw [hl, hw, hp]; field_simp
  subst hsc hlp hw
  subst hpv
  obtain ⟨hc1, hc3⟩ := ta_c_bounds hθ hθ1 hρ0 hρ hc
  have hx0 : 0 ≤ p ^ 2 * v := by positivity
  have hAx : 6 / θ ^ 2 + 1 / (10 * θ) ≤ p ^ 2 * v := by
    have h1 : (p * v) ^ 2 = (p ^ 2 * v) * v := by ring
    rw [h1] at hA
    exact le_of_mul_le_mul_right hA hv
  have hx6 : 6 ≤ θ ^ 2 * (p ^ 2 * v) := by
    have h0 : 0 < 1 / (10 * θ) := by positivity
    have h6 : 6 / θ ^ 2 ≤ p ^ 2 * v := by linarith
    have := (div_le_iff₀ (by positivity : 0 < θ ^ 2)).1 h6
    linarith
  have hx4 : 4 ≤ η * (p ^ 2 * v) := by
    have h0 : 0 < 6 / θ ^ 2 := by positivity
    have h4 : 1 / (10 * θ) ≤ p ^ 2 * v := by linarith
    have h5 := (div_le_iff₀ (by positivity : 0 < 10 * θ)).1 h4
    have h6 : 40 * θ * (p ^ 2 * v) ≤ η * (p ^ 2 * v) := mul_le_mul_of_nonneg_right hθη hx0
    linarith
  have he0 : 0 ≤ p * b := mul_nonneg hp0.le hb
  have he : p * b ≤ θ ^ 2 / 1600 := by
    have h1 : (p * b) * v ≤ (θ ^ 2 / 1600) * v := by linarith
    exact le_of_mul_le_mul_right h1 hv
  obtain ⟨k1, k2, k3, k4⟩ := ta_pure hθ hθ1 hθη hρ0 hρ he0 he hx0 hx6 hx4 hc
  have hc0 : 0 ≤ c := by linarith
  refine ⟨mul_nonneg hc0 hp0.le, mul_nonneg hθ.le hp0.le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) hp0.le
  · have e1 : (c * p + θ * p) * b = (c + θ) * (p * b) := by ring
    rw [e1]; exact k1
  · have e1 : c * p * v * (1 - ρ) = (c * (1 - ρ)) * (p * v) := by ring
    rw [e1, hc]; ring
  · convert k2 using 2; ring
  · convert k3 using 2; ring
  · have e1 : (p * v) ^ 2 / (2 * v) = (p ^ 2 * v) / 2 := by field_simp
    have e2 : (c * p) ^ 2 * v * (1 + ρ) / 2 + c * p * (θ * (p * v)) + 2 * (c * p) ^ 3 * b * v
        = (p ^ 2 * v) * c ^ 2 * (1 + ρ) / 2 + c * θ * (p ^ 2 * v)
          + 2 * c ^ 3 * (p * b) * (p ^ 2 * v) := by ring
    rw [e1, e2]; exact k4

theorem tail_arith : TailArith := by
  intro η hη
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = min η 1 / 40 := ⟨_, rfl⟩
  have hm : 0 < min η 1 := lt_min hη one_pos
  have hθ : 0 < θ := by rw [hθdef]; exact div_pos hm (by norm_num)
  have hθ1 : θ ≤ 1 / 40 := by rw [hθdef]; have := min_le_right η 1; linarith
  have hθη : 40 * θ ≤ η := by rw [hθdef]; have := min_le_left η 1; linarith
  refine ⟨θ, θ ^ 2 / 1600, 6 / θ ^ 2 + 1 / (10 * θ), θ, hθ, by linarith, by positivity, hθ,
    ?_⟩
  intro v a ρ b hv ha hρ0 hρ hb hA hε w s l
  exact ta_main hθ hθ1 hθη hv ha hρ0 hρ hb hA hε rfl rfl rfl

end CERW.Generic.Martingale.Tilt
