import CERW.Support.Statements
import CERW.Support.Norm.Freedman
import CERW.Support.Norm.MoreauCap
import CERW.Support.Norm.Geometry
import CERW.Support.Norm.Crossing
import CERW.Support.Norm.BallLayer
import CERW.Support.Norm.Radial
import CERW.Support.Norm.OuterCrossing
import CERW.Support.Norm.CellGradient
import CERW.Support.Norm.Coarse
import CERW.Support.Norm.LocalTime
import CERW.Support.Norm.ContactPotential
import CERW.Support.Norm.VectorBound
import CERW.Support.Geometry.BallCompare
import CERW.Support.Main.BorelCantelli
import CERW.Support.Main.ScaleLimits

/-!
# The limit shape for a norm

Proposition 5.1 (`prop:norm-shape`): for every `p > 0` there is a constant `C`, not depending on
the choice of subgradients, such that with probability at least `1 - C n^{-p}` the inner radius
`inf_{y ∉ D_n} Ψ(y)`, the outer radius `max_{j ≤ n} Ψ(X_j)` and the local times `ℓ_n` are within
the stated rates of `r_n` and of the cone `2dε (r_n - Ψ)_+`. It follows from the local-time
potential estimate, the coarse bounds, the contact bound, the layer and ball potentials, the
Moreau cap and the outer crossing lemma, which are carried as hypotheses, together with the
martingale events of Section 5.2 (the vector bound `eq:vector`, from
`CERW.Support.Norm.VectorBound`, and the linear martingales `eq:linear-mart`), proved by
Freedman's inequality at dyadic brackets.

The inner radius is determined by the mass identity `∫_{B(0,S)} U_{D_n} = 2ε ∫_{D_n} Ψ` and the
local-time approximation of the potential, the excess `∫_E (Ψ - b)` is bounded through the
potential at a contact point of the cell set, and the outer radius through the Moreau envelope.
Theorem 2.1 (`thm:norm-shape`) follows from Proposition 5.1 with `p = 2` by the Borel–Cantelli
lemma.

The names `layer_potential`, `norm_ball_potential`, `norm_potential_geometry`, `moreau_cap` and
`drift_crossing` are also the names of proved theorems in `CERW.Support.Norm`; the two assembly
theorems are therefore declared from within `CERW.Support.Statements`, where these names refer to
the statements.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The rates -/

/-- The rate `q` as a function of `r` and `ℓ = log n`. -/
private noncomputable def rateQ (d : ℕ) (r ℓ : ℝ) : ℝ :=
  if d = 2 then Real.sqrt (ℓ / r) else ℓ / r

end CERW.Support.Norm

namespace CERW.Support.Norm.RateScales

/-- A power of a square root is a power of the radicand: `(√x)^a = x^(a/2)`. -/
private theorem sqrt_rpow_eq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    Real.sqrt x ^ a = x ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

/-- For positive `r` and `ℓ`, `r * (ℓ / r)^a = r^(1 - a) * ℓ^a`. -/
private theorem mul_div_rpow_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) (a : ℝ) :
    r * (ℓ / r) ^ a = r ^ (1 - a) * ℓ ^ a := by
  rw [Real.div_rpow hℓ.le hr.le, Real.rpow_sub hr, Real.rpow_one]
  ring

/-- The exponent `1 - 1/(d+1)` equals `d/(d+1)`. -/
private theorem one_sub_inv_succ (d : ℕ) :
    (1 : ℝ) - 1 / ((d : ℝ) + 1) = (d : ℝ) / ((d : ℝ) + 1) := by
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The exponent `1/(d+1) + 1` equals `(d+2)/(d+1)`. -/
private theorem inv_succ_add_one (d : ℕ) :
    (1 : ℝ) / ((d : ℝ) + 1) + 1 = ((d : ℝ) + 2) / ((d : ℝ) + 1) := by
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The exponent `1/(d+1) - 1` equals `-(d/(d+1))`. -/
private theorem inv_succ_sub_one (d : ℕ) :
    (1 : ℝ) / ((d : ℝ) + 1) - 1 = -((d : ℝ) / ((d : ℝ) + 1)) := by
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- For positive `X`, the quantity `((d+1) n / X)^(1/(d+1))` is
`((d+1)/X)^(1/(d+1)) * n^(1/(d+1))`. -/
private theorem scale_eq_mul (d : ℕ) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    (((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1)) =
      (((d : ℝ) + 1) / X) ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [show ((d : ℝ) + 1) * n / X = ((d : ℝ) + 1) / X * n by ring,
    Real.mul_rpow (div_pos hd1 hX).le (Nat.cast_nonneg n)]

end CERW.Support.Norm.RateScales

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- `r q^{1/2}` is the rate of the inner radius in Proposition 5.1. -/
private theorem rate_inner_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    r * rateQ d r ℓ ^ ((1 : ℝ) / 2) =
      if d = 2 then r ^ ((3 : ℝ) / 4) * ℓ ^ ((1 : ℝ) / 4) else (r * ℓ) ^ ((1 : ℝ) / 2) := by
  have hq : 0 ≤ ℓ / r := div_nonneg hℓ.le hr.le
  by_cases h2 : d = 2
  · simp only [rateQ, if_pos h2]
    rw [RateScales.sqrt_rpow_eq hq, RateScales.mul_div_rpow_eq hr hℓ]
    norm_num
  · simp only [rateQ, if_neg h2]
    rw [RateScales.mul_div_rpow_eq hr hℓ, Real.mul_rpow hr.le hℓ.le]
    norm_num

/-- `r q^{1/(d+1)}` is the rate of the local times in Proposition 5.1. -/
private theorem rate_local_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) =
      if d = 2 then r ^ ((5 : ℝ) / 6) * ℓ ^ ((1 : ℝ) / 6)
      else r ^ ((d : ℝ) / (d + 1)) * ℓ ^ ((1 : ℝ) / (d + 1)) := by
  have hq : 0 ≤ ℓ / r := div_nonneg hℓ.le hr.le
  by_cases h2 : d = 2
  · have hd2 : (d : ℝ) = 2 := by exact_mod_cast h2
    simp only [rateQ, if_pos h2]
    rw [RateScales.sqrt_rpow_eq hq, RateScales.mul_div_rpow_eq hr hℓ, hd2]
    norm_num
  · simp only [rateQ, if_neg h2]
    rw [RateScales.mul_div_rpow_eq hr hℓ, RateScales.one_sub_inv_succ]

/-- `r q^{1/(d+1)} log n` is the rate of the outer radius in Proposition 5.1. -/
private theorem rate_outer_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ =
      if d = 2 then r ^ ((5 : ℝ) / 6) * ℓ ^ ((7 : ℝ) / 6)
      else r ^ ((d : ℝ) / (d + 1)) * ℓ ^ (((d : ℝ) + 2) / (d + 1)) := by
  rw [rate_local_eq hr hℓ]
  by_cases h2 : d = 2
  · simp only [if_pos h2]
    rw [mul_assoc, ← Real.rpow_add_one hℓ.ne']
    norm_num
  · simp only [if_neg h2]
    rw [mul_assoc, ← Real.rpow_add_one hℓ.ne', RateScales.inv_succ_add_one]

/-- The scale `r_n = ((d+1) n / X)^{1/(d+1)}` tends to infinity. -/
private theorem tendsto_scale (d : ℕ) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun n : ℕ => (((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1))) atTop atTop := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have he : (0 : ℝ) < (1 : ℝ) / ((d : ℝ) + 1) := div_pos one_pos hd1
  have hlin : Tendsto (fun n : ℕ => ((d : ℝ) + 1) * n / X) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hd1).atTop_div_const hX
  exact (tendsto_rpow_atTop he).comp hlin

/-- Every real power of `log n` is negligible against the scale `r_n`. -/
private theorem tendsto_log_rpow_div_scale (d : ℕ) {X : ℝ} (hX : 0 < X) (K : ℝ) :
    Tendsto (fun n : ℕ => Real.log n ^ K / (((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1)))
      atTop (𝓝 0) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have he : (0 : ℝ) < (1 : ℝ) / ((d : ℝ) + 1) := div_pos one_pos hd1
  have hbase : Tendsto (fun n : ℕ => Real.log n ^ K / (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)))
      atTop (𝓝 0) :=
    ((isLittleO_log_rpow_rpow_atTop K he).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have hmul := hbase.const_mul ((((d : ℝ) + 1) / X) ^ ((1 : ℝ) / ((d : ℝ) + 1)))⁻¹
  rw [mul_zero] at hmul
  refine hmul.congr (fun n => ?_)
  rw [RateScales.scale_eq_mul d hX n]
  ring

/-- The scale is small against `n`: `r_n / n → 0`. -/
private theorem tendsto_scale_div_self (d : ℕ) (hd : 1 ≤ d) {X : ℝ} (hX : 0 < X) :
    Tendsto (fun n : ℕ => (((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1)) / n) atTop (𝓝 0) := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hde : (0 : ℝ) < (d : ℝ) / ((d : ℝ) + 1) := div_pos (Nat.cast_pos.mpr hd) hd1
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ (-((d : ℝ) / ((d : ℝ) + 1)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hde).comp tendsto_natCast_atTop_atTop
  have hmul := hbase.const_mul ((((d : ℝ) + 1) / X) ^ ((1 : ℝ) / ((d : ℝ) + 1)))
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [RateScales.scale_eq_mul d hX n, mul_div_assoc, ← Real.rpow_sub_one hn0.ne',
    RateScales.inv_succ_sub_one]

end CERW.Support.Norm

namespace CERW.Support.Norm.RateInequalities

variable {d : ℕ}

/-- The rate is positive for positive `r` and `ℓ`. -/
private lemma rateQ_pos (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) : 0 < rateQ d r ℓ := by
  unfold rateQ
  split_ifs
  · exact Real.sqrt_pos.2 (div_pos hℓ hr)
  · exact div_pos hℓ hr

/-- The rate is at most `1` once `ℓ ≤ r`. -/
private lemma rateQ_le_one (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓr : ℓ ≤ r) :
    rateQ d r ℓ ≤ 1 := by
  have h : ℓ / r ≤ 1 := (div_le_one hr).2 hℓr
  unfold rateQ
  split_ifs
  · exact Real.sqrt_le_one.2 h
  · exact h

/-- The rate dominates `ℓ / r` once `ℓ ≤ r`. -/
private lemma div_le_rateQ (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) :
    ℓ / r ≤ rateQ d r ℓ := by
  have h0 : 0 ≤ ℓ / r := (div_pos hℓ hr).le
  have h1 : ℓ / r ≤ 1 := (div_le_one hr).2 hℓr
  unfold rateQ
  split_ifs
  · exact (Real.le_sqrt h0 h0).2 (pow_le_of_le_one h0 h1 two_ne_zero)
  · exact le_rfl

/-- The scale regime: `M ℓ^(d+5) ≤ r` with `M ≥ 1` and `ℓ ≥ 1` gives `ℓ ^ (d+5) ≤ r`,
`ℓ ^ 3 ≤ r` and `ℓ ≤ r`. -/
private lemma regime {d : ℕ} (hd : 2 ≤ d) {ℓ r M : ℝ} (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ)
    (h : M * ℓ ^ (d + 5) ≤ r) : ℓ ^ (d + 5) ≤ r ∧ ℓ ^ 3 ≤ r ∧ ℓ ≤ r := by
  have hpos : 0 ≤ ℓ ^ (d + 5) := pow_nonneg (by linarith) _
  have h1 : ℓ ^ (d + 5) ≤ r := (le_mul_of_one_le_left hpos hM).trans h
  have h2 : ℓ ^ 3 ≤ ℓ ^ (d + 5) := pow_le_pow_right₀ hℓ (by omega)
  have h3 : ℓ ≤ ℓ ^ 3 := le_self_pow₀ hℓ (by norm_num)
  exact ⟨h1, h2.trans h1, h3.trans (h2.trans h1)⟩

/-- Taking the power `1 / (d + 1)` undoes raising to the power `d + 1`. -/
private lemma pow_succ_rpow_inv (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have h : ((d + 1 : ℕ) : ℝ) * ((1 : ℝ) / (d + 1)) = 1 := by
    push_cast
    field_simp
  rw [h, Real.rpow_one]

/-- The square of the half power of the rate is the rate. -/
private lemma rpow_half_sq (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ) :
    (rateQ d r ℓ ^ ((1 : ℝ) / 2)) ^ 2 = rateQ d r ℓ := by
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (rateQ_pos d hr hℓ).le

/-- The half power of the rate is at most the `1 / (d + 1)` power of the rate. -/
private lemma rpow_half_le_rpow_inv (d : ℕ) (hd : 1 ≤ d) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ)
    (hℓr : ℓ ≤ r) :
    rateQ d r ℓ ^ ((1 : ℝ) / 2) ≤ rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) + 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact Real.rpow_le_rpow_of_exponent_ge (rateQ_pos d hr hℓ) (rateQ_le_one d hr hℓr)
    (one_div_le_one_div_of_le (by norm_num) hd')

/-- The fluctuation scale is at most `r` times the half power of the rate. -/
private lemma fluct_le {r ℓ : ℝ} (hr : 0 < r) (hℓ : 1 ≤ ℓ) (hℓ3 : ℓ ^ 3 ≤ r) :
    (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) ≤
      r * rateQ d r ℓ ^ ((1 : ℝ) / 2) := by
  have hℓ0 : 0 < ℓ := by linarith
  by_cases hd2 : d = 2
  · rw [if_pos hd2]
    have hq : rateQ d r ℓ = Real.sqrt (ℓ / r) := by simp [rateQ, hd2]
    rw [hq, ← Real.sqrt_eq_rpow]
    have hsr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
    have hp2 : Real.sqrt (Real.sqrt (ℓ / r)) ^ 2 = Real.sqrt (ℓ / r) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have hp4 : Real.sqrt (Real.sqrt (ℓ / r)) ^ 4 = ℓ / r := by
      calc Real.sqrt (Real.sqrt (ℓ / r)) ^ 4
          = (Real.sqrt (Real.sqrt (ℓ / r)) ^ 2) ^ 2 := by ring
        _ = ℓ / r := by rw [hp2]; exact Real.sq_sqrt (div_pos hℓ0 hr).le
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num)
      (mul_nonneg hr.le (Real.sqrt_nonneg _)) ?_
    have hl : (Real.sqrt r * ℓ) ^ 4 = r ^ 2 * ℓ ^ 4 := by
      calc (Real.sqrt r * ℓ) ^ 4 = (Real.sqrt r ^ 2) ^ 2 * ℓ ^ 4 := by ring
        _ = r ^ 2 * ℓ ^ 4 := by rw [hsr]
    have hrr : (r * Real.sqrt (Real.sqrt (ℓ / r))) ^ 4 = r ^ 3 * ℓ := by
      rw [mul_pow, hp4]
      field_simp
    rw [hl, hrr]
    calc r ^ 2 * ℓ ^ 4 = (r ^ 2 * ℓ) * ℓ ^ 3 := by ring
      _ ≤ (r ^ 2 * ℓ) * r := mul_le_mul_of_nonneg_left hℓ3 (by positivity)
      _ = r ^ 3 * ℓ := by ring
  · rw [if_neg hd2]
    have hq : rateQ d r ℓ = ℓ / r := by simp [rateQ, hd2]
    rw [hq, ← Real.sqrt_eq_rpow]
    apply le_of_eq
    calc Real.sqrt (r * ℓ) = Real.sqrt (r ^ 2 * (ℓ / r)) := by
          congr 1
          field_simp
      _ = r * Real.sqrt (ℓ / r) := by rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]

/-- Mean value bound `y^(n+1) - x^(n+1) ≤ (n+1) (y - x) y^n` for `0 ≤ x ≤ y`. -/
private lemma pow_succ_sub_pow_succ_le (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y ^ (n + 1) - x ^ (n + 1) ≤ ((n : ℝ) + 1) * (y - x) * y ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : x ^ (k + 1) ≤ y ^ (k + 1) := pow_le_pow_left₀ hx hxy _
    have h2 : 0 ≤ y - x := sub_nonneg.2 hxy
    have h3 : (y - x) * x ^ (k + 1) ≤ (y - x) * y ^ (k + 1) :=
      mul_le_mul_of_nonneg_left h1 h2
    have hy : 0 ≤ y := hx.trans hxy
    have h4 : y * (y ^ (k + 1) - x ^ (k + 1)) ≤ y * (((k : ℝ) + 1) * (y - x) * y ^ k) :=
      mul_le_mul_of_nonneg_left ih hy
    calc y ^ (k + 1 + 1) - x ^ (k + 1 + 1)
        = y * (y ^ (k + 1) - x ^ (k + 1)) + (y - x) * x ^ (k + 1) := by ring
      _ ≤ y * (((k : ℝ) + 1) * (y - x) * y ^ k) + (y - x) * y ^ (k + 1) := add_le_add h4 h3
      _ = (((k + 1 : ℕ) : ℝ) + 1) * (y - x) * y ^ (k + 1) := by push_cast; ring

/-- Mean value bound `y^n - x^n ≤ n (y - x) y^(n-1)` for `0 ≤ x ≤ y` and `n ≥ 1`. -/
private lemma pow_sub_pow_le_mul {n : ℕ} (hn : 1 ≤ n) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y ^ n - x ^ n ≤ n * (y - x) * y ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using pow_succ_sub_pow_succ_le k hx hxy

/-- Bound on the shell term: `(b + s)^d - b^d ≤ d s (K^(d-1) r^(d-1))` when `b + s ≤ K r`. -/
private lemma shell_bound {d : ℕ} (hd : 1 ≤ d) {b s K r : ℝ} (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hK : b + s ≤ K * r) :
    (b + s) ^ d - b ^ d ≤ d * s * (K ^ (d - 1) * r ^ (d - 1)) := by
  have h1 := pow_sub_pow_le_mul hd hb (le_add_of_nonneg_right hs : b ≤ b + s)
  have h2 : (b + s) ^ (d - 1) ≤ (K * r) ^ (d - 1) :=
    pow_le_pow_left₀ (add_nonneg hb hs) hK _
  have h3 : (d : ℝ) * s * (b + s) ^ (d - 1) ≤ d * s * (K * r) ^ (d - 1) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg (Nat.cast_nonneg d) hs)
  rw [add_sub_cancel_left] at h1
  calc (b + s) ^ d - b ^ d ≤ d * s * (b + s) ^ (d - 1) := by
        have : (d : ℝ) * s * (b + s) ^ (d - 1) = d * (b + s - b) * (b + s) ^ (d - 1) := by ring
        rw [this, ← add_sub_cancel_left (a := b) (b := s)]
        simpa using h1
    _ ≤ d * s * (K * r) ^ (d - 1) := h3
    _ = d * s * (K ^ (d - 1) * r ^ (d - 1)) := by rw [mul_pow]

/-- The volume of the shell is at most `(V d (C_R+1)^(d-1) + C_I C_c) r^d p`. -/
private lemma ev_bound {d : ℕ} (hd : 1 ≤ d) {V C_R C_c C_I r p b I Ev : ℝ} (hV : 0 < V)
    (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) (hb : 0 < b) (hbR : b ≤ C_R * r)
    (hI : I ≤ C_I * C_c * (r ^ (d + 1) * p ^ 2))
    (hEv : Ev ≤ V * ((b + r * p) ^ d - b ^ d) + I / (r * p)) :
    Ev ≤ (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c) * (r ^ d * p) := by
  have hs : 0 < r * p := mul_pos hr hp
  have hK : b + r * p ≤ (C_R + 1) * r :=
    calc b + r * p ≤ C_R * r + r := add_le_add hbR (mul_le_of_le_one_right hr.le hp1)
      _ = (C_R + 1) * r := by ring
  have h1 := shell_bound hd hb.le hs.le hK
  have hrd : r * r ^ (d - 1) = r ^ d := mul_pow_sub_one (by omega) r
  have h2 : V * ((b + r * p) ^ d - b ^ d) ≤ V * d * (C_R + 1) ^ (d - 1) * (r ^ d * p) :=
    calc V * ((b + r * p) ^ d - b ^ d)
        ≤ V * (d * (r * p) * ((C_R + 1) ^ (d - 1) * r ^ (d - 1))) :=
          mul_le_mul_of_nonneg_left h1 hV.le
      _ = V * d * (C_R + 1) ^ (d - 1) * (r ^ d * p) := by rw [← hrd]; ring
  have h3 : I / (r * p) ≤ C_I * C_c * (r ^ d * p) := by
    rw [div_le_iff₀ hs]
    calc I ≤ C_I * C_c * (r ^ (d + 1) * p ^ 2) := hI
      _ = C_I * C_c * (r ^ d * p) * (r * p) := by ring
  calc Ev ≤ V * ((b + r * p) ^ d - b ^ d) + I / (r * p) := hEv
    _ ≤ V * d * (C_R + 1) ^ (d - 1) * (r ^ d * p) + C_I * C_c * (r ^ d * p) :=
        add_le_add h2 h3
    _ = (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c) * (r ^ d * p) := by ring

/-- For `0 ≤ x ≤ y`: `y^n (y - x) ≤ y^(n+1) - x^(n+1)`. -/
private lemma pow_succ_sub_ge (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y ^ n * (y - x) ≤ y ^ (n + 1) - x ^ (n + 1) := by
  have h1 : x ^ n ≤ y ^ n := pow_le_pow_left₀ hx hxy n
  have h2 : x * x ^ n ≤ x * y ^ n := mul_le_mul_of_nonneg_left h1 hx
  rw [pow_succ, pow_succ]
  linarith

/-- For `r > 0` and `b ≥ 0`: `r^d |r - b| ≤ |r^(d+1) - b^(d+1)|`. -/
private lemma pow_mul_abs_sub_le (d : ℕ) {r b : ℝ} (hr : 0 < r) (hb : 0 ≤ b) :
    r ^ d * |r - b| ≤ |r ^ (d + 1) - b ^ (d + 1)| := by
  rcases le_total b r with h | h
  · have h1 := pow_succ_sub_ge d hb h
    rw [abs_of_nonneg (sub_nonneg.2 h),
      abs_of_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hb h _))]
    exact h1
  · have h1 := pow_succ_sub_ge d hr.le h
    have h2 : r ^ d ≤ b ^ d := pow_le_pow_left₀ hr.le h d
    rw [abs_of_nonpos (sub_nonpos.2 h),
      abs_of_nonpos (sub_nonpos.2 (pow_le_pow_left₀ hr.le h _)), neg_sub, neg_sub]
    calc r ^ d * (b - r) ≤ b ^ d * (b - r) := mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 h)
      _ ≤ b ^ (d + 1) - r ^ (d + 1) := h1

/-- The comparison of the norm volume with the inner radius gives `|b - r| ≤ C r p`. -/
private lemma cmp_bound {d : ℕ} (hd : 1 ≤ d) {ε V C_m C_e C_δ C_Ev : ℝ} (hε : 0 < ε)
    (hV : 0 < V) (hC_m : 0 < C_m) (hC_e : 0 < C_e) (hC_δ : 0 < C_δ)
    {r p b Ev δ w nn : ℝ} (hr : 0 < r) (hb : 0 ≤ b)
    (hnn : nn = 2 * ε * d * V * r ^ (d + 1) / (d + 1)) (hw : w ≤ r * p)
    (hδ : δ ≤ C_δ * w) (hEv : Ev ≤ C_Ev * (r ^ d * p))
    (hcmp : |nn - 2 * ε * (d * V * b ^ (d + 1) / (d + 1))| ≤ C_m * r ^ d * δ + C_e * r * Ev) :
    |b - r| ≤ ((C_m * C_δ + C_e * C_Ev) / (2 * ε * d * V / (d + 1))) * (r * p) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 2 * ε * d * V / (d + 1) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    exact div_pos (mul_pos (mul_pos (mul_pos two_pos hε) hd') hV) (by positivity)
  have hcast : nn - 2 * ε * (d * V * b ^ (d + 1) / (d + 1)) = κ * (r ^ (d + 1) - b ^ (d + 1)) := by
    rw [hnn, hκdef]
    ring
  rw [hcast, abs_mul, abs_of_pos hκ] at hcmp
  have hδr : δ ≤ C_δ * (r * p) := hδ.trans (mul_le_mul_of_nonneg_left hw hC_δ.le)
  have h2 : C_m * r ^ d * δ + C_e * r * Ev ≤
      (C_m * C_δ + C_e * C_Ev) * (r ^ d * (r * p)) :=
    calc C_m * r ^ d * δ + C_e * r * Ev
        ≤ C_m * r ^ d * (C_δ * (r * p)) + C_e * r * (C_Ev * (r ^ d * p)) :=
          add_le_add (mul_le_mul_of_nonneg_left hδr (by positivity))
            (mul_le_mul_of_nonneg_left hEv (by positivity))
      _ = (C_m * C_δ + C_e * C_Ev) * (r ^ d * (r * p)) := by ring
  have h3 : r ^ d * (κ * |b - r|) ≤ r ^ d * ((C_m * C_δ + C_e * C_Ev) * (r * p)) :=
    calc r ^ d * (κ * |b - r|) = κ * (r ^ d * |r - b|) := by rw [abs_sub_comm]; ring
      _ ≤ κ * |r ^ (d + 1) - b ^ (d + 1)| :=
          mul_le_mul_of_nonneg_left (pow_mul_abs_sub_le d hr hb) hκ.le
      _ ≤ C_m * r ^ d * δ + C_e * r * Ev := hcmp
      _ ≤ (C_m * C_δ + C_e * C_Ev) * (r ^ d * (r * p)) := h2
      _ = r ^ d * ((C_m * C_δ + C_e * C_Ev) * (r * p)) := by ring
  have h4 : κ * |b - r| ≤ (C_m * C_δ + C_e * C_Ev) * (r * p) :=
    le_of_mul_le_mul_left h3 (pow_pos hr d)
  rw [← hκdef, div_mul_eq_mul_div, le_div_iff₀ hκ]
  linarith

/-- The upper bound for the local time mass in terms of the rate. -/
private lemma mass_bound {d : ℕ} {C_I C_c r q H I : ℝ} (hC_I : 0 < C_I) (hr : 0 < r)
    (hI : I ≤ C_I * r ^ d * H) (hH : H ≤ C_c * r * q) :
    I ≤ C_I * C_c * (r ^ (d + 1) * q) :=
  calc I ≤ C_I * r ^ d * H := hI
    _ ≤ C_I * r ^ d * (C_c * r * q) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = C_I * C_c * (r ^ (d + 1) * q) := by ring

/-- The power `1 / (d + 1)` of a bounded quantity. -/
private lemma rpow_inv_le_of_le (d : ℕ) {I c r q : ℝ} (hI : 0 ≤ I) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hq : 0 ≤ q) (h : I ≤ c * (r ^ (d + 1) * q)) :
    I ^ ((1 : ℝ) / (d + 1)) ≤ c ^ ((1 : ℝ) / (d + 1)) * (r * q ^ ((1 : ℝ) / (d + 1))) := by
  have he : (0 : ℝ) ≤ (1 : ℝ) / (d + 1) := by positivity
  calc I ^ ((1 : ℝ) / (d + 1)) ≤ (c * (r ^ (d + 1) * q)) ^ ((1 : ℝ) / (d + 1)) :=
        Real.rpow_le_rpow hI h he
    _ = c ^ ((1 : ℝ) / (d + 1)) * ((r ^ (d + 1)) ^ ((1 : ℝ) / (d + 1)) *
          q ^ ((1 : ℝ) / (d + 1))) := by
        rw [Real.mul_rpow hc (mul_nonneg (pow_nonneg hr _) hq),
          Real.mul_rpow (pow_nonneg hr _) hq]
    _ = c ^ ((1 : ℝ) / (d + 1)) * (r * q ^ ((1 : ℝ) / (d + 1))) := by
        rw [pow_succ_rpow_inv d hr]

/-- The square of `q ℓ^(d+1)` is at most `ℓ^(d+5) / r`. -/
private lemma rate_mul_pow_sq_le (hd : 2 ≤ d) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 1 ≤ ℓ)
    (hℓr : ℓ ^ (d + 5) ≤ r) :
    (rateQ d r ℓ * ℓ ^ (d + 1)) ^ 2 ≤ ℓ ^ (d + 5) / r := by
  have hℓ0 : 0 < ℓ := by linarith
  by_cases hd2 : d = 2
  · subst hd2
    have hq : rateQ 2 r ℓ = Real.sqrt (ℓ / r) := by simp [rateQ]
    rw [hq, mul_pow, Real.sq_sqrt (div_pos hℓ0 hr).le]
    apply le_of_eq
    ring
  · have hq : rateQ d r ℓ = ℓ / r := by simp [rateQ, hd2]
    rw [hq]
    have h1 : ℓ / r * ℓ ^ (d + 1) ≤ ℓ ^ (d + 5) / r := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hr.le
      calc ℓ * ℓ ^ (d + 1) = ℓ ^ (d + 2) := by ring
        _ ≤ ℓ ^ (d + 5) := pow_le_pow_right₀ hℓ (by omega)
    have h2 : ℓ ^ (d + 5) / r ≤ 1 := (div_le_one hr).2 hℓr
    have h3 : 0 ≤ ℓ / r * ℓ ^ (d + 1) := by positivity
    exact (pow_le_of_le_one h3 (h1.trans h2) two_ne_zero).trans h1

/-- The product of the `1 / (d + 1)` power of the rate with `ℓ` is small in the regime
`M ℓ^(d+5) ≤ r` with `M` large. -/
private lemma rate_local_mul_le (hd : 2 ≤ d) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r ℓ : ℝ, 1 ≤ ℓ → M * ℓ ^ (d + 5) ≤ r →
      rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ ≤ θ := by
  have hθ' : 0 < θ ^ (d + 1) := pow_pos hθ _
  refine ⟨1 / (θ ^ (d + 1)) ^ 2 + 1, by
    have : 0 ≤ 1 / (θ ^ (d + 1)) ^ 2 := by positivity
    linarith, ?_⟩
  intro r ℓ hℓ hM
  have hM1 : 1 ≤ 1 / (θ ^ (d + 1)) ^ 2 + 1 := by
    have : 0 ≤ 1 / (θ ^ (d + 1)) ^ 2 := by positivity
    linarith
  obtain ⟨hℓ5, -, hℓr⟩ := regime hd hM1 hℓ hM
  have hℓ0 : 0 < ℓ := by linarith
  have hr : 0 < r := by linarith
  have hsq := rate_mul_pow_sq_le hd hr hℓ hℓ5
  have hMθ : 1 ≤ (θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2 + 1) := by
    have h0 : (θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2) = 1 := by field_simp
    have h1 : 0 ≤ (θ ^ (d + 1)) ^ 2 := by positivity
    calc (1 : ℝ) = (θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2) := h0.symm
      _ ≤ (θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2 + 1) := by
          rw [mul_add, mul_one]
          linarith
  have hpos : 0 ≤ ℓ ^ (d + 5) := pow_nonneg hℓ0.le _
  have h2 : ℓ ^ (d + 5) / r ≤ (θ ^ (d + 1)) ^ 2 := by
    rw [div_le_iff₀ hr]
    calc ℓ ^ (d + 5) = 1 * ℓ ^ (d + 5) := (one_mul _).symm
      _ ≤ ((θ ^ (d + 1)) ^ 2 * (1 / (θ ^ (d + 1)) ^ 2 + 1)) * ℓ ^ (d + 5) :=
          mul_le_mul_of_nonneg_right hMθ hpos
      _ = (θ ^ (d + 1)) ^ 2 * ((1 / (θ ^ (d + 1)) ^ 2 + 1) * ℓ ^ (d + 5)) := by ring
      _ ≤ (θ ^ (d + 1)) ^ 2 * r := mul_le_mul_of_nonneg_left hM (by positivity)
  have hq0 : 0 ≤ rateQ d r ℓ := (rateQ_pos d hr hℓ0).le
  have hz : rateQ d r ℓ * ℓ ^ (d + 1) ≤ θ ^ (d + 1) :=
    le_of_pow_le_pow_left₀ two_ne_zero hθ'.le (hsq.trans h2)
  have hy : 0 ≤ rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hq0 _
  refine le_of_pow_le_pow_left₀ (n := d + 1) (Nat.succ_ne_zero d) hθ.le ?_
  rw [mul_pow, CERW.Support.Geometry.rpow_inv_succ_pow d hq0]
  exact hz

/-- The product `r q^(1/(d+1))` is at least `1` when `r, ℓ ≥ 1` and `ℓ ≤ r`. -/
private lemma one_le_mul_rpow (d : ℕ) {r ℓ : ℝ} (hr : 1 ≤ r) (hℓ : 1 ≤ ℓ) (hℓr : ℓ ≤ r) :
    1 ≤ r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) := by
  have hr0 : 0 < r := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hq0 : 0 ≤ rateQ d r ℓ := (rateQ_pos d hr0 hℓ0).le
  have hq : ℓ / r ≤ rateQ d r ℓ := div_le_rateQ d hr0 hℓ0 hℓr
  have hy : 0 ≤ rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hq0 _
  have h1 : 1 ≤ (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) := by
    rw [mul_pow, CERW.Support.Geometry.rpow_inv_succ_pow d hq0]
    calc (1 : ℝ) ≤ r ^ d * ℓ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hr) hℓ
      _ = r ^ (d + 1) * (ℓ / r) := by
          field_simp
          ring
      _ ≤ r ^ (d + 1) * rateQ d r ℓ := mul_le_mul_of_nonneg_left hq (by positivity)
  exact (one_le_pow_iff_of_nonneg (mul_nonneg hr0.le hy) (Nat.succ_ne_zero d)).1 h1

/-- The pure real-variable form of the outer-radius smallness conditions. -/
private lemma outer_core {K₁ C₀ η Λsq E θ r ℓ x : ℝ} (hK₁ : 0 < K₁) (hC₀ : 0 < C₀)
    (hη : 0 < η) (hΛsq : 0 < Λsq) (hE : 0 < E) (hθ : 0 < θ)
    (hθs : K₁ * (1 + C₀) * θ * (η + Λsq) ≤ 1 / 4) (hr : 0 < r) (hℓ : 0 ≤ ℓ) (hx : 1 ≤ x)
    (hxℓ : x * ℓ ≤ r * θ) :
    η * (K₁ * (1 + C₀ * x) * ℓ) ≤ r / 2 ∧ K₁ * (1 + C₀ * x) * ℓ * Λsq < r / 2 ∧
      E * (K₁ * (1 + C₀ * x) * ℓ) ≤ E * (K₁ * (1 + C₀)) * (x * ℓ) := by
  have hA : 0 < K₁ * (1 + C₀) := by positivity
  have hτ1 : K₁ * (1 + C₀ * x) * ℓ ≤ K₁ * (1 + C₀) * (x * ℓ) := by
    have h : 1 + C₀ * x ≤ (1 + C₀) * x := by
      have e : (1 + C₀) * x = x + C₀ * x := by ring
      linarith
    calc K₁ * (1 + C₀ * x) * ℓ ≤ K₁ * ((1 + C₀) * x) * ℓ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hK₁.le) hℓ
      _ = K₁ * (1 + C₀) * (x * ℓ) := by ring
  have hτ2 : K₁ * (1 + C₀ * x) * ℓ ≤ K₁ * (1 + C₀) * (r * θ) :=
    hτ1.trans (mul_le_mul_of_nonneg_left hxℓ hA.le)
  have hκ : 0 ≤ K₁ * (1 + C₀) * θ := by positivity
  have hκη : K₁ * (1 + C₀) * θ * η ≤ 1 / 4 := by
    have h1 : 0 ≤ K₁ * (1 + C₀) * θ * Λsq := mul_nonneg hκ hΛsq.le
    have h2 : K₁ * (1 + C₀) * θ * (η + Λsq) =
        K₁ * (1 + C₀) * θ * η + K₁ * (1 + C₀) * θ * Λsq := mul_add _ _ _
    linarith
  have hκΛ : K₁ * (1 + C₀) * θ * Λsq ≤ 1 / 4 := by
    have h1 : 0 ≤ K₁ * (1 + C₀) * θ * η := mul_nonneg hκ hη.le
    have h2 : K₁ * (1 + C₀) * θ * (η + Λsq) =
        K₁ * (1 + C₀) * θ * η + K₁ * (1 + C₀) * θ * Λsq := mul_add _ _ _
    linarith
  refine ⟨?_, ?_, ?_⟩
  · calc η * (K₁ * (1 + C₀ * x) * ℓ) ≤ η * (K₁ * (1 + C₀) * (r * θ)) :=
          mul_le_mul_of_nonneg_left hτ2 hη.le
      _ = r * (K₁ * (1 + C₀) * θ * η) := by ring
      _ ≤ r * (1 / 4) := mul_le_mul_of_nonneg_left hκη hr.le
      _ ≤ r / 2 := by linarith
  · calc K₁ * (1 + C₀ * x) * ℓ * Λsq ≤ K₁ * (1 + C₀) * (r * θ) * Λsq :=
          mul_le_mul_of_nonneg_right hτ2 hΛsq.le
      _ = r * (K₁ * (1 + C₀) * θ * Λsq) := by ring
      _ ≤ r * (1 / 4) := mul_le_mul_of_nonneg_left hκΛ hr.le
      _ < r / 2 := by linarith
  · calc E * (K₁ * (1 + C₀ * x) * ℓ) ≤ E * (K₁ * (1 + C₀) * (x * ℓ)) :=
          mul_le_mul_of_nonneg_left hτ1 hE.le
      _ = E * (K₁ * (1 + C₀)) * (x * ℓ) := by ring

end CERW.Support.Norm.RateInequalities

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The inner radius and the local mass are controlled by the rates, from the shell bound, the
volume comparison and the fluctuation bound on the boundary layer. -/
private theorem inner_rates_arith (hd : 2 ≤ d) {ε V : ℝ} (hε : 0 < ε) (hV : 0 < V)
    {C_R C_c C_δ C_I C_m C_e : ℝ} (hC_R : 0 < C_R) (hC_c : 0 < C_c) (hC_δ : 0 < C_δ)
    (hC_I : 0 < C_I) (hC_m : 0 < C_m) (hC_e : 0 < C_e) :
    ∃ C r₀ M : ℝ, 0 < C ∧ 0 < M ∧ ∀ r ℓ b I Ev H δ nn : ℝ, r₀ ≤ r → 1 ≤ ℓ →
      M * ℓ ^ (d + 5) ≤ r →
      nn = 2 * ε * d * V * r ^ (d + 1) / (d + 1) →
      0 < b → b ≤ C_R * r →
      0 ≤ I → I ≤ C_I * r ^ d * H →
      0 ≤ H → H ≤ C_c * r * rateQ d r ℓ →
      0 ≤ Ev → (∀ s : ℝ, 0 < s → Ev ≤ V * ((b + s) ^ d - b ^ d) + I / s) →
      0 ≤ δ → δ ≤ C_δ * (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) →
      |nn - 2 * ε * (d * V * b ^ (d + 1) / (d + 1))| ≤ C_m * r ^ d * δ + C_e * r * Ev →
      |b - r| ≤ C * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) ∧
        I ≤ C * (r ^ (d + 1) * rateQ d r ℓ) := by
  have hCI : 0 < C_I * C_c := mul_pos hC_I hC_c
  refine ⟨C_I * C_c + (C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
      (2 * ε * d * V / (d + 1)), 1, 1, ?_, one_pos, ?_⟩
  · have hd' : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
    positivity
  · intro r ℓ b I Ev H δ nn hr hℓ hM hnn hb hbR hI0 hI hH0 hH hEv0 hEv hδ0 hδ hcmp
    obtain ⟨-, hℓ3, hℓr⟩ := RateInequalities.regime hd le_rfl hℓ hM
    have hr0 : 0 < r := by linarith
    have hℓ0 : 0 < ℓ := by linarith
    have hq0 : 0 < rateQ d r ℓ := RateInequalities.rateQ_pos d hr0 hℓ0
    have hq1 : rateQ d r ℓ ≤ 1 := RateInequalities.rateQ_le_one d hr0 hℓr
    have hp0 : 0 < rateQ d r ℓ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hq0 _
    have hp2 : (rateQ d r ℓ ^ ((1 : ℝ) / 2)) ^ 2 = rateQ d r ℓ :=
      RateInequalities.rpow_half_sq d hr0 hℓ0
    have hp1 : rateQ d r ℓ ^ ((1 : ℝ) / 2) ≤ 1 := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_one.2 hq1
    have hw := RateInequalities.fluct_le (d := d) hr0 hℓ hℓ3
    have hmass := RateInequalities.mass_bound (d := d) hC_I hr0 hI hH
    have hmass' : I ≤ C_I * C_c * (r ^ (d + 1) * (rateQ d r ℓ ^ ((1 : ℝ) / 2)) ^ 2) := by
      rw [hp2]
      exact hmass
    have hEvb := RateInequalities.ev_bound (by omega) hV hr0 hp0 hp1 hb hbR hmass'
      (hEv (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) (mul_pos hr0 hp0))
    have hcb := RateInequalities.cmp_bound (by omega) hε hV hC_m hC_e hC_δ hr0 hb.le hnn hw
      hδ hEvb hcmp
    constructor
    · calc |b - r| ≤ ((C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
            (2 * ε * d * V / (d + 1))) * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) := hcb
        _ ≤ (C_I * C_c + (C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
            (2 * ε * d * V / (d + 1))) * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCI.le) (mul_nonneg hr0.le hp0.le)
    · calc I ≤ C_I * C_c * (r ^ (d + 1) * rateQ d r ℓ) := hmass
        _ ≤ (C_I * C_c + (C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
            (2 * ε * d * V / (d + 1))) * (r ^ (d + 1) * rateQ d r ℓ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hd' : (0 : ℝ) < d := Nat.cast_pos.2 (by omega)
          have : 0 ≤ (C_m * C_δ + C_e * (V * d * (C_R + 1) ^ (d - 1) + C_I * C_c)) /
              (2 * ε * d * V / (d + 1)) := by positivity
          exact le_add_of_nonneg_right this

/-- The profile error is controlled by `r q^(1/(d+1))`, from the inner-radius and mass bounds. -/
private theorem profile_arith (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {C_L C_I' C_b C_δ : ℝ} (hC_L : 0 < C_L) (hC_I' : 0 < C_I') (hC_b : 0 < C_b)
    (hC_δ : 0 < C_δ) :
    ∃ C r₀ M : ℝ, 0 < C ∧ 0 < M ∧ ∀ r ℓ b I δ : ℝ, r₀ ≤ r → 1 ≤ ℓ →
      M * ℓ ^ (d + 5) ≤ r →
      0 ≤ I → I ≤ C_I' * (r ^ (d + 1) * rateQ d r ℓ) →
      |b - r| ≤ C_b * (r * rateQ d r ℓ ^ ((1 : ℝ) / 2)) →
      0 ≤ δ → δ ≤ C_δ * (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) →
      δ + C_L * I ^ ((1 : ℝ) / (d + 1)) + 2 * d * ε * |b - r| ≤
        C * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) := by
  refine ⟨C_δ + C_L * C_I' ^ ((1 : ℝ) / (d + 1)) + 2 * d * ε * C_b, 1, 1, ?_, one_pos, ?_⟩
  · have : 0 < C_I' ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hC_I' _
    positivity
  · intro r ℓ b I δ hr hℓ hM hI0 hI hb hδ0 hδ
    obtain ⟨-, hℓ3, hℓr⟩ := RateInequalities.regime hd le_rfl hℓ hM
    have hr0 : 0 < r := by linarith
    have hℓ0 : 0 < ℓ := by linarith
    have hq0 : 0 < rateQ d r ℓ := RateInequalities.rateQ_pos d hr0 hℓ0
    have hp_y := RateInequalities.rpow_half_le_rpow_inv d (by omega) hr0 hℓ0 hℓr
    have hw := RateInequalities.fluct_le (d := d) hr0 hℓ hℓ3
    have hry : 0 ≤ r := hr0.le
    have h1 : δ ≤ C_δ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) :=
      hδ.trans (mul_le_mul_of_nonneg_left
        (hw.trans (mul_le_mul_of_nonneg_left hp_y hry)) hC_δ.le)
    have h2 : I ^ ((1 : ℝ) / (d + 1)) ≤
        C_I' ^ ((1 : ℝ) / (d + 1)) * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) :=
      RateInequalities.rpow_inv_le_of_le d hI0 hC_I'.le hry hq0.le hI
    have h3 : |b - r| ≤ C_b * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) :=
      hb.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp_y hry) hC_b.le)
    have hc1 : (0 : ℝ) ≤ 2 * d * ε := by positivity
    calc δ + C_L * I ^ ((1 : ℝ) / (d + 1)) + 2 * d * ε * |b - r|
        ≤ C_δ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) +
          C_L * (C_I' ^ ((1 : ℝ) / (d + 1)) * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) +
          2 * d * ε * (C_b * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) :=
          add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left h2 hC_L.le))
            (mul_le_mul_of_nonneg_left h3 hc1)
      _ = (C_δ + C_L * C_I' ^ ((1 : ℝ) / (d + 1)) + 2 * d * ε * C_b) *
          (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) := by ring

/-- The smallness conditions and the size bound for the outer-radius time scale. -/
private theorem outer_arith (hd : 2 ≤ d) {K₁ C₀ η Λsq E : ℝ} (hK₁ : 0 < K₁) (hC₀ : 0 < C₀)
    (hη : 0 < η) (hΛsq : 0 < Λsq) (hE : 0 < E) :
    ∃ C r₀ M : ℝ, 0 < C ∧ 0 < M ∧ ∀ r ℓ : ℝ, r₀ ≤ r → 1 ≤ ℓ → M * ℓ ^ (d + 5) ≤ r →
      η * (K₁ * (1 + C₀ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) * ℓ) ≤ r / 2 ∧
      K₁ * (1 + C₀ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) * ℓ * Λsq < r / 2 ∧
      E * (K₁ * (1 + C₀ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)))) * ℓ) ≤
        C * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ) := by
  have hA : 0 < K₁ * (1 + C₀) := by positivity
  have hP : 0 < η + Λsq := add_pos hη hΛsq
  have hθ : 0 < 1 / (4 * (K₁ * (1 + C₀)) * (η + Λsq)) := by positivity
  obtain ⟨M, hM1, hM⟩ := RateInequalities.rate_local_mul_le hd hθ
  refine ⟨E * (K₁ * (1 + C₀)), 1, M, by positivity, by linarith, ?_⟩
  intro r ℓ hr hℓ hMr
  obtain ⟨-, -, hℓr⟩ := RateInequalities.regime hd hM1 hℓ hMr
  have hr0 : 0 < r := by linarith
  have hy := hM r ℓ hℓ hMr
  have hx1 := RateInequalities.one_le_mul_rpow d hr hℓ hℓr
  have hxℓ : r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ ≤
      r * (1 / (4 * (K₁ * (1 + C₀)) * (η + Λsq))) := by
    calc r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ
        = r * (rateQ d r ℓ ^ ((1 : ℝ) / (d + 1)) * ℓ) := by ring
      _ ≤ r * (1 / (4 * (K₁ * (1 + C₀)) * (η + Λsq))) :=
          mul_le_mul_of_nonneg_left hy hr0.le
  have hθs : K₁ * (1 + C₀) * (1 / (4 * (K₁ * (1 + C₀)) * (η + Λsq))) * (η + Λsq) ≤ 1 / 4 := by
    apply le_of_eq
    field_simp
  exact RateInequalities.outer_core hK₁ hC₀ hη hΛsq hE hθ hθs hr0 (by linarith) hx1 hxℓ

end CERW.Support.Norm

namespace CERW.Support.Norm.BallFacts

open CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- For `d ≥ 1`, the largest value `Λ_Ψ` of a norm on the unit sphere is positive. -/
private theorem normMax_pos' (hd : 1 ≤ d) (hΨ : IsNorm Ψ) : 0 < normMax Ψ :=
  lt_of_lt_of_le (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd).1
    (ContactAssembly.normMin_le_normMax hd hΨ)

/-- The sublevel set `{Ψ < ρ}` of a norm is invariant under scaling: it is `ρ • {Ψ < 1}`
for `ρ > 0`. -/
private theorem normSublevel_eq_smul (hΨ : IsNorm Ψ) {ρ : ℝ} (hρ : 0 < ρ) :
    {v : EuclideanSpace ℝ (Fin d) | Ψ v < ρ} = ρ • {v : EuclideanSpace ℝ (Fin d) | Ψ v < 1} := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_smul_set]
  constructor
  · intro hv
    refine ⟨ρ⁻¹ • v, ?_, by rw [smul_inv_smul₀ hρ.ne']⟩
    rw [hΨ.smul, abs_inv, abs_of_pos hρ, inv_mul_lt_iff₀ hρ]
    simpa using hv
  · rintro ⟨w, hw, rfl⟩
    rw [hΨ.smul, abs_of_pos hρ]
    calc ρ * Ψ w < ρ * 1 := mul_lt_mul_of_pos_left hw hρ
      _ = ρ := mul_one ρ

end CERW.Support.Norm.BallFacts

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## Sublevel sets of a norm -/

/-- The sublevel sets `{Ψ < ρ}` of a norm are measurable. -/
private theorem measurableSet_normSublevel (hΨ : IsNorm Ψ) (ρ : ℝ) :
    MeasurableSet {v : EuclideanSpace ℝ (Fin d) | Ψ v < ρ} :=
  measurableSet_lt (CERW.Generic.Norm.norm_continuous hΨ).measurable measurable_const

/-- The sublevel set `{Ψ < ρ}` lies in the Euclidean ball of radius `ρ / c_Ψ`. -/
private theorem normSublevel_subset_ball (hd : 1 ≤ d) (hΨ : IsNorm Ψ) (ρ : ℝ) :
    {v : EuclideanSpace ℝ (Fin d) | Ψ v < ρ} ⊆ Metric.ball 0 (ρ / normMin Ψ) := by
  obtain ⟨hc, hle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  intro v hv
  rw [mem_ball_zero_iff, lt_div_iff₀ hc]
  calc ‖v‖ * normMin Ψ = normMin Ψ * ‖v‖ := mul_comm _ _
    _ ≤ Ψ v := hle v
    _ < ρ := hv

/-- The Euclidean ball of radius `ρ / Λ_Ψ` lies in the sublevel set `{Ψ < ρ}`. -/
private theorem ball_subset_normSublevel (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ρ : ℝ} :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (ρ / normMax Ψ) ⊆ {v | Ψ v < ρ} := by
  have hΛ := BallFacts.normMax_pos' hd hΨ
  intro v hv
  rw [mem_ball_zero_iff, lt_div_iff₀ hΛ] at hv
  calc Ψ v ≤ normMax Ψ * ‖v‖ := CERW.Generic.Norm.le_normMax_mul hΨ v
    _ = ‖v‖ * normMax Ψ := mul_comm _ _
    _ < ρ := hv

/-- The volume of the sublevel set `{Ψ < ρ}` is `ρ ^ d` times the volume of the unit ball of
`Ψ`. -/
private theorem volume_normSublevel (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume {v : EuclideanSpace ℝ (Fin d) | Ψ v < ρ} =
      ENNReal.ofReal (ρ ^ d * normBallVolume Ψ) := by
  rcases hρ.eq_or_lt with rfl | hρ
  · have hempty : {v : EuclideanSpace ℝ (Fin d) | Ψ v < 0} = ∅ := by
      ext v
      simpa using (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 v
    rw [hempty, measure_empty, zero_pow (by omega), zero_mul, ENNReal.ofReal_zero]
  · have hfin : volume {v : EuclideanSpace ℝ (Fin d) | Ψ v < 1} ≠ ⊤ :=
      ((measure_mono (normSublevel_subset_ball hd hΨ 1)).trans_lt measure_ball_lt_top).ne
    rw [BallFacts.normSublevel_eq_smul hΨ hρ, Measure.addHaar_smul_of_nonneg _ hρ.le,
      finrank_euclideanSpace_fin, normBallVolume, ← ENNReal.ofReal_toReal hfin,
      ← ENNReal.ofReal_mul (pow_nonneg hρ.le _)]
    simp [ENNReal.toReal_nonneg]

end CERW.Support.Norm

namespace CERW.Support.Norm.BallFacts

open CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The real volume of the sublevel set `{Ψ < ρ}` is `ρ ^ d` times the volume of the unit
ball of `Ψ`, for `ρ ≥ 0`. -/
private theorem real_volume_sublevel (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume.real {v : EuclideanSpace ℝ (Fin d) | Ψ v < ρ} = ρ ^ d * normBallVolume Ψ := by
  rw [measureReal_def, volume_normSublevel hd hΨ hρ]
  exact ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hρ _)
    (ENNReal.toReal_nonneg))

/-- The sublevel set `{Ψ < ρ}` of a norm has finite volume. -/
private theorem volume_sublevel_ne_top (hd : 1 ≤ d) (hΨ : IsNorm Ψ) (ρ : ℝ) :
    volume {v : EuclideanSpace ℝ (Fin d) | Ψ v < ρ} ≠ ⊤ :=
  ((measure_mono (normSublevel_subset_ball hd hΨ ρ)).trans_lt measure_ball_lt_top).ne

/-- A continuous function is integrable on every bounded set. -/
private theorem integrableOn_of_isBounded {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) {E : Set (EuclideanSpace ℝ (Fin d))} (hEb : Bornology.IsBounded E) :
    IntegrableOn f E volume := by
  obtain ⟨r, hr⟩ := hEb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hr

end CERW.Support.Norm.BallFacts

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The integral of the cone function `max (b - Ψ) 0` over a ball of radius `S ≥ b / c_Ψ` is
`|B_Ψ| b ^ (d + 1) / (d + 1)`. -/
private theorem integral_cone (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {b S : ℝ} (hb : 0 ≤ b)
    (hS : b / normMin Ψ ≤ S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, max (b - Ψ y) 0 =
      normBallVolume Ψ * b ^ (d + 1) / (d + 1) := by
  obtain ⟨hc, hle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hcont : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  have hnn : ∀ y, 0 ≤ Ψ y := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1
  have hfcont : Continuous fun y : EuclideanSpace ℝ (Fin d) => max (b - Ψ y) 0 :=
    (continuous_const.sub hcont).max continuous_const
  have hfzero : ∀ y : EuclideanSpace ℝ (Fin d), S ≤ ‖y‖ → max (b - Ψ y) 0 = 0 := by
    intro y hy
    have hby : b ≤ Ψ y := by
      calc b = (b / normMin Ψ) * normMin Ψ := (div_mul_cancel₀ b hc.ne').symm
        _ ≤ ‖y‖ * normMin Ψ := mul_le_mul_of_nonneg_right (hS.trans hy) hc.le
        _ = normMin Ψ * ‖y‖ := mul_comm _ _
        _ ≤ Ψ y := hle y
    exact max_eq_right (by linarith)
  have hint : Integrable fun y : EuclideanSpace ℝ (Fin d) => max (b - Ψ y) 0 := by
    refine hfcont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S) ?_)
    intro y hy
    refine hfzero y ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    exact hy.le
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hfzero y (by
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hy
    exact hy)),
    hint.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun y => le_max_right _ _)]
  have hlayer : ∀ t ∈ Set.Ioi (0 : ℝ),
      volume.real {a : EuclideanSpace ℝ (Fin d) | t < max (b - Ψ a) 0} =
        (max (b - t) 0) ^ d * normBallVolume Ψ := by
    intro t ht
    have ht0 : 0 < t := ht
    rcases lt_or_ge t b with htb | htb
    · have hset : {a : EuclideanSpace ℝ (Fin d) | t < max (b - Ψ a) 0} =
          {a | Ψ a < b - t} := by
        ext a
        simp only [Set.mem_setOf_eq, lt_max_iff]
        constructor
        · rintro (h | h)
          · linarith
          · linarith
        · intro h
          exact Or.inl (by linarith)
      rw [hset, BallFacts.real_volume_sublevel hd hΨ (by linarith),
        max_eq_left (by linarith : 0 ≤ b - t)]
    · have hset : {a : EuclideanSpace ℝ (Fin d) | t < max (b - Ψ a) 0} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, lt_max_iff, Set.mem_empty_iff_false, iff_false, not_or,
          not_lt]
        exact ⟨by linarith [hnn a], ht0.le⟩
      rw [hset, max_eq_right (by linarith : b - t ≤ 0), zero_pow (by omega)]
      simp
  have hsd : ∫ t in Set.Ioi (0 : ℝ), (max (b - t) 0) ^ d * normBallVolume Ψ =
      ∫ t in Set.Ioc (0 : ℝ) b, (max (b - t) 0) ^ d * normBallVolume Ψ := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      Set.Ioc_subset_Ioi_self (Filter.Eventually.of_forall fun t ht => ?_)
    have hbt : b < t := by
      by_contra h
      exact ht.2 ⟨ht.1, not_lt.mp h⟩
    rw [max_eq_right (by linarith : b - t ≤ 0), zero_pow (by omega), zero_mul]
  have hcongr : ∫ t in (0 : ℝ)..b, (max (b - t) 0) ^ d * normBallVolume Ψ =
      ∫ t in (0 : ℝ)..b, (b - t) ^ d * normBallVolume Ψ := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hb] at ht
    rw [max_eq_left (by linarith [ht.2])]
  rw [setIntegral_congr_fun measurableSet_Ioi hlayer, hsd, ← intervalIntegral.integral_of_le hb,
    hcongr, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ d) b, sub_self, sub_zero,
    integral_pow, zero_pow (Nat.succ_ne_zero d), sub_zero]
  ring

/-- Volume of a set `E ⊆ {b ≤ Ψ}` in terms of the integral of `Ψ - b` over `E`: the part of `E`
below level `b + s` lies in a shell of volume `|B_Ψ| ((b + s) ^ d - b ^ d)`, and the rest is
controlled by Markov's inequality. -/
private theorem volume_excess_le (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) {b : ℝ} (hb : 0 ≤ b)
    (hEsub : E ⊆ {v | b ≤ Ψ v}) {s : ℝ} (hs : 0 < s) :
    (volume E).toReal ≤ normBallVolume Ψ * ((b + s) ^ d - b ^ d) +
      (∫ v in E, (Ψ v - b)) / s := by
  have hcont : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  set A : Set (EuclideanSpace ℝ (Fin d)) := {v | Ψ v < b + s} with hA
  set B : Set (EuclideanSpace ℝ (Fin d)) := {v | Ψ v < b} with hB
  have hAm : MeasurableSet A := measurableSet_normSublevel hΨ _
  have hBm : MeasurableSet B := measurableSet_normSublevel hΨ _
  have hAfin : volume A ≠ ⊤ := BallFacts.volume_sublevel_ne_top hd hΨ _
  have hAvol : volume.real A = (b + s) ^ d * normBallVolume Ψ :=
    BallFacts.real_volume_sublevel hd hΨ (by linarith)
  have hBvol : volume.real B = b ^ d * normBallVolume Ψ :=
    BallFacts.real_volume_sublevel hd hΨ hb
  have hsplit : volume.real (E ∩ A) + volume.real (E \ A) = volume.real E :=
    measureReal_inter_add_sdiff hAm hEfin
  have hE₁ : volume.real (E ∩ A) ≤ normBallVolume Ψ * ((b + s) ^ d - b ^ d) := by
    have hsub : E ∩ A ⊆ A \ B := fun v hv => ⟨hv.2, fun hvB => by
      have h₁ : b ≤ Ψ v := hEsub hv.1
      have h₂ : Ψ v < b := hvB
      linarith⟩
    have hBA : B ⊆ A := fun v hv => lt_trans hv (by linarith : b < b + s)
    calc volume.real (E ∩ A) ≤ volume.real (A \ B) := measureReal_mono hsub
          (measure_ne_top_of_subset Set.sdiff_subset hAfin)
      _ = (b + s) ^ d * normBallVolume Ψ - b ^ d * normBallVolume Ψ := by
          rw [measureReal_sdiff hBA hBm hAfin, hAvol, hBvol]
      _ = normBallVolume Ψ * ((b + s) ^ d - b ^ d) := by ring
  have hint : IntegrableOn (fun v => Ψ v - b) E volume :=
    BallFacts.integrableOn_of_isBounded (hcont.sub continuous_const) hEb
  have hE₂ : s * volume.real (E \ A) ≤ ∫ v in E, (Ψ v - b) := by
    have hE₂m : MeasurableSet (E \ A) := hE.diff hAm
    have hE₂fin : volume (E \ A) ≠ ⊤ := measure_ne_top_of_subset Set.sdiff_subset hEfin
    calc s * volume.real (E \ A) = ∫ _ in E \ A, s := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ v in E \ A, (Ψ v - b) := by
          refine setIntegral_mono_on (integrableOn_const hE₂fin)
            (hint.mono_set Set.sdiff_subset) hE₂m fun v hv => ?_
          have : b + s ≤ Ψ v := not_lt.mp hv.2
          linarith
      _ ≤ ∫ v in E, (Ψ v - b) := by
          refine setIntegral_mono_set hint ?_ (Set.sdiff_subset.eventuallyLE)
          rw [Filter.EventuallyLE, ae_restrict_iff' hE]
          refine Filter.Eventually.of_forall fun v hv => ?_
          have : b ≤ Ψ v := hEsub hv
          simp only [Pi.zero_apply]
          linarith
  have hE₂' : volume.real (E \ A) ≤ (∫ v in E, (Ψ v - b)) / s := by
    rw [le_div_iff₀ hs, mul_comm]
    exact hE₂
  have hreal : (volume E).toReal = volume.real E := rfl
  rw [hreal, ← hsplit]
  exact add_le_add hE₁ hE₂'

/-! ## The inner radius and the contact point -/

/-- The cell set of a path started at the origin, run for at least one step, contains the ball
of radius `1 / 2`: it contains the cell of the origin. -/
private theorem ball_subset_cellSet (X : ℕ → Site d) (n : ℕ) (hX0 : X 0 = 0) (hn : 1 ≤ n) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) ⊆ cellSet X n := by
  intro v hv
  have h0 : (0 : Site d) ∈ departureRange X n :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), hX0⟩
  refine Set.mem_iUnion₂.mpr ⟨0, h0, fun i => ?_⟩
  have hcoord : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  have hv' : ‖v‖ < 1 / 2 := mem_ball_zero_iff.mp hv
  have habs := abs_lt.mp (lt_of_le_of_lt hcoord hv')
  simp only [Pi.zero_apply, Int.cast_zero]
  constructor <;> linarith [habs.1, habs.2]

/-- The inner radius `inf_{y ∉ D} Ψ(y)` of a bounded set containing a ball about the origin is
positive, the sublevel set of `Ψ` at that radius lies in `D`, and the infimum is attained in the
closure of the complement. -/
private theorem inradius_facts (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDb : Bornology.IsBounded D) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ D) :
    0 < sInf (Ψ '' Dᶜ) ∧ {v | Ψ v < sInf (Ψ '' Dᶜ)} ⊆ D ∧
      ∃ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = sInf (Ψ '' Dᶜ) ∧ y₀ ∈ closure Dᶜ := by
  obtain ⟨hc, hle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd
  have hcont : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  have hnn : ∀ y, 0 ≤ Ψ y := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1
  have hne : (Dᶜ).Nonempty := by
    haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
    rw [Set.nonempty_compl]
    rintro rfl
    exact NormedSpace.unbounded_univ ℝ _ hDb
  have hbdd : BddBelow (Ψ '' Dᶜ) := ⟨0, by rintro _ ⟨y, _, rfl⟩; exact hnn y⟩
  have hge : ∀ y ∈ Dᶜ, sInf (Ψ '' Dᶜ) ≤ Ψ y := fun y hy =>
    csInf_le hbdd (Set.mem_image_of_mem Ψ hy)
  have hpos : 0 < sInf (Ψ '' Dᶜ) := by
    refine lt_of_lt_of_le (mul_pos hc hρ) (le_csInf (hne.image Ψ) ?_)
    rintro _ ⟨y, hy, rfl⟩
    have hyρ : ρ ≤ ‖y‖ := by
      by_contra h
      exact hy (hball (mem_ball_zero_iff.mpr (not_le.mp h)))
    calc normMin Ψ * ρ ≤ normMin Ψ * ‖y‖ := mul_le_mul_of_nonneg_left hyρ hc.le
      _ ≤ Ψ y := hle y
  refine ⟨hpos, fun v hv => ?_, ?_⟩
  · by_contra hvD
    exact absurd (hge v hvD) (not_le.mpr hv)
  · set K : Set (EuclideanSpace ℝ (Fin d)) := closure Dᶜ ∩ {y | Ψ y ≤ sInf (Ψ '' Dᶜ) + 1} with hK
    have hKclosed : IsClosed K := isClosed_closure.inter (isClosed_le hcont continuous_const)
    have hKsub : K ⊆ Metric.closedBall 0 ((sInf (Ψ '' Dᶜ) + 1) / normMin Ψ) := by
      intro y hy
      rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc]
      calc ‖y‖ * normMin Ψ = normMin Ψ * ‖y‖ := mul_comm _ _
        _ ≤ Ψ y := hle y
        _ ≤ sInf (Ψ '' Dᶜ) + 1 := hy.2
    have hKcpt : IsCompact K := (isCompact_closedBall _ _).of_isClosed_subset hKclosed hKsub
    have hlt : ∀ η : ℝ, 0 < η → ∃ y ∈ Dᶜ, Ψ y < sInf (Ψ '' Dᶜ) + η := fun η hη => by
      obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image Ψ)
        (by linarith : sInf (Ψ '' Dᶜ) < sInf (Ψ '' Dᶜ) + η)
      exact ⟨y, hy, hlt⟩
    obtain ⟨y₁, hy₁, hy₁lt⟩ := hlt 1 one_pos
    have hKne : K.Nonempty := ⟨y₁, subset_closure hy₁, hy₁lt.le⟩
    obtain ⟨y₀, hy₀K, hmin⟩ := hKcpt.exists_isMinOn hKne hcont.continuousOn
    have hclosed : closure Dᶜ ⊆ {y | sInf (Ψ '' Dᶜ) ≤ Ψ y} :=
      closure_minimal hge (isClosed_le continuous_const hcont)
    have hy₀ge : sInf (Ψ '' Dᶜ) ≤ Ψ y₀ := hclosed hy₀K.1
    refine ⟨y₀, le_antisymm ?_ hy₀ge, hy₀K.1⟩
    by_contra hgt
    have hgt' : sInf (Ψ '' Dᶜ) < Ψ y₀ := not_le.mp hgt
    obtain ⟨y, hy, hylt⟩ := hlt (min ((Ψ y₀ - sInf (Ψ '' Dᶜ)) / 2) 1)
      (lt_min (by linarith) one_pos)
    have hyK : y ∈ K := ⟨subset_closure hy, (hylt.trans_le (by
      linarith [min_le_right ((Ψ y₀ - sInf (Ψ '' Dᶜ)) / 2) 1])).le⟩
    have h₁ := isMinOn_iff.mp hmin y hyK
    linarith [min_le_left ((Ψ y₀ - sInf (Ψ '' Dᶜ)) / 2) 1]

/-- The inner radius `inf_{y ∉ D} Ψ(y)` of a set `D ⊆ B(0, R)` containing a ball about the
origin is at most `Λ_Ψ R`. -/
private theorem inradius_le (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDb : Bornology.IsBounded D) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) ρ ⊆ D) {R : ℝ}
    (hDR : D ⊆ Metric.ball 0 R) : sInf (Ψ '' Dᶜ) ≤ normMax Ψ * R := by
  obtain ⟨hpos, hsub, -⟩ := inradius_facts hd hΨ hDb hρ hball
  have hΛ := BallFacts.normMax_pos' hd hΨ
  have hR : 0 < R := by
    have h0 := hDR (hball (Metric.mem_ball_self hρ))
    rwa [mem_ball_zero_iff, norm_zero] at h0
  have hcontain : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (sInf (Ψ '' Dᶜ) / normMax Ψ) ⊆
      Metric.ball 0 R := (ball_subset_normSublevel hd hΨ).trans (hsub.trans hDR)
  have hle : sInf (Ψ '' Dᶜ) / normMax Ψ ≤ R := by
    by_contra h
    have hlt : R < sInf (Ψ '' Dᶜ) / normMax Ψ := not_le.mp h
    set u : EuclideanSpace ℝ (Fin d) := coordVec (⟨0, by omega⟩ : Fin d) with hu
    have hun : ‖u‖ = 1 := by simp [hu, coordVec, PiLp.norm_single]
    set t : ℝ := (R + sInf (Ψ '' Dᶜ) / normMax Ψ) / 2 with ht
    have hyn : ‖t • u‖ = t := by
      rw [norm_smul, hun, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hmem : t • u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d))
        (sInf (Ψ '' Dᶜ) / normMax Ψ) := by
      rw [mem_ball_zero_iff, hyn]
      linarith
    have := mem_ball_zero_iff.mp (hcontain hmem)
    rw [hyn] at this
    linarith
  rw [div_le_iff₀ hΛ] at hle
  linarith

end CERW.Support.Norm

namespace CERW.Support.Norm.PotentialSplit

open CERW CERW.Generic.Norm CERW.Generic.Kernel

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A measurable field weighted by the Newtonian kernel has a measurable integrand. -/
private lemma measurable_fieldIntegrand {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (y : EuclideanSpace ℝ (Fin d)) :
    Measurable (fun v : EuclideanSpace ℝ (Fin d) => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) := by
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - y) :=
    measurable_id.sub measurable_const
  exact (hg.inner hsub).div (hsub.norm.pow_const d)

/-- The integrand of the field potential is at most `Λ` times the Newtonian kernel `|v - y|^{1-d}`
when the field has norm at most `Λ`. -/
private lemma abs_fieldIntegrand_le {Λ : ℝ} {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ ≤ Λ)
    (v y : EuclideanSpace ℝ (Fin d)) :
    |inner ℝ ξ (v - y) / ‖v - y‖ ^ d| ≤ Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
  have hΛ : 0 ≤ Λ := (norm_nonneg ξ).trans hξ
  rcases eq_or_ne v y with rfl | hne
  · simp only [sub_self, inner_zero_right, zero_div, abs_zero]
    exact mul_nonneg hΛ (Real.rpow_nonneg (norm_nonneg _) _)
  · have hw : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hden : 0 < ‖v - y‖ ^ d := pow_pos hw d
    have h1 : |inner ℝ ξ (v - y)| ≤ ‖ξ‖ * ‖v - y‖ := abs_real_inner_le_norm _ _
    have h2 : ‖ξ‖ * ‖v - y‖ ≤ Λ * ‖v - y‖ := mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
    calc |inner ℝ ξ (v - y) / ‖v - y‖ ^ d|
        = |inner ℝ ξ (v - y)| / ‖v - y‖ ^ d := by rw [abs_div, abs_of_nonneg hden.le]
      _ ≤ (Λ * ‖v - y‖) / ‖v - y‖ ^ d :=
          div_le_div_of_nonneg_right (h1.trans h2) hden.le
      _ = Λ * ‖v - y‖ ^ (1 - (d : ℝ)) := by
          rw [mul_div_assoc, CERW.Support.Geometry.div_pow_eq_rpow_sub hw d]

/-- On a set of finite volume the integrand of a bounded measurable field potential is
integrable. -/
private lemma integrableOn_fieldIntegrand (hd : 1 ≤ d)
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hg : Measurable g) {Λ : ℝ}
    (hΛ : ∀ v, ‖g v‖ ≤ Λ) {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (g v) (v - y) / ‖v - y‖ ^ d) D := by
  obtain ⟨hint, _⟩ := integrableOn_and_setIntegral_le (d := d) hd hD hDfin y
  refine (hint.const_mul Λ).mono' (measurable_fieldIntegrand hg y).aestronglyMeasurable ?_
  filter_upwards with v
  rw [Real.norm_eq_abs]
  exact abs_fieldIntegrand_le (hΛ v) v y

/-- The gradient of a function on `ℝ^d` is measurable. -/
private lemma measurable_gradient (Ψ : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measurable (gradient Ψ) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ψ)

/-- For `d ≥ 1`, `Λ_Ψ ≥ 0`. -/
private lemma normMax_nonneg (hΨ : IsNorm Ψ) (hd : 1 ≤ d) : 0 ≤ normMax Ψ := by
  have h1 := normMin_pos_mul_le hΨ hd
  have hn : ‖coordVec (⟨0, by omega⟩ : Fin d)‖ = 1 := by
    simp [coordVec, PiLp.norm_single]
  have h2 := le_normMax_mul hΨ (coordVec (⟨0, by omega⟩ : Fin d))
  have h3 := h1.2 (coordVec (⟨0, by omega⟩ : Fin d))
  rw [hn] at h2 h3
  linarith [h1.1]

/-- The gradient of a norm has Euclidean norm at most `Λ_Ψ` everywhere: where `Ψ` is
differentiable it is a subgradient, and elsewhere it is `0`. -/
private lemma norm_gradient_le (hΨ : IsNorm Ψ) (hd : 1 ≤ d) (v : EuclideanSpace ℝ (Fin d)) :
    ‖gradient Ψ v‖ ≤ normMax Ψ := by
  by_cases hv : DifferentiableAt ℝ Ψ v
  · have h := (subgradient_euler hΨ (gradient_isSubgradient hΨ hv)).2 (gradient Ψ v)
    have h2 := le_normMax_mul hΨ (gradient Ψ v)
    rw [real_inner_self_eq_norm_mul_norm] at h
    have h3 : ‖gradient Ψ v‖ * ‖gradient Ψ v‖ ≤ normMax Ψ * ‖gradient Ψ v‖ := h.trans h2
    rcases eq_or_lt_of_le (norm_nonneg (gradient Ψ v)) with h0 | h0
    · rw [← h0]
      exact normMax_nonneg hΨ hd
    · exact le_of_mul_le_mul_right h3 h0
  · have h0 : gradient Ψ v = 0 := by
      rw [gradient, fderiv_zero_of_not_differentiableAt hv]
      simp
    rw [h0, norm_zero]
    exact normMax_nonneg hΨ hd

/-- On a set of finite volume the integrand `∇Ψ(v) · (v - y) |v - y|^{-d}` of the potential of a
norm is integrable. -/
private lemma integrableOn_gradientIntegrand (hd : 1 ≤ d) (hΨ : IsNorm Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (y : EuclideanSpace ℝ (Fin d)) :
    IntegrableOn (fun v => inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d) D :=
  integrableOn_fieldIntegrand hd (measurable_gradient Ψ) (norm_gradient_le hΨ hd) hD hDfin y

/-- Splitting the potential of a norm over a measurable subset of finite volume. -/
private lemma normPotential_sdiff (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ D y = normPotential d ε Ψ A y + normPotential d ε Ψ (D \ A) y := by
  have hF := integrableOn_gradientIntegrand hd hΨ hD hDfin y
  have hFA := hF.mono_set hAD
  have hFE := hF.mono_set (Set.sdiff_subset : D \ A ⊆ D)
  have hsplit : ∫ v in D, inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d =
      (∫ v in A, inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d) +
      (∫ v in D \ A, inner ℝ (gradient Ψ v) (v - y) / ‖v - y‖ ^ d) := by
    conv_lhs => rw [← Set.union_sdiff_cancel hAD]
    exact setIntegral_union Set.disjoint_sdiff_right (hD.diff hA) hFA hFE
  unfold normPotential
  rw [hsplit]
  ring

/-- A norm is integrable (minus a constant) on every bounded set. -/
private lemma integrableOn_sub_const (hΨ : IsNorm Ψ) {E : Set (EuclideanSpace ℝ (Fin d))}
    (hEb : Bornology.IsBounded E) (b : ℝ) : IntegrableOn (fun v => Ψ v - b) E := by
  obtain ⟨r, hr⟩ := hEb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hc : ContinuousOn (fun v => Ψ v - b) (Metric.closedBall 0 r) :=
    ((norm_continuous hΨ).sub continuous_const).continuousOn
  exact (hc.integrableOn_compact (isCompact_closedBall 0 r)).mono_set hr

/-- The potential of a set `E ⊆ {b ≤ Ψ}` is at most `2dεa` plus the geometric bound for the part of
`E` where `Ψ > b + a`, whose volume is at most `(∫_E (Ψ - b)) / a`. -/
private lemma abs_potential_le_layer_add_tail (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    (hε : 0 < ε) (hlayer : Statements.layer_potential) {Cg : ℝ} (hCg0 : 0 ≤ Cg)
    (hCg : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |normPotential d ε Ψ D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d))
    {b : ℝ} (hb : 0 ≤ b) {E : Set (EuclideanSpace ℝ (Fin d))} (hE : MeasurableSet E)
    (hEb : Bornology.IsBounded E) (hEsub : E ⊆ {v | b ≤ Ψ v}) (y : EuclideanSpace ℝ (Fin d))
    {a : ℝ} (ha : 0 < a) :
    |normPotential d ε Ψ E y| ≤
      2 * d * ε * a + Cg * ε * ((∫ v in E, (Ψ v - b)) / a) ^ ((1 : ℝ) / d) := by
  have hd1 : 1 ≤ d := by omega
  have hΨc : Continuous Ψ := norm_continuous hΨ
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  have hE₁m : MeasurableSet (E ∩ {v | Ψ v ≤ b + a}) :=
    hE.inter (measurableSet_le hΨc.measurable measurable_const)
  have hsplit := normPotential_sdiff hd1 hΨ (ε := ε) hE₁m hE hEfin Set.inter_subset_left y
  have h1 : |normPotential d ε Ψ (E ∩ {v | Ψ v ≤ b + a}) y| ≤ 2 * d * ε * a :=
    hlayer hd hΨ hε hb ha hE₁m (fun v hv => ⟨hEsub hv.1, hv.2⟩) y
  have hE₂m : MeasurableSet (E \ (E ∩ {v | Ψ v ≤ b + a})) := hE.diff hE₁m
  have hE₂sub : E \ (E ∩ {v | Ψ v ≤ b + a}) ⊆ E := Set.sdiff_subset
  have hE₂b : Bornology.IsBounded (E \ (E ∩ {v | Ψ v ≤ b + a})) := hEb.subset hE₂sub
  have hE₂fin : volume (E \ (E ∩ {v | Ψ v ≤ b + a})) ≠ ⊤ := hE₂b.measure_lt_top.ne
  have h2 := hCg _ hE₂m hE₂b y
  have hint : IntegrableOn (fun v => Ψ v - b) E := integrableOn_sub_const hΨ hEb b
  have hmarkov : a * (volume (E \ (E ∩ {v | Ψ v ≤ b + a}))).toReal ≤ ∫ v in E, (Ψ v - b) := by
    calc a * (volume (E \ (E ∩ {v | Ψ v ≤ b + a}))).toReal
        = ∫ _v in E \ (E ∩ {v | Ψ v ≤ b + a}), a := by
          rw [setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
      _ ≤ ∫ v in E \ (E ∩ {v | Ψ v ≤ b + a}), (Ψ v - b) := by
          refine setIntegral_mono_on (integrableOn_const hE₂fin) (hint.mono_set hE₂sub) hE₂m ?_
          intro v hv
          have hlt : b + a < Ψ v := by
            by_contra hcon
            exact hv.2 ⟨hv.1, not_lt.mp hcon⟩
          linarith
      _ ≤ ∫ v in E, (Ψ v - b) := by
          refine setIntegral_mono_set hint ?_ (Set.sdiff_subset : _ ⊆ E).eventuallyLE
          filter_upwards [ae_restrict_mem hE] with v hv
          exact sub_nonneg.mpr (hEsub hv)
  have hvol : (volume (E \ (E ∩ {v | Ψ v ≤ b + a}))).toReal ≤ (∫ v in E, (Ψ v - b)) / a := by
    rw [le_div_iff₀ ha, mul_comm]
    exact hmarkov
  have hexp : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
  have h3 : (volume (E \ (E ∩ {v | Ψ v ≤ b + a}))).toReal ^ ((1 : ℝ) / d) ≤
      ((∫ v in E, (Ψ v - b)) / a) ^ ((1 : ℝ) / d) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hvol hexp
  have h4 : Cg * ε * (volume (E \ (E ∩ {v | Ψ v ≤ b + a}))).toReal ^ ((1 : ℝ) / d) ≤
      Cg * ε * ((∫ v in E, (Ψ v - b)) / a) ^ ((1 : ℝ) / d) :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg hCg0 hε.le)
  calc |normPotential d ε Ψ E y|
      = |normPotential d ε Ψ (E ∩ {v | Ψ v ≤ b + a}) y +
          normPotential d ε Ψ (E \ (E ∩ {v | Ψ v ≤ b + a})) y| := by rw [← hsplit]
    _ ≤ |normPotential d ε Ψ (E ∩ {v | Ψ v ≤ b + a}) y| +
          |normPotential d ε Ψ (E \ (E ∩ {v | Ψ v ≤ b + a})) y| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 (h2.trans h4)

end CERW.Support.Norm.PotentialSplit

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Splitting the potential of a norm over a measurable subset of finite volume:
`U_D = U_A + U_{D \ A}` for `A ⊆ D`. -/
private theorem normPotential_sdiff_eq (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    normPotential d ε Ψ D y = normPotential d ε Ψ A y + normPotential d ε Ψ (D \ A) y :=
  PotentialSplit.normPotential_sdiff hd hΨ hA hD hDfin hAD y

/-- The excess `∫_{D \ {Ψ < b}} (Ψ - b)` of a set `D` containing `{Ψ < b}` is at most
`(ω_d / (2ε)) (R₁ + R₂)^d U_D(y₀)` at a point `y₀` with `Ψ(y₀) = b`: the subgradient inequality at
`y₀` makes `∇Ψ(v) · (v - y₀) ≥ Ψ(v) - b` on `D \ {Ψ < b}`. -/
private theorem excess_le_potential (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hball : Statements.norm_ball_potential) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {b R₁ R₂ : ℝ} (hb : 0 < b) (hDR : D ⊆ Metric.ball 0 R₁)
    (hsub : {v | Ψ v < b} ⊆ D) {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : Ψ y₀ = b)
    (hy₀R : ‖y₀‖ ≤ R₂) :
    ∫ v in D \ {v | Ψ v < b}, (Ψ v - b) ≤
      unitBallVolume d / (2 * ε) * (R₁ + R₂) ^ d * normPotential d ε Ψ D y₀ := by
  have hd1 : 1 ≤ d := by omega
  have hΨc : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  have hSm : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | Ψ v < b} :=
    measurableSet_lt hΨc.measurable measurable_const
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDR
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hEm : MeasurableSet (D \ {v | Ψ v < b}) := hD.diff hSm
  have hEb : Bornology.IsBounded (D \ {v | Ψ v < b}) := hDb.subset Set.sdiff_subset
  have hEfin : volume (D \ {v | Ψ v < b}) ≠ ⊤ := hEb.measure_lt_top.ne
  have hsplit := PotentialSplit.normPotential_sdiff hd1 hΨ (ε := ε) hSm hD hDfin hsub y₀
  rw [hball hd hΨ ε hb y₀, hy₀, sub_self, max_self, mul_zero, zero_add] at hsplit
  have hR₁ : 0 < R₁ := by
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ {v | Ψ v < b} := by
      show Ψ 0 < b
      rw [(CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1]
      exact hb
    simpa using hDR (hsub h0)
  have hR : 0 < R₁ + R₂ := add_pos_of_pos_of_nonneg hR₁ ((norm_nonneg y₀).trans hy₀R)
  have hpt : ∀ᵐ v ∂(volume.restrict (D \ {v | Ψ v < b})),
      (Ψ v - b) / (R₁ + R₂) ^ d ≤ inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d := by
    filter_upwards [ae_restrict_mem hEm,
      ae_restrict_of_ae (CERW.Generic.Norm.ae_differentiableAt hΨ)] with v hvE hvdiff
    by_cases hv0 : v = y₀
    · rw [hv0]
      simp [hy₀]
    · have hvb : b ≤ Ψ v := not_lt.mp hvE.2
      have hsg := CERW.Generic.Norm.gradient_isSubgradient hΨ hvdiff y₀
      have hneg : inner ℝ (gradient Ψ v) (y₀ - v) = -inner ℝ (gradient Ψ v) (v - y₀) := by
        rw [← inner_neg_right, neg_sub]
      have hin : Ψ v - b ≤ inner ℝ (gradient Ψ v) (v - y₀) := by
        rw [hy₀] at hsg
        linarith
      have hvR : ‖v‖ < R₁ := by simpa using hDR hvE.1
      have hnorm : ‖v - y₀‖ ≤ R₁ + R₂ :=
        (norm_sub_le v y₀).trans (by linarith)
      have hpos : 0 < ‖v - y₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv0)
      calc (Ψ v - b) / (R₁ + R₂) ^ d
          ≤ inner ℝ (gradient Ψ v) (v - y₀) / (R₁ + R₂) ^ d :=
            div_le_div_of_nonneg_right hin (pow_nonneg hR.le d)
        _ ≤ inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d :=
            div_le_div_of_nonneg_left (by linarith) (pow_pos hpos d)
              (pow_le_pow_left₀ hpos.le hnorm d)
  have hint1 : IntegrableOn (fun v => (Ψ v - b) / (R₁ + R₂) ^ d) (D \ {v | Ψ v < b}) :=
    (PotentialSplit.integrableOn_sub_const hΨ hEb b).div_const _
  have hint2 := PotentialSplit.integrableOn_gradientIntegrand hd1 hΨ hEm hEfin y₀
  have hle := setIntegral_mono_ae_restrict hint1 hint2 hpt
  rw [integral_div] at hle
  have hPpos : 0 < (R₁ + R₂) ^ d := pow_pos hR d
  have hω := unitBallVolume_pos d
  rw [hsplit]
  unfold normPotential
  rw [div_le_iff₀ hPpos] at hle
  calc ∫ v in D \ {v | Ψ v < b}, (Ψ v - b)
      ≤ (∫ v in D \ {v | Ψ v < b}, inner ℝ (gradient Ψ v) (v - y₀) / ‖v - y₀‖ ^ d) *
        (R₁ + R₂) ^ d := hle
    _ = _ := by
        field_simp

/-- The potential of a bounded measurable set `E ⊆ {b ≤ Ψ}` is at most `C (∫_E (Ψ - b))^{1/(d+1)}`
in absolute value: the layer `{Ψ ≤ b + a}` contributes at most `2dεa` and the rest has volume at
most `(∫_E (Ψ - b)) / a`; take `a = (∫_E (Ψ - b))^{1/(d+1)}`. -/
private theorem abs_potential_excess_le (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hlayer : Statements.layer_potential) (hgeom : Statements.norm_potential_geometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℝ}, 0 ≤ b → ∀ {E : Set (EuclideanSpace ℝ (Fin d))},
      MeasurableSet E → Bornology.IsBounded E → E ⊆ {v | b ≤ Ψ v} →
      ∀ y : EuclideanSpace ℝ (Fin d),
        |normPotential d ε Ψ E y| ≤ C * (∫ v in E, (Ψ v - b)) ^ ((1 : ℝ) / (d + 1)) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  obtain ⟨Cg, hCg, hgeo⟩ := hgeom hd Ψ hΨ
  have hCg' : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |normPotential d ε Ψ D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d) :=
    fun D hD hDb y => (hgeo ε hε D hD hDb).1 y
  refine ⟨2 * d * ε + Cg * ε + 1, by positivity, ?_⟩
  intro b hb E hE hEb hEsub y
  have hI0 : 0 ≤ ∫ v in E, (Ψ v - b) :=
    setIntegral_nonneg hE (fun v hv => sub_nonneg.mpr (hEsub hv))
  have key := fun a (ha : 0 < a) =>
    PotentialSplit.abs_potential_le_layer_add_tail hd hΨ hε hlayer hCg.le hCg' hb hE hEb hEsub y ha
  generalize (∫ v in E, (Ψ v - b)) = I at hI0 key ⊢
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by positivity), mul_zero]
    refine _root_.le_of_forall_pos_le_add fun δ hδ => ?_
    have hc : 0 < 2 * (d : ℝ) * ε := by positivity
    have hk := key (δ / (2 * d * ε)) (by positivity)
    rw [← h0, zero_div, Real.zero_rpow (one_div_ne_zero hdpos.ne'), mul_zero, add_zero,
      mul_div_cancel₀ _ hc.ne'] at hk
    linarith
  · obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = I ^ ((1 : ℝ) / (d + 1)) := ⟨_, rfl⟩
    have ha : 0 < a := by
      rw [ha_def]
      exact Real.rpow_pos_of_pos hpos _
    have hIa : a ^ (d + 1) = I := by
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      have : (1 : ℝ) / (d + 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [this, Real.rpow_one]
    have hdiv : I / a = a ^ d := by
      rw [← hIa, pow_succ, mul_div_cancel_right₀ _ ha.ne']
    have hrt : (a ^ d) ^ ((1 : ℝ) / d) = a := by
      rw [one_div]
      exact Real.pow_rpow_inv_natCast ha.le (by omega)
    have hk := key a ha
    rw [hdiv, hrt] at hk
    rw [← ha_def]
    calc |normPotential d ε Ψ E y| ≤ 2 * d * ε * a + Cg * ε * a := hk
      _ = (2 * d * ε + Cg * ε) * a := by ring
      _ ≤ (2 * d * ε + Cg * ε + 1) * a :=
          mul_le_mul_of_nonneg_right (by linarith) ha.le

end CERW.Support.Norm

namespace CERW.Support.Norm.MassIdentity

open MeasureTheory
open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The radial integral of the exchanged weight: for `0 ≤ t ≤ S`,
`∫_0^S 1{r < t} r^{d-1} dr = t^d / d`. -/
private lemma integral_Ioo_indicator_pow (hd : 1 ≤ d) {S t : ℝ} (ht0 : 0 ≤ t) (htS : t ≤ S) :
    ∫ r in Set.Ioo 0 S, (Set.Iio t).indicator (fun r : ℝ => r ^ (d - 1)) r = t ^ d / d := by
  rw [setIntegral_indicator measurableSet_Iio, Set.Ioo_inter_Iio, min_eq_right htS,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht0, integral_pow]
  have h1 : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have h2 : ((d - 1 : ℕ) : ℝ) + 1 = d := by
    rw [Nat.cast_sub hd, Nat.cast_one, sub_add_cancel]
  rw [h1, h2, zero_pow (by omega), sub_zero]

/-- The exchanged weight `r ↦ 1{r < |v|} r^{d-1} Ψ(v) |v|^{-d}` integrates over `(0, S)` to
`Ψ(v)/d` whenever `|v| ≤ S`. -/
private lemma integral_Ioo_exchange_weighted (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {S : ℝ}
    (v : EuclideanSpace ℝ (Fin d)) (hvS : ‖v‖ ≤ S) :
    ∫ r in Set.Ioo 0 S, (if r < ‖v‖ then r ^ (d - 1) * (Ψ v / ‖v‖ ^ d) else 0) = Ψ v / d := by
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 : Ψ 0 = 0 := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).1
    simp [h0]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hind : ∀ r : ℝ, (if r < ‖v‖ then r ^ (d - 1) * (Ψ v / ‖v‖ ^ d) else 0) =
      (Ψ v / ‖v‖ ^ d) * (Set.Iio ‖v‖).indicator (fun r : ℝ => r ^ (d - 1)) r := by
    intro r
    by_cases hr : r < ‖v‖
    · simp only [hr, if_true, Set.indicator_of_mem (Set.mem_Iio.mpr hr)]
      ring
    · simp only [hr, if_false, Set.indicator_of_notMem (mt Set.mem_Iio.mp hr), mul_zero]
  simp_rw [hind]
  rw [integral_const_mul, integral_Ioo_indicator_pow (by omega) (norm_nonneg v) hvS]
  have hne : ‖v‖ ^ d ≠ 0 := pow_ne_zero d hvpos.ne'
  field_simp

/-- The exchanged weight is jointly integrable over `(0, S) × D`. -/
private lemma integrable_exchange_weighted (hd : 2 ≤ d) (hΨ : IsNorm Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤) (S : ℝ) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      if p.1 < ‖p.2‖ then p.1 ^ (d - 1) * (Ψ p.2 / ‖p.2‖ ^ d) else 0)
      ((volume.restrict (Set.Ioo 0 S)).prod (volume.restrict D)) := by
  have hd1 : 1 ≤ d := by omega
  have hΨm : Measurable Ψ := (CERW.Generic.Norm.norm_continuous hΨ).measurable
  have hmeas : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      if p.1 < ‖p.2‖ then p.1 ^ (d - 1) * (Ψ p.2 / ‖p.2‖ ^ d) else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd.norm)
      ((measurable_fst.pow_const _).mul ((hΨm.comp measurable_snd).div
        (measurable_snd.norm.pow_const _))) measurable_const
  have hker : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖ ^ (1 - (d : ℝ))) D := by
    simpa using (CERW.Generic.Kernel.integrableOn_and_setIntegral_le (d := d) hd1 hD hDfin 0).1
  have hbound : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      S ^ (d - 1) * (normMax Ψ * ‖p.2‖ ^ (1 - (d : ℝ))))
      ((volume.restrict (Set.Ioo 0 S)).prod (volume.restrict D)) := by
    have hc : Integrable (fun _ : ℝ => S ^ (d - 1)) (volume.restrict (Set.Ioo 0 S)) :=
      integrable_const _
    exact hc.mul_prod (hker.const_mul (normMax Ψ))
  refine hbound.mono' hmeas.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (measurableSet_Ioo.prod hD) fun p hp => ?_
  have hnn : 0 ≤ ‖p.2‖ ^ (1 - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hΛ : 0 ≤ normMax Ψ :=
    (lt_of_lt_of_le (CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1).1
      (CERW.Support.Norm.ContactAssembly.normMin_le_normMax hd1 hΨ)).le
  split_ifs with hlt
  · have hvpos : 0 < ‖p.2‖ := lt_of_le_of_lt hp.1.1.le hlt
    have hΨle : Ψ p.2 ≤ normMax Ψ * ‖p.2‖ := CERW.Generic.Norm.le_normMax_mul hΨ p.2
    have hΨ0 : 0 ≤ Ψ p.2 := (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 p.2
    have hdiv : Ψ p.2 / ‖p.2‖ ^ d ≤ normMax Ψ * ‖p.2‖ ^ (1 - (d : ℝ)) := by
      rw [← CERW.Support.Geometry.div_pow_eq_rpow_sub hvpos d, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hΨle (pow_pos hvpos d).le
    have hdiv0 : 0 ≤ Ψ p.2 / ‖p.2‖ ^ d := div_nonneg hΨ0 (pow_pos hvpos d).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hp.1.1.le _) hdiv0)]
    exact mul_le_mul (pow_le_pow_left₀ hp.1.1.le hp.1.2.le _) hdiv hdiv0
      (pow_nonneg (hp.1.1.le.trans hp.1.2.le) _)
  · rw [norm_zero]
    exact mul_nonneg (pow_nonneg (hp.1.2.le.trans' hp.1.1.le) _) (mul_nonneg hΛ hnn)

/-- The radial average of the spherical mean: for `D ⊆ B(0, S)`,
`∫_0^S r^{d-1} ∫_{D ∩ {|v| > r}} Ψ(v) |v|^{-d} dv dr = d⁻¹ ∫_D Ψ`, by Tonelli. -/
private lemma integral_Ioo_pow_mul_weighted (hd : 2 ≤ d) (hΨ : IsNorm Ψ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) {S : ℝ}
    (hDS : D ⊆ Metric.ball 0 S) :
    ∫ r in Set.Ioo 0 S, r ^ (d - 1) * ∫ v in D ∩ {v | r < ‖v‖}, Ψ v / ‖v‖ ^ d =
      (d : ℝ)⁻¹ * ∫ v in D, Ψ v := by
  have hDfin : volume D ≠ ⊤ := (measure_mono hDS |>.trans_lt measure_ball_lt_top).ne
  have hpt : ∀ r : ℝ, r ^ (d - 1) * ∫ v in D ∩ {v | r < ‖v‖}, Ψ v / ‖v‖ ^ d =
      ∫ v in D, (if r < ‖v‖ then r ^ (d - 1) * (Ψ v / ‖v‖ ^ d) else 0) := by
    intro r
    have hset : MeasurableSet {v : EuclideanSpace ℝ (Fin d) | r < ‖v‖} :=
      measurableSet_lt measurable_const measurable_norm
    have hind : ∀ v : EuclideanSpace ℝ (Fin d),
        (if r < ‖v‖ then r ^ (d - 1) * (Ψ v / ‖v‖ ^ d) else 0) =
          {v : EuclideanSpace ℝ (Fin d) | r < ‖v‖}.indicator
            (fun v => r ^ (d - 1) * (Ψ v / ‖v‖ ^ d)) v := fun v => by
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    simp_rw [hind]
    rw [setIntegral_indicator hset, integral_const_mul, Set.inter_comm]
  simp_rw [hpt]
  rw [integral_integral_swap (integrable_exchange_weighted hd hΨ hD hDfin S)]
  rw [setIntegral_congr_fun hD fun v hv => integral_Ioo_exchange_weighted hd hΨ v
    (mem_ball_zero_iff.mp (hDS hv)).le, integral_div, inv_mul_eq_div]

/-- `eq:massidentity` for the norm potential: for a bounded measurable `D ⊆ B(0, S)`,
`∫_{B(0,S)} U_D = 2ε ∫_D Ψ(v) dv`, by the spherical means of `U_D`. -/
private theorem integral_ball_eq (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hgeom : Statements.norm_potential_geometry) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {S : ℝ} (hDS : D ⊆ Metric.ball 0 S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, normPotential d ε Ψ D y =
      2 * ε * ∫ v in D, Ψ v := by
  have hd1 : 1 ≤ d := by omega
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDS
  have hω := unitBallVolume_pos d
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    exact this.ne'
  obtain ⟨Cd, hCd0, hgeo⟩ := hgeom hd Ψ hΨ
  have hgeo' : (∀ y z, |normPotential d ε Ψ D y - normPotential d ε Ψ D z| ≤
        Cd * ε * (volume D).toReal ^ ((1 : ℝ) / (2 * d)) * ‖y - z‖ ^ ((1 : ℝ) / 2)) ∧
      (∀ s : ℝ, 0 < s → ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          normPotential d ε Ψ D (s • (θ : EuclideanSpace ℝ (Fin d)))
            ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        d * unitBallVolume d * (2 * ε / unitBallVolume d *
          ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d)) := by
    obtain ⟨-, h2, h3⟩ := hgeo ε hε D hD hDb
    refine ⟨h2, fun s hs => ?_⟩
    obtain ⟨hAB, -, -, -⟩ := h3 s hs
    have hAB' : ((d : ℝ) * unitBallVolume d)⁻¹ * ∫ θ : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin d)) 1, normPotential d ε Ψ D (s • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
        2 * ε / unitBallVolume d * ∫ v in D ∩ {v | s < ‖v‖}, Ψ v / ‖v‖ ^ d := hAB
    rw [← hAB']
    exact (mul_inv_cancel_left₀ (by positivity) _).symm
  obtain ⟨hhol, hsph⟩ := hgeo'
  have hcont : Continuous (normPotential d ε Ψ D) :=
    CERW.Support.Geometry.continuous_of_holder_half (by positivity) hhol
  have hint : IntegrableOn (normPotential d ε Ψ D) (Metric.ball 0 S) :=
    (hcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
      Metric.ball_subset_closedBall
  have hpolar := CERW.Generic.Newton.integral_eq_integral_Ioi_sphere hd1
    ((integrable_indicator_iff measurableSet_ball).2 hint)
  rw [integral_indicator measurableSet_ball] at hpolar
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      r ^ (d - 1) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S).indicator (normPotential d ε Ψ D)
          (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      (Set.Iio S).indicator (fun r : ℝ => r ^ (d - 1) * ∫ θ : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin d)) 1, normPotential d ε Ψ D
          (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) r := by
    intro r hr
    have hnorm : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := fun θ => by
      have hθ : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
        rw [← dist_zero_right]
        exact Metric.mem_sphere.mp θ.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hθ, mul_one]
    by_cases hrS : r < S
    · rw [Set.indicator_of_mem (Set.mem_Iio.mpr hrS)]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      exact Set.indicator_of_mem (mem_ball_zero_iff.mpr (by rw [hnorm θ]; exact hrS)) _
    · rw [Set.indicator_of_notMem (mt Set.mem_Iio.mp hrS)]
      have hz : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
          (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S).indicator (normPotential d ε Ψ D)
            (r • (θ : EuclideanSpace ℝ (Fin d))) = 0 := fun θ =>
        Set.indicator_of_notMem (fun h => hrS (by rw [← hnorm θ]; exact mem_ball_zero_iff.mp h)) _
      simp [hz]
  rw [hpolar, setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  have hsph' : ∀ r ∈ Set.Ioo (0 : ℝ) S,
      r ^ (d - 1) * ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        normPotential d ε Ψ D (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      2 * ε * d * (r ^ (d - 1) * ∫ v in D ∩ {v | r < ‖v‖}, Ψ v / ‖v‖ ^ d) := by
    intro r hr
    rw [hsph r hr.1]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hsph', integral_const_mul,
    integral_Ioo_pow_mul_weighted hd hΨ hD hDS]
  field_simp

/-- The cell-center map is measurable. -/
private theorem measurable_cellCenter :
    Measurable (cellCenter : EuclideanSpace ℝ (Fin d) → Site d) := by
  rw [measurable_pi_iff]
  intro i
  exact Measurable.floor
    (((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))).add_const (1 / 2))

/-- The cell local time is measurable. -/
private theorem measurable_cellLocalTime (X : ℕ → Site d) (n : ℕ) :
    Measurable (cellLocalTime X n) :=
  (measurable_of_countable (fun x : Site d => (localTime X n x : ℝ))).comp measurable_cellCenter

/-- `|n - ∫_{B(0,S)} U_{D_n}| ≤ ω_d S^d δ` when `D_n ⊆ B(0, S)` and `|ℓ̃_n - U_{D_n}| ≤ δ`
there, for the norm potential. -/
private theorem abs_sub_integral_ball_le (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    (hε : 0 < ε) (hgeom : Statements.norm_potential_geometry) (X : ℕ → Site d) (n : ℕ)
    {S δ : ℝ} (hS : 0 < S) (hDS : cellSet X n ⊆ Metric.ball 0 S)
    (happrox : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤ δ) :
    |(n : ℝ) - ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        normPotential d ε Ψ (cellSet X n) y| ≤ unitBallVolume d * S ^ d * δ := by
  have hDmeas : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDb : Bornology.IsBounded (cellSet X n) := Metric.isBounded_ball.subset hDS
  have hballfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) < ⊤ :=
    measure_ball_lt_top
  have hballmeas : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) :=
    measurableSet_ball
  have hcellint : ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      cellLocalTime X n y = n :=
    CERW.Support.Occupation.setIntegral_cellLocalTime_of_subset X n hballmeas hDS
  obtain ⟨Cd, hCd0, hgeo⟩ := hgeom hd Ψ hΨ
  have hholder : ∀ y z, |normPotential d ε Ψ (cellSet X n) y -
      normPotential d ε Ψ (cellSet X n) z| ≤
      Cd * ε * (volume (cellSet X n)).toReal ^ ((1 : ℝ) / (2 * d)) *
        ‖y - z‖ ^ ((1 : ℝ) / 2) := (hgeo ε hε _ hDmeas hDb).2.1
  have hcont : Continuous (normPotential d ε Ψ (cellSet X n)) :=
    CERW.Support.Geometry.continuous_of_holder_half (by positivity) hholder
  have hpotint : IntegrableOn (normPotential d ε Ψ (cellSet X n))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) :=
    ((hcont.continuousOn).integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) S)).mono_set
        Metric.ball_subset_closedBall
  have hcellint_on : IntegrableOn (cellLocalTime X n)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S) := by
    refine IntegrableOn.of_bound hballfin
      (measurable_cellLocalTime X n).aestronglyMeasurable.restrict (maxLocalTime X n : ℝ) ?_
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (cellLocalTime_nonneg X n v)]
    show (localTime X n (cellCenter v) : ℝ) ≤ (maxLocalTime X n : ℝ)
    exact_mod_cast localTime_le_maxLocalTime X n (cellCenter v)
  have hsub := integral_sub hcellint_on hpotint
  have hmain : ‖∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        (cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y)‖
        = |(n : ℝ) - ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
            normPotential d ε Ψ (cellSet X n) y| := by
    rw [hsub, hcellint, Real.norm_eq_abs]
  have hbound : ‖∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
        (cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y)‖
        ≤ δ * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal :=
    norm_setIntegral_le_of_norm_le_const hballfin fun y hy => by
      rw [Real.norm_eq_abs]
      exact happrox y hy
  have hvol : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal =
      S ^ d * unitBallVolume d := by
    rw [Measure.addHaar_ball_of_pos (μ := volume) (0 : EuclideanSpace ℝ (Fin d)) hS,
      finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hfinal : δ * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S)).toReal =
      unitBallVolume d * S ^ d * δ := by
    rw [hvol]
    ring
  rw [← hmain]
  exact hbound.trans_eq hfinal

end CERW.Support.Norm.MassIdentity

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The mass identity -/

/-- `eq:massidentity` for the norm potential: `∫_{B(0,S)} U_D = 2ε ∫_D Ψ` for a measurable
`D ⊆ B(0, S)`. -/
private theorem integral_ball_normPotential (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hgeom : Statements.norm_potential_geometry) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD : MeasurableSet D) {S : ℝ} (hDS : D ⊆ Metric.ball 0 S) :
    ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S, normPotential d ε Ψ D y =
      2 * ε * ∫ v in D, Ψ v :=
  MassIdentity.integral_ball_eq hd hΨ hε hgeom hD hDS

/-- The mass error for the norm potential: `|n - 2ε ∫_{D_n} Ψ| ≤ ω_d S^d δ` when
`D_n ⊆ B(0, S)` and `|ℓ̃_n - U_{D_n}| ≤ δ` there. -/
private theorem abs_sub_integral_normPotential_le (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    (hε : 0 < ε) (hgeom : Statements.norm_potential_geometry) (X : ℕ → Site d) (n : ℕ)
    {S δ : ℝ} (hS : 0 < S) (hDS : cellSet X n ⊆ Metric.ball 0 S)
    (happrox : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) S,
      |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤ δ) :
    |(n : ℝ) - 2 * ε * ∫ v in cellSet X n, Ψ v| ≤ unitBallVolume d * S ^ d * δ := by
  have hDmeas : MeasurableSet (cellSet X n) := CERW.Support.Occupation.measurableSet_cellSet X n
  rw [← integral_ball_normPotential hd hΨ hε hgeom hDmeas hDS]
  exact MassIdentity.abs_sub_integral_ball_le hd hΨ hε hgeom X n hS hDS happrox

/-- The mass of a sublevel set of the norm: `∫_{Ψ < b} Ψ = d ω_Ψ b^{d+1}/(d+1)`, from the
mass identity with `ε = 1` and the explicit potential of the sublevel set. -/
private theorem integral_normSublevel_self (hd : 2 ≤ d) (hΨ : IsNorm Ψ)
    (hball : Statements.norm_ball_potential) (hgeom : Statements.norm_potential_geometry)
    {b : ℝ} (hb : 0 < b) :
    ∫ v in {v : EuclideanSpace ℝ (Fin d) | Ψ v < b}, Ψ v =
      d * normBallVolume Ψ * b ^ (d + 1) / (d + 1) := by
  have hd1 : 1 ≤ d := by omega
  have hmass := integral_ball_normPotential hd hΨ one_pos hgeom (measurableSet_normSublevel hΨ b)
    (normSublevel_subset_ball hd1 hΨ b)
  have hcone := integral_cone hd1 hΨ hb.le (le_refl (b / normMin Ψ))
  have hpot : ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / normMin Ψ),
      normPotential d 1 Ψ {v | Ψ v < b} y =
      2 * d * ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (b / normMin Ψ),
        max (b - Ψ y) 0 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun y _ => ?_
    rw [hball hd hΨ 1 hb y]
    ring
  rw [hpot, hcone] at hmass
  have hd0 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp at hmass ⊢
  linarith

end CERW.Support.Norm

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The geometry of the inner radius -/

/-- The deterministic geometry of the inner radius: the contact bound controls the excess
`∫_E (Ψ - b)`, the mass identity controls `b`, and the layer bound controls the profile. -/
theorem inner_geometry (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hball : Statements.norm_ball_potential) (hlayer : Statements.layer_potential)
    (hgeom : Statements.norm_potential_geometry) :
    ∃ C_L : ℝ, 0 < C_L ∧ ∀ (X : ℕ → Site d) (n : ℕ), X 0 = 0 → 1 ≤ n →
      ∀ {R δ H : ℝ}, cellSet X n ⊆ Metric.ball 0 R →
      (∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R,
        |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤ δ) →
      (∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ X n →
        y₀ ∈ closure (cellSet X n)ᶜ → normPotential d ε Ψ (cellSet X n) y₀ ≤ H) →
      0 < normInnerRadius Ψ X n ∧ normInnerRadius Ψ X n ≤ normMax Ψ * R ∧
      0 ≤ (∫ v in cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n},
          (Ψ v - normInnerRadius Ψ X n)) ∧
      ∫ v in cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n},
          (Ψ v - normInnerRadius Ψ X n) ≤
        unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * R) ^ d * H ∧
      (∀ s : ℝ, 0 < s →
        (volume (cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n})).toReal ≤
          normBallVolume Ψ * ((normInnerRadius Ψ X n + s) ^ d - normInnerRadius Ψ X n ^ d) +
            (∫ v in cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n},
              (Ψ v - normInnerRadius Ψ X n)) / s) ∧
      |(n : ℝ) - 2 * ε * (d * normBallVolume Ψ * normInnerRadius Ψ X n ^ (d + 1) / (d + 1))| ≤
        unitBallVolume d * R ^ d * δ + 2 * ε * normMax Ψ * R *
          (volume (cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n})).toReal ∧
      ∀ y : EuclideanSpace ℝ (Fin d),
        |cellLocalTime X n y - 2 * d * ε * max (normInnerRadius Ψ X n - Ψ y) 0| ≤
          δ + C_L * (∫ v in cellSet X n \ {v | Ψ v < normInnerRadius Ψ X n},
            (Ψ v - normInnerRadius Ψ X n)) ^ ((1 : ℝ) / (d + 1)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C_L, hCL, hCLb⟩ := abs_potential_excess_le hd hΨ hε hlayer hgeom
  refine ⟨C_L, hCL, ?_⟩
  intro X n hX0 hn R δ H hDR happrox hcon
  set D : Set (EuclideanSpace ℝ (Fin d)) := cellSet X n with hD
  set b : ℝ := normInnerRadius Ψ X n with hb
  have hbdef : b = sInf (Ψ '' Dᶜ) := rfl
  have hDmeas : MeasurableSet D := CERW.Support.Occupation.measurableSet_cellSet X n
  have hDb : Bornology.IsBounded D := Metric.isBounded_ball.subset hDR
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hball0 : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) ⊆ D :=
    ball_subset_cellSet X n hX0 hn
  obtain ⟨hb0, hsub, y₀, hy₀, hy₀cl⟩ :=
    inradius_facts (Ψ := Ψ) hd1 hΨ hDb (ρ := 1 / 2) (by norm_num) hball0
  rw [← hbdef] at hb0 hsub hy₀
  have hbR : b ≤ normMax Ψ * R := by
    rw [hbdef]
    exact inradius_le hd1 hΨ hDb (ρ := 1 / 2) (by norm_num) hball0 hDR
  have hR0 : 0 < R := by
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ D :=
      hball0 (by rw [Metric.mem_ball, dist_self]; norm_num)
    have := hDR h0
    rwa [Metric.mem_ball, dist_self] at this
  obtain ⟨hc0, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛc : 0 < normMax Ψ := lt_of_lt_of_le hc0 (ContactAssembly.normMin_le_normMax hd1 hΨ)
  have hy₀R : ‖y₀‖ ≤ normMax Ψ / normMin Ψ * R := by
    have h1 : normMin Ψ * ‖y₀‖ ≤ b := hy₀ ▸ hcle y₀
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    calc ‖y₀‖ * normMin Ψ = normMin Ψ * ‖y₀‖ := mul_comm _ _
      _ ≤ b := h1
      _ ≤ normMax Ψ * R := hbR
  set E : Set (EuclideanSpace ℝ (Fin d)) := D \ {v | Ψ v < b} with hE
  have hEmeas : MeasurableSet E := hDmeas.diff (measurableSet_normSublevel hΨ b)
  have hEb : Bornology.IsBounded E := hDb.subset Set.sdiff_subset
  have hEsub : E ⊆ {v | b ≤ Ψ v} := fun v hv => (not_lt.mp hv.2 : b ≤ Ψ v)
  set I : ℝ := ∫ v in E, (Ψ v - b) with hI
  have hΨcont : Continuous Ψ := CERW.Generic.Norm.norm_continuous hΨ
  have hΨint : IntegrableOn Ψ D :=
    (hΨcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) R)).mono_set
      (hDR.trans Metric.ball_subset_closedBall)
  have hI0 : 0 ≤ I := setIntegral_nonneg hEmeas fun v hv => sub_nonneg.mpr (hEsub hv)
  have hexc := excess_le_potential hd hΨ hε hball hDmeas (b := b) (R₁ := R)
    (R₂ := normMax Ψ / normMin Ψ * R) hb0 hDR hsub hy₀ hy₀R
  have hH := hcon y₀ hy₀ hy₀cl
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hcoef : 0 ≤ unitBallVolume d / (2 * ε) * (R + normMax Ψ / normMin Ψ * R) ^ d := by
    positivity
  have hrew : (1 + normMax Ψ / normMin Ψ) * R = R + normMax Ψ / normMin Ψ * R := by ring
  have hmass := abs_sub_integral_normPotential_le hd hΨ hε hgeom X n hR0 hDR happrox
  have hsplit : ∫ v in D, Ψ v = (∫ v in {v | Ψ v < b}, Ψ v) + ∫ v in E, Ψ v := by
    have hunion : D = {v | Ψ v < b} ∪ E := (Set.union_sdiff_cancel hsub).symm
    conv_lhs => rw [hunion]
    exact setIntegral_union (Set.disjoint_sdiff_right) hEmeas
      (hΨint.mono_set hsub) (hΨint.mono_set Set.sdiff_subset)
  have hball_int := integral_normSublevel_self hd hΨ hball hgeom hb0
  have hEΨ0 : 0 ≤ ∫ v in E, Ψ v :=
    setIntegral_nonneg hEmeas fun v _ => (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 v
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top hDfin (measure_mono Set.sdiff_subset)
  have hEΨle : ∫ v in E, Ψ v ≤ normMax Ψ * R * (volume E).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := E)
      (f := Ψ) (C := normMax Ψ * R) (lt_top_iff_ne_top.mpr hEfin) (fun v hv => by
        rw [Real.norm_eq_abs, abs_of_nonneg ((CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 v)]
        have h1 := CERW.Generic.Norm.le_normMax_mul hΨ v
        have h2 : ‖v‖ ≤ R := by
          have := hDR hv.1
          rw [mem_ball_zero_iff] at this
          exact this.le
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hΛc.le))
    rw [Real.norm_eq_abs, abs_of_nonneg hEΨ0, measureReal_def] at this
    linarith [this]
  refine ⟨hb0, hbR, hI0, ?_, ?_, ?_, ?_⟩
  · rw [hrew]
    calc I ≤ unitBallVolume d / (2 * ε) * (R + normMax Ψ / normMin Ψ * R) ^ d *
          normPotential d ε Ψ D y₀ := hexc
      _ ≤ unitBallVolume d / (2 * ε) * (R + normMax Ψ / normMin Ψ * R) ^ d * H :=
          mul_le_mul_of_nonneg_left hH hcoef
  · intro s hs
    exact volume_excess_le hd1 hΨ hEmeas hEb hb0.le hEsub hs
  · have h1 : (n : ℝ) - 2 * ε * (d * normBallVolume Ψ * b ^ (d + 1) / (d + 1)) =
        ((n : ℝ) - 2 * ε * ∫ v in D, Ψ v) + 2 * ε * ∫ v in E, Ψ v := by
      rw [hsplit, hball_int]
      ring
    rw [h1]
    calc |((n : ℝ) - 2 * ε * ∫ v in D, Ψ v) + 2 * ε * ∫ v in E, Ψ v|
        ≤ |(n : ℝ) - 2 * ε * ∫ v in D, Ψ v| + |2 * ε * ∫ v in E, Ψ v| := abs_add_le _ _
      _ ≤ unitBallVolume d * R ^ d * δ + 2 * ε * normMax Ψ * R * (volume E).toReal := by
          rw [abs_of_nonneg (by positivity : 0 ≤ 2 * ε * ∫ v in E, Ψ v)]
          have h2 : 2 * ε * ∫ v in E, Ψ v ≤ 2 * ε * (normMax Ψ * R * (volume E).toReal) :=
            mul_le_mul_of_nonneg_left hEΨle (by positivity)
          have h3 : 2 * ε * (normMax Ψ * R * (volume E).toReal) =
              2 * ε * normMax Ψ * R * (volume E).toReal := by ring
          linarith [hmass]
  · intro y
    have hδ0 : 0 ≤ δ := by
      have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R :=
        by rw [Metric.mem_ball, dist_self]; exact hR0
      exact (abs_nonneg _).trans (happrox 0 h0)
    have hIp : 0 ≤ I ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hI0 _
    by_cases hyD : y ∈ D
    · have hyball : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R := hDR hyD
      have hloc := happrox y hyball
      have hsp := normPotential_sdiff_eq (ε := ε) hd1 hΨ
        (measurableSet_normSublevel hΨ b) hDmeas hDfin hsub y
      have hUb := hball hd hΨ ε hb0 y
      have hUE := hCLb hb0.le hEmeas hEb hEsub y
      rw [hUb] at hsp
      have hsplit' : cellLocalTime X n y - 2 * d * ε * max (b - Ψ y) 0 =
          (cellLocalTime X n y - normPotential d ε Ψ D y) + normPotential d ε Ψ E y := by
        rw [hsp]
        ring
      rw [hsplit']
      calc |(cellLocalTime X n y - normPotential d ε Ψ D y) + normPotential d ε Ψ E y|
          ≤ |cellLocalTime X n y - normPotential d ε Ψ D y| + |normPotential d ε Ψ E y| :=
            abs_add_le _ _
        _ ≤ δ + C_L * I ^ ((1 : ℝ) / (d + 1)) := add_le_add hloc hUE
    · have hloc0 : cellLocalTime X n y = 0 :=
        CERW.Support.Occupation.cellLocalTime_eq_zero_of_not_mem X n hyD
      have hbdd : BddBelow (Ψ '' Dᶜ) :=
        ⟨0, by
          rintro _ ⟨v, -, rfl⟩
          exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 v⟩
      have hby : b ≤ Ψ y := by
        rw [hbdef]
        exact csInf_le hbdd ⟨y, hyD, rfl⟩
      have hmax : max (b - Ψ y) 0 = 0 := max_eq_right (by linarith)
      rw [hloc0, hmax]
      simp only [mul_zero, sub_zero, abs_zero]
      exact add_nonneg hδ0 (mul_nonneg hCL.le hIp)

/-! ## The inner radius and the local time profile -/

/-- The rate `q` is nonnegative. -/
private lemma rateQ_nonneg (d : ℕ) {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 ≤ ℓ) : 0 ≤ rateQ d r ℓ := by
  unfold rateQ
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact div_nonneg hℓ hr.le

/-- The approximation error of the local times is at most a constant times the scale `√r ℓ`
(in the plane) or `√(r ℓ)` (in higher dimension), once `M ≤ C r` and `1 ≤ ℓ ≤ r`. -/
private lemma approx_error_le (d : ℕ) {C_loc C_co M r ℓ : ℝ} (hC_loc : 0 ≤ C_loc)
    (hC_co : 0 ≤ C_co) (hM : M ≤ C_co * r) (hr : 1 ≤ r) (hℓ : 1 ≤ ℓ) (hℓr : ℓ ≤ r) :
    C_loc * ℓ + C_loc * (if d = 2 then Real.sqrt M * ℓ else Real.sqrt (M * ℓ)) ≤
      C_loc * (1 + Real.sqrt C_co) *
        (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) := by
  have hℓ0 : 0 ≤ ℓ := by linarith
  split_ifs with h2
  · have h1 : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr hr
    have hsq : Real.sqrt M ≤ Real.sqrt C_co * Real.sqrt r := by
      rw [← Real.sqrt_mul hC_co]
      exact Real.sqrt_le_sqrt hM
    have a1 : ℓ ≤ Real.sqrt r * ℓ := le_mul_of_one_le_left hℓ0 h1
    have a2 : Real.sqrt M * ℓ ≤ Real.sqrt C_co * Real.sqrt r * ℓ :=
      mul_le_mul_of_nonneg_right hsq hℓ0
    calc C_loc * ℓ + C_loc * (Real.sqrt M * ℓ)
        ≤ C_loc * (Real.sqrt r * ℓ) + C_loc * (Real.sqrt C_co * Real.sqrt r * ℓ) :=
          add_le_add (mul_le_mul_of_nonneg_left a1 hC_loc)
            (mul_le_mul_of_nonneg_left a2 hC_loc)
      _ = C_loc * (1 + Real.sqrt C_co) * (Real.sqrt r * ℓ) := by ring
  · have a1 : ℓ ≤ Real.sqrt (r * ℓ) := by
      refine (le_abs_self ℓ).trans (Real.abs_le_sqrt ?_)
      calc ℓ ^ 2 = ℓ * ℓ := sq ℓ
        _ ≤ r * ℓ := mul_le_mul_of_nonneg_right hℓr hℓ0
    have hsq : Real.sqrt (M * ℓ) ≤ Real.sqrt C_co * Real.sqrt (r * ℓ) := by
      rw [← Real.sqrt_mul hC_co]
      refine Real.sqrt_le_sqrt ?_
      calc M * ℓ ≤ C_co * r * ℓ := mul_le_mul_of_nonneg_right hM hℓ0
        _ = C_co * (r * ℓ) := by ring
    calc C_loc * ℓ + C_loc * Real.sqrt (M * ℓ)
        ≤ C_loc * Real.sqrt (r * ℓ) + C_loc * (Real.sqrt C_co * Real.sqrt (r * ℓ)) :=
          add_le_add (mul_le_mul_of_nonneg_left a1 hC_loc)
            (mul_le_mul_of_nonneg_left hsq hC_loc)
      _ = C_loc * (1 + Real.sqrt C_co) * Real.sqrt (r * ℓ) := by ring

/-- The inner radius and the local time profile: the geometry of the inner radius combined with
the rates. -/
private theorem inner_rates (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hball : Statements.norm_ball_potential) (hlayer : Statements.layer_potential)
    (hgeom : Statements.norm_potential_geometry) {C_co C_loc C_c : ℝ} (hC_co : 0 < C_co)
    (hC_loc : 0 < C_loc) (hC_c : 0 < C_c) :
    ∃ C_in C_lt r₀ M : ℝ, 0 < C_in ∧ 0 < C_lt ∧ 0 < M ∧
      ∀ (X : ℕ → Site d) (n : ℕ) (r : ℝ), X 0 = 0 → 2 ≤ n →
        r₀ ≤ r → 1 ≤ Real.log n → M * Real.log n ^ (d + 5) ≤ r → (C_co + 1) * r ≤ 2 * n →
        (n : ℝ) = 2 * ε * d * normBallVolume Ψ * r ^ (d + 1) / (d + 1) →
        maxRadius X n ≤ C_co * r → (maxLocalTime X n : ℝ) ≤ C_co * r →
        (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
          |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤
            C_loc * Real.log n + C_loc * (if d = 2
              then Real.sqrt (maxLocalTime X n) * Real.log n
              else Real.sqrt (maxLocalTime X n * Real.log n))) →
        (∀ y₀ : EuclideanSpace ℝ (Fin d), Ψ y₀ = normInnerRadius Ψ X n →
          y₀ ∈ closure (cellSet X n)ᶜ →
          normPotential d ε Ψ (cellSet X n) y₀ ≤ C_c * r * rateQ d r (Real.log n)) →
        |normInnerRadius Ψ X n - r| ≤ C_in * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / 2)) ∧
        ∀ y : EuclideanSpace ℝ (Fin d),
          |cellLocalTime X n y - 2 * d * ε * max (r - Ψ y) 0| ≤
            C_lt * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume Ψ := ContactAssembly.normBallVolume_pos' hd1 hΨ
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  obtain ⟨hc0, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 (ContactAssembly.normMin_le_normMax hd1 hΨ)
  obtain ⟨C_L, hCL, hgeoC⟩ := inner_geometry hd hΨ hε hball hlayer hgeom
  set K : ℝ := C_co + 1 with hK
  have hK0 : 0 < K := by linarith
  set C_δ : ℝ := C_loc * (1 + Real.sqrt C_co) with hCδ
  have hCδ0 : 0 < C_δ := mul_pos hC_loc (by linarith [Real.sqrt_nonneg C_co])
  have hCI0 : 0 < unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * K) ^ d := by
    positivity
  obtain ⟨C₁, r₁, M₁, hC₁, hM₁, harith⟩ := inner_rates_arith hd hε hV
    (C_R := normMax Ψ * K) (C_c := C_c) (C_δ := C_δ)
    (C_I := unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * K) ^ d)
    (C_m := unitBallVolume d * K ^ d) (C_e := 2 * ε * normMax Ψ * K)
    (mul_pos hΛ hK0) hC_c hCδ0 hCI0 (mul_pos hω (pow_pos hK0 d))
    (mul_pos (mul_pos (mul_pos two_pos hε) hΛ) hK0)
  obtain ⟨C₂, r₂, M₂, hC₂, hM₂, hprof⟩ := profile_arith hd hε hCL hC₁ hC₁ hCδ0
  refine ⟨C₁, C₂, max (max r₁ r₂) (max 1 (Real.sqrt d)), max (max M₁ M₂) 1, hC₁, hC₂,
    lt_max_of_lt_right one_pos, ?_⟩
  intro X n r hX0 hn hr hℓ hMℓ hK2n hnr hH hMloc happrox hcon
  set ℓ : ℝ := Real.log n with hℓdef
  have hr1 : 1 ≤ r :=
    le_trans (le_trans (le_max_left 1 _) (le_max_right _ _)) hr
  have hrd : Real.sqrt d ≤ r :=
    le_trans (le_trans (le_max_right 1 _) (le_max_right _ _)) hr
  have hr₁ : r₁ ≤ r := le_trans (le_trans (le_max_left r₁ r₂) (le_max_left _ _)) hr
  have hr₂ : r₂ ≤ r := le_trans (le_trans (le_max_right r₁ r₂) (le_max_left _ _)) hr
  have hr0 : 0 < r := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hpowℓ : 0 ≤ ℓ ^ (d + 5) := pow_nonneg hℓ0 _
  have hℓpow : ℓ ^ (d + 5) ≤ r :=
    calc ℓ ^ (d + 5) = 1 * ℓ ^ (d + 5) := (one_mul _).symm
      _ ≤ max (max M₁ M₂) 1 * ℓ ^ (d + 5) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpowℓ
      _ ≤ r := hMℓ
  have hℓr : ℓ ≤ r := (le_self_pow₀ hℓ (by omega)).trans hℓpow
  have hM₁ℓ : M₁ * ℓ ^ (d + 5) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left M₁ M₂) (le_max_left _ _)) hpowℓ) hMℓ
  have hM₂ℓ : M₂ * ℓ ^ (d + 5) ≤ r :=
    le_trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right M₁ M₂) (le_max_left _ _)) hpowℓ) hMℓ
  have hDR : cellSet X n ⊆ Metric.ball 0 (K * r) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 X n).trans
      (Metric.ball_subset_ball (by
        have : K * r = C_co * r + 1 * r := by rw [hK]; ring
        linarith))
  set δ : ℝ := C_loc * ℓ + C_loc * (if d = 2
      then Real.sqrt (maxLocalTime X n) * ℓ else Real.sqrt (maxLocalTime X n * ℓ)) with hδdef
  have hδapp : ∀ y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (K * r),
      |cellLocalTime X n y - normPotential d ε Ψ (cellSet X n) y| ≤ δ := by
    intro y hy
    rw [mem_ball_zero_iff] at hy
    exact happrox y (by linarith)
  have hδ0 : 0 ≤ δ := by
    refine add_nonneg (mul_nonneg hC_loc.le hℓ0) (mul_nonneg hC_loc.le ?_)
    split_ifs
    · exact mul_nonneg (Real.sqrt_nonneg _) hℓ0
    · exact Real.sqrt_nonneg _
  have hδle : δ ≤ C_δ * (if d = 2 then Real.sqrt r * ℓ else Real.sqrt (r * ℓ)) :=
    approx_error_le d hC_loc.le hC_co.le hMloc hr1 hℓ hℓr
  have hqnn : 0 ≤ rateQ d r ℓ := rateQ_nonneg d hr0 hℓ0
  obtain ⟨hb0, hbR, hI0, hexc, hshell, hmass, hprof'⟩ :=
    hgeoC X n hX0 (by omega) (R := K * r) (δ := δ) (H := C_c * r * rateQ d r ℓ) hDR hδapp hcon
  set b : ℝ := normInnerRadius Ψ X n with hb
  set E : Set (EuclideanSpace ℝ (Fin d)) := cellSet X n \ {v | Ψ v < b} with hE
  set I : ℝ := ∫ v in E, (Ψ v - b) with hI
  set Ev : ℝ := (volume E).toReal with hEv
  have hbR' : b ≤ normMax Ψ * K * r := by
    calc b ≤ normMax Ψ * (K * r) := hbR
      _ = normMax Ψ * K * r := by ring
  have hexc' : I ≤ unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * K) ^ d * r ^ d *
      (C_c * r * rateQ d r ℓ) := by
    calc I ≤ unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * (K * r)) ^ d *
          (C_c * r * rateQ d r ℓ) := hexc
      _ = unitBallVolume d / (2 * ε) * ((1 + normMax Ψ / normMin Ψ) * K) ^ d * r ^ d *
          (C_c * r * rateQ d r ℓ) := by
          rw [show (1 + normMax Ψ / normMin Ψ) * (K * r) =
            ((1 + normMax Ψ / normMin Ψ) * K) * r by ring, mul_pow]
          ring
  have hmass' : |(n : ℝ) - 2 * ε * (d * normBallVolume Ψ * b ^ (d + 1) / (d + 1))| ≤
      unitBallVolume d * K ^ d * r ^ d * δ + 2 * ε * normMax Ψ * K * r * Ev := by
    calc _ ≤ unitBallVolume d * (K * r) ^ d * δ + 2 * ε * normMax Ψ * (K * r) * Ev := hmass
      _ = _ := by rw [mul_pow]; ring
  obtain ⟨hbrate, hIrate⟩ := harith r ℓ b I Ev (C_c * r * rateQ d r ℓ) δ (n : ℝ) hr₁ hℓ hM₁ℓ
    hnr hb0 hbR' hI0 hexc' (mul_nonneg (mul_nonneg hC_c.le hr0.le) hqnn) le_rfl
    ENNReal.toReal_nonneg hshell hδ0 hδle hmass'
  have hprofC := hprof r ℓ b I δ hr₂ hℓ hM₂ℓ hI0 hIrate hbrate hδ0 hδle
  refine ⟨hbrate, fun y => ?_⟩
  have h1 := hprof' y
  have hmx : |max (b - Ψ y) 0 - max (r - Ψ y) 0| ≤ |b - r| := by
    have := abs_max_sub_max_le_abs (b - Ψ y) (r - Ψ y) 0
    rwa [show (b - Ψ y) - (r - Ψ y) = b - r by ring] at this
  have hcoef : 0 ≤ 2 * (d : ℝ) * ε := by positivity
  have hsplit : cellLocalTime X n y - 2 * d * ε * max (r - Ψ y) 0 =
      (cellLocalTime X n y - 2 * d * ε * max (b - Ψ y) 0) +
        2 * d * ε * (max (b - Ψ y) 0 - max (r - Ψ y) 0) := by ring
  rw [hsplit]
  calc |(cellLocalTime X n y - 2 * d * ε * max (b - Ψ y) 0) +
        2 * d * ε * (max (b - Ψ y) 0 - max (r - Ψ y) 0)|
      ≤ |cellLocalTime X n y - 2 * d * ε * max (b - Ψ y) 0| +
        |2 * d * ε * (max (b - Ψ y) 0 - max (r - Ψ y) 0)| := abs_add_le _ _
    _ ≤ (δ + C_L * I ^ ((1 : ℝ) / (d + 1))) + 2 * d * ε * |b - r| := by
        refine add_le_add h1 ?_
        rw [abs_mul, abs_of_nonneg hcoef]
        exact mul_le_mul_of_nonneg_left hmx hcoef
    _ ≤ C₂ * (r * rateQ d r ℓ ^ ((1 : ℝ) / (d + 1))) := by linarith

end CERW.Support.Norm

namespace CERW.Support.Norm.OuterRadius

open CERW

variable {d : ℕ}

/-- The origin of the lattice embeds as the origin of Euclidean space. -/
private theorem toSpace_zero_eq : toSpace (0 : Site d) = 0 := by
  ext i
  simp [toSpace]

/-- A vector `y` whose pairing with a vector `q` of norm at most `Λ` is at least `s`, where
`τ Λ² < s`, has norm greater than `τ Λ`. -/
private theorem lt_norm_of_lt_inner {q y : EuclideanSpace ℝ (Fin d)} {Λ τ s : ℝ}
    (hΛ : 0 < Λ) (hq : ‖q‖ ≤ Λ) (hs : τ * Λ ^ 2 < s) (hy : s ≤ inner ℝ q y) :
    τ * Λ < ‖y‖ := by
  have h1 : inner ℝ q y ≤ Λ * ‖y‖ :=
    (real_inner_le_norm q y).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg y))
  have h2 : (τ * Λ) * Λ < ‖y‖ * Λ :=
    calc (τ * Λ) * Λ = τ * Λ ^ 2 := by ring
      _ < s := hs
      _ ≤ inner ℝ q y := hy
      _ ≤ Λ * ‖y‖ := h1
      _ = ‖y‖ * Λ := by ring
  exact lt_of_mul_lt_mul_right h2 hΛ.le

/-- If every site whose pairing with `q` is at least `r` has local time at most `Lb`, then the
largest local time among the points of the departure range with this property is at most `Lb`. -/
private theorem sup_localTime_le {q : EuclideanSpace ℝ (Fin d)} {r Lb : ℝ} (hLb : 0 ≤ Lb)
    (x : ℕ → Site d) (n : ℕ)
    (h : ∀ z : Site d, r ≤ inner ℝ q (toSpace z) → (localTime x n z : ℝ) ≤ Lb) :
    ((((departureRange x n).filter (fun z => r ≤ inner ℝ q (toSpace z))).sup
      (localTime x n) : ℕ) : ℝ) ≤ Lb := by
  have h1 : ((departureRange x n).filter (fun z => r ≤ inner ℝ q (toSpace z))).sup
      (localTime x n) ≤ ⌊Lb⌋₊ :=
    Finset.sup_le fun z hz => Nat.le_floor (h z (Finset.mem_filter.1 hz).2)
  exact (Nat.cast_le.2 h1).trans (Nat.floor_le hLb)

end CERW.Support.Norm.OuterRadius

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The outer radius from the crossing lemma and the cap of the Moreau envelope, for a path on
which the vector bound and the linear martingale bounds hold and the local times beyond `r` are
at most `L_b`: the scale `τ` of the envelope is fixed by `4 C_out (1 + L_b) log n ≤ η τ`. -/
private theorem outer_deterministic (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    (hcap : Statements.moreau_cap) (houter : Statements.outer_crossing)
    {C₁ : ℝ} (hC₁ : 0 < C₁) :
    ∃ C_out : ℝ, 0 < C_out ∧ ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (n : ℕ), 2 ≤ n → ∀ (x : ℕ → Site d), x 0 = 0 →
      (∀ j, x (j + 1) - x j ∈ unitSteps d) → ∀ (τ r Lb : ℝ), 0 < τ → 0 < r → 0 ≤ Lb →
      normMin Ψ ^ 4 / (8 * normMax Ψ ^ 2) * τ ≤ r / 2 →
      τ * normMax Ψ ^ 2 < r / 2 →
      4 * C_out * (1 + Lb) * Real.log n ≤ normMin Ψ ^ 4 / (8 * normMax Ψ ^ 2) * τ →
      (∀ z : Site d, r ≤ Ψ (toSpace z) → (localTime x n z : ℝ) ≤ Lb) →
      (∀ s t : ℕ, s < t → t ≤ n →
        ‖(toSpace (x t) + ε • ∑ j ∈ Finset.range t,
            if x j ∉ departureRange x j then ξ (x j) else 0) -
          (toSpace (x s) + ε • ∑ j ∈ Finset.range s,
            if x j ∉ departureRange x j then ξ (x j) else 0)‖ ≤
          C₁ * Real.sqrt (((t : ℝ) - s) * Real.log n)) →
      (∀ j : ℕ, j ≤ n → x j ≠ 0 → ∀ k : ℕ, k ≤ n →
        |dynkinMart (driftStepProb d ε ξ)
            (fun z => max (inner ℝ (gradient (moreauEnvelope Ψ τ) (toSpace (x j)))
              (toSpace z) - k * normMax Ψ) 0) x n| ≤
          C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
              (fun z => (k : ℝ) * normMax Ψ - normMax Ψ <
                inner ℝ (gradient (moreauEnvelope Ψ τ) (toSpace (x j))) (toSpace z)),
            (localTime x n z : ℝ)) + Real.log n)) →
      normMaxRadius Ψ x n ≤
        r + (normMin Ψ ^ 4 / (8 * normMax Ψ ^ 2) / 4 + normMax Ψ ^ 2 / 2) * τ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hcpos, -⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hcΛ : normMin Ψ ≤ normMax Ψ :=
    CERW.Support.Norm.ContactAssembly.normMin_le_normMax hd1 hΨ
  have hΛpos : 0 < normMax Ψ := lt_of_lt_of_le hcpos hcΛ
  have hα : 0 < normMin Ψ ^ 2 / 2 := div_pos (pow_pos hcpos 2) two_pos
  obtain ⟨C, hCpos, hC⟩ := houter hd Ψ hΨ ε hε hell _ hα C₁ hC₁
  refine ⟨C, hCpos, ?_⟩
  intro ξ hξ hξ0 n hn x hx0 hstep τ r Lb hτ hr hLb hη1 hη2 hη3 hloc hZ hmart
  have hη : 0 < normMin Ψ ^ 4 / (8 * normMax Ψ ^ 2) :=
    div_pos (pow_pos hcpos 4) (mul_pos (by norm_num) (pow_pos hΛpos 2))
  set η := normMin Ψ ^ 4 / (8 * normMax Ψ ^ 2) with hηdef
  have hητ : 0 < η * τ := mul_pos hη hτ
  obtain ⟨j₀, hj₀mem, hj₀max⟩ :=
    Finset.exists_max_image (Finset.range (n + 1))
      (fun j => moreauEnvelope Ψ τ (toSpace (x j)))
      ⟨0, Finset.mem_range.2 (Nat.succ_pos n)⟩
  have hj₀n : j₀ ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj₀mem)
  have hmax : ∀ j ≤ n,
      moreauEnvelope Ψ τ (toSpace (x j)) ≤ moreauEnvelope Ψ τ (toSpace (x j₀)) :=
    fun j hj => hj₀max j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hsub := isSubgradient_gradient_moreauEnvelope hΨ hτ (toSpace (x j₀))
  have hmart₀ := hmart j₀ hj₀n
  set q := gradient (moreauEnvelope Ψ τ) (toSpace (x j₀)) with hq
  have hqΛ : ‖q‖ ≤ normMax Ψ := norm_le_normMax_of_isSubgradient hΨ hsub
  have hqΨ : ∀ y, inner ℝ q y ≤ Ψ y := (CERW.Generic.Norm.subgradient_euler hΨ hsub).2
  have hlin : ∀ j ≤ n, inner ℝ q (toSpace (x j)) ≤ inner ℝ q (toSpace (x j₀)) := by
    intro j hj
    have h1 : moreauEnvelope Ψ τ (toSpace (x j₀))
        + (inner ℝ q (toSpace (x j)) - inner ℝ q (toSpace (x j₀)))
        ≤ moreauEnvelope Ψ τ (toSpace (x j)) := by
      rw [← inner_sub_right]
      exact moreauEnvelope_ge_linear hΨ hτ (toSpace (x j₀)) (toSpace (x j))
    have h2 := hmax j hj
    linarith
  have hΨle : ∀ j ≤ n,
      Ψ (toSpace (x j)) ≤ inner ℝ q (toSpace (x j₀)) + τ * normMax Ψ ^ 2 / 2 := by
    intro j hj
    have h1 := (moreauEnvelope_comparison hΨ hτ (toSpace (x j))).1
    have h2 := hmax j hj
    have h3 : moreauEnvelope Ψ τ (toSpace (x j₀)) ≤ inner ℝ q (toSpace (x j₀)) :=
      ((moreauEnvelope_comparison hΨ hτ (toSpace (x j₀))).2).trans (min_le_right _ _)
    linarith
  have hradius : normMaxRadius Ψ x n ≤ inner ℝ q (toSpace (x j₀)) + τ * normMax Ψ ^ 2 / 2 := by
    unfold normMaxRadius
    exact Finset.sup'_le _ _ fun j hj => hΨle j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have hkey : inner ℝ q (toSpace (x j₀)) ≤ r + η * τ / 4 := by
    by_cases hTr : inner ℝ q (toSpace (x j₀)) ≤ r
    · linarith
    · replace hTr := not_le.1 hTr
      have hx₀ : x j₀ ≠ 0 := by
        intro h0
        rw [h0, OuterRadius.toSpace_zero_eq, inner_zero_right] at hTr
        linarith
      have hcapH : ∀ j ≤ n, inner ℝ q (toSpace (x j₀)) - η * τ < inner ℝ q (toSpace (x j)) →
          normMin Ψ ^ 2 / 2 ≤ inner ℝ q (ξ (x j)) := by
        intro j hj hlt
        have hs : r / 2 ≤ inner ℝ q (toSpace (x j)) := by linarith
        have hnorm : τ * normMax Ψ < ‖toSpace (x j)‖ :=
          OuterRadius.lt_norm_of_lt_inner hΛpos hqΛ hη2 hs
        have hne : toSpace (x j) ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hnorm
          have := mul_pos hτ hΛpos
          linarith
        have hxj : x j ≠ 0 := fun h0 => hne (by rw [h0, OuterRadius.toSpace_zero_eq])
        exact hcap hd hΨ hτ (toSpace (x j₀)) (toSpace (x j)) (hmax j hj) hlt hnorm
          (ξ (x j)) (hξ (x j) hxj)
      have hcross := hC ξ hξ hξ0 n hn q hqΛ x hx0 hstep hZ (fun k hk => hmart₀ hx₀ k hk)
        j₀ hj₀n hlin (η * τ) hητ hcapH r hr.le
      have hsup := OuterRadius.sup_localTime_le (q := q) (r := r) hLb x n
        (fun z hz => hloc z (hz.trans (hqΨ _)))
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      have hE : C * (1 + ((((departureRange x n).filter
            (fun z => r ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ))
            * Real.log n ≤ η * τ / 4 := by
        have h1 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add_left hsup 1) hCpos.le) hlog
        linarith
      rcases max_cases (inner ℝ q (toSpace (x j₀)) - η * τ) r with ⟨hm, _⟩ | ⟨hm, _⟩
      · rw [hm] at hcross
        linarith
      · rw [hm] at hcross
        linarith
  linarith

end CERW.Support.Norm

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The outer radius from the profile -/

/-- The outer radius bound: the deterministic crossing argument combined with the arithmetic of
the rates. The constant `K₁` fixes the scale `τ = K₁ (1 + L_b) log n` of the Moreau envelope. -/
private theorem outer_rates (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ))
    (hcap : Statements.moreau_cap) (houter : Statements.outer_crossing)
    {C₁ C_lt : ℝ} (hC₁ : 0 < C₁) (hC_lt : 0 < C_lt) :
    ∃ K₁ C r₀ M : ℝ, 0 < K₁ ∧ 0 < C ∧ 0 < M ∧
      ∀ (ξ : Site d → EuclideanSpace ℝ (Fin d)),
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ (n : ℕ), 2 ≤ n → ∀ (x : ℕ → Site d), x 0 = 0 →
      (∀ j, x (j + 1) - x j ∈ unitSteps d) → ∀ (τ r : ℝ), r₀ ≤ r → 1 ≤ Real.log n →
      M * Real.log n ^ (d + 5) ≤ r →
      τ = K₁ * (1 + C_lt * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)))) *
        Real.log n →
      (∀ z : Site d, r ≤ Ψ (toSpace z) →
        (localTime x n z : ℝ) ≤ C_lt * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)))) →
      (∀ s t : ℕ, s < t → t ≤ n →
        ‖(toSpace (x t) + ε • ∑ j ∈ Finset.range t,
            if x j ∉ departureRange x j then ξ (x j) else 0) -
          (toSpace (x s) + ε • ∑ j ∈ Finset.range s,
            if x j ∉ departureRange x j then ξ (x j) else 0)‖ ≤
          C₁ * Real.sqrt (((t : ℝ) - s) * Real.log n)) →
      (∀ j : ℕ, j ≤ n → x j ≠ 0 → ∀ k : ℕ, k ≤ n →
        |dynkinMart (driftStepProb d ε ξ)
            (fun z => max (inner ℝ (gradient (moreauEnvelope Ψ τ) (toSpace (x j)))
              (toSpace z) - k * normMax Ψ) 0) x n| ≤
          C₁ * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange x n).filter
              (fun z => (k : ℝ) * normMax Ψ - normMax Ψ <
                inner ℝ (gradient (moreauEnvelope Ψ τ) (toSpace (x j))) (toSpace z)),
            (localTime x n z : ℝ)) + Real.log n)) →
      normMaxRadius Ψ x n - r ≤
        C * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)) * Real.log n) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hc0, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 (ContactAssembly.normMin_le_normMax hd1 hΨ)
  obtain ⟨C_out, hCout, hdet⟩ := outer_deterministic hd hΨ hε hell hcap houter hC₁
  set η : ℝ := normMin Ψ ^ 4 / (8 * normMax Ψ ^ 2) with hηdef
  have hη : 0 < η := by positivity
  set K₁ : ℝ := 4 * C_out / η with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  obtain ⟨C_oa, r_oa, M_oa, hCoa, hMoa, hoa⟩ := outer_arith hd (K₁ := K₁) (C₀ := C_lt)
    (η := η) (Λsq := normMax Ψ ^ 2) (E := η / 4 + normMax Ψ ^ 2 / 2) hK₁0 hC_lt hη
    (by positivity) (by positivity)
  refine ⟨K₁, C_oa, max r_oa 1, M_oa, hK₁0, hCoa, hMoa, ?_⟩
  intro ξ hξ hξ0 n hn x hx0 hstep τ r hr hℓ hM hτ hprof hvec hLM
  have hr_oa : r_oa ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hr)
  obtain ⟨h1, h2, h3⟩ := hoa r (Real.log n) hr_oa hℓ hM
  have hℓ0 : 0 < Real.log n := lt_of_lt_of_le one_pos hℓ
  have hqnn : 0 ≤ rateQ d r (Real.log n) := rateQ_nonneg d hr0 hℓ0.le
  set Lb : ℝ := C_lt * (r * rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1))) with hLb
  have hLb0 : 0 ≤ Lb := by
    have : 0 ≤ rateQ d r (Real.log n) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_nonneg hqnn _
    positivity
  have hτ0 : 0 < τ := by
    rw [hτ]
    have : 0 < 1 + Lb := by linarith
    positivity
  have hτ' : τ = K₁ * (1 + Lb) * Real.log n := hτ
  rw [← hτ'] at h1 h2 h3
  have h4 : 4 * C_out * (1 + Lb) * Real.log n ≤ η * τ := by
    rw [hτ', hK₁]
    have : η * (4 * C_out / η * (1 + Lb) * Real.log n) = 4 * C_out * (1 + Lb) * Real.log n := by
      field_simp
    rw [this]
  have hfin := hdet ξ hξ hξ0 n hn x hx0 hstep τ r Lb hτ0 hr0 hLb0 h1 h2 h4 hprof hvec hLM
  linarith

end CERW.Support.Norm

namespace CERW.Support.Norm.LinearEvent

open CERW CERW.Support.Drift CERW.Support.Law

variable {d : ℕ}

/-- The embedding of lattice sites into `ℝ^d` is additive. -/
private lemma toSpace_add (x y : Site d) : toSpace (x + y) = toSpace x + toSpace y := by
  ext i
  simp [toSpace]

/-- A unit step changes a projection `⟨q, ·⟩` of the embedded position by at most `‖q‖`. -/
private lemma abs_inner_toSpace_le (q : EuclideanSpace ℝ (Fin d)) {e : Site d}
    (he : e ∈ unitSteps d) : |inner ℝ q (toSpace e)| ≤ ‖q‖ := by
  have h := abs_real_inner_le_norm q (toSpace e)
  rw [norm_toSpace, euclidNorm_of_mem_unitSteps he, mul_one] at h
  exact h

/-- `Λ_Ψ ≥ 0` for a norm `Ψ`. -/
private lemma normMax_nonneg {Ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hΨ : IsNorm Ψ) :
    0 ≤ normMax Ψ := by
  refine Real.sSup_nonneg ?_
  rintro _ ⟨u, -, rfl⟩
  exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 u

/-- The ramp `max (⟨q, ·⟩ - a) 0` moves by at most `‖q‖` in one unit step. -/
private lemma abs_ramp_sub_le (q : EuclideanSpace ℝ (Fin d)) (a : ℝ) (z : Site d) {e : Site d}
    (he : e ∈ unitSteps d) :
    |max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0| ≤ ‖q‖ := by
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have h : inner ℝ q (toSpace (z + e)) - a - (inner ℝ q (toSpace z) - a) =
      inner ℝ q (toSpace e) := by
    rw [toSpace_add, inner_add_right]
    ring
  rw [h]
  exact abs_inner_toSpace_le q he

/-- The squared one-step oscillation of the ramp is at most `Λ²` when the current value of
`⟨q, ·⟩` exceeds `a - Λ`, and vanishes otherwise. -/
private lemma ramp_sq_sub_le {q : EuclideanSpace ℝ (Fin d)} {Λ : ℝ} (hq : ‖q‖ ≤ Λ) (a : ℝ)
    (z : Site d) {e : Site d} (he : e ∈ unitSteps d) :
    (max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0) ^ 2 ≤
      Λ ^ 2 * (if a - Λ < inner ℝ q (toSpace z) then 1 else 0) := by
  split_ifs with h
  · rw [mul_one, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_ramp_sub_le q a z he).trans hq) 2
  · rw [mul_zero]
    have hle : inner ℝ q (toSpace z) ≤ a - Λ := not_lt.mp h
    have he' := (abs_le.mp (abs_inner_toSpace_le q he)).2
    have hq0 := norm_nonneg q
    have h1 : max (inner ℝ q (toSpace (z + e)) - a) 0 = 0 := by
      rw [toSpace_add, inner_add_right]
      exact max_eq_right (by linarith)
    have h2 : max (inner ℝ q (toSpace z) - a) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2]
    norm_num

/-- The one-step mean square oscillation of the ramp under a probability vector on the unit
steps is at most `Λ² 1{a - Λ < ⟨q, z⟩}`. -/
private lemma sum_ramp_sq_le {q : EuclideanSpace ℝ (Fin d)} {Λ : ℝ} (hq : ‖q‖ ≤ Λ) (a : ℝ)
    (z : Site d) {w : Site d → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∑ e ∈ unitSteps d, w e = 1) :
    ∑ e ∈ unitSteps d, w e *
        (max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0) ^ 2 ≤
      Λ ^ 2 * (if a - Λ < inner ℝ q (toSpace z) then 1 else 0) := by
  calc ∑ e ∈ unitSteps d, w e *
        (max (inner ℝ q (toSpace (z + e)) - a) 0 - max (inner ℝ q (toSpace z) - a) 0) ^ 2
      ≤ ∑ e ∈ unitSteps d,
          w e * (Λ ^ 2 * (if a - Λ < inner ℝ q (toSpace z) then 1 else 0)) :=
        Finset.sum_le_sum fun e he =>
          mul_le_mul_of_nonneg_left (ramp_sq_sub_le hq a z he) (hw0 e)
    _ = Λ ^ 2 * (if a - Λ < inner ℝ q (toSpace z) then 1 else 0) := by
        rw [← Finset.sum_mul, hw1, one_mul]

/-- The predictable bracket of the rescaling `c M` of a martingale is at most
`c² K ∑_{t<n} g_t` whenever the conditional variances of the increments of `M` are at most
`K g_t`. -/
private lemma predBracket_smul_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (ℱ : Filtration ℕ m0) (M : ℕ → Ω → ℝ) (c K : ℝ) (g : ℕ → Ω → ℝ)
    (hvar : ∀ t, μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t] ≤ᵐ[μ] fun ω => K * g t ω) :
    ∀ᵐ ω ∂μ, ∀ n, predBracket μ ℱ (fun t ω => c * M t ω) (fun t ω => c * M t ω) n ω ≤
      c ^ 2 * (K * ∑ t ∈ Finset.range n, g t ω) := by
  have hscale : ∀ t,
      μ[fun ω => (c * M (t + 1) ω - c * M t ω) * (c * M (t + 1) ω - c * M t ω) | ℱ t]
        =ᵐ[μ] fun ω => c ^ 2 * μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t] ω := by
    intro t
    have hfun : (fun ω => (c * M (t + 1) ω - c * M t ω) * (c * M (t + 1) ω - c * M t ω)) =
        (c ^ 2) • fun ω => (M (t + 1) ω - M t ω) ^ 2 := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun]
    exact condExp_smul (c ^ 2) _ (ℱ t)
  filter_upwards [ae_all_iff.mpr hvar, ae_all_iff.mpr hscale] with ω h1 h2 n
  unfold predBracket
  rw [Finset.sum_apply]
  calc ∑ t ∈ Finset.range n,
        μ[fun ω => (c * M (t + 1) ω - c * M t ω) * (c * M (t + 1) ω - c * M t ω) | ℱ t] ω
      ≤ ∑ t ∈ Finset.range n, c ^ 2 * (K * g t ω) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [h2 t]
        exact mul_le_mul_of_nonneg_left (h1 t) (sq_nonneg c)
    _ = c ^ 2 * (K * ∑ t ∈ Finset.range n, g t ω) := by
        rw [Finset.mul_sum, Finset.mul_sum]

/-- The local times summed over the sites of the departure range that satisfy `P` count the
times `t < n` at which the path satisfies `P`. -/
private lemma sum_filter_localTime (Y : ℕ → Site d) (n : ℕ) (P : Site d → Prop)
    [DecidablePred P] :
    ∑ z ∈ (departureRange Y n).filter P, (localTime Y n z : ℝ) =
      ∑ t ∈ Finset.range n, if P (Y t) then (1 : ℝ) else 0 := by
  have h := CERW.Support.LocalTime.sum_range_eq_sum_localTime Y n
    (fun z => if P z then (1 : ℝ) else 0)
  refine Eq.trans ?_ h.symm
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : P z <;> simp [hz]

/-- Rescaling: if `|c M_n - c M_0| ≤ C_F (√(b L) + L)` with `c (2 B) = 1`, `M_0 = 0` and
`b ≤ S`, then `|M_n| ≤ 2 B C_F (√(L S) + L)`. -/
private lemma abs_le_of_rescaled {c B C_F L b S M₀ Mₙ : ℝ} (hB : 0 ≤ B) (hc : c * (2 * B) = 1)
    (hC_F : 0 ≤ C_F) (hL : 0 ≤ L) (hbS : b ≤ S) (hM₀ : M₀ = 0)
    (h : |c * Mₙ - c * M₀| ≤ C_F * (Real.sqrt (b * L) + L)) :
    |Mₙ| ≤ 2 * B * C_F * (Real.sqrt (L * S) + L) := by
  have hMn : Mₙ = 2 * B * (c * Mₙ) := by
    calc Mₙ = (c * (2 * B)) * Mₙ := by rw [hc, one_mul]
      _ = 2 * B * (c * Mₙ) := by ring
  rw [hM₀, mul_zero, sub_zero] at h
  have habs : |Mₙ| = 2 * B * |c * Mₙ| := by
    have h2B : (0 : ℝ) ≤ 2 * B := by linarith
    calc |Mₙ| = |2 * B * (c * Mₙ)| := congrArg (fun x => |x|) hMn
      _ = 2 * B * |c * Mₙ| := by rw [abs_mul, abs_of_nonneg h2B]
  have hsqrt : Real.sqrt (b * L) ≤ Real.sqrt (L * S) :=
    Real.sqrt_le_sqrt (by rw [mul_comm L S]; exact mul_le_mul_of_nonneg_right hbS hL)
  calc |Mₙ| = 2 * B * |c * Mₙ| := habs
    _ ≤ 2 * B * (C_F * (Real.sqrt (b * L) + L)) :=
        mul_le_mul_of_nonneg_left h (by linarith)
    _ ≤ 2 * B * (C_F * (Real.sqrt (L * S) + L)) := by
        gcongr
    _ = 2 * B * C_F * (Real.sqrt (L * S) + L) := by ring

/-- For one pair `(q, k)`, the Dynkin martingale of the ramp `max (⟨q, ·⟩ - kΛ) 0` of the drift
walk exceeds `2 (Λ + 1) C_F (√(log n · S) + log n)` with probability at most `C_F n^{-p}`, where
`S` is the total local time of the sites with `⟨q, z⟩ > kΛ - Λ`, given Freedman's bound for the
natural filtration of the walk. -/
private lemma measure_linear_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ε : ℝ} {ξ : Site d → EuclideanSpace ℝ (Fin d)}
    {X : ℕ → Ω → Site d} (hd : 1 ≤ d) (hε : 0 ≤ ε) (hξ : ∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ))
    (hX : IsDriftCERW μ ε ξ X) {Λ : ℝ} (hΛ : 0 ≤ Λ) {q : EuclideanSpace ℝ (Fin d)}
    (hq : ‖q‖ ≤ Λ) (k : ℕ) {n : ℕ} {C_F p : ℝ} (hC_F : 0 ≤ C_F)
    (hF : ∀ Z : ℕ → Ω → ℝ, Martingale Z (pathFiltration hX.measurable) μ →
      (∀ᵐ ω ∂μ, ∀ t, |Z (t + 1) ω - Z t ω| ≤ 1) →
      μ {ω | ¬ |Z n ω - Z 0 ω| ≤ C_F * (Real.sqrt (predBracket μ (pathFiltration hX.measurable)
          Z Z n ω * Real.log n) + Real.log n)} ≤ ENNReal.ofReal (C_F * (n : ℝ) ^ (-p))) :
    μ {ω | 2 * (Λ + 1) * C_F * (Real.sqrt (Real.log n *
          ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
          (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
        |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * Λ) 0) (fun j => X j ω) n|} ≤
      ENNReal.ofReal (C_F * (n : ℝ) ^ (-p)) := by
  classical
  set ℱ := pathFiltration hX.measurable with hℱ
  set f : Site d → ℝ := fun z => max (inner ℝ q (toSpace z) - k * Λ) 0 with hf
  set c : ℝ := (2 * (Λ + 1))⁻¹ with hc
  have hB : 0 < 2 * (Λ + 1) := by linarith
  have hc0 : 0 ≤ c := inv_nonneg.mpr hB.le
  have hc1 : c * (2 * (Λ + 1)) = 1 := inv_mul_cancel₀ hB.ne'
  have hc2 : c * (2 * Λ) ≤ 1 := by
    calc c * (2 * Λ) ≤ c * (2 * (Λ + 1)) := mul_le_mul_of_nonneg_left (by linarith) hc0
      _ = 1 := hc1
  have hcΛ : c * Λ ≤ 1 := by
    have h2 : c * (2 * Λ) = 2 * (c * Λ) := by ring
    linarith
  have hM := martingale_driftDynkin hd hε hξ hX f
  have hZ : Martingale (fun t ω => c * driftDynkin ε ξ f X t ω) ℱ μ := hM.smul c
  have hinc : ∀ᵐ ω ∂μ, ∀ t,
      |driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω| ≤ 2 * Λ := by
    filter_upwards [ae_abs_driftDynkin_succ_sub_le hd hε hξ hX f] with ω hω t
    exact hω t Λ fun e he => (abs_ramp_sub_le q (k * Λ) (X t ω) he).trans hq
  have hincZ : ∀ᵐ ω ∂μ, ∀ t,
      |c * driftDynkin ε ξ f X (t + 1) ω - c * driftDynkin ε ξ f X t ω| ≤ 1 := by
    filter_upwards [hinc] with ω hω t
    rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left (hω t) hc0).trans hc2
  have hvar : ∀ t, μ[fun ω => (driftDynkin ε ξ f X (t + 1) ω - driftDynkin ε ξ f X t ω) ^ 2 |
        ℱ t] ≤ᵐ[μ]
      fun ω => Λ ^ 2 * (if (k : ℝ) * Λ - Λ < inner ℝ q (toSpace (X t ω)) then 1 else 0) := by
    intro t
    refine (condExp_sq_driftDynkin_succ_sub_le hd hε hξ hX f t).trans
      (Filter.Eventually.of_forall fun ω => ?_)
    exact sum_ramp_sq_le hq (k * Λ) (X t ω) (fun e => driftStepProb_nonneg hε hξ _ t e)
      (sum_driftStepProb hd ε ξ _ t)
  have hbr := predBracket_smul_le ℱ (driftDynkin ε ξ f X) c (Λ ^ 2)
    (fun t ω => if (k : ℝ) * Λ - Λ < inner ℝ q (toSpace (X t ω)) then 1 else 0) hvar
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  refine le_trans (measure_mono_ae ?_) (hF _ hZ hincZ)
  filter_upwards [hbr] with ω hω hmem
  intro hle
  have hcount : ∑ z ∈ (departureRange (fun j => X j ω) n).filter
        (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
        (localTime (fun j => X j ω) n z : ℝ) =
      ∑ t ∈ Finset.range n,
        (if (k : ℝ) * Λ - Λ < inner ℝ q (toSpace (X t ω)) then (1 : ℝ) else 0) :=
    sum_filter_localTime (fun j => X j ω) n _
  have hS0 : 0 ≤ ∑ z ∈ (departureRange (fun j => X j ω) n).filter
        (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
        (localTime (fun j => X j ω) n z : ℝ) :=
    Finset.sum_nonneg fun z _ => Nat.cast_nonneg _
  have hcΛ2 : c ^ 2 * Λ ^ 2 ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg hc0 hΛ) hcΛ
  have hbS : predBracket μ ℱ (fun t ω => c * driftDynkin ε ξ f X t ω)
        (fun t ω => c * driftDynkin ε ξ f X t ω) n ω ≤
      ∑ z ∈ (departureRange (fun j => X j ω) n).filter
        (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
        (localTime (fun j => X j ω) n z : ℝ) := by
    calc predBracket μ ℱ (fun t ω => c * driftDynkin ε ξ f X t ω)
          (fun t ω => c * driftDynkin ε ξ f X t ω) n ω
        ≤ c ^ 2 * (Λ ^ 2 * ∑ t ∈ Finset.range n,
            (if (k : ℝ) * Λ - Λ < inner ℝ q (toSpace (X t ω)) then (1 : ℝ) else 0)) := hω n
      _ = (c ^ 2 * Λ ^ 2) * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
            (localTime (fun j => X j ω) n z : ℝ) := by
          rw [hcount]
          ring
      _ ≤ 1 * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
            (localTime (fun j => X j ω) n z : ℝ) :=
          mul_le_mul_of_nonneg_right hcΛ2 hS0
      _ = _ := one_mul _
  have hmem' : 2 * (Λ + 1) * C_F * (Real.sqrt (Real.log n *
          ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * Λ - Λ < inner ℝ q (toSpace z)),
          (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
        |driftDynkin ε ξ f X n ω| := by
    rw [← dynkinMart_driftStepProb_eq_driftDynkin hd ε ξ f X n ω]
    exact hmem
  exact absurd hmem' (not_lt.mpr (abs_le_of_rescaled (by linarith) hc1 hC_F hL hbS
    (driftDynkin_zero ε ξ f X ω) hle))

end CERW.Support.Norm.LinearEvent

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## The linear martingales -/

/-- A simultaneous half-space martingale bound for a deterministic finite family of directions. -/
theorem exists_linear_martingale_bound (hd : 2 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ}
    (hε : 0 < ε) (hell : ∀ i : Fin d, ε * Ψ (coordVec i) < 1 / (d : ℝ)) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ξ : Site d → EuclideanSpace ℝ (Fin d)},
      (∀ x : Site d, x ≠ 0 → IsSubgradient Ψ (toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        {X : ℕ → Ω → Site d}, IsDriftCERW μ ε ξ X → ∀ n : ℕ, 2 ≤ n →
        ∀ Q : Finset (EuclideanSpace ℝ (Fin d)), (∀ q ∈ Q, ‖q‖ ≤ normMax Ψ) →
        μ {ω | ∃ q ∈ Q, ∃ k : ℕ, k ≤ n ∧
          C * (Real.sqrt (Real.log n * ∑ z ∈ (departureRange (fun j => X j ω) n).filter
                (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
              (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
            |dynkinMart (driftStepProb d ε ξ)
              (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0)
              (fun j => X j ω) n|} ≤
          ENNReal.ofReal (C * ((Q.card : ℝ) * ((n : ℝ) + 1)) * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  have hΛ : 0 ≤ normMax Ψ := LinearEvent.normMax_nonneg hΨ
  obtain ⟨C_F, hC_F, hfree⟩ := freedman_bound p hp
  refine ⟨(2 * (normMax Ψ + 1) + 1) * C_F, mul_pos (by linarith) hC_F, ?_⟩
  intro ξ hξ hξ0 Ω inst μ inst' X hX n hn Q hQ
  have hcoord := ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
  have hF := hfree n hn μ (CERW.Support.Law.pathFiltration hX.measurable)
  set E : EuclideanSpace ℝ (Fin d) → ℕ → Set Ω := fun q k =>
    {ω | 2 * (normMax Ψ + 1) * C_F * (Real.sqrt (Real.log n *
        ∑ z ∈ (departureRange (fun j => X j ω) n).filter
          (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
        (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
      |dynkinMart (driftStepProb d ε ξ)
        (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) (fun j => X j ω) n|} with hE
  have key : ∀ q ∈ Q, ∀ k : ℕ, μ (E q k) ≤ ENNReal.ofReal (C_F * (n : ℝ) ^ (-p)) :=
    fun q hq k => LinearEvent.measure_linear_le hd1 hε.le hcoord hX hΛ (hQ q hq) k hC_F.le hF
  have hsub : {ω | ∃ q ∈ Q, ∃ k : ℕ, k ≤ n ∧
        (2 * (normMax Ψ + 1) + 1) * C_F * (Real.sqrt (Real.log n *
          ∑ z ∈ (departureRange (fun j => X j ω) n).filter
            (fun z => (k : ℝ) * normMax Ψ - normMax Ψ < inner ℝ q (toSpace z)),
          (localTime (fun j => X j ω) n z : ℝ)) + Real.log n) <
        |dynkinMart (driftStepProb d ε ξ)
          (fun z => max (inner ℝ q (toSpace z) - k * normMax Ψ) 0) (fun j => X j ω) n|} ⊆
      ⋃ q ∈ Q, ⋃ k ∈ Finset.range (n + 1), E q k := by
    intro ω hω
    obtain ⟨q, hq, k, hk, hlt⟩ := hω
    simp only [Set.mem_iUnion]
    refine ⟨q, hq, k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), ?_⟩
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hC_F.le) ?_) hlt
    exact add_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n)
  have hR : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine (measure_mono hsub).trans ?_
  calc μ (⋃ q ∈ Q, ⋃ k ∈ Finset.range (n + 1), E q k)
      ≤ ∑ q ∈ Q, μ (⋃ k ∈ Finset.range (n + 1), E q k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Q, ∑ k ∈ Finset.range (n + 1), μ (E q k) :=
        Finset.sum_le_sum fun q _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ Q, ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (C_F * (n : ℝ) ^ (-p)) :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun k _ => key q hq k
    _ = ENNReal.ofReal ((Q.card : ℝ) * (((n + 1 : ℕ) : ℝ) * (C_F * (n : ℝ) ^ (-p)))) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (((2 * (normMax Ψ + 1) + 1) * C_F) *
          ((Q.card : ℝ) * ((n : ℝ) + 1)) * (n : ℝ) ^ (-p)) := by
        apply ENNReal.ofReal_le_ofReal
        have hK : 1 ≤ 2 * (normMax Ψ + 1) + 1 := by linarith
        have hP : 0 ≤ (Q.card : ℝ) * ((n : ℝ) + 1) * (n : ℝ) ^ (-p) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
            (add_nonneg (Nat.cast_nonneg n) zero_le_one)) hR
        calc (Q.card : ℝ) * (((n + 1 : ℕ) : ℝ) * (C_F * (n : ℝ) ^ (-p)))
            = C_F * ((Q.card : ℝ) * ((n : ℝ) + 1) * (n : ℝ) ^ (-p)) := by
              push_cast
              ring
          _ ≤ ((2 * (normMax Ψ + 1) + 1) * C_F) *
              ((Q.card : ℝ) * ((n : ℝ) + 1) * (n : ℝ) ^ (-p)) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hC_F.le hK) hP
          _ = ((2 * (normMax Ψ + 1) + 1) * C_F) *
              ((Q.card : ℝ) * ((n : ℝ) + 1)) * (n : ℝ) ^ (-p) := by ring

end CERW.Support.Norm
namespace CERW.Support.Norm.ShapeOfRates

open CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A site whose norm is below the norm inner radius lies in the departure range. -/
private theorem mem_departureRange_of_lt_normInnerRadius (hΨ : IsNorm Ψ) (Y : ℕ → Site d)
    (n : ℕ) {x : Site d} (hx : Ψ (toSpace x) < normInnerRadius Ψ Y n) :
    x ∈ departureRange Y n := by
  rw [← CERW.Support.Occupation.toSpace_mem_cellSet_iff]
  by_contra hnot
  have hbdd : BddBelow (Ψ '' (cellSet Y n)ᶜ) :=
    ⟨0, by
      rintro _ ⟨y, -, rfl⟩
      exact (CERW.Generic.Norm.map_zero_nonneg_neg hΨ).2.1 y⟩
  exact absurd hx (not_lt.mpr (csInf_le hbdd ⟨toSpace x, hnot, rfl⟩))

/-- A site of the departure range has norm at most the norm outer radius. -/
private theorem le_normMaxRadius_of_mem (Y : ℕ → Site d) (n : ℕ) {x : Site d}
    (hx : x ∈ departureRange Y n) : Ψ (toSpace x) ≤ normMaxRadius Ψ Y n := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.le_sup' (fun j => Ψ (toSpace (Y j)))
    (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hj)))

/-- For `α < 1` and `ℓ ≥ 0`, `r^α ℓ^β / r = (ℓ^{β/(1-α)} / r)^{1-α}`. -/
private lemma rpow_mul_rpow_div_eq {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 ≤ ℓ) {α : ℝ} (hα : α < 1)
    (β : ℝ) : r ^ α * ℓ ^ β / r = (ℓ ^ (β / (1 - α)) / r) ^ (1 - α) := by
  have h1 : 1 - α ≠ 0 := (sub_pos.mpr hα).ne'
  have h2 : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  rw [Real.div_rpow (Real.rpow_nonneg hℓ _) hr.le, ← Real.rpow_mul hℓ, div_mul_cancel₀ _ h1,
    Real.rpow_sub hr, Real.rpow_one]
  field_simp

/-- `r^α (log n)^β` is negligible against `r` for `α < 1`, when every power of `log n` is
negligible against `r`. -/
private lemma tendsto_rpow_mul_rpow_log_div {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hlog : ∀ K : ℝ, Tendsto (fun n : ℕ => Real.log n ^ K / r n) atTop (𝓝 0)) {α : ℝ}
    (hα : α < 1) (β : ℝ) :
    Tendsto (fun n : ℕ => r n ^ α * Real.log n ^ β / r n) atTop (𝓝 0) := by
  have hpos : 0 < 1 - α := sub_pos.mpr hα
  have hlim := (hlog (β / (1 - α))).rpow_const (Or.inr hpos.le)
  rw [Real.zero_rpow hpos.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [hr.eventually_gt_atTop 0] with n hn
  exact (rpow_mul_rpow_div_eq hn (Real.log_natCast_nonneg n) hα β).symm

/-- The three error rates of the norm shape bounds are negligible against the scale `r`. -/
private theorem error_rates_small (hd : 2 ≤ d) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (hlog : ∀ K : ℝ, Tendsto (fun n : ℕ => Real.log n ^ K / r n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (if d = 2 then r n ^ ((3 : ℝ) / 4) * Real.log n ^ ((1 : ℝ) / 4)
        else (r n * Real.log n) ^ ((1 : ℝ) / 2)) / r n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((7 : ℝ) / 6)
        else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ (((d : ℝ) + 2) / (d + 1))) / r n)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (if d = 2 then r n ^ ((5 : ℝ) / 6) * Real.log n ^ ((1 : ℝ) / 6)
        else r n ^ ((d : ℝ) / (d + 1)) * Real.log n ^ ((1 : ℝ) / (d + 1))) / r n)
      atTop (𝓝 0) := by
  by_cases h2 : d = 2
  · simp only [if_pos h2]
    exact ⟨tendsto_rpow_mul_rpow_log_div hr hlog (by norm_num) _,
      tendsto_rpow_mul_rpow_log_div hr hlog (by norm_num) _,
      tendsto_rpow_mul_rpow_log_div hr hlog (by norm_num) _⟩
  · simp only [if_neg h2]
    have hdpos : (0 : ℝ) < d + 1 := by positivity
    have hα : (d : ℝ) / (d + 1) < 1 := by
      rw [div_lt_one hdpos]
      linarith
    refine ⟨?_, tendsto_rpow_mul_rpow_log_div hr hlog hα _,
      tendsto_rpow_mul_rpow_log_div hr hlog hα _⟩
    refine (tendsto_rpow_mul_rpow_log_div hr hlog (α := 1 / 2) (by norm_num) (1 / 2)).congr' ?_
    filter_upwards [hr.eventually_gt_atTop 0] with n hn
    rw [Real.mul_rpow hn.le (Real.log_natCast_nonneg n)]

/-- Multiplying a negligible error by a constant keeps it negligible. -/
private lemma tendsto_const_mul_div {r e : ℕ → ℝ} (C : ℝ)
    (h : Tendsto (fun n => e n / r n) atTop (𝓝 0)) :
    Tendsto (fun n => C * e n / r n) atTop (𝓝 0) := by
  simpa only [mul_zero, mul_div_assoc] using h.const_mul C

/-- The local times of a site visited only finitely often are bounded. -/
private lemma localTime_le_of_eventually_ne (Y : ℕ → Site d) (x : Site d) (m : ℕ)
    (hm : ∀ j : ℕ, m ≤ j → Y j ≠ x) (n : ℕ) : localTime Y n x ≤ m := by
  rw [localTime]
  calc ((Finset.range n).filter fun j => Y j = x).card
      ≤ (Finset.range m).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter] at hj
        obtain ⟨hjn, hjx⟩ := hj
        rw [Finset.mem_range] at hjn ⊢
        by_contra hjm
        exact hm j (Nat.le_of_not_lt hjm) hjx
    _ = m := Finset.card_range m

/-- The deterministic core of Theorem 2.1: if the inner radius, the outer radius and the local
times of a path agree with the scale `r` up to errors negligible against `r`, then the range is
asymptotically the `Ψ`-ball of radius `r`, the local times follow the profile, and every site is
visited infinitely often. -/
private theorem shape_of_small_errors (hd : 1 ≤ d) (hΨ : IsNorm Ψ) {ε : ℝ} (hε : 0 < ε)
    {r e₁ e₂ e₃ : ℕ → ℝ} (hr : Tendsto r atTop atTop)
    (h₁ : Tendsto (fun n => e₁ n / r n) atTop (𝓝 0))
    (h₂ : Tendsto (fun n => e₂ n / r n) atTop (𝓝 0))
    (h₃ : Tendsto (fun n => e₃ n / r n) atTop (𝓝 0)) (Y : ℕ → Site d)
    (hY : ∀ᶠ n : ℕ in atTop, |normInnerRadius Ψ Y n - r n| ≤ e₁ n ∧
        normMaxRadius Ψ Y n - r n ≤ e₂ n ∧
        ∀ x : Site d,
          |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - Ψ (toSpace x)) 0| ≤ e₃ n) :
    (∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
      {x : Site d | Ψ (toSpace x) < (1 - η) * r n} ⊆ ↑(departureRange Y n) ∧
      (↑(departureRange Y n) : Set (Site d)) ⊆ {x | Ψ (toSpace x) < (1 + η) * r n}) ∧
    (∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - Ψ (toSpace x)) 0| ≤ η * r n) ∧
    (∀ x : Site d, ∃ᶠ j in atTop, Y j = x) := by
  have hsmall : ∀ {e : ℕ → ℝ}, Tendsto (fun n => e n / r n) atTop (𝓝 0) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, e n < η * r n := by
    intro e he η hη
    filter_upwards [he.eventually (gt_mem_nhds hη), hr.eventually_gt_atTop 0] with n h1 h2
    exact (div_lt_iff₀ h2).mp h1
  have hloc : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop, ∀ x : Site d,
      |(localTime Y n x : ℝ) - 2 * d * ε * max (r n - Ψ (toSpace x)) 0| ≤ η * r n := by
    intro η hη
    filter_upwards [hY, hsmall h₃ η hη] with n hn h3 x
    exact (hn.2.2 x).trans h3.le
  refine ⟨?_, hloc, ?_⟩
  · intro η hη hη1
    filter_upwards [hY, hsmall h₁ η hη, hsmall h₂ η hη] with n hn h1 h2
    obtain ⟨hin, hout, -⟩ := hn
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · refine mem_departureRange_of_lt_normInnerRadius hΨ Y n ?_
      have h3 := (abs_le.mp hin).1
      simp only [Set.mem_setOf_eq] at hx
      linarith
    · have h3 := le_normMaxRadius_of_mem (Ψ := Ψ) Y n (Finset.mem_coe.mp hx)
      simp only [Set.mem_setOf_eq]
      linarith
  · intro x
    by_contra hnot
    rw [not_frequently] at hnot
    obtain ⟨m, hm⟩ := eventually_atTop.mp hnot
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hκ : 0 < (d : ℝ) * ε := mul_pos hdpos hε
    obtain ⟨n, hn1, hn2⟩ := ((hloc _ hκ).and
      (hr.eventually_gt_atTop ((m + 2 * ((d : ℝ) * ε) * Ψ (toSpace x)) / ((d : ℝ) * ε)))).exists
    have hle : (localTime Y n x : ℝ) ≤ m := by
      exact_mod_cast localTime_le_of_eventually_ne Y x m hm n
    have h4 := (abs_le.mp (hn1 x)).1
    have h5 : r n - Ψ (toSpace x) ≤ max (r n - Ψ (toSpace x)) 0 := le_max_left _ _
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * d * ε)
    have h7 := (div_lt_iff₀ hκ).mp hn2
    linarith

end CERW.Support.Norm.ShapeOfRates

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## Theorem 2.1 from Proposition 5.1 -/

/-- Theorem 2.1 follows from Proposition 5.1 by the Borel-Cantelli lemma: the rates of
Proposition 5.1 with `p = 2` hold eventually almost surely, and they are negligible against the
scale `r_n`. -/
private theorem norm_shape_of_rates (hrates : Statements.norm_shape_rates.{u}) :
    Statements.norm_shape.{u} := by
  intro d hd Ψ hΨ ξ hξ hξ0 ε hε hell Ω _ μ _ X hX r
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hV : 0 < normBallVolume Ψ := ContactAssembly.normBallVolume_pos' hd1 hΨ
  have hX0 : 0 < 2 * (d : ℝ) * ε * normBallVolume Ψ := by positivity
  obtain ⟨C, hC, hCb⟩ := hrates hd Ψ hΨ ε hε hell 2 (by norm_num)
  have hr : Tendsto r atTop atTop := tendsto_scale d hX0
  have hlog : ∀ K : ℝ, Tendsto (fun n : ℕ => Real.log n ^ K / r n) atTop (𝓝 0) :=
    tendsto_log_rpow_div_scale d hX0
  obtain ⟨t₁, t₂, t₃⟩ := ShapeOfRates.error_rates_small hd hr hlog
  have hev := CERW.Support.Main.ae_eventually_of_le_rpow (p := 2) (n₀ := 2) (by norm_num)
    (fun n hn => hCb ξ hξ hξ0 μ X hX n hn)
  filter_upwards [hev] with ω hω
  exact ShapeOfRates.shape_of_small_errors hd1 hΨ hε hr (ShapeOfRates.tendsto_const_mul_div C t₁)
    (ShapeOfRates.tendsto_const_mul_div C t₂) (ShapeOfRates.tendsto_const_mul_div C t₃)
    (fun j => X j ω) hω

end CERW.Support.Norm

namespace CERW.Support.Norm

open CERW.Support.Statements CERW

variable {d : ℕ} {Ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ## Proposition 5.1 -/

/-- A set covered by five events of small probability and a null event has small probability. -/
private lemma measure_le_of_subset_union_five {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {S E₁ E₂ E₃ E₄ E₅ N : Set Ω} {a₁ a₂ a₃ a₄ a₅ C : ℝ}
    (hS : S ⊆ E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ N)
    (h₁ : μ E₁ ≤ ENNReal.ofReal a₁) (h₂ : μ E₂ ≤ ENNReal.ofReal a₂)
    (h₃ : μ E₃ ≤ ENNReal.ofReal a₃) (h₄ : μ E₄ ≤ ENNReal.ofReal a₄)
    (h₅ : μ E₅ ≤ ENNReal.ofReal a₅) (hN : μ N = 0) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (ha₃ : 0 ≤ a₃) (ha₄ : 0 ≤ a₄) (ha₅ : 0 ≤ a₅) (hC : a₁ + a₂ + a₃ + a₄ + a₅ ≤ C) :
    μ S ≤ ENNReal.ofReal C := by
  calc μ S ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ N) := measure_mono hS
    _ ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅) + μ N := measure_union_le _ _
    _ = μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅) := by rw [hN, add_zero]
    _ ≤ μ (E₁ ∪ E₂ ∪ E₃ ∪ E₄) + μ E₅ := measure_union_le _ _
    _ ≤ (μ (E₁ ∪ E₂ ∪ E₃) + μ E₄) + μ E₅ := add_le_add (measure_union_le _ _) le_rfl
    _ ≤ ((μ (E₁ ∪ E₂) + μ E₃) + μ E₄) + μ E₅ :=
        add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    _ ≤ (((μ E₁ + μ E₂) + μ E₃) + μ E₄) + μ E₅ :=
        add_le_add (add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ (((ENNReal.ofReal a₁ + ENNReal.ofReal a₂) + ENNReal.ofReal a₃) + ENNReal.ofReal a₄) +
          ENNReal.ofReal a₅ := by gcongr
    _ = ENNReal.ofReal (a₁ + a₂ + a₃ + a₄ + a₅) := by
        rw [ENNReal.ofReal_add (by positivity) ha₅, ENNReal.ofReal_add (by positivity) ha₄,
          ENNReal.ofReal_add (add_nonneg ha₁ ha₂) ha₃, ENNReal.ofReal_add ha₁ ha₂]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC

/-- The scale relation `n = X r^{d+1}/(d+1)` for `r = ((d+1) n / X)^{1/(d+1)}`. -/
private lemma nat_eq_scale_pow (d : ℕ) {X : ℝ} (hX : 0 < X) (n : ℕ) :
    (n : ℝ) = X * ((((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) / (d + 1) := by
  have hx : (0 : ℝ) ≤ ((d : ℝ) + 1) * n / X := by positivity
  have h : ((((d : ℝ) + 1) * n / X) ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) =
      ((d : ℝ) + 1) * n / X := by
    rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
      rw [one_div, Nat.cast_add, Nat.cast_one]]
    exact Real.rpow_inv_natCast_pow hx (by omega)
  rw [h]
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The count of the vectors in the union bound: at most `(2n+1)^d` vectors and `n + 1` levels
cost at most `2 · 3^d n^{d+1}`, which `n^{-(p+d+1)}` turns into `n^{-p}`. -/
private lemma union_count_arith {C p : ℝ} (hC : 0 ≤ C) (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : c ≤ (2 * (n : ℝ) + 1) ^ d) :
    C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1)) ≤ (C * 2 * 3 ^ d) * (n : ℝ) ^ (-p) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hrp : 0 ≤ (n : ℝ) ^ (-(p + d + 1)) := Real.rpow_nonneg hnpos.le _
  have h1 : (2 * (n : ℝ) + 1) ^ d ≤ (3 * n) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have h2 : c * ((n : ℝ) + 1) ≤ 3 ^ d * (n : ℝ) ^ d * (2 * n) := by
    calc c * ((n : ℝ) + 1) ≤ (3 * (n : ℝ)) ^ d * (2 * n) :=
          mul_le_mul (hc.trans h1) (by linarith) (by positivity) (by positivity)
      _ = 3 ^ d * (n : ℝ) ^ d * (2 * n) := by rw [mul_pow]
  have h3 : (n : ℝ) ^ (-(p + d + 1)) = (n : ℝ) ^ (-p) * ((n : ℝ) ^ (d + 1))⁻¹ := by
    rw [show -(p + d + 1) = -p + -((d + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hnpos, Real.rpow_neg hnpos.le ((d + 1 : ℕ) : ℝ), Real.rpow_natCast]
  have h4 : (n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹ = 1 := by
    rw [← pow_succ]
    exact mul_inv_cancel₀ (pow_ne_zero _ hnpos.ne')
  calc C * (c * ((n : ℝ) + 1)) * (n : ℝ) ^ (-(p + d + 1))
      ≤ C * (3 ^ d * (n : ℝ) ^ d * (2 * n)) * (n : ℝ) ^ (-(p + d + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC) hrp
    _ = (C * 2 * 3 ^ d) * (n : ℝ) ^ (-p) * ((n : ℝ) ^ d * n * ((n : ℝ) ^ (d + 1))⁻¹) := by
        rw [h3]
        ring
    _ = (C * 2 * 3 ^ d) * (n : ℝ) ^ (-p) := by rw [h4, mul_one]

/-- Proposition 5.1 from the estimates of Sections 3 to 5 and the assumed lemmas. -/
private theorem main_rates (hlocal : Statements.norm_local_time_potential.{u})
    (hcoarse : Statements.norm_coarse_bounds.{u}) (hcontact : Statements.contact_potential.{u})
    (hlayer : Statements.layer_potential) (hcap : Statements.moreau_cap)
    (houter : Statements.outer_crossing) (hgeom : Statements.norm_potential_geometry)
    (hball : Statements.norm_ball_potential) : Statements.norm_shape_rates.{u} := by
  intro d hd Ψ hΨ ε hε hell r p hp
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume Ψ := ContactAssembly.normBallVolume_pos' hd1 hΨ
  obtain ⟨hc0, hcle⟩ := CERW.Generic.Norm.normMin_pos_mul_le hΨ hd1
  have hΛ : 0 < normMax Ψ := lt_of_lt_of_le hc0 (ContactAssembly.normMin_le_normMax hd1 hΨ)
  obtain ⟨c_co, C_co, hc_co, hC_co, hco⟩ := hcoarse hd Ψ hΨ ε hε hell p hp
  obtain ⟨C_loc, hC_loc, hloc⟩ := hlocal hd Ψ hΨ ε hε hell p hp
  obtain ⟨C_c, hC_c, n_c, hcon⟩ := hcontact hd Ψ hΨ ε hε hell p hp
  obtain ⟨C_in, C_lt, r_in, M_in, hC_in, hC_lt, hM_in, hin⟩ :=
    inner_rates hd hΨ hε hball hlayer hgeom hC_co hC_loc hC_c
  obtain ⟨C_V, hC_V, hvec⟩ := VectorBound.exists_driftCompensated_bound.{u} hd1 hε.le hp
  obtain ⟨C_LM, hC_LM, hLM⟩ := exists_linear_martingale_bound.{u} hd hΨ hε hell
    (p := p + d + 1) (by positivity)
  obtain ⟨K₁, C_ob, r_ob, M_ob, hK₁, hC_ob, hM_ob, hout⟩ :=
    outer_rates hd hΨ hε hell hcap houter (C₁ := max C_V C_LM) (C_lt := C_lt)
      (lt_max_of_lt_left hC_V) hC_lt
  set X₀ : ℝ := 2 * d * ε * normBallVolume Ψ with hX₀
  have hX₀pos : 0 < X₀ := by positivity
  have hrdef : ∀ n : ℕ, r n = (((d : ℝ) + 1) * n / X₀) ^ ((1 : ℝ) / (d + 1)) := fun n => rfl
  set M₀ : ℝ := max M_in M_ob with hM₀
  have hM₀pos : 0 < M₀ := lt_max_of_lt_left hM_in
  have hreg : ∀ᶠ n : ℕ in atTop, max n_c 3 ≤ n ∧ max r_in r_ob ≤ r n ∧
      M₀ * Real.log n ^ (d + 5) ≤ r n ∧ (C_co + 1) * r n ≤ 2 * n := by
    have h1 : ∀ᶠ n : ℕ in atTop, max n_c 3 ≤ n := eventually_ge_atTop _
    have hrt := tendsto_scale d hX₀pos
    have h2 : ∀ᶠ n : ℕ in atTop, max r_in r_ob ≤ r n := hrt.eventually_ge_atTop _
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < r n := hrt.eventually_gt_atTop 0
    have h3 : ∀ᶠ n : ℕ in atTop, M₀ * Real.log n ^ (d + 5) ≤ r n := by
      have ht := tendsto_log_rpow_div_scale d hX₀pos ((d + 5 : ℕ) : ℝ)
      have ht' := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / M₀ by positivity))
      filter_upwards [ht', hpos] with n hn hrn
      have hn' : Real.log n ^ ((d + 5 : ℕ) : ℝ) / r n < 1 / M₀ := hn
      rw [Real.rpow_natCast, div_lt_iff₀ hrn] at hn'
      calc M₀ * Real.log n ^ (d + 5) ≤ M₀ * (1 / M₀ * r n) :=
            mul_le_mul_of_nonneg_left hn'.le hM₀pos.le
        _ = r n := by field_simp
    have h4 : ∀ᶠ n : ℕ in atTop, (C_co + 1) * r n ≤ 2 * n := by
      have ht := tendsto_scale_div_self d hd1 hX₀pos
      have hK : 0 < C_co + 1 := by linarith
      have ht' := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 2 / (C_co + 1) by positivity))
      filter_upwards [ht', eventually_ge_atTop 1] with n hn hn1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hn' : r n / n < 2 / (C_co + 1) := hn
      rw [div_lt_div_iff₀ hn0 hK] at hn'
      linarith
    filter_upwards [h1, h2, h3, h4] with n a b c' d'
    exact ⟨a, b, c', d'⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hreg
  set C_prob : ℝ := C_co + C_loc + C_c + C_V + C_LM * 2 * 3 ^ d with hCprob
  have hCprob0 : 0 < C_prob := by positivity
  set C₀ : ℝ := max (max (max C_in C_lt) C_ob) C_prob with hC₀
  refine ⟨max C₀ ((N₁ : ℝ) ^ p), lt_max_of_lt_left (lt_max_of_lt_right hCprob0), ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnp : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  by_cases hnN : N₁ ≤ n
  · obtain ⟨hnmax, hrr, hMlog, hK2n⟩ := hN₁ n hnN
    have hn_c : n_c ≤ n := (le_max_left _ _).trans hnmax
    have hn3 : 3 ≤ n := (le_max_right _ _).trans hnmax
    have hℓ1 : (1 : ℝ) ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hnpos]
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      linarith [Real.exp_one_lt_three]
    have hℓ0 : 0 < Real.log n := by linarith
    have hr_in : r_in ≤ r n := (le_max_left _ _).trans hrr
    have hr_ob : r_ob ≤ r n := (le_max_right _ _).trans hrr
    have hrpos : 0 < r n := by
      rw [hrdef n]
      exact Real.rpow_pos_of_pos (by positivity) _
    have hpowℓ : 0 ≤ Real.log n ^ (d + 5) := pow_nonneg hℓ0.le _
    have hM_in' : M_in * Real.log n ^ (d + 5) ≤ r n :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpowℓ) hMlog
    have hM_ob' : M_ob * Real.log n ^ (d + 5) ≤ r n :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpowℓ) hMlog
    have hξ' := ContactAssembly.drift_coord_le hΨ hε hell hξ hξ0
    have hpath : ∀ᵐ ω ∂μ, X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d := by
      have h0 : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
        rw [ae_iff]
        exact hX.start
      filter_upwards [h0, ae_all_iff.mpr
        (CERW.Support.Drift.ae_sub_mem_unitSteps_drift hd1 hε.le hξ' hX)] with ω h0 hs
      exact ⟨h0, hs⟩
    have hN : μ {ω | ¬ (X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d)} = 0 :=
      ae_iff.mp hpath
    obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = K₁ * (1 + C_lt * (r n * rateQ d (r n) (Real.log n) ^
        ((1 : ℝ) / (d + 1)))) * Real.log n := ⟨_, rfl⟩
    have hτ0 : 0 < τ := by
      have hq := rateQ_nonneg d hrpos hℓ0.le
      have h : 0 ≤ C_lt * (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
        have := Real.rpow_nonneg hq ((1 : ℝ) / (d + 1))
        positivity
      have h' : 0 < 1 + C_lt * (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
        linarith
      rw [hτdef]
      positivity
    set Q : Finset (EuclideanSpace ℝ (Fin d)) := (LatticeProb.ballFinset d (n : ℝ)).image
      (fun z => gradient (moreauEnvelope Ψ τ) (toSpace z)) with hQdef
    have hQ : ∀ q ∈ Q, ‖q‖ ≤ normMax Ψ := by
      intro q hq
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
      exact norm_le_normMax_of_isSubgradient hΨ (isSubgradient_gradient_moreauEnvelope hΨ hτ0 _)
    have hc1 : Q.card ≤ (LatticeProb.ballFinset d (n : ℝ)).card := Finset.card_image_le
    have hcard : (Q.card : ℝ) ≤ (2 * (n : ℝ) + 1) ^ d :=
      (Nat.cast_le.mpr hc1).trans (LatticeProb.card_ballFinset_le d hnpos.le)
    have h₁ := hco ξ hξ hξ0 μ X hX n hn2
    have h₂ := hloc ξ hξ hξ0 μ X hX n hn2
    have h₃ := hcon ξ hξ hξ0 μ X hX n hn_c
    have h₄ := hvec hξ' hξ0 hX n hn2
    have h₅ := hLM hξ hξ0 hX n hn2 Q hQ
    have h₅' := h₅.trans (ENNReal.ofReal_le_ofReal
      (union_count_arith (p := p) hC_LM.le d (by omega) hcard))
    refine measure_le_of_subset_union_five ?_ h₁ h₂ h₃ h₄ h₅' hN (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) ?_
    · intro ω hω
      by_contra hnot
      simp only [Set.mem_union, not_or] at hnot
      obtain ⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩ := hnot
      have hpathω : X 0 ω = 0 ∧ ∀ j, X (j + 1) ω - X j ω ∈ unitSteps d := by
        by_contra hc
        exact g6 hc
      obtain ⟨-, -, -, hMω, -, hRadω⟩ := not_not.mp g1
      obtain ⟨-, -, hlocω⟩ := not_not.mp g2
      have hconω := not_not.mp g3
      have hnr : (n : ℝ) = 2 * ε * d * normBallVolume Ψ * r n ^ (d + 1) / (d + 1) := by
        have h := nat_eq_scale_pow d hX₀pos n
        change (n : ℝ) = X₀ * r n ^ (d + 1) / (d + 1) at h
        rw [h, hX₀]
        ring
      obtain ⟨hinner, hprofile⟩ := hin (fun j => X j ω) n (r n) hpathω.1 hn2 hr_in hℓ1 hM_in'
        hK2n hnr hRadω hMω hlocω hconω
      have hprofω : ∀ z : Site d, r n ≤ Ψ (toSpace z) →
          (localTime (fun j => X j ω) n z : ℝ) ≤
            C_lt * (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1))) := by
        intro z hz
        have h := hprofile (toSpace z)
        rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell z),
          max_eq_right (by linarith), mul_zero, sub_zero,
          abs_of_nonneg (Nat.cast_nonneg _)] at h
        exact h
      have hfin := hout ξ hξ hξ0 n hn2 (fun j => X j ω) hpathω.1 hpathω.2 τ (r n) hr_ob hℓ1
        hM_ob' hτdef hprofω (by
          intro s t hst htn
          by_contra hcon'
          apply g4
          exact ⟨s, t, hst, htn, lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
            (not_le.mp hcon')⟩) (by
          intro j hj hxj k hk
          by_contra hcon'
          apply g5
          refine ⟨gradient (moreauEnvelope Ψ τ) (toSpace (X j ω)), ?_, k, hk, ?_⟩
          · exact Finset.mem_image.mpr ⟨X j ω, LatticeProb.mem_ballFinset_iff.mpr
              ((CERW.Support.Occupation.euclidNorm_le_of_steps (fun j => X j ω) hpathω.1
                hpathω.2 j).trans (by exact_mod_cast hj)), rfl⟩
          · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right _ _)
              (add_nonneg (Real.sqrt_nonneg _) hℓ0.le)) (not_le.mp hcon'))
      simp only [Set.mem_setOf_eq] at hω
      apply hω
      have hCin : C_in ≤ max C₀ ((N₁ : ℝ) ^ p) :=
        ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
          (le_max_left _ _)
      have hClt : C_lt ≤ max C₀ ((N₁ : ℝ) ^ p) :=
        ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
          (le_max_left _ _)
      have hCob : C_ob ≤ max C₀ ((N₁ : ℝ) ^ p) :=
        ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
      have hq := rateQ_nonneg d hrpos hℓ0.le
      refine ⟨?_, ?_, ?_⟩
      · calc |normInnerRadius Ψ (fun j => X j ω) n - r n|
            ≤ C_in * (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / 2)) := hinner
          _ ≤ max C₀ ((N₁ : ℝ) ^ p) * (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_right hCin
                (mul_nonneg hrpos.le (Real.rpow_nonneg hq _))
          _ = _ := by rw [rate_inner_eq hrpos hℓ0]
      · calc normMaxRadius Ψ (fun j => X j ω) n - r n
            ≤ C_ob * (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1)) * Real.log n) :=
              hfin
          _ ≤ max C₀ ((N₁ : ℝ) ^ p) *
                (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1)) * Real.log n) :=
              mul_le_mul_of_nonneg_right hCob
                (mul_nonneg (mul_nonneg hrpos.le (Real.rpow_nonneg hq _)) hℓ0.le)
          _ = _ := by rw [rate_outer_eq hrpos hℓ0]
      · intro x
        have h := hprofile (toSpace x)
        rw [cellLocalTime_of_mem_cell _ _ (toSpace_mem_cell x)] at h
        calc |(localTime (fun j => X j ω) n x : ℝ) -
              2 * d * ε * max (r n - Ψ (toSpace x)) 0|
            ≤ C_lt * (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1))) := h
          _ ≤ max C₀ ((N₁ : ℝ) ^ p) *
                (r n * rateQ d (r n) (Real.log n) ^ ((1 : ℝ) / (d + 1))) :=
              mul_le_mul_of_nonneg_right hClt (mul_nonneg hrpos.le (Real.rpow_nonneg hq _))
          _ = _ := by rw [rate_local_eq hrpos hℓ0]
    · calc C_co * (n : ℝ) ^ (-p) + C_loc * (n : ℝ) ^ (-p) + C_c * (n : ℝ) ^ (-p) +
          C_V * (n : ℝ) ^ (-p) + (C_LM * 2 * 3 ^ d) * (n : ℝ) ^ (-p) =
          C_prob * (n : ℝ) ^ (-p) := by rw [hCprob]; ring
        _ ≤ C₀ * (n : ℝ) ^ (-p) := mul_le_mul_of_nonneg_right (le_max_right _ _) hnp
        _ ≤ max C₀ ((N₁ : ℝ) ^ p) * (n : ℝ) ^ (-p) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hnp
  · have hnN' : n < N₁ := not_le.mp hnN
    calc _ ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (max C₀ ((N₁ : ℝ) ^ p) * (n : ℝ) ^ (-p)) := by
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (n : ℝ) ^ p ≤ (N₁ : ℝ) ^ p :=
            Real.rpow_le_rpow hnpos.le (by exact_mod_cast hnN'.le) hp.le
          have h2 : (1 : ℝ) ≤ (N₁ : ℝ) ^ p * (n : ℝ) ^ (-p) := by
            rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv]
            exact (one_le_div (Real.rpow_pos_of_pos hnpos p)).mpr h1
          exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnp)

end CERW.Support.Norm

namespace CERW.Support.Statements

/-- Proposition 5.1 (prop:norm-shape): the rates for the inner radius, the outer radius and the
local times of the centrally excited random walk with a norm, from Lemmas 3.1, 4.1, 5.4, 5.2, 5.5,
5.3, 3.4 and 2.2. The constant does not depend on the choice of subgradients. -/
theorem _root_.CERW.Support.Norm.norm_shape_rates_of (hlocal : norm_local_time_potential.{u})
    (hcoarse : norm_coarse_bounds.{u}) (hcontact : contact_potential.{u})
    (hlayer : layer_potential) (hcap : moreau_cap) (houter : outer_crossing)
    (hgeom : norm_potential_geometry) (hball : norm_ball_potential) :
    norm_shape_rates.{u} :=
  CERW.Support.Norm.main_rates hlocal hcoarse hcontact hlayer hcap houter hgeom hball

/-- Theorem 2.1 from Proposition 5.1. -/
theorem _root_.CERW.Support.Norm.norm_shape_of (hrates : norm_shape_rates.{u}) :
    norm_shape.{u} :=
  CERW.Support.Norm.norm_shape_of_rates hrates

end CERW.Support.Statements
