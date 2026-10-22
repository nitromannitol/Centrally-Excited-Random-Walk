import CERW.Support.Outer.Radius.PathProbability

/-!
# Radius Asymptotics

The radius and its error scale are positive and satisfy the required asymptotic comparisons. These
estimates compare logarithmic errors with powers of the radius.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- The radius is positive for `n ≥ 1`. -/
lemma radius_pos (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    0 < radius d ε n := by
  unfold radius
  have hω := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- For `n ≥ 2`, `q_n = (log n / r_n)^β` with `β = 1/2` in the plane and `β = 1` otherwise. -/
lemma tk_qrate_eq (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    qrate d ε n = (Real.log n / radius d ε n) ^ (if d = 2 then (1 : ℝ) / 2 else 1) := by
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  unfold qrate
  split_ifs
  · exact Real.sqrt_eq_rpow _
  · exact (Real.rpow_one _).symm

/-- `r_n q_n^{1/d} = r_n^{1-γ} (log n)^γ` with `γ = β/d`. -/
lemma tk_rq_rpow (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n) :
    radius d ε n * qrate d ε n ^ ((1 : ℝ) / d) =
      radius d ε n ^ (1 - (if d = 2 then (1 : ℝ) / 2 else 1) / d) *
        Real.log n ^ ((if d = 2 then (1 : ℝ) / 2 else 1) / d) := by
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hx : 0 ≤ Real.log n / radius d ε n := div_nonneg hlog hr.le
  rw [tk_qrate_eq hd hε hn, ← Real.rpow_mul hx, Real.div_rpow hlog hr.le,
    show (if d = 2 then (1 : ℝ) / 2 else 1) * ((1 : ℝ) / d) =
      (if d = 2 then (1 : ℝ) / 2 else 1) / d by ring,
    Real.rpow_sub hr, Real.rpow_one]
  have hg : 0 < radius d ε n ^ ((if d = 2 then (1 : ℝ) / 2 else 1) / d) :=
    Real.rpow_pos_of_pos hr _
  field_simp

/-- `q_n ≤ 1` eventually. -/
lemma tk_qrate_le_one (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, qrate d ε n ≤ 1 := by
  filter_upwards [tk_log_pow_le hd hε (A := 1) zero_le_one 1 (s := 1) one_pos,
    eventually_ge_atTop 2] with n hn hn2
  have hr := radius_pos hd hε (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  rw [Real.rpow_one, Real.rpow_one, one_mul] at hn
  have h1 : Real.log n / radius d ε n ≤ 1 := (div_le_one hr).2 hn
  unfold qrate
  split_ifs
  · exact Real.sqrt_le_one.mpr h1
  · exact h1

/-- The a priori smallness used to absorb the width: `B log^{d+1} (1 + r q^{1/d}) ≤ r`. -/
lemma tk_small (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, B * Real.log n ^ ((d : ℝ) + 1) *
      (1 + radius d ε n * qrate d ε n ^ ((1 : ℝ) / d)) ≤ radius d ε n := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  set β : ℝ := if d = 2 then (1 : ℝ) / 2 else 1 with hβ
  have hβ0 : 0 < β := by rw [hβ]; split_ifs <;> norm_num
  have hβ1 : β ≤ 1 := by rw [hβ]; split_ifs <;> norm_num
  set γ : ℝ := β / d with hγ
  have hγ0 : 0 < γ := div_pos hβ0 hd0
  have hγ1 : γ ≤ 1 := by
    rw [hγ, div_le_one hd0]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    linarith
  filter_upwards [tk_log_pow_le hd1 hε (A := (d : ℝ) + 1) (by positivity) (2 * |B|)
      (s := 1) one_pos,
    tk_log_pow_le hd1 hε (A := (d : ℝ) + 1 + γ) (by positivity) (2 * |B|) hγ0,
    eventually_ge_atTop 2] with n h1 h2 hn2
  have hr := radius_pos hd1 hε (by omega : 1 ≤ n)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rw [Real.rpow_one] at h1
  rw [tk_rq_rpow hd1 hε hn2, ← hβ, ← hγ]
  have hL1 : 0 ≤ Real.log n ^ ((d : ℝ) + 1) := Real.rpow_nonneg hlog.le _
  have hL2 : Real.log n ^ ((d : ℝ) + 1 + γ) =
      Real.log n ^ ((d : ℝ) + 1) * Real.log n ^ γ := Real.rpow_add hlog _ _
  have hr2 : radius d ε n ^ γ * radius d ε n ^ (1 - γ) = radius d ε n := by
    rw [← Real.rpow_add hr]; simp
  have hBb : B * Real.log n ^ ((d : ℝ) + 1) ≤ |B| * Real.log n ^ ((d : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self B) hL1
  have hpow : 0 ≤ radius d ε n ^ (1 - γ) := Real.rpow_nonneg hr.le _
  have hlg : 0 ≤ Real.log n ^ γ := Real.rpow_nonneg hlog.le _
  calc B * Real.log n ^ ((d : ℝ) + 1) *
        (1 + radius d ε n ^ (1 - γ) * Real.log n ^ γ)
      = B * Real.log n ^ ((d : ℝ) + 1) +
        B * Real.log n ^ ((d : ℝ) + 1) * (radius d ε n ^ (1 - γ) * Real.log n ^ γ) := by ring
    _ ≤ |B| * Real.log n ^ ((d : ℝ) + 1) +
        |B| * Real.log n ^ ((d : ℝ) + 1) * (radius d ε n ^ (1 - γ) * Real.log n ^ γ) := by
        refine add_le_add hBb (mul_le_mul_of_nonneg_right hBb (mul_nonneg hpow hlg))
    _ = |B| * Real.log n ^ ((d : ℝ) + 1) +
        |B| * Real.log n ^ ((d : ℝ) + 1 + γ) * radius d ε n ^ (1 - γ) := by
        rw [hL2]; ring
    _ ≤ radius d ε n / 2 + radius d ε n ^ γ / 2 * radius d ε n ^ (1 - γ) := by
        refine add_le_add (by linarith) (mul_le_mul_of_nonneg_right (by linarith) hpow)
    _ = radius d ε n := by rw [div_mul_eq_mul_div, hr2]; ring

/-- The rate `q_n` is nonnegative for `n ≥ 1`. -/
lemma qrate_nonneg (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ qrate d ε n := by
  unfold qrate
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hr := radius_pos hd hε hn
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact div_nonneg hlog hr.le

/-- `r_n q_n` is `√(r_n log n)` in the plane and `log n` in higher dimensions. -/
lemma radius_mul_qrate (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    radius d ε n * qrate d ε n =
      if d = 2 then Real.sqrt (radius d ε n * Real.log n) else Real.log n := by
  have hr := radius_pos hd hε hn
  unfold qrate
  split_ifs
  · have hnn : 0 ≤ radius d ε n := hr.le
    rw [← Real.sqrt_sq hnn, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnn]
    congr 1
    field_simp
  · field_simp

end CERW.Support.Outer.Radius
