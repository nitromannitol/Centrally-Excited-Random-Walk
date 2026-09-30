import CERW.Support.Law.StepMean
import CERW.Generic.Kernel.ScalarTaylor
import CERW.Model.Potential
import CERW.Support.Occupation.SiteArith

/-!
# The central difference of the potential kernel

The first estimate of `eq:gradient`: `Db(x) = (2/ω_d) x/|x|^d + O(|x|^{-d})`. It is derived from
the asymptotics `eq:kernel-asymptotics`, which enter here as a hypothesis on `b`. With
`1 + t_± = |x ± e_i|²/|x|² = 1 + (1 ± 2x_i)/|x|²`, the second-order bounds for `log(1 + t)`
and `(1 + t)^α` give the leading term. The asymptotic error at `x ± e_i` is `O(|x|^{-d})`.
-/

namespace CERW.Support.LocalTime

open LatticeProb CERW CERW.Support.Law CERW.Generic.Kernel
open CERW.Support.Occupation

variable {d : ℕ}

/-- The square of the Euclidean norm is the sum of the squared coordinates. -/
private lemma euclidNorm_sq (x : Site d) :
    euclidNorm x ^ 2 = ∑ i : Fin d, (((x i : ℤ) : ℝ)) ^ 2 := by
  rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

/-- A coordinate is bounded by the Euclidean norm. -/
private lemma abs_coord_le_euclidNorm (x : Site d) (i : Fin d) :
    |((x i : ℤ) : ℝ)| ≤ euclidNorm x := by
  have hle : ((x i : ℤ) : ℝ) ^ 2 ≤ euclidNorm x ^ 2 := by
    rw [euclidNorm_sq]
    exact Finset.single_le_sum (f := fun j : Fin d => (((x j : ℤ) : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hρ := euclidNorm_nonneg x
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (((x i : ℤ) : ℝ) + euclidNorm x)]
  · nlinarith [sq_nonneg (((x i : ℤ) : ℝ) - euclidNorm x)]

/-- For `ρ > 0`, `ρ/2 ≤ ρp`, and `k : ℕ`, `ρp^{-k} ≤ 2^k ρ^{-k}`. -/
private lemma rpow_neg_le_of_half_le {ρ ρp : ℝ} (hρ : 0 < ρ) (hp : ρ / 2 ≤ ρp) (k : ℕ) :
    ρp ^ (-(k : ℝ)) ≤ 2 ^ k * ρ ^ (-(k : ℝ)) := by
  have hbase : (ρ / 2) ^ (-(k : ℝ)) = 2 ^ k * ρ ^ (-(k : ℝ)) := by
    rw [show (-(k : ℝ)) = -(((k : ℕ) : ℝ)) by norm_num,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ ρ / 2), Real.rpow_natCast]
    rw [div_pow]
    rw [show ρ ^ (-(((k : ℕ) : ℝ))) = (ρ ^ k)⁻¹ by
      rw [Real.rpow_neg hρ.le, Real.rpow_natCast]]
    rw [inv_div, div_eq_mul_inv]
  calc ρp ^ (-(k : ℝ)) ≤ (ρ / 2) ^ (-(k : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hp (neg_nonpos.mpr (Nat.cast_nonneg k))
    _ = 2 ^ k * ρ ^ (-(k : ℝ)) := hbase

/-- `ρ^{-n} = (ρ^n)⁻¹` for `ρ ≥ 0`. -/
private lemma rpow_neg_natCast_eq_inv {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    ρ ^ (-(n : ℝ)) = (ρ ^ n)⁻¹ := by
  rw [Real.rpow_neg hρ, Real.rpow_natCast]

/-- For `ρ ≥ 1` and `|c| ≤ ρ`, `|(1 + 2c)/ρ²| ≤ 3/ρ`. -/
private lemma abs_one_add_two_mul_div_sq_le_three {ρ c : ℝ} (hρ : 1 ≤ ρ) (hc : |c| ≤ ρ) :
    |(1 + 2 * c) / ρ ^ 2| ≤ 3 / ρ := by
  have hρpos : 0 < ρ := by linarith
  have hnum : |1 + 2 * c| ≤ 1 + 2 * ρ := by
    calc |1 + 2 * c| ≤ |(1 : ℝ)| + |2 * c| := abs_add_le _ _
      _ = 1 + 2 * |c| := by rw [abs_one, abs_mul]; norm_num
      _ ≤ 1 + 2 * ρ := by linarith
  rw [abs_div, abs_of_nonneg (sq_nonneg ρ), div_le_iff₀ (by positivity)]
  have h3 : 3 / ρ * ρ ^ 2 = 3 * ρ := by field_simp
  rw [h3]
  nlinarith

/-- Log of the norm after adding a unit vector. -/
private lemma log_euclidNorm_add_unit (x : Site d) (i : Fin d) (hρ : 0 < euclidNorm x)
    (ht : 0 < 1 + (1 + 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2) :
    Real.log (euclidNorm (x + unit i)) =
      Real.log (euclidNorm x) +
        (1 / 2) * Real.log (1 + (1 + 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2) := by
  set ρ := euclidNorm x with hρdef
  set k : ℝ := ((x i : ℤ) : ℝ) with hkdef
  set tp : ℝ := (1 + 2 * k) / ρ ^ 2 with htpdef
  have hρne : ρ ≠ 0 := hρ.ne'
  have hfac : euclidNorm (x + unit i) ^ 2 = ρ ^ 2 * (1 + tp) := by
    rw [euclidNorm_add_unit_sq, hρdef, ← hkdef, htpdef]
    field_simp
    ring
  have hρp_eq : euclidNorm (x + unit i) = ρ * Real.sqrt (1 + tp) := by
    calc euclidNorm (x + unit i) = Real.sqrt (euclidNorm (x + unit i) ^ 2) :=
          (Real.sqrt_sq (euclidNorm_nonneg _)).symm
      _ = Real.sqrt (ρ ^ 2 * (1 + tp)) := by rw [hfac]
      _ = Real.sqrt (ρ ^ 2) * Real.sqrt (1 + tp) := Real.sqrt_mul (sq_nonneg ρ) _
      _ = ρ * Real.sqrt (1 + tp) := by rw [Real.sqrt_sq hρ.le]
  rw [hρp_eq, Real.log_mul hρne (Real.sqrt_pos_of_pos ht).ne']
  rw [Real.log_sqrt ht.le]
  ring

/-- Log of the norm after subtracting a unit vector. -/
private lemma log_euclidNorm_sub_unit (x : Site d) (i : Fin d) (hρ : 0 < euclidNorm x)
    (ht : 0 < 1 + (1 - 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2) :
    Real.log (euclidNorm (x - unit i)) =
      Real.log (euclidNorm x) +
        (1 / 2) * Real.log (1 + (1 - 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2) := by
  set ρ := euclidNorm x with hρdef
  set k : ℝ := ((x i : ℤ) : ℝ) with hkdef
  set tm : ℝ := (1 - 2 * k) / ρ ^ 2 with htmdef
  have hρne : ρ ≠ 0 := hρ.ne'
  have hfac : euclidNorm (x - unit i) ^ 2 = ρ ^ 2 * (1 + tm) := by
    rw [euclidNorm_sub_unit_sq, hρdef, ← hkdef, htmdef]
    field_simp
    ring
  have hρm_eq : euclidNorm (x - unit i) = ρ * Real.sqrt (1 + tm) := by
    calc euclidNorm (x - unit i) = Real.sqrt (euclidNorm (x - unit i) ^ 2) :=
          (Real.sqrt_sq (euclidNorm_nonneg _)).symm
      _ = Real.sqrt (ρ ^ 2 * (1 + tm)) := by rw [hfac]
      _ = Real.sqrt (ρ ^ 2) * Real.sqrt (1 + tm) := Real.sqrt_mul (sq_nonneg ρ) _
      _ = ρ * Real.sqrt (1 + tm) := by rw [Real.sqrt_sq hρ.le]
  rw [hρm_eq, Real.log_mul hρne (Real.sqrt_pos_of_pos ht).ne']
  rw [Real.log_sqrt ht.le]
  ring

/-- `ρ^{2-d}/ρ² = ρ^{-d}` for `ρ > 0`. -/
private lemma rpow_two_sub_natCast_div_sq {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    ρ ^ (2 - (d : ℝ)) / ρ ^ 2 = ρ ^ (-(d : ℝ)) := by
  rw [div_eq_iff (pow_ne_zero 2 hρ.ne'), ← Real.rpow_two,
    ← Real.rpow_add hρ (-(d : ℝ)) (2 : ℝ)]
  congr 1
  ring

/-- The power law `|x + e_i|^{2-d} = |x|^{2-d} (1 + t_+)^{(2-d)/2}`. -/
private lemma rpow_euclidNorm_add_unit (x : Site d) (i : Fin d) (hρ : 0 < euclidNorm x)
    (hpos : 0 < 1 + (1 + 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2) :
    euclidNorm (x + unit i) ^ (2 - (d : ℝ)) =
      euclidNorm x ^ (2 - (d : ℝ)) *
        (1 + (1 + 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2) ^ ((2 - (d : ℝ)) / 2) := by
  set ρ := euclidNorm x with hρdef
  set k : ℝ := ((x i : ℤ) : ℝ) with hkdef
  set tp : ℝ := (1 + 2 * k) / ρ ^ 2 with htpdef
  set β : ℝ := 2 - (d : ℝ) with hβdef
  have hfac : euclidNorm (x + unit i) ^ 2 = ρ ^ 2 * (1 + tp) := by
    rw [euclidNorm_add_unit_sq, hρdef, ← hkdef, htpdef]; field_simp; ring
  have hp : 0 ≤ euclidNorm (x + unit i) := euclidNorm_nonneg _
  have h1tp : 0 ≤ 1 + tp := hpos.le
  have hnat : euclidNorm (x + unit i) ^ 2 = euclidNorm (x + unit i) ^ (((2 : ℕ) : ℝ)) :=
    (Real.rpow_natCast _ 2).symm
  have hnatρ : ρ ^ 2 = ρ ^ (((2 : ℕ) : ℝ)) := (Real.rpow_natCast ρ 2).symm
  calc euclidNorm (x + unit i) ^ β
      = (euclidNorm (x + unit i) ^ 2) ^ (β / 2) := by
        rw [hnat, ← Real.rpow_mul hp (((2 : ℕ) : ℝ)) (β / 2),
          show (((2 : ℕ) : ℝ)) * (β / 2) = β by ring]
    _ = (ρ ^ 2 * (1 + tp)) ^ (β / 2) := by rw [hfac]
    _ = (ρ ^ 2) ^ (β / 2) * (1 + tp) ^ (β / 2) := Real.mul_rpow (sq_nonneg ρ) h1tp
    _ = ρ ^ β * (1 + tp) ^ (β / 2) := by
        rw [hnatρ, ← Real.rpow_mul hρ.le (((2 : ℕ) : ℝ)) (β / 2),
          show (((2 : ℕ) : ℝ)) * (β / 2) = β by ring]

/-- The power law `|x - e_i|^{2-d} = |x|^{2-d} (1 + t_-)^{(2-d)/2}`. -/
private lemma rpow_euclidNorm_sub_unit (x : Site d) (i : Fin d) (hρ : 0 < euclidNorm x)
    (hpos : 0 < 1 + (1 - 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2) :
    euclidNorm (x - unit i) ^ (2 - (d : ℝ)) =
      euclidNorm x ^ (2 - (d : ℝ)) *
        (1 + (1 - 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2) ^ ((2 - (d : ℝ)) / 2) := by
  set ρ := euclidNorm x with hρdef
  set k : ℝ := ((x i : ℤ) : ℝ) with hkdef
  set tm : ℝ := (1 - 2 * k) / ρ ^ 2 with htmdef
  set β : ℝ := 2 - (d : ℝ) with hβdef
  have hfac : euclidNorm (x - unit i) ^ 2 = ρ ^ 2 * (1 + tm) := by
    rw [euclidNorm_sub_unit_sq, hρdef, ← hkdef, htmdef]; field_simp; ring
  have hp : 0 ≤ euclidNorm (x - unit i) := euclidNorm_nonneg _
  have h1tm : 0 ≤ 1 + tm := hpos.le
  have hnat : euclidNorm (x - unit i) ^ 2 = euclidNorm (x - unit i) ^ (((2 : ℕ) : ℝ)) :=
    (Real.rpow_natCast _ 2).symm
  have hnatρ : ρ ^ 2 = ρ ^ (((2 : ℕ) : ℝ)) := (Real.rpow_natCast ρ 2).symm
  calc euclidNorm (x - unit i) ^ β
      = (euclidNorm (x - unit i) ^ 2) ^ (β / 2) := by
        rw [hnat, ← Real.rpow_mul hp (((2 : ℕ) : ℝ)) (β / 2),
          show (((2 : ℕ) : ℝ)) * (β / 2) = β by ring]
    _ = (ρ ^ 2 * (1 + tm)) ^ (β / 2) := by rw [hfac]
    _ = (ρ ^ 2) ^ (β / 2) * (1 + tm) ^ (β / 2) := Real.mul_rpow (sq_nonneg ρ) h1tm
    _ = ρ ^ β * (1 + tm) ^ (β / 2) := by
        rw [hnatρ, ← Real.rpow_mul hρ.le (((2 : ℕ) : ℝ)) (β / 2),
          show (((2 : ℕ) : ℝ)) * (β / 2) = β by ring]

/-- If `|t| ≤ a` and `0 ≤ a`, then `t ^ 2 ≤ a ^ 2`. -/
private lemma sq_le_sq_of_abs_le {t a : ℝ} (ha : 0 ≤ a) (h : |t| ≤ a) :
    t ^ 2 ≤ a ^ 2 :=
  sq_le_sq.mpr (by rwa [abs_of_nonneg ha])

/-- If `|t| ≤ 3 / ρ` and `0 < ρ`, then `t ^ 2 ≤ 9 / ρ ^ 2`. -/
private lemma sq_le_nine_div_sq_of_abs_le_three_div {t ρ : ℝ} (hρ : 0 < ρ)
    (h : |t| ≤ 3 / ρ) : t ^ 2 ≤ 9 / ρ ^ 2 := by
  have h' := sq_le_sq_of_abs_le (show (0 : ℝ) ≤ 3 / ρ by positivity) h
  rw [div_pow] at h'
  norm_num at h'
  exact h'

/-- If `|t| ≤ 3 / ρ` and `6 ≤ ρ`, then `|t| ≤ 1 / 2`. -/
private lemma abs_le_half_of_abs_le_three_div {t ρ : ℝ} (hρ : 6 ≤ ρ)
    (h : |t| ≤ 3 / ρ) : |t| ≤ 1 / 2 := by
  have hpos : 0 < ρ := by linarith only [hρ]
  have h3 : 3 / ρ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hρ]
  linarith only [h, h3]

/-- If `|t| ≤ 1 / 2`, then `0 < 1 + t`. -/
private lemma one_add_pos_of_abs_le_half {t : ℝ} (h : |t| ≤ 1 / 2) : 0 < 1 + t := by
  have h' := (abs_le.mp h).1
  linarith only [h']

/-- `|x| - 1 ≤ |x + e_i|` when `|x| ≥ 1`. -/
private lemma euclidNorm_sub_one_le_add_unit (x : Site d) (i : Fin d)
    (hρ : 1 ≤ euclidNorm x) : euclidNorm x - 1 ≤ euclidNorm (x + unit i) := by
  have hk : |((x i : ℤ) : ℝ)| ≤ euclidNorm x := abs_coord_le_euclidNorm x i
  have hx : -euclidNorm x ≤ ((x i : ℤ) : ℝ) := (abs_le.mp hk).1
  have hsq : (euclidNorm x - 1) ^ 2 ≤ euclidNorm (x + unit i) ^ 2 := by
    rw [euclidNorm_add_unit_sq]
    nlinarith only [hx]
  have hle := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (by linarith only [hρ]), abs_of_nonneg (euclidNorm_nonneg _)] at hle

/-- `|x| - 1 ≤ |x - e_i|` when `|x| ≥ 1`. -/
private lemma euclidNorm_sub_one_le_sub_unit (x : Site d) (i : Fin d)
    (hρ : 1 ≤ euclidNorm x) : euclidNorm x - 1 ≤ euclidNorm (x - unit i) := by
  have hk : |((x i : ℤ) : ℝ)| ≤ euclidNorm x := abs_coord_le_euclidNorm x i
  have hx : ((x i : ℤ) : ℝ) ≤ euclidNorm x := (abs_le.mp hk).2
  have hsq : (euclidNorm x - 1) ^ 2 ≤ euclidNorm (x - unit i) ^ 2 := by
    rw [euclidNorm_sub_unit_sq]
    nlinarith only [hx]
  have hle := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (by linarith only [hρ]), abs_of_nonneg (euclidNorm_nonneg _)] at hle

/-- Planar coordinate bound for the central difference error. -/
private lemma coord_bound_two {b : Site 2 → ℝ} {κ Cb Rb : ℝ}
    (hb : ∀ x, Rb ≤ euclidNorm x →
      |b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤ Cb * euclidNorm x ^ (-2 : ℝ))
    (x : Site 2) (i : Fin 2) (hR : Rb + 1 ≤ euclidNorm x) (hρ6 : 6 ≤ euclidNorm x) :
    |(b (x + unit i) - b (x - unit i)) / 2
        - (2 / Real.pi / euclidNorm x ^ 2) * ((x i : ℤ) : ℝ)|
      ≤ (18 / Real.pi + 4 * max Cb 0) * euclidNorm x ^ (-2 : ℝ) := by
  set ρ := euclidNorm x with hρdef
  set k : ℝ := ((x i : ℤ) : ℝ) with hkdef
  set tp : ℝ := (1 + 2 * k) / ρ ^ 2 with htpdef
  set tm : ℝ := (1 - 2 * k) / ρ ^ 2 with htmdef
  set ρp : ℝ := euclidNorm (x + unit i) with hρpdef
  set ρm : ℝ := euclidNorm (x - unit i) with hρmdef
  set ep : ℝ := b (x + unit i)
    - (2 / Real.pi * Real.log (euclidNorm (x + unit i)) + κ) with hepdef
  set em : ℝ := b (x - unit i)
    - (2 / Real.pi * Real.log (euclidNorm (x - unit i)) + κ) with hemdef
  set wp : ℝ := Real.log (1 + tp) - tp with hwpdef
  set wm : ℝ := Real.log (1 + tm) - tm with hwmdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith only [hρ6]
  have hρ1 : 1 ≤ ρ := by rw [hρdef]; linarith only [hρ6]
  have hρ6' : 6 ≤ ρ := by rw [hρdef]; exact hρ6
  have hk : |k| ≤ ρ := by rw [hkdef, hρdef]; exact abs_coord_le_euclidNorm x i
  have htp3 : |tp| ≤ 3 / ρ := by
    rw [htpdef]; exact abs_one_add_two_mul_div_sq_le_three hρ1 hk
  have htm3 : |tm| ≤ 3 / ρ := by
    rw [htmdef]
    have h : |(1 - 2 * k) / ρ ^ 2| = |(1 + 2 * (-k)) / ρ ^ 2| := by ring_nf
    rw [h]
    exact abs_one_add_two_mul_div_sq_le_three hρ1 (by rw [abs_neg]; exact hk)
  have htp2 : tp ^ 2 ≤ 9 / ρ ^ 2 := sq_le_nine_div_sq_of_abs_le_three_div hρpos htp3
  have htm2 : tm ^ 2 ≤ 9 / ρ ^ 2 := sq_le_nine_div_sq_of_abs_le_three_div hρpos htm3
  have htp_half : |tp| ≤ 1 / 2 := abs_le_half_of_abs_le_three_div hρ6' htp3
  have htm_half : |tm| ≤ 1 / 2 := abs_le_half_of_abs_le_three_div hρ6' htm3
  have h1tp : 0 < 1 + tp := one_add_pos_of_abs_le_half htp_half
  have h1tm : 0 < 1 + tm := one_add_pos_of_abs_le_half htm_half
  have hρp_sq : euclidNorm (x + unit i) ^ 2 = ρ ^ 2 * (1 + tp) := by
    rw [euclidNorm_add_unit_sq, hρdef, ← hkdef, htpdef]; field_simp; ring
  have hρm_sq : euclidNorm (x - unit i) ^ 2 = ρ ^ 2 * (1 + tm) := by
    rw [euclidNorm_sub_unit_sq, hρdef, ← hkdef, htmdef]; field_simp; ring
  have hρp_ge : ρ - 1 ≤ ρp := by
    rw [hρpdef]
    exact euclidNorm_sub_one_le_add_unit x i (by rw [← hρdef]; exact hρ1)
  have hρm_ge : ρ - 1 ≤ ρm := by
    rw [hρmdef]
    exact euclidNorm_sub_one_le_sub_unit x i (by rw [← hρdef]; exact hρ1)
  have hρp_half : ρ / 2 ≤ ρp := by linarith only [hρp_ge, hρdef, hρ6]
  have hρm_half : ρ / 2 ≤ ρm := by linarith only [hρm_ge, hρdef, hρ6]
  have hRb_p : Rb ≤ ρp := by linarith only [hR, hρdef, hρp_ge]
  have hRb_m : Rb ≤ ρm := by linarith only [hR, hρdef, hρm_ge]
  have hlogp : Real.log ρp = Real.log ρ + (1 / 2) * Real.log (1 + tp) := by
    rw [hρpdef]
    have ht : 0 < 1 + (1 + 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2 := by
      rw [← hρdef, ← hkdef, ← htpdef]; exact h1tp
    rw [hρdef, htpdef, hkdef]
    exact log_euclidNorm_add_unit x i hρpos ht
  have hlogm : Real.log ρm = Real.log ρ + (1 / 2) * Real.log (1 + tm) := by
    rw [hρmdef]
    have ht : 0 < 1 + (1 - 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2 := by
      rw [← hρdef, ← hkdef, ← htmdef]; exact h1tm
    rw [hρdef, htmdef, hkdef]
    exact log_euclidNorm_sub_unit x i hρpos ht
  have hep : |ep| ≤ Cb * ρp ^ (-2 : ℝ) := by rw [hepdef, hρpdef]; exact hb _ hRb_p
  have hem : |em| ≤ Cb * ρm ^ (-2 : ℝ) := by rw [hemdef, hρmdef]; exact hb _ hRb_m
  have hep4 : |ep| ≤ 4 * max Cb 0 * ρ ^ (-2 : ℝ) := by
    have h1 : Cb * ρp ^ (-2 : ℝ) ≤ max Cb 0 * ρp ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by linarith [hρp_half, hρpos] : (0 : ℝ) ≤ ρp) _)
    have h2 : ρp ^ (-2 : ℝ) ≤ 4 * ρ ^ (-2 : ℝ) := by
      have := rpow_neg_le_of_half_le hρpos hρp_half 2
      norm_num at this ⊢
      exact this
    calc |ep| ≤ Cb * ρp ^ (-2 : ℝ) := hep
      _ ≤ max Cb 0 * ρp ^ (-2 : ℝ) := h1
      _ ≤ max Cb 0 * (4 * ρ ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = 4 * max Cb 0 * ρ ^ (-2 : ℝ) := by ring
  have hem4 : |em| ≤ 4 * max Cb 0 * ρ ^ (-2 : ℝ) := by
    have h1 : Cb * ρm ^ (-2 : ℝ) ≤ max Cb 0 * ρm ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by linarith [hρm_half, hρpos] : (0 : ℝ) ≤ ρm) _)
    have h2 : ρm ^ (-2 : ℝ) ≤ 4 * ρ ^ (-2 : ℝ) := by
      have := rpow_neg_le_of_half_le hρpos hρm_half 2
      norm_num at this ⊢
      exact this
    calc |em| ≤ Cb * ρm ^ (-2 : ℝ) := hem
      _ ≤ max Cb 0 * ρm ^ (-2 : ℝ) := h1
      _ ≤ max Cb 0 * (4 * ρ ^ (-2 : ℝ)) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = 4 * max Cb 0 * ρ ^ (-2 : ℝ) := by ring
  have hwp : |wp| ≤ 2 * tp ^ 2 := by rw [hwpdef]; exact abs_log_one_add_sub_le htp_half
  have hwm : |wm| ≤ 2 * tm ^ 2 := by rw [hwmdef]; exact abs_log_one_add_sub_le htm_half
  have hcoord_eq : (b (x + unit i) - b (x - unit i)) / 2 - (2 / Real.pi / ρ ^ 2) * k
      = (2 / Real.pi) * ((1 / 4) * (wp - wm)) + (ep - em) / 2 := by
    have hbpe : b (x + unit i) = 2 / Real.pi * Real.log ρp + κ + ep := by rw [hepdef]; ring
    have hbme : b (x - unit i) = 2 / Real.pi * Real.log ρm + κ + em := by rw [hemdef]; ring
    have hwpwm : (1 / 4) * (wp - wm)
        = (1 / 4) * (Real.log (1 + tp) - Real.log (1 + tm)) - k / ρ ^ 2 := by
      rw [hwpdef, hwmdef]
      have htpk : tp - tm = 4 * k / ρ ^ 2 := by rw [htpdef, htmdef]; ring
      linear_combination (-(1 / 4)) * htpk
    rw [hbpe, hbme, hlogp, hlogm, hwpwm]
    ring
  have hmain : |(2 / Real.pi) * ((1 / 4) * (wp - wm)) + (ep - em) / 2|
      ≤ (18 / Real.pi + 4 * max Cb 0) * ρ ^ (-2 : ℝ) := by
    have hwp' : |wp| ≤ 2 * (9 / ρ ^ 2) := by linarith only [hwp, htp2]
    have hwm' : |wm| ≤ 2 * (9 / ρ ^ 2) := by linarith only [hwm, htm2]
    have hsum : |wp - wm| ≤ 2 * (9 / ρ ^ 2) + 2 * (9 / ρ ^ 2) := by
      calc |wp - wm| ≤ |wp| + |wm| := abs_sub _ _
        _ ≤ 2 * (9 / ρ ^ 2) + 2 * (9 / ρ ^ 2) := add_le_add hwp' hwm'
    have h1 : |(2 / Real.pi) * ((1 / 4) * (wp - wm))| ≤ 18 / Real.pi * ρ ^ (-2 : ℝ) := by
      have hc : |(2 / Real.pi) * ((1 / 4) * (wp - wm))|
          = (2 / Real.pi) * ((1 / 4) * |wp - wm|) := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi),
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      rw [hc]
      have hb : (2 / Real.pi) * ((1 / 4) * (2 * (9 / ρ ^ 2) + 2 * (9 / ρ ^ 2)))
          = 18 / Real.pi / ρ ^ 2 := by ring
      calc (2 / Real.pi) * ((1 / 4) * |wp - wm|)
          ≤ (2 / Real.pi) * ((1 / 4) * (2 * (9 / ρ ^ 2) + 2 * (9 / ρ ^ 2))) := by
            gcongr
        _ = 18 / Real.pi / ρ ^ 2 := hb
        _ = 18 / Real.pi * ρ ^ (-2 : ℝ) := by
            rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
              rpow_neg_natCast_eq_inv hρpos.le 2]
            ring
    have h2 : |(ep - em) / 2| ≤ 4 * max Cb 0 * ρ ^ (-2 : ℝ) := by
      have hsplit : (ep - em) / 2 = (1 / 2) * ep - (1 / 2) * em := by ring
      rw [hsplit]
      calc |(1 / 2) * ep - (1 / 2) * em| ≤ |(1 / 2) * ep| + |(1 / 2) * em| := abs_sub _ _
        _ = (1 / 2) * |ep| + (1 / 2) * |em| := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        _ ≤ (1 / 2) * (4 * max Cb 0 * ρ ^ (-2 : ℝ))
            + (1 / 2) * (4 * max Cb 0 * ρ ^ (-2 : ℝ)) := by
            gcongr
        _ = 4 * max Cb 0 * ρ ^ (-2 : ℝ) := by ring
    calc |(2 / Real.pi) * ((1 / 4) * (wp - wm)) + (ep - em) / 2|
        ≤ |(2 / Real.pi) * ((1 / 4) * (wp - wm))| + |(ep - em) / 2| := abs_add_le _ _
      _ ≤ 18 / Real.pi * ρ ^ (-2 : ℝ) + 4 * max Cb 0 * ρ ^ (-2 : ℝ) := add_le_add h1 h2
      _ = (18 / Real.pi + 4 * max Cb 0) * ρ ^ (-2 : ℝ) := by ring
  rw [hcoord_eq]
  exact hmain

/-- Coordinate bound for the central difference error in dimensions `d ≥ 3`. -/
private lemma coord_bound_ge_three {G : Site d → ℝ} {CG RG : ℝ} (hd : 3 ≤ d)
    (hG : ∀ x, RG ≤ euclidNorm x →
      |G x - 2 / (((d : ℝ) - 2) * unitBallVolume d) * euclidNorm x ^ (2 - (d : ℝ))| ≤
        CG * euclidNorm x ^ (-(d : ℝ)))
    (x : Site d) (i : Fin d) (hR : RG + 1 ≤ euclidNorm x) (hρ6 : 6 ≤ euclidNorm x) :
    |(G (x - unit i) - G (x + unit i)) / 2
        - (2 / unitBallVolume d) * ((x i : ℤ) : ℝ) * euclidNorm x ^ (-(d : ℝ))|
      ≤ (9 * |2 / (((d : ℝ) - 2) * unitBallVolume d)|
            * (|(2 - (d : ℝ)) / 2| * |(2 - (d : ℝ)) / 2 - 1| * 2 ^ |(2 - (d : ℝ)) / 2 - 2|)
          + 2 ^ d * max CG 0) * euclidNorm x ^ (-(d : ℝ)) := by
  set ρ := euclidNorm x with hρdef
  set k : ℝ := ((x i : ℤ) : ℝ) with hkdef
  set tp : ℝ := (1 + 2 * k) / ρ ^ 2 with htpdef
  set tm : ℝ := (1 - 2 * k) / ρ ^ 2 with htmdef
  set β : ℝ := 2 - (d : ℝ) with hβdef
  set α : ℝ := (2 - (d : ℝ)) / 2 with hαdef
  set c : ℝ := 2 / (((d : ℝ) - 2) * unitBallVolume d) with hcdef
  set K : ℝ := |(2 - (d : ℝ)) / 2| * |(2 - (d : ℝ)) / 2 - 1| * 2 ^ |(2 - (d : ℝ)) / 2 - 2|
    with hKdef
  set ρp : ℝ := euclidNorm (x + unit i) with hρpdef
  set ρm : ℝ := euclidNorm (x - unit i) with hρmdef
  set ep : ℝ := G (x + unit i) - c * ρp ^ β with hepdef
  set em : ℝ := G (x - unit i) - c * ρm ^ β with hemdef
  set up : ℝ := (1 + tp) ^ α - 1 - α * tp with hupdef
  set um : ℝ := (1 + tm) ^ α - 1 - α * tm with humdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith only [hρ6]
  have hρ1 : 1 ≤ ρ := by rw [hρdef]; linarith only [hρ6]
  have hρ6' : 6 ≤ ρ := by rw [hρdef]; exact hρ6
  have hk : |k| ≤ ρ := by rw [hkdef, hρdef]; exact abs_coord_le_euclidNorm x i
  have htp3 : |tp| ≤ 3 / ρ := by
    rw [htpdef]; exact abs_one_add_two_mul_div_sq_le_three hρ1 hk
  have htm3 : |tm| ≤ 3 / ρ := by
    rw [htmdef]
    have h : |(1 - 2 * k) / ρ ^ 2| = |(1 + 2 * (-k)) / ρ ^ 2| := by ring_nf
    rw [h]
    exact abs_one_add_two_mul_div_sq_le_three hρ1 (by rw [abs_neg]; exact hk)
  have htp2 : tp ^ 2 ≤ 9 / ρ ^ 2 := sq_le_nine_div_sq_of_abs_le_three_div hρpos htp3
  have htm2 : tm ^ 2 ≤ 9 / ρ ^ 2 := sq_le_nine_div_sq_of_abs_le_three_div hρpos htm3
  have htp_half : |tp| ≤ 1 / 2 := abs_le_half_of_abs_le_three_div hρ6' htp3
  have htm_half : |tm| ≤ 1 / 2 := abs_le_half_of_abs_le_three_div hρ6' htm3
  have h1tp : 0 < 1 + tp := one_add_pos_of_abs_le_half htp_half
  have h1tm : 0 < 1 + tm := one_add_pos_of_abs_le_half htm_half
  have hρp_ge : ρ - 1 ≤ ρp := by
    rw [hρpdef]
    exact euclidNorm_sub_one_le_add_unit x i (by rw [← hρdef]; exact hρ1)
  have hρm_ge : ρ - 1 ≤ ρm := by
    rw [hρmdef]
    exact euclidNorm_sub_one_le_sub_unit x i (by rw [← hρdef]; exact hρ1)
  have hρp_half : ρ / 2 ≤ ρp := by linarith only [hρp_ge, hρdef, hρ6]
  have hρm_half : ρ / 2 ≤ ρm := by linarith only [hρm_ge, hρdef, hρ6]
  have hRb_p : RG ≤ ρp := by linarith only [hR, hρdef, hρp_ge]
  have hRb_m : RG ≤ ρm := by linarith only [hR, hρdef, hρm_ge]
  have hρp_pow : ρp ^ β = ρ ^ β * (1 + tp) ^ α := by
    rw [hβdef, hαdef, hρpdef]
    have ht : 0 < 1 + (1 + 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2 := by
      rw [← hρdef, ← hkdef, ← htpdef]; exact h1tp
    have h := rpow_euclidNorm_add_unit x i hρpos ht
    rw [← hρdef, ← hkdef, ← htpdef] at h
    exact h
  have hρm_pow : ρm ^ β = ρ ^ β * (1 + tm) ^ α := by
    rw [hβdef, hαdef, hρmdef]
    have ht : 0 < 1 + (1 - 2 * ((x i : ℤ) : ℝ)) / euclidNorm x ^ 2 := by
      rw [← hρdef, ← hkdef, ← htmdef]; exact h1tm
    have h := rpow_euclidNorm_sub_unit x i hρpos ht
    rw [← hρdef, ← hkdef, ← htmdef] at h
    exact h
  have hep : |ep| ≤ CG * ρp ^ (-(d : ℝ)) := by
    rw [hepdef, hρpdef]
    exact hG (x + unit i) (by rw [← hρpdef]; exact hRb_p)
  have hem : |em| ≤ CG * ρm ^ (-(d : ℝ)) := by
    rw [hemdef, hρmdef]
    exact hG (x - unit i) (by rw [← hρmdef]; exact hRb_m)
  have hep_d : |ep| ≤ 2 ^ d * max CG 0 * ρ ^ (-(d : ℝ)) := by
    have h1 : CG * ρp ^ (-(d : ℝ)) ≤ max CG 0 * ρp ^ (-(d : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by linarith [hρp_half, hρpos] : (0 : ℝ) ≤ ρp) _)
    have h2 : ρp ^ (-(d : ℝ)) ≤ 2 ^ d * ρ ^ (-(d : ℝ)) :=
      rpow_neg_le_of_half_le hρpos hρp_half d
    calc |ep| ≤ CG * ρp ^ (-(d : ℝ)) := hep
      _ ≤ max CG 0 * ρp ^ (-(d : ℝ)) := h1
      _ ≤ max CG 0 * (2 ^ d * ρ ^ (-(d : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = 2 ^ d * max CG 0 * ρ ^ (-(d : ℝ)) := by ring
  have hem_d : |em| ≤ 2 ^ d * max CG 0 * ρ ^ (-(d : ℝ)) := by
    have h1 : CG * ρm ^ (-(d : ℝ)) ≤ max CG 0 * ρm ^ (-(d : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (by linarith [hρm_half, hρpos] : (0 : ℝ) ≤ ρm) _)
    have h2 : ρm ^ (-(d : ℝ)) ≤ 2 ^ d * ρ ^ (-(d : ℝ)) :=
      rpow_neg_le_of_half_le hρpos hρm_half d
    calc |em| ≤ CG * ρm ^ (-(d : ℝ)) := hem
      _ ≤ max CG 0 * ρm ^ (-(d : ℝ)) := h1
      _ ≤ max CG 0 * (2 ^ d * ρ ^ (-(d : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = 2 ^ d * max CG 0 * ρ ^ (-(d : ℝ)) := by ring
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hup : |up| ≤ K * tp ^ 2 := by
    simpa only [hupdef, hαdef, hKdef] using abs_one_add_rpow_sub_le ((2 - (d : ℝ)) / 2) htp_half
  have hum : |um| ≤ K * tm ^ 2 := by
    simpa only [humdef, hαdef, hKdef] using abs_one_add_rpow_sub_le ((2 - (d : ℝ)) / 2) htm_half
  have hup9 : |up| ≤ K * (9 / ρ ^ 2) :=
    le_trans hup (mul_le_mul_of_nonneg_left htp2 hKnn)
  have hum9 : |um| ≤ K * (9 / ρ ^ 2) :=
    le_trans hum (mul_le_mul_of_nonneg_left htm2 hKnn)
  have htmk : tm - tp = -4 * k / ρ ^ 2 := by rw [htpdef, htmdef]; ring
  have hβd : ρ ^ β / ρ ^ 2 = ρ ^ (-(d : ℝ)) := by
    rw [hβdef]; exact rpow_two_sub_natCast_div_sq hρpos d
  have hαc : -2 * c * α = 2 / unitBallVolume d := by
    rw [hcdef, hαdef]
    have h1 : (d : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have h2 : unitBallVolume d ≠ 0 := (unitBallVolume_pos d).ne'
    field_simp
    ring
  have hdiff_eq : (G (x - unit i) - G (x + unit i)) / 2
        - (2 / unitBallVolume d) * k * ρ ^ (-(d : ℝ))
      = c * (ρ ^ β / 2) * (um - up) + (em - ep) / 2 := by
    have hbpe : G (x + unit i) = c * ρp ^ β + ep := by rw [hepdef]; ring
    have hbme : G (x - unit i) = c * ρm ^ β + em := by rw [hemdef]; ring
    have hαtm : c * ρ ^ β / 2 * α * (tm - tp)
        = (2 / unitBallVolume d) * k * ρ ^ (-(d : ℝ)) := by
      rw [htmk]
      have h1 : c * ρ ^ β / 2 * α * (-4 * k / ρ ^ 2)
          = (-2 * c * α) * k * (ρ ^ β / ρ ^ 2) := by
        ring
      rw [h1, hβd, hαc]
    calc (G (x - unit i) - G (x + unit i)) / 2 - (2 / unitBallVolume d) * k * ρ ^ (-(d : ℝ))
        = c * (ρm ^ β - ρp ^ β) / 2 + (em - ep) / 2
            - (2 / unitBallVolume d) * k * ρ ^ (-(d : ℝ)) := by rw [hbme, hbpe]; ring
      _ = c * ρ ^ β / 2 * ((1 + tm) ^ α - (1 + tp) ^ α) + (em - ep) / 2
            - (2 / unitBallVolume d) * k * ρ ^ (-(d : ℝ)) := by rw [hρm_pow, hρp_pow]; ring
      _ = c * ρ ^ β / 2 * ((um - up) + α * (tm - tp)) + (em - ep) / 2
            - (2 / unitBallVolume d) * k * ρ ^ (-(d : ℝ)) := by
            rw [show (1 + tm) ^ α - (1 + tp) ^ α = (um - up) + α * (tm - tp) by
              rw [hupdef, humdef]; ring]
      _ = c * ρ ^ β / 2 * (um - up) + c * ρ ^ β / 2 * α * (tm - tp) + (em - ep) / 2
            - (2 / unitBallVolume d) * k * ρ ^ (-(d : ℝ)) := by ring
      _ = c * (ρ ^ β / 2) * (um - up) + (em - ep) / 2 := by rw [hαtm]; ring
  rw [hdiff_eq]
  have hfirst : |c * (ρ ^ β / 2) * (um - up)| ≤ 9 * |c| * K * ρ ^ (-(d : ℝ)) := by
    have hcabs : |c * (ρ ^ β / 2) * (um - up)| = |c| * (ρ ^ β / 2) * |um - up| := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (div_nonneg (Real.rpow_nonneg hρpos.le _) (by norm_num : (0 : ℝ) ≤ 2))]
    rw [hcabs]
    have hupum : |um - up| ≤ K * (9 / ρ ^ 2) + K * (9 / ρ ^ 2) := by
      calc |um - up| ≤ |um| + |up| := abs_sub _ _
        _ ≤ K * (9 / ρ ^ 2) + K * (9 / ρ ^ 2) := add_le_add hum9 hup9
    have hnn : 0 ≤ |c| * (ρ ^ β / 2) :=
      mul_nonneg (abs_nonneg _)
        (div_nonneg (Real.rpow_nonneg hρpos.le _) (by norm_num : (0 : ℝ) ≤ 2))
    have hstep : |c| * (ρ ^ β / 2) * |um - up|
        ≤ |c| * (ρ ^ β / 2) * (K * (9 / ρ ^ 2) + K * (9 / ρ ^ 2)) :=
      mul_le_mul_of_nonneg_left hupum hnn
    have hsimp : |c| * (ρ ^ β / 2) * (K * (9 / ρ ^ 2) + K * (9 / ρ ^ 2))
        = 9 * |c| * K * ρ ^ (-(d : ℝ)) := by
      have h1 : |c| * (ρ ^ β / 2) * (K * (9 / ρ ^ 2) + K * (9 / ρ ^ 2))
          = 9 * |c| * K * (ρ ^ β / ρ ^ 2) := by ring
      rw [h1, hβd]
    linarith [hstep, hsimp.le, hsimp.ge]
  have hsecond : |(em - ep) / 2| ≤ 2 ^ d * max CG 0 * ρ ^ (-(d : ℝ)) := by
    have hsplit : (em - ep) / 2 = (1 / 2) * em - (1 / 2) * ep := by ring
    rw [hsplit]
    calc |(1 / 2) * em - (1 / 2) * ep| ≤ |(1 / 2) * em| + |(1 / 2) * ep| := abs_sub _ _
      _ = (1 / 2) * |em| + (1 / 2) * |ep| := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      _ ≤ (1 / 2) * (2 ^ d * max CG 0 * ρ ^ (-(d : ℝ)))
            + (1 / 2) * (2 ^ d * max CG 0 * ρ ^ (-(d : ℝ))) := by gcongr
      _ = 2 ^ d * max CG 0 * ρ ^ (-(d : ℝ)) := by ring
  calc |c * (ρ ^ β / 2) * (um - up) + (em - ep) / 2|
      ≤ |c * (ρ ^ β / 2) * (um - up)| + |(em - ep) / 2| := abs_add_le _ _
    _ ≤ 9 * |c| * K * ρ ^ (-(d : ℝ)) + 2 ^ d * max CG 0 * ρ ^ (-(d : ℝ)) :=
        add_le_add hfirst hsecond
    _ = (9 * |c| * K + 2 ^ d * max CG 0) * ρ ^ (-(d : ℝ)) := by ring

/-- The planar case: if `|b(x) - ((2/π) log|x| + κ)| ≤ C_b |x|^{-2}` for `|x| ≥ R_b`, then
`|Db(x) - (2/π) x/|x|²| ≤ C |x|^{-2}` for all large `|x|`. -/
theorem exists_norm_centralDiff_sub_le_two {b : Site 2 → ℝ} {κ Cb Rb : ℝ}
    (hb : ∀ x, Rb ≤ euclidNorm x →
      |b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤ Cb * euclidNorm x ^ (-2 : ℝ)) :
    ∃ C R : ℝ, ∀ x : Site 2, R ≤ euclidNorm x →
      ‖centralDiff b x - (2 / Real.pi / euclidNorm x ^ 2) • toSpace x‖ ≤
        C * euclidNorm x ^ (-2 : ℝ) := by

  refine ⟨36 / Real.pi + 8 * max Cb 0, max Rb 0 + 6, ?_⟩
  intro x hx
  have hρ6 : 6 ≤ euclidNorm x := by
    have := hx
    linarith [le_max_right Rb 0]
  have hR : Rb + 1 ≤ euclidNorm x := by
    have := le_max_left Rb 0
    linarith
  have hcoord : ∀ i : Fin 2,
      |(centralDiff b x - (2 / Real.pi / euclidNorm x ^ 2) • toSpace x) i|
        ≤ (18 / Real.pi + 4 * max Cb 0) * euclidNorm x ^ (-2 : ℝ) := by
    intro i
    have hc := coord_bound_two hb x i hR hρ6
    simpa only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, centralDiff, PiLp.toLp_apply,
        toSpace_apply]
      using hc
  calc ‖centralDiff b x - (2 / Real.pi / euclidNorm x ^ 2) • toSpace x‖
      ≤ ∑ i : Fin 2, |(centralDiff b x - (2 / Real.pi / euclidNorm x ^ 2) • toSpace x) i| :=
        norm_le_sum_abs _
    _ ≤ ∑ _i : Fin 2, (18 / Real.pi + 4 * max Cb 0) * euclidNorm x ^ (-2 : ℝ) :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = 2 * ((18 / Real.pi + 4 * max Cb 0) * euclidNorm x ^ (-2 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ = (36 / Real.pi + 8 * max Cb 0) * euclidNorm x ^ (-2 : ℝ) := by ring

/-- The case `d ≥ 3`, with `b = -G`: if `|G(x) - c_d |x|^{2-d}| ≤ C_G |x|^{-d}` for `|x| ≥ R_G`,
where `c_d = 2/((d - 2) ω_d)`, then `|D(-G)(x) - (2/ω_d) x/|x|^d| ≤ C |x|^{-d}` for all large
`|x|`. -/
theorem exists_norm_centralDiff_sub_le {G : Site d → ℝ} {CG RG : ℝ} (hd : 3 ≤ d)
    (hG : ∀ x, RG ≤ euclidNorm x →
      |G x - 2 / (((d : ℝ) - 2) * unitBallVolume d) * euclidNorm x ^ (2 - (d : ℝ))| ≤
        CG * euclidNorm x ^ (-(d : ℝ))) :
    ∃ C R : ℝ, ∀ x : Site d, R ≤ euclidNorm x →
      ‖centralDiff (fun y => -G y) x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖ ≤
        C * euclidNorm x ^ (-(d : ℝ)) := by

  refine ⟨(d : ℝ) * (9 * |2 / (((d : ℝ) - 2) * unitBallVolume d)|
            * (|(2 - (d : ℝ)) / 2| * |(2 - (d : ℝ)) / 2 - 1| * 2 ^ |(2 - (d : ℝ)) / 2 - 2|)
          + 2 ^ d * max CG 0), max RG 0 + 6, ?_⟩
  intro x hx
  have hρ6 : 6 ≤ euclidNorm x := by
    have := hx
    linarith [le_max_right RG 0]
  have hR : RG + 1 ≤ euclidNorm x := by
    have := le_max_left RG 0
    linarith
  have hcoord : ∀ i : Fin d,
      |(centralDiff (fun y => -G y) x
          - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x) i|
        ≤ (9 * |2 / (((d : ℝ) - 2) * unitBallVolume d)|
            * (|(2 - (d : ℝ)) / 2| * |(2 - (d : ℝ)) / 2 - 1| * 2 ^ |(2 - (d : ℝ)) / 2 - 2|)
          + 2 ^ d * max CG 0) * euclidNorm x ^ (-(d : ℝ)) := by
    intro i
    have hc := coord_bound_ge_three hd hG x i hR hρ6
    have hcoeff : (2 / unitBallVolume d / euclidNorm x ^ d) * ((x i : ℤ) : ℝ)
        = (2 / unitBallVolume d) * ((x i : ℤ) : ℝ) * euclidNorm x ^ (-(d : ℝ)) := by
      rw [rpow_neg_natCast_eq_inv (euclidNorm_nonneg x) d]
      ring
    have hcoord_i : (centralDiff (fun y => -G y) x
        - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x) i
        = (G (x - unit i) - G (x + unit i)) / 2
            - (2 / unitBallVolume d) * ((x i : ℤ) : ℝ) * euclidNorm x ^ (-(d : ℝ)) := by
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, centralDiff, toSpace_apply]
      rw [hcoeff]
      ring
    rw [hcoord_i]
    exact hc
  calc ‖centralDiff (fun y => -G y) x - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x‖
      ≤ ∑ i : Fin d, |(centralDiff (fun y => -G y) x
          - (2 / unitBallVolume d / euclidNorm x ^ d) • toSpace x) i| := norm_le_sum_abs _
    _ ≤ ∑ _i : Fin d, (9 * |2 / (((d : ℝ) - 2) * unitBallVolume d)|
            * (|(2 - (d : ℝ)) / 2| * |(2 - (d : ℝ)) / 2 - 1| * 2 ^ |(2 - (d : ℝ)) / 2 - 2|)
          + 2 ^ d * max CG 0) * euclidNorm x ^ (-(d : ℝ)) :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * ((9 * |2 / (((d : ℝ) - 2) * unitBallVolume d)|
            * (|(2 - (d : ℝ)) / 2| * |(2 - (d : ℝ)) / 2 - 1| * 2 ^ |(2 - (d : ℝ)) / 2 - 2|)
          + 2 ^ d * max CG 0) * euclidNorm x ^ (-(d : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((d : ℝ) * (9 * |2 / (((d : ℝ) - 2) * unitBallVolume d)|
            * (|(2 - (d : ℝ)) / 2| * |(2 - (d : ℝ)) / 2 - 1| * 2 ^ |(2 - (d : ℝ)) / 2 - 2|)
          + 2 ^ d * max CG 0)) * euclidNorm x ^ (-(d : ℝ)) := by ring

end CERW.Support.LocalTime
