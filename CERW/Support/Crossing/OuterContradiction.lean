import CERW.Support.Main.ScaleLimits

/-!
# The outer crossing bound is eventually contradictory

In the outer bound a crossing of height `h = A W L`, with `W = N Q^{1/d}`, through at most
`C₁ N L` departure sites would force
`(h - 1)² ≤ C ((C₁NL)^γ L^γ + C₁NL λ_n L)`, where `γ = 2d/(2d-1)` and `λ_n` is `L²`
(`d = 2`) or `L` (`d ≥ 3`) (`eq:outer-contradiction`). The right side is `o(h²)` in every
dimension `d ≥ 2`, so this fails for all large `n`.
-/

namespace CERW.Support.Crossing

open Filter Topology
open CERW.Support.Main

/-- For positive `x, y`, a quotient of monomials combines exponents. -/
lemma rpow_div_combine (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (a b c d : ℝ) :
    (x ^ a * y ^ b) / (x ^ c * y ^ d) = x ^ (a - c) * y ^ (b - d) := by
  rw [div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg (le_of_lt hx), ← Real.rpow_neg (le_of_lt hy)]
  rw [show x ^ a * y ^ b * (y ^ (-d) * x ^ (-c))
        = (x ^ a * x ^ (-c)) * (y ^ b * y ^ (-d)) by ring]
  rw [← Real.rpow_add hx, ← Real.rpow_add hy]
  ring_nf

/-- The outer height has the exponent form `N^{1 - θ e} L^{1 + θ e}`. -/
lemma outer_height_eq (N L θ e : ℝ) (hN : 0 < N) (hL : 0 < L) :
    N * ((L / N) ^ θ) ^ e * L = N ^ ((1:ℝ) - θ * e) * L ^ ((1:ℝ) + θ * e) := by
  have hLN : 0 ≤ L / N := le_of_lt (div_pos hL hN)
  have hLθe : 0 ≤ L ^ (θ * e) := Real.rpow_nonneg (le_of_lt hL) _
  have hNθe : 0 ≤ N ^ (θ * e) := Real.rpow_nonneg (le_of_lt hN) _
  rw [← Real.rpow_mul hLN θ e, Real.div_rpow (le_of_lt hL) (le_of_lt hN)]
  rw [show N * (L ^ (θ * e) / N ^ (θ * e)) * L
        = (N ^ (1:ℝ) / N ^ (θ * e)) * (L ^ (θ * e) * L ^ (1:ℝ)) by
      rw [Real.rpow_one, Real.rpow_one]; ring]
  rw [← Real.rpow_sub hN, ← Real.rpow_add hL]
  rw [show θ * e + 1 = 1 + θ * e by ring]

/-- The squared outer height is `N^{2 - 2 θ e} L^{2 + 2 θ e}`. -/
lemma outer_height_sq (N L θ e : ℝ) (hN : 0 < N) (hL : 0 < L) :
    (N * ((L / N) ^ θ) ^ e * L) ^ 2
      = N ^ ((2:ℝ) - 2 * (θ * e)) * L ^ ((2:ℝ) + 2 * (θ * e)) := by
  have hLN : 0 ≤ L / N := le_of_lt (div_pos hL hN)
  have hLθe : 0 ≤ L ^ (θ * e) := Real.rpow_nonneg (le_of_lt hL) _
  have hNθe : 0 ≤ N ^ (θ * e) := Real.rpow_nonneg (le_of_lt hN) _
  rw [← Real.rpow_mul hLN θ e]
  rw [Real.div_rpow (le_of_lt hL) (le_of_lt hN)]
  simp only [← Real.rpow_natCast, Nat.cast_ofNat]
  rw [Real.mul_rpow (mul_nonneg (le_of_lt hN) (div_nonneg hLθe hNθe)) (le_of_lt hL)]
  rw [Real.mul_rpow (le_of_lt hN) (div_nonneg hLθe hNθe)]
  rw [Real.div_rpow hLθe hNθe]
  rw [← Real.rpow_mul (le_of_lt hL), ← Real.rpow_mul (le_of_lt hN)]
  rw [show (θ * e) * (2:ℝ) = 2 * (θ * e) by ring]
  rw [show N ^ (2:ℝ) * (L ^ (2 * (θ * e)) / N ^ (2 * (θ * e))) * L ^ (2:ℝ)
        = (N ^ (2:ℝ) / N ^ (2 * (θ * e))) * (L ^ (2 * (θ * e)) * L ^ (2:ℝ)) by ring]
  rw [← Real.rpow_sub hN, ← Real.rpow_add hL]
  rw [show 2 * (θ * e) + 2 = 2 + 2 * (θ * e) by ring]

/-- The first outer term divided by the squared height. -/
lemma outer_first_ratio (C₁ N L θ e γ : ℝ) (hC₁ : 0 < C₁) (hN : 0 < N) (hL : 0 < L) :
    ((C₁ * N * L) ^ γ * L ^ γ) / (N * ((L / N) ^ θ) ^ e * L) ^ 2
      = C₁ ^ γ * N ^ (γ - ((2:ℝ) - 2 * (θ * e)))
          * L ^ (2 * γ - ((2:ℝ) + 2 * (θ * e))) := by
  have hnum : (C₁ * N * L) ^ γ * L ^ γ = C₁ ^ γ * (N ^ γ * L ^ (2 * γ)) := by
    rw [Real.mul_rpow (mul_nonneg (le_of_lt hC₁) (le_of_lt hN)) (le_of_lt hL)]
    rw [Real.mul_rpow (le_of_lt hC₁) (le_of_lt hN)]
    rw [show (C₁ ^ γ * N ^ γ) * L ^ γ * L ^ γ
          = C₁ ^ γ * N ^ γ * (L ^ γ * L ^ γ) by ring]
    rw [← Real.rpow_add hL γ γ]
    rw [show γ + γ = 2 * γ by ring]
    ring
  rw [hnum, outer_height_sq N L θ e hN hL]
  rw [show C₁ ^ γ * (N ^ γ * L ^ (2 * γ))
        / (N ^ ((2:ℝ) - 2 * (θ * e)) * L ^ ((2:ℝ) + 2 * (θ * e)))
        = C₁ ^ γ * ((N ^ γ * L ^ (2 * γ))
        / (N ^ ((2:ℝ) - 2 * (θ * e)) * L ^ ((2:ℝ) + 2 * (θ * e)))) by ring]
  rw [rpow_div_combine N L hN hL]
  ring

/-- The second outer term divided by the squared height. -/
lemma outer_second_ratio (C₁ N L θ e : ℝ) (lam : ℕ) (hN : 0 < N) (hL : 0 < L) :
    (C₁ * N * L * L ^ lam * L) / (N * ((L / N) ^ θ) ^ e * L) ^ 2
      = C₁ * N ^ ((1:ℝ) - ((2:ℝ) - 2 * (θ * e)))
          * L ^ (((lam:ℝ) + 2) - ((2:ℝ) + 2 * (θ * e))) := by
  have hLprod : L * L ^ lam * L = L ^ ((lam:ℝ) + 2) := by
    rw [← Real.rpow_natCast L lam]
    rw [show (lam:ℝ) + 2 = (lam:ℝ) + 1 + 1 by ring]
    rw [Real.rpow_add hL, Real.rpow_add hL]
    simp only [Real.rpow_one]
    ring
  have hnum : C₁ * N * L * L ^ lam * L = C₁ * (N ^ (1:ℝ) * L ^ ((lam:ℝ) + 2)) := by
    rw [show C₁ * N * L * L ^ lam * L = C₁ * N * (L * L ^ lam * L) by ring]
    rw [hLprod]
    simp only [Real.rpow_one]
    ring
  rw [hnum, outer_height_sq N L θ e hN hL]
  rw [show C₁ * (N ^ (1:ℝ) * L ^ ((lam:ℝ) + 2))
        / (N ^ ((2:ℝ) - 2 * (θ * e)) * L ^ ((2:ℝ) + 2 * (θ * e)))
        = C₁ * ((N ^ (1:ℝ) * L ^ ((lam:ℝ) + 2))
        / (N ^ ((2:ℝ) - 2 * (θ * e)) * L ^ ((2:ℝ) + 2 * (θ * e)))) by ring]
  rw [rpow_div_combine N L hN hL]
  ring

/-- The first outer term ratio tends to zero for `d = 2`. -/
lemma tendsto_outer_first_two (C₁ : ℝ) (hC₁ : 0 < C₁) :
    Tendsto (fun n : ℕ =>
      ((C₁ * (n:ℝ)^((1:ℝ)/3) * Real.log ((n:ℝ)+2))^((4:ℝ)/3)
        * Real.log ((n:ℝ)+2)^((4:ℝ)/3))
      / ((n:ℝ)^((1:ℝ)/3)
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
          * Real.log ((n:ℝ)+2))^2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => C₁^((4:ℝ)/3)
      * (Real.log ((n:ℝ)+2)^((1:ℝ)/6) / (n:ℝ)^((1:ℝ)/18))) atTop (𝓝 0) := by
    simpa using
      (tendsto_log_rpow_div_rpow ((1:ℝ)/6) (c := 1/18) (by norm_num)).const_mul (C₁^((4:ℝ)/3))
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n:ℝ)^((1:ℝ)/3) := Real.rpow_pos_of_pos hnpos _
  have hL : 0 < Real.log ((n:ℝ)+2) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  rw [outer_first_ratio C₁ ((n:ℝ)^((1:ℝ)/3)) (Real.log ((n:ℝ)+2)) (1/2) (1/2) (4/3)
        hC₁ hN hL]
  have hNa : ((n:ℝ)^((1:ℝ)/3)) ^ (-(1:ℝ)/6) = (n:ℝ)^((1:ℝ)/3 * (-(1:ℝ)/6)) :=
    (Real.rpow_mul (Nat.cast_nonneg n) ((1:ℝ)/3) (-(1:ℝ)/6)).symm
  rw [show (4:ℝ)/3 - (2 - 2 * ((1:ℝ)/2 * ((1:ℝ)/2))) = -(1:ℝ)/6 by norm_num]
  rw [show (2:ℝ) * (4/3) - (2 + 2 * ((1:ℝ)/2 * ((1:ℝ)/2))) = (1:ℝ)/6 by norm_num]
  rw [hNa]
  rw [show (1:ℝ)/3 * (-(1:ℝ)/6) = (-(1:ℝ))/18 by norm_num]
  rw [show (-(1:ℝ))/18 = -((1:ℝ)/18) by ring, Real.rpow_neg (Nat.cast_nonneg n)]
  rw [div_eq_mul_inv]
  ring

/-- The second outer term ratio tends to zero for `d = 2`. -/
lemma tendsto_outer_second_two (C₁ : ℝ) :
    Tendsto (fun n : ℕ =>
      (C₁ * (n:ℝ)^((1:ℝ)/3) * Real.log ((n:ℝ)+2) * Real.log ((n:ℝ)+2)^2
          * Real.log ((n:ℝ)+2))
      / ((n:ℝ)^((1:ℝ)/3)
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
          * Real.log ((n:ℝ)+2))^2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => C₁
      * (Real.log ((n:ℝ)+2)^((3:ℝ)/2) / (n:ℝ)^((1:ℝ)/6))) atTop (𝓝 0) := by
    simpa using
      (tendsto_log_rpow_div_rpow ((3:ℝ)/2) (c := 1/6) (by norm_num)).const_mul C₁
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n:ℝ)^((1:ℝ)/3) := Real.rpow_pos_of_pos hnpos _
  have hL : 0 < Real.log ((n:ℝ)+2) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  rw [outer_second_ratio C₁ ((n:ℝ)^((1:ℝ)/3)) (Real.log ((n:ℝ)+2)) (1/2) (1/2) 2 hN hL]
  simp only [Nat.cast_ofNat]
  rw [show (1:ℝ) - (2 - 2 * ((1:ℝ)/2 * ((1:ℝ)/2))) = -(1:ℝ)/2 by norm_num]
  rw [show ((2:ℝ) + 2) - (2 + 2 * ((1:ℝ)/2 * ((1:ℝ)/2))) = (3:ℝ)/2 by norm_num]
  have hNa : ((n:ℝ)^((1:ℝ)/3)) ^ (-(1:ℝ)/2) = (n:ℝ)^((1:ℝ)/3 * (-(1:ℝ)/2)) :=
    (Real.rpow_mul (Nat.cast_nonneg n) ((1:ℝ)/3) (-(1:ℝ)/2)).symm
  rw [hNa]
  rw [show (1:ℝ)/3 * (-(1:ℝ)/2) = (-(1:ℝ))/6 by norm_num]
  rw [show (-(1:ℝ))/6 = -((1:ℝ)/6) by ring, Real.rpow_neg (Nat.cast_nonneg n)]
  rw [div_eq_mul_inv]
  ring

/-- The outer height tends to infinity for `d = 2`. -/
lemma tendsto_height_two :
    Tendsto (fun n : ℕ =>
      (n:ℝ)^((1:ℝ)/3) * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
        * Real.log ((n:ℝ)+2)) atTop atTop := by
  have hbase : Tendsto (fun n : ℕ =>
      (n:ℝ)^((1:ℝ)/4) * Real.log ((n:ℝ)+2)^((5:ℝ)/4)) atTop atTop := by
    apply Tendsto.atTop_mul_atTop₀
    · exact (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).comp tendsto_natCast_atTop_atTop
    · exact (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 5/4)).comp
        (Real.tendsto_log_atTop.comp
          (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_natCast_atTop_atTop))
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n:ℝ)^((1:ℝ)/3) := Real.rpow_pos_of_pos hnpos _
  have hL : 0 < Real.log ((n:ℝ)+2) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  rw [outer_height_eq ((n:ℝ)^((1:ℝ)/3)) (Real.log ((n:ℝ)+2)) (1/2) (1/2) hN hL]
  rw [show (1:ℝ) - (1/2) * (1/2) = 3/4 by norm_num,
      show (1:ℝ) + (1/2) * (1/2) = 5/4 by norm_num]
  rw [show ((n:ℝ)^((1:ℝ)/3)) ^ ((3:ℝ)/4) = (n:ℝ)^((1:ℝ)/3 * (3/4)) by
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]]
  rw [show (1:ℝ)/3 * (3/4) = 1/4 by norm_num]

/-- The first outer term ratio tends to zero for `d ≥ 3`. -/
lemma tendsto_outer_first_three (d : ℕ) (hd : 3 ≤ d) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    Tendsto (fun n : ℕ =>
      ((C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2))
          ^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1))
        * Real.log ((n:ℝ)+2)^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1)))
      / ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
              ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
          * Real.log ((n:ℝ)+2))^2) atTop (𝓝 0) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd0 : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  have hd1pos : (0:ℝ) < 2*(d:ℝ)-1 := by
    have h1 : (3:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd1 : 2*(d:ℝ)-1 ≠ 0 := ne_of_gt hd1pos
  have hypos : (0:ℝ) < (2*(d:ℝ)-4)/((2*(d:ℝ)-1)*((d:ℝ)+1)) := by
    have h1 : (0:ℝ) < 2*(d:ℝ)-4 := by
      have h2 : (3:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have h3 : (0:ℝ) < (d:ℝ)+1 := by positivity
    exact div_pos h1 (mul_pos hd1pos h3)
  have hlim : Tendsto (fun n : ℕ => C₁^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1))
      * (n:ℝ)^(-((2*(d:ℝ)-4)/((2*(d:ℝ)-1)*((d:ℝ)+1))))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hypos).comp tendsto_natCast_atTop_atTop).const_mul
      (C₁^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1)))
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) := Real.rpow_pos_of_pos hnpos _
  have hL : 0 < Real.log ((n:ℝ)+2) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  rw [outer_first_ratio C₁ ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))) (Real.log ((n:ℝ)+2))
        ((d:ℝ)/(2*(d:ℝ)-1)) ((1:ℝ)/(d:ℝ)) ((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1)) hC₁ hN hL]
  have hA : (2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1)
        - (2 - 2*(((d:ℝ)/(2*(d:ℝ)-1)) * ((1:ℝ)/(d:ℝ))))
      = (-(2*(d:ℝ)-4))/(2*(d:ℝ)-1) := by
    field_simp
    ring
  have hB : (2:ℝ)*((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1))
        - (2 + 2*(((d:ℝ)/(2*(d:ℝ)-1)) * ((1:ℝ)/(d:ℝ)))) = 0 := by
    field_simp
    ring
  rw [hA, hB, Real.rpow_zero, mul_one]
  have hNa : ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))) ^ ((-(2*(d:ℝ)-4))/(2*(d:ℝ)-1))
      = (n:ℝ)^(((1:ℝ)/((d:ℝ)+1)) * ((-(2*(d:ℝ)-4))/(2*(d:ℝ)-1))) :=
    (Real.rpow_mul (Nat.cast_nonneg n) _ _).symm
  rw [hNa]
  rw [show ((1:ℝ)/((d:ℝ)+1)) * ((-(2*(d:ℝ)-4))/(2*(d:ℝ)-1))
        = -((2*(d:ℝ)-4)/((2*(d:ℝ)-1)*((d:ℝ)+1))) by
      field_simp]

/-- The second outer term ratio tends to zero for `d ≥ 3`. -/
lemma tendsto_outer_second_three (d : ℕ) (hd : 3 ≤ d) (C₁ : ℝ) :
    Tendsto (fun n : ℕ =>
      (C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2)
          * Real.log ((n:ℝ)+2) * Real.log ((n:ℝ)+2))
      / ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
              ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
          * Real.log ((n:ℝ)+2))^2) atTop (𝓝 0) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd0 : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  have hd1pos : (0:ℝ) < 2*(d:ℝ)-1 := by
    have h1 : (3:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd1 : 2*(d:ℝ)-1 ≠ 0 := ne_of_gt hd1pos
  have hcc : (0:ℝ) < (2*(d:ℝ)-3)/((2*(d:ℝ)-1)*((d:ℝ)+1)) := by
    apply div_pos
    · have h2 : (3:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    · exact mul_pos hd1pos (by positivity)
  have hlim : Tendsto (fun n : ℕ => C₁
      * (Real.log ((n:ℝ)+2)^((2*(d:ℝ)-3)/(2*(d:ℝ)-1))
          / (n:ℝ)^((2*(d:ℝ)-3)/((2*(d:ℝ)-1)*((d:ℝ)+1))))) atTop (𝓝 0) := by
    simpa using (tendsto_log_rpow_div_rpow _ hcc).const_mul C₁
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) := Real.rpow_pos_of_pos hnpos _
  have hL : 0 < Real.log ((n:ℝ)+2) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  rw [show C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2) * Real.log ((n:ℝ)+2)
        * Real.log ((n:ℝ)+2)
        = C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2)
          * (Real.log ((n:ℝ)+2))^1 * Real.log ((n:ℝ)+2) by ring]
  rw [outer_second_ratio C₁ ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))) (Real.log ((n:ℝ)+2))
        ((d:ℝ)/(2*(d:ℝ)-1)) ((1:ℝ)/(d:ℝ)) 1 hN hL]
  simp only [Nat.cast_one]
  have hA : (1:ℝ) - (2 - 2*(((d:ℝ)/(2*(d:ℝ)-1)) * ((1:ℝ)/(d:ℝ))))
      = (-(2*(d:ℝ)-3))/(2*(d:ℝ)-1) := by
    field_simp
    ring
  have hB : ((1:ℝ)+2) - (2 + 2*(((d:ℝ)/(2*(d:ℝ)-1)) * ((1:ℝ)/(d:ℝ))))
      = (2*(d:ℝ)-3)/(2*(d:ℝ)-1) := by
    field_simp
    ring
  rw [hA, hB]
  have hNa : ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))) ^ ((-(2*(d:ℝ)-3))/(2*(d:ℝ)-1))
      = (n:ℝ)^(((1:ℝ)/((d:ℝ)+1)) * ((-(2*(d:ℝ)-3))/(2*(d:ℝ)-1))) :=
    (Real.rpow_mul (Nat.cast_nonneg n) _ _).symm
  rw [hNa]
  rw [show ((1:ℝ)/((d:ℝ)+1)) * ((-(2*(d:ℝ)-3))/(2*(d:ℝ)-1))
        = -((2*(d:ℝ)-3)/((2*(d:ℝ)-1)*((d:ℝ)+1))) by field_simp]
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  rw [div_eq_mul_inv]
  ring

/-- The outer height tends to infinity for `d ≥ 3`. -/
lemma tendsto_height_three (d : ℕ) (hd : 3 ≤ d) :
    Tendsto (fun n : ℕ =>
      (n:ℝ)^((1:ℝ)/((d:ℝ)+1))
        * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
            ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
        * Real.log ((n:ℝ)+2)) atTop atTop := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd0 : (d:ℝ) ≠ 0 := ne_of_gt hdpos
  have hd1pos : (0:ℝ) < 2*(d:ℝ)-1 := by
    have h1 : (3:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd1 : 2*(d:ℝ)-1 ≠ 0 := ne_of_gt hd1pos
  have haa : (0:ℝ) < (2*(d:ℝ)-2)/((2*(d:ℝ)-1)*((d:ℝ)+1)) := by
    apply div_pos
    · have h2 : (3:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    · exact mul_pos hd1pos (by positivity)
  have hbb : (0:ℝ) < (2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1) := div_pos (by positivity) hd1pos
  have hbase : Tendsto (fun n : ℕ =>
      (n:ℝ)^((2*(d:ℝ)-2)/((2*(d:ℝ)-1)*((d:ℝ)+1)))
        * Real.log ((n:ℝ)+2)^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1))) atTop atTop := by
    apply Tendsto.atTop_mul_atTop₀
    · exact (tendsto_rpow_atTop haa).comp tendsto_natCast_atTop_atTop
    · exact (tendsto_rpow_atTop hbb).comp
        (Real.tendsto_log_atTop.comp
          (tendsto_atTop_add_const_right atTop (2:ℝ) tendsto_natCast_atTop_atTop))
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) := Real.rpow_pos_of_pos hnpos _
  have hL : 0 < Real.log ((n:ℝ)+2) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  rw [outer_height_eq ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))) (Real.log ((n:ℝ)+2))
        ((d:ℝ)/(2*(d:ℝ)-1)) ((1:ℝ)/(d:ℝ)) hN hL]
  have hθe : ((d:ℝ)/(2*(d:ℝ)-1)) * ((1:ℝ)/(d:ℝ)) = 1/(2*(d:ℝ)-1) := by
    rw [div_mul_div_comm, mul_one, mul_comm ((2:ℝ)*(d:ℝ)-1) (d:ℝ)]
    rw [div_mul_cancel_left₀ hd0]
    rw [one_div]
  rw [hθe]
  rw [show (1:ℝ) - 1/(2*(d:ℝ)-1) = (2*(d:ℝ)-2)/(2*(d:ℝ)-1) by field_simp; ring,
      show (1:ℝ) + 1/(2*(d:ℝ)-1) = (2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1) by field_simp; ring]
  rw [show ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))) ^ ((2*(d:ℝ)-2)/(2*(d:ℝ)-1))
        = (n:ℝ)^(((1:ℝ)/((d:ℝ)+1)) * ((2*(d:ℝ)-2)/(2*(d:ℝ)-1))) by
      rw [← Real.rpow_mul (Nat.cast_nonneg n)]]
  rw [show ((1:ℝ)/((d:ℝ)+1)) * ((2*(d:ℝ)-2)/(2*(d:ℝ)-1))
        = (2*(d:ℝ)-2)/((2*(d:ℝ)-1)*((d:ℝ)+1)) by field_simp]


/-- For `d ≥ 2` and positive `A, C, C₁`, eventually
`C ((C₁NL)^γ L^γ + C₁NL λ_n L) < (A W L - 1)²`. -/
theorem eventually_outer_lt {d : ℕ} (hd : 2 ≤ d) {A C C₁ : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hC₁ : 0 < C₁) :
    ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      let W : ℝ := N * Q ^ ((1 : ℝ) / d)
      let γ : ℝ := 2 * d / (2 * d - 1)
      let lam : ℝ := if d = 2 then L ^ 2 else L
      C * ((C₁ * N * L) ^ γ * L ^ γ + C₁ * N * L * lam * L) < (A * W * L - 1) ^ 2 := by
  have hCpos : 0 < C := hC
  by_cases h2 : d = 2
  · subst d
    dsimp only
    simp only [reduceIte]
    push_cast
    rw [show (1:ℝ)/(2+1) = 1/3 by norm_num,
        show (2:ℝ)*2/(2*2-1) = 4/3 by norm_num]
    have h1 : ∀ᶠ n : ℕ in atTop,
        C * ((C₁ * (n:ℝ)^((1:ℝ)/3) * Real.log ((n:ℝ)+2))^((4:ℝ)/3)
            * Real.log ((n:ℝ)+2)^((4:ℝ)/3))
          / ((n:ℝ)^((1:ℝ)/3)
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
              * Real.log ((n:ℝ)+2))^2 < A^2/8 := by
      have hlim : Tendsto (fun n : ℕ =>
          C * (((C₁ * (n:ℝ)^((1:ℝ)/3) * Real.log ((n:ℝ)+2))^((4:ℝ)/3)
            * Real.log ((n:ℝ)+2)^((4:ℝ)/3))
          / ((n:ℝ)^((1:ℝ)/3)
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
              * Real.log ((n:ℝ)+2))^2)) atTop (𝓝 0) := by
        simpa using (tendsto_outer_first_two C₁ hC₁).const_mul C
      have hlt := hlim.eventually_lt_const (show (0:ℝ) < A^2/8 by positivity)
      filter_upwards [hlt] with n hn
      simpa only [mul_div_assoc] using hn
    have h2' : ∀ᶠ n : ℕ in atTop,
        C * (C₁ * (n:ℝ)^((1:ℝ)/3) * Real.log ((n:ℝ)+2) * Real.log ((n:ℝ)+2)^2
            * Real.log ((n:ℝ)+2))
          / ((n:ℝ)^((1:ℝ)/3)
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
              * Real.log ((n:ℝ)+2))^2 < A^2/8 := by
      have hlim : Tendsto (fun n : ℕ =>
          C * ((C₁ * (n:ℝ)^((1:ℝ)/3) * Real.log ((n:ℝ)+2) * Real.log ((n:ℝ)+2)^2
            * Real.log ((n:ℝ)+2))
          / ((n:ℝ)^((1:ℝ)/3)
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
              * Real.log ((n:ℝ)+2))^2)) atTop (𝓝 0) := by
        simpa using (tendsto_outer_second_two C₁).const_mul C
      have hlt := hlim.eventually_lt_const (show (0:ℝ) < A^2/8 by positivity)
      filter_upwards [hlt] with n hn
      simpa only [mul_div_assoc] using hn
    have h3 : ∀ᶠ n : ℕ in atTop,
        2 < A * ((n:ℝ)^((1:ℝ)/3)
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
          * Real.log ((n:ℝ)+2)) :=
      (tendsto_height_two.const_mul_atTop hA).eventually_gt_atTop 2
    have hp : ∀ᶠ n : ℕ in atTop,
        0 < (n:ℝ)^((1:ℝ)/3)
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
          * Real.log ((n:ℝ)+2) :=
      tendsto_height_two.eventually_gt_atTop 0
    filter_upwards [h1, h2', h3, hp] with n hn1 hn2 hn3 hpn
    set WL : ℝ := (n:ℝ)^((1:ℝ)/3)
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/3))^((1:ℝ)/2))^((1:ℝ)/2)
          * Real.log ((n:ℝ)+2) with hWL
    have hsq : 0 < WL^2 := pow_pos hpn 2
    have e1 : C * ((C₁ * (n:ℝ)^((1:ℝ)/3) * Real.log ((n:ℝ)+2))^((4:ℝ)/3)
            * Real.log ((n:ℝ)+2)^((4:ℝ)/3)) < A^2/8 * WL^2 := (div_lt_iff₀ hsq).mp hn1
    have e2 : C * (C₁ * (n:ℝ)^((1:ℝ)/3) * Real.log ((n:ℝ)+2) * Real.log ((n:ℝ)+2)^2
            * Real.log ((n:ℝ)+2)) < A^2/8 * WL^2 := (div_lt_iff₀ hsq).mp hn2
    have hquad : A^2/4 * WL^2 < (A * WL - 1)^2 := by
      nlinarith [mul_pos (show (0:ℝ) < 3*(A*WL) - 2 by linarith)
                       (show (0:ℝ) < A*WL - 2 by linarith)]
    nlinarith [e1, e2, hquad, hC]
  · have hd3 : 3 ≤ d := by omega
    dsimp only
    simp only [if_neg h2]
    have h1 : ∀ᶠ n : ℕ in atTop,
        C * (((C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2))
            ^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1))
          * Real.log ((n:ℝ)+2)^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1)))
        / ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))
            * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
                ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
            * Real.log ((n:ℝ)+2))^2) < A^2/8 := by
      have hlim : Tendsto (fun n : ℕ =>
          C * (((C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2))
              ^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1))
            * Real.log ((n:ℝ)+2)^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1)))
          / ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))
              * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
                  ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
              * Real.log ((n:ℝ)+2))^2)) atTop (𝓝 0) := by
        simpa using (tendsto_outer_first_three d hd3 C₁ hC₁).const_mul C
      have hlt := hlim.eventually_lt_const (show (0:ℝ) < A^2/8 by positivity)
      filter_upwards [hlt] with n hn
      simpa only [mul_div_assoc] using hn
    have h2' : ∀ᶠ n : ℕ in atTop,
        C * ((C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2)
            * Real.log ((n:ℝ)+2) * Real.log ((n:ℝ)+2))
        / ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))
            * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
                ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
            * Real.log ((n:ℝ)+2))^2) < A^2/8 := by
      have hlim : Tendsto (fun n : ℕ =>
          C * ((C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2)
              * Real.log ((n:ℝ)+2) * Real.log ((n:ℝ)+2))
          / ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))
              * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
                  ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
              * Real.log ((n:ℝ)+2))^2)) atTop (𝓝 0) := by
        simpa using (tendsto_outer_second_three d hd3 C₁).const_mul C
      have hlt := hlim.eventually_lt_const (show (0:ℝ) < A^2/8 by positivity)
      filter_upwards [hlt] with n hn
      simpa only [mul_div_assoc] using hn
    have h3 : ∀ᶠ n : ℕ in atTop,
        2 < A * ((n:ℝ)^((1:ℝ)/((d:ℝ)+1))
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
              ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
          * Real.log ((n:ℝ)+2)) :=
      (tendsto_height_three d hd3).const_mul_atTop hA |>.eventually_gt_atTop 2
    have hp : ∀ᶠ n : ℕ in atTop,
        0 < (n:ℝ)^((1:ℝ)/((d:ℝ)+1))
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
              ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
          * Real.log ((n:ℝ)+2) :=
      (tendsto_height_three d hd3).eventually_gt_atTop 0
    filter_upwards [h1, h2', h3, hp] with n hn1 hn2 hn3 hpn
    set WL : ℝ := (n:ℝ)^((1:ℝ)/((d:ℝ)+1))
          * ((Real.log ((n:ℝ)+2) / (n:ℝ)^((1:ℝ)/((d:ℝ)+1)))
              ^((d:ℝ)/(2*(d:ℝ)-1)))^((1:ℝ)/(d:ℝ))
          * Real.log ((n:ℝ)+2) with hWL
    rw [← mul_div_assoc] at hn1 hn2
    have hsq : 0 < WL^2 := pow_pos hpn 2
    have e1 : C * ((C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2))
            ^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1))
          * Real.log ((n:ℝ)+2)^((2:ℝ)*(d:ℝ)/(2*(d:ℝ)-1))) < A^2/8 * WL^2 :=
      (div_lt_iff₀ hsq).mp hn1
    have e2 : C * (C₁ * (n:ℝ)^((1:ℝ)/((d:ℝ)+1)) * Real.log ((n:ℝ)+2)
            * Real.log ((n:ℝ)+2) * Real.log ((n:ℝ)+2)) < A^2/8 * WL^2 :=
      (div_lt_iff₀ hsq).mp hn2
    have hquad : A^2/4 * WL^2 < (A * WL - 1)^2 := by
      nlinarith [mul_pos (show (0:ℝ) < 3*(A*WL) - 2 by linarith)
                       (show (0:ℝ) < A*WL - 2 by linarith)]
    nlinarith [e1, e2, hquad, hC]


end CERW.Support.Crossing
