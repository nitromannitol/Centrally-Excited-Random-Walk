import CERW.Support.Lower.PlanarGap.Annulus
import CERW.Support.Lower.PlanarGap.VectorClt
import CERW.Support.Lower.PlanarGap.Width

/-!
# The vector small-ball bound for the width of the planar range

For the planar walk with `0 < ε < 1/2` let `Z_n = X_n + ε Σ_{x ∈ A_n} u_x` be the compensated
position, `G_n = R_out(n) − R_in(n)` the width of the range and
`r_n = (3 n / (4 π ε))^{1/3}` the radius of `eq:radius`.

*The geometric inequality.* The direction-free annulus bound
`‖Σ_{x ∈ A} u_x‖ ≤ R² − ρ² + C (R + 1)` for a finite set `A` between the lattice disks of radii
`ρ` and `R` (`PlanarGap.Annulus`), applied to the departure range with `ρ = R_in(n)` and
`R = R_out(n)`, gives the pathwise bound
`‖Z_n‖ ≤ R_out + ε (G_n (R_out + R_in) + C (R_out + 1))`. On the event on which the proved radius
rates hold, `R_out + R_in = 2 r_n + O(√r_n (log n)^{5/2})`, and `2 ε r_n^{3/2} = √(3 ε / π) √n`
exactly, so that
`‖Z_n‖ / √n ≤ √(3 ε / π) · G_n / √r_n + o(1)`
with a deterministic `o(1)` (`compensated_le_gap`).

*The small-ball bound.* The vector central limit theorem (`PlanarGap.VectorClt`) gives
`Z_n / √n ⇒ N(0, I/2)`, the Mathlib multivariate Gaussian with covariance `(1/2) I`. Portmanteau
on closed balls and continuity from above of the Gaussian measure give
`limsup P(G_n ≤ a √r_n) ≤ N(0, I/2)(B̄(0, a √(3 ε / π)))` for every `a ≥ 0`, the case `a = 0`
included (`gap_limsup_le_gaussian_ball`). The closed ball of radius `t` carries mass
`1 − exp(−t²)` under this Gaussian; that identification is a separate statement that this file
does not use: the bound above is stated against the literal Gaussian measure.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower.PlanarGap

open CERW CERW.Support.Law CERW.Support.Lower

/-! ### The annulus bound on the departure range -/

/-- The inner radius is nonnegative. -/
private theorem innerRadius_nonneg' {d : ℕ} (X : ℕ → Site d) (n : ℕ) :
    0 ≤ innerRadius X n := by
  refine Real.sInf_nonneg ?_
  rintro _ ⟨y, -, rfl⟩
  exact norm_nonneg y

/-- The outer radius is nonnegative. -/
private theorem maxRadius_nonneg' {d : ℕ} (X : ℕ → Site d) (n : ℕ) : 0 ≤ maxRadius X n :=
  (LatticeProb.euclidNorm_nonneg (X 0)).trans (euclidNorm_le_maxRadius X (Nat.zero_le n))

/-- A site in the open ball of radius the inner radius belongs to the departure range. -/
private theorem mem_departureRange_of_lt_innerRadius' {d : ℕ} {X : ℕ → Site d} {n : ℕ}
    {x : Site d} (h : euclidNorm x < innerRadius X n) : x ∈ departureRange X n := by
  by_contra hx
  have hmem : toSpace x ∈ (cellSet X n)ᶜ := fun hc =>
    hx ((CERW.Support.Occupation.toSpace_mem_cellSet_iff X n x).mp hc)
  have hle : innerRadius X n ≤ ‖toSpace x‖ := by
    refine csInf_le ⟨0, ?_⟩ ⟨toSpace x, hmem, rfl⟩
    rintro _ ⟨y, -, rfl⟩
    exact norm_nonneg y
  rw [norm_toSpace] at hle
  exact absurd h (not_lt.mpr hle)

/-- A site of the departure range is within the outer radius. -/
private theorem euclidNorm_le_maxRadius_of_mem' {d : ℕ} {X : ℕ → Site d} {n : ℕ} {x : Site d}
    (hx : x ∈ departureRange X n) : euclidNorm x ≤ maxRadius X n :=
  LatticeProb.mem_ballFinset_iff.mp
    (CERW.Support.Occupation.departureRange_subset_ballFinset X n hx)

/-- **The annulus bound on the departure range.** There is an absolute constant `C` such that for
every planar path and every time, `‖Σ_{x ∈ A_n} u_x‖ ≤ R_out² − R_in² + C (R_out + 1)`. -/
theorem norm_sum_departureRange_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℕ → Site 2) (n : ℕ),
      ‖∑ z ∈ departureRange x n, unitDir (toSpace z)‖ ≤
        maxRadius x n ^ 2 - innerRadius x n ^ 2 + C * (maxRadius x n + 1) := by
  obtain ⟨C, hC, h⟩ := norm_sum_unitDir_le
  exact ⟨C, hC, fun x n => h (departureRange x n) (innerRadius_nonneg' x n)
    (maxRadius_nonneg' x n) (fun z hz => mem_departureRange_of_lt_innerRadius' hz)
    (fun z hz => euclidNorm_le_maxRadius_of_mem' hz)⟩

/-- **The pathwise bound for the compensated position.** With the constant `C` of
`norm_sum_departureRange_le` and `ε ≥ 0`,
`‖X_n + ε Σ_{x ∈ A_n} u_x‖ ≤ R_out + ε (R_out² − R_in² + C (R_out + 1))`, and the bracket is
nonnegative. -/
theorem norm_compensated_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ}, 0 ≤ ε → ∀ (x : ℕ → Site 2) (n : ℕ),
      ‖toSpace (x n) + ε • ∑ z ∈ departureRange x n, unitDir (toSpace z)‖ ≤
        maxRadius x n + ε * (maxRadius x n ^ 2 - innerRadius x n ^ 2 +
          C * (maxRadius x n + 1)) ∧
      0 ≤ maxRadius x n ^ 2 - innerRadius x n ^ 2 + C * (maxRadius x n + 1) := by
  obtain ⟨C, hC, h⟩ := norm_sum_departureRange_le
  refine ⟨C, hC, fun {ε} hε x n => ⟨?_, (norm_nonneg _).trans (h x n)⟩⟩
  have hx : ‖toSpace (x n)‖ ≤ maxRadius x n := by
    rw [norm_toSpace]
    exact euclidNorm_le_maxRadius x le_rfl
  calc ‖toSpace (x n) + ε • ∑ z ∈ departureRange x n, unitDir (toSpace z)‖
      ≤ ‖toSpace (x n)‖ + ‖ε • ∑ z ∈ departureRange x n, unitDir (toSpace z)‖ :=
        norm_add_le _ _
    _ = ‖toSpace (x n)‖ + ε * ‖∑ z ∈ departureRange x n, unitDir (toSpace z)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hε]
    _ ≤ maxRadius x n + ε * (maxRadius x n ^ 2 - innerRadius x n ^ 2 +
          C * (maxRadius x n + 1)) :=
        add_le_add hx (mul_le_mul_of_nonneg_left (h x n) hε)

/-! ### The arithmetic of the radii -/

/-- The real-number core of the geometric inequality. Here `r` is the radius scale, `δ` the radius
error, `ρ` and `R` the two radii and `N` the norm of the compensated position. -/
private theorem radii_arith {ε C₀ r δ ρ R N : ℝ} (hε : 0 < ε) (hC₀ : 0 < C₀) (hδ : 0 ≤ δ)
    (hδr : 4 * δ ≤ r) (h4 : 4 ≤ r) (hN : N ≤ R + ε * (R ^ 2 - ρ ^ 2 + C₀ * (R + 1)))
    (hann : 0 ≤ R ^ 2 - ρ ^ 2 + C₀ * (R + 1)) (hR0 : 0 ≤ R)
    (hρ : |ρ - r| ≤ δ) (hR : R - r ≤ δ) :
    N ≤ 2 * ε * r * (R - ρ) +
      ((r + δ) + ε * (4 * δ ^ 2 + C₀ * (r + δ + 1)) + 4 * ε * C₀ * r) := by
  obtain ⟨hρ1, hρ2⟩ := abs_le.mp hρ
  rcases le_or_gt 0 (R - ρ) with hG | hG
  · -- the positive case
    have hsum : R + ρ ≤ 2 * r + 2 * δ := by linarith
    have hGδ : R - ρ ≤ 2 * δ := by linarith
    have h1 : (R - ρ) * (R + ρ) ≤ (R - ρ) * (2 * r + 2 * δ) :=
      mul_le_mul_of_nonneg_left hsum hG
    have h2 : (R - ρ) * (2 * δ) ≤ (2 * δ) * (2 * δ) :=
      mul_le_mul_of_nonneg_right hGδ (by linarith)
    have h3 : R ^ 2 - ρ ^ 2 ≤ 2 * r * (R - ρ) + 4 * δ ^ 2 := by nlinarith
    have h4' : C₀ * (R + 1) ≤ C₀ * (r + δ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀.le
    have h5 : ε * (R ^ 2 - ρ ^ 2 + C₀ * (R + 1)) ≤
        ε * (2 * r * (R - ρ) + 4 * δ ^ 2 + C₀ * (r + δ + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hε.le
    have h6 : 0 ≤ 4 * ε * C₀ * r := by positivity
    nlinarith
  · -- the negative case: the width is bounded below by the annulus bound
    have hlow : r - δ ≤ R + ρ := by linarith
    have hneg : 0 ≤ -(R - ρ) := by linarith
    have h1 : -(R - ρ) * (3 * r / 4) ≤ -(R - ρ) * (R + ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) hneg
    have h2 : -(R - ρ) * (R + ρ) ≤ C₀ * (R + 1) := by nlinarith
    have h3 : C₀ * (R + 1) ≤ C₀ * (3 * r / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀.le
    have hGlow : -(R - ρ) ≤ 2 * C₀ := by
      by_contra hcon
      have hc : 2 * C₀ < -(R - ρ) := not_le.mp hcon
      nlinarith
    have hRρ : R ^ 2 - ρ ^ 2 ≤ 0 := by nlinarith
    have h4' : C₀ * (R + 1) ≤ C₀ * (r + δ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hC₀.le
    have h5 : ε * (R ^ 2 - ρ ^ 2 + C₀ * (R + 1)) ≤ ε * (C₀ * (r + δ + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hε.le
    have h6 : 0 ≤ 2 * ε * r * (R - ρ + 2 * C₀) := by
      have : 0 ≤ R - ρ + 2 * C₀ := by linarith
      positivity
    have hnn : 0 ≤ 4 * δ ^ 2 := by positivity
    nlinarith

/-! ### The error is a vanishing sequence -/

/-- `(log n)^b / n^s → 0` for `s > 0`. -/
theorem tendsto_log_rpow_div_rpow (b : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => Real.log n ^ b / (n : ℝ) ^ s) atTop (𝓝 0) :=
  ((isLittleO_log_rpow_rpow_atTop b hs).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop

/-- `(log n)^b / (n^{1/6})^m → 0` for `m ≠ 0`. -/
theorem tendsto_log_rpow_div_sixth_pow (b : ℝ) {m : ℕ} (hm : m ≠ 0) :
    Tendsto (fun n : ℕ => Real.log n ^ b / ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ m) atTop (𝓝 0) := by
  have hs : 0 < (m : ℝ) / 6 := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) (by norm_num)
  refine (tendsto_log_rpow_div_rpow b hs).congr fun n => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 2
  ring

/-- The radius error of the geometric inequality, divided by `√n`, tends to zero: with
`r = K q²`, `q = n^{1/6}` and `δ = C √r (log n)^{5/2}`, the quantity
`(r + δ + ε (4 δ² + C₀ (r + δ + 1)) + 4 ε C₀ r) / √n` is a combination of `1/q`,
`(log n)^{5/2} / q²`, `(log n)^5 / q` and `1/q³`. -/
private theorem tendsto_gap_error {K ε C C₀ : ℝ} (hK : 0 < K) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, r n = K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) :
    Tendsto (fun n : ℕ =>
      ((r n + C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)) +
        ε * (4 * (C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)) ^ 2 +
          C₀ * (r n + C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) + 1)) +
        4 * ε * C₀ * r n) / Real.sqrt n) atTop (𝓝 0) := by
  have hq1 := tendsto_inv_rpow_sixth_pow (m := 1) one_ne_zero
  have hq3 := tendsto_inv_rpow_sixth_pow (m := 3) (by norm_num)
  have hA := tendsto_log_rpow_div_sixth_pow ((5 : ℝ) / 2) (m := 2) two_ne_zero
  have hB : Tendsto (fun n : ℕ => (Real.log n ^ ((5 : ℝ) / 2)) ^ 2 /
      ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 1) atTop (𝓝 0) := by
    refine (tendsto_log_rpow_div_sixth_pow (5 : ℝ) one_ne_zero).congr fun n => ?_
    have hL : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have h52 : (Real.log (n : ℝ) ^ ((5 : ℝ) / 2)) ^ 2 = Real.log (n : ℝ) ^ (5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
      norm_num
    rw [h52]
  have hsum := (((hq1.const_mul (K + ε * C₀ * K + 4 * ε * C₀ * K)).add
    (hA.const_mul (C * Real.sqrt K + ε * C₀ * C * Real.sqrt K))).add
    (hB.const_mul (4 * ε * C ^ 2 * K))).add (hq3.const_mul (ε * C₀))
  have hlim : (K + ε * C₀ * K + 4 * ε * C₀ * K) * 0 +
      (C * Real.sqrt K + ε * C₀ * C * Real.sqrt K) * 0 + 4 * ε * C ^ 2 * K * 0 +
      ε * C₀ * 0 = 0 := by ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hq0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  rw [hr n, sqrt_natCast_eq_rpow_sixth_cube n, Real.sqrt_mul hK.le, Real.sqrt_sq hq0.le]
  have hsK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  generalize (n : ℝ) ^ ((1 : ℝ) / 6) = q at hq0 ⊢
  generalize Real.log n ^ ((5 : ℝ) / 2) = M
  field_simp
  linear_combination (-(4 * q ^ 2 * ε * C ^ 2 * M ^ 2)) * hsK

/-! ### The asymptotic geometric inequality -/

/-- **The asymptotic geometric inequality.** For `ε > 0` and every constant `C ≥ 0` there is a
deterministic sequence `e_n → 0` such that, for all large `n` and every planar path whose radii
satisfy the proved rates
`|R_in(n) − r_n| ≤ C √(r_n log n)` and `R_out(n) − r_n ≤ C √r_n (log n)^{5/2}`,
`‖Z_n‖ / √n ≤ √(3 ε / π) · (R_out(n) − R_in(n)) / √r_n + e_n`,
where `Z_n = X_n + ε Σ_{x ∈ A_n} u_x` is the compensated position and `r_n` the radius of
`eq:radius`. The coefficient of the width is exactly `√(3 ε / π)`. -/
theorem compensated_le_gap {ε : ℝ} (hε0 : 0 < ε) {C : ℝ} (hC : 0 ≤ C) :
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop, ∀ x : ℕ → Site 2,
      |innerRadius x n - r n| ≤ C * Real.sqrt (r n * Real.log n) →
      maxRadius x n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) →
      ‖(Real.sqrt n)⁻¹ • (toSpace (x n) +
          ε • ∑ z ∈ departureRange x n, unitDir (toSpace z))‖ ≤
        Real.sqrt (3 * ε / Real.pi) * ((maxRadius x n - innerRadius x n) / Real.sqrt (r n)) +
          e n := by
  intro r
  obtain ⟨C₀, hC₀, hgeo⟩ := norm_compensated_le
  set K : ℝ := (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) with hKdef
  have hK : 0 < K := by positivity
  have hr : ∀ n : ℕ, r n = K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := fun n => planar_radius_eq hε0 n
  have hc := two_mul_eps_mul_radius_const hε0
  rw [← hKdef] at hc
  refine ⟨fun n : ℕ => ((r n + C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)) +
      ε * (4 * (C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)) ^ 2 +
        C₀ * (r n + C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) + 1)) +
      4 * ε * C₀ * r n) / Real.sqrt n, tendsto_gap_error (C := C) (C₀ := C₀) hK r hr, ?_⟩
  have hr4 : ∀ᶠ n : ℕ in atTop, 4 ≤ r n := by
    have hlim : Tendsto (fun n : ℕ => K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop hK ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_rpow_sixth)
    filter_upwards [hlim.eventually_ge_atTop 4] with n hn
    rw [hr n]
    exact hn
  filter_upwards [eventually_sqrt_mul_log_le hK C (η := 1 / 4) (by norm_num),
    eventually_ge_atTop 3, hr4] with n hsmall hn3 hn4 x hρ hR
  have hn0 : (0 : ℝ) < n := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hq0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hn0 _
  have hrpos : 0 < r n := by rw [hr n]; positivity
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have := Real.exp_one_lt_d9
    linarith
  set δ : ℝ := C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδr : 4 * δ ≤ r n := by
    have h1 : δ ≤ 1 / 4 * r n := by
      rw [hδdef, hr n]
      exact hsmall
    linarith
  have hsqrt : Real.sqrt (r n * Real.log n) ≤ Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_mul hrpos.le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hρδ : |innerRadius x n - r n| ≤ δ :=
    hρ.trans (by rw [hδdef, mul_assoc]; exact mul_le_mul_of_nonneg_left hsqrt hC)
  obtain ⟨hN, hann⟩ := hgeo hε0.le x n
  have hcore := radii_arith hε0 hC₀ hδ0 hδr hn4 hN hann (maxRadius_nonneg' x n) hρδ hR
  have hS : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hS.le, ← div_eq_inv_mul]
  have hid : Real.sqrt (3 * ε / Real.pi) *
      ((maxRadius x n - innerRadius x n) / Real.sqrt (r n)) =
      2 * ε * r n * (maxRadius x n - innerRadius x n) / Real.sqrt n := by
    rw [← hc, hr n, sqrt_natCast_eq_rpow_sixth_cube n, Real.sqrt_mul hK.le,
      Real.sqrt_sq hq0.le]
    have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
    generalize (n : ℝ) ^ ((1 : ℝ) / 6) = q at hq0 ⊢
    field_simp
  rw [hid, ← add_div]
  exact div_le_div_of_nonneg_right hcore hS.le

/-- **The geometric inequality holds with probability tending to one.** For the walk itself there
is a deterministic `e_n → 0` such that the probability that
`‖Z_n‖ / √n > √(3 ε / π) · G_n / √r_n + e_n` tends to zero: off the event on which the proved radius
rates fail, `compensated_le_gap` applies. -/
theorem compensated_le_gap_in_probability {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) :
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => μ {ω | Real.sqrt (3 * ε / Real.pi) *
          ((maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n) /
            Real.sqrt (r n)) + e n <
        ‖(Real.sqrt n)⁻¹ • (toSpace (X n ω) +
          ε • ∑ x ∈ departureRange (fun j => X j ω) n, unitDir (toSpace x))‖})
        atTop (𝓝 0) := by
  intro r
  obtain ⟨C, hC, hbadT⟩ := planar_radii_bad_tendsto hε0 hεd
  obtain ⟨e, he, hgeoE⟩ := compensated_le_gap hε0 hC.le
  refine ⟨e, he, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hbadT μ X hX)
    (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [hgeoE] with n hn
  refine measure_mono fun ω hω => ?_
  by_contra hg
  simp only [Set.mem_setOf_eq, not_not] at hg
  exact absurd hω (not_lt.mpr (hn (fun j => X j ω) hg.1 hg.2))

/-! ### Closed balls under a limit law -/

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- Continuity from above for closed balls: the measures of the closed balls of radius
`t + 1/(k+1)` about the origin tend to that of the closed ball of radius `t`. -/
theorem tendsto_measure_closedBall_add_inv (ν : Measure E2) [IsFiniteMeasure ν] (t : ℝ) :
    Tendsto (fun k : ℕ => ν (Metric.closedBall 0 (t + 1 / ((k : ℝ) + 1)))) atTop
      (𝓝 (ν (Metric.closedBall 0 t))) := by
  have hanti : Antitone (fun k : ℕ => Metric.closedBall (0 : E2) (t + 1 / ((k : ℝ) + 1))) := by
    intro i j hij
    have h : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    exact Metric.closedBall_subset_closedBall (by linarith)
  have hlim := tendsto_measure_iInter_atTop (μ := ν)
    (fun k => Metric.isClosed_closedBall.measurableSet.nullMeasurableSet) hanti
    ⟨0, measure_ne_top ν _⟩
  have hinter : (⋂ k : ℕ, Metric.closedBall (0 : E2) (t + 1 / ((k : ℝ) + 1))) =
      Metric.closedBall 0 t := by
    ext z
    simp only [Set.mem_iInter, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h
      by_contra hlt
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ‖z‖ - t by linarith [not_le.mp hlt])
      linarith [h k]
    · intro h k
      have hk : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hinter] at hlim
  exact hlim

/-- Portmanteau for closed balls about the origin: if `f n ⇒ ν` then
`limsup P(‖f n‖ ≤ t) ≤ ν(B̄(0, t))`. -/
theorem limsup_measure_norm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : ℕ → Ω → E2} {ν : Measure E2} [IsProbabilityMeasure ν]
    (h : TendstoInDistribution f atTop id (fun _ => μ) ν) (t : ℝ) :
    limsup (fun n => μ {ω | ‖f n ω‖ ≤ t}) atTop ≤ ν (Metric.closedBall 0 t) := by
  have h1 := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto
    (Metric.isClosed_closedBall (x := (0 : E2)) (ε := t))
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at h1
  have h2 : ∀ n, μ.map (f n) (Metric.closedBall 0 t) = μ {ω | ‖f n ω‖ ≤ t} := fun n => by
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n)
      Metric.isClosed_closedBall.measurableSet]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq]
  simpa only [h2] using h1

/-- The Gaussian with covariance `(1/2) I` has no atom at the origin. -/
theorem multivariateGaussian_half_singleton_zero :
    multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) {0} = 0 := by
  set ν := multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) with hν
  set t : E2 := EuclideanSpace.single 0 1 with ht
  have htn : ‖t‖ = 1 := by simp [ht]
  have h := map_inner_multivariateGaussian_half t
  rw [← hν, htn] at h
  haveI : NullSingletonClass (gaussianReal 0 (((1 : ℝ) ^ 2 / 2).toNNReal)) :=
    nullSingletonClass_gaussianReal (by simp)
  have hmeas : Measurable (fun z : E2 => inner ℝ z t) :=
    (continuous_id.inner continuous_const).measurable
  refine nonpos_iff_eq_zero.mp ?_
  calc ν {0} ≤ ν ((fun z : E2 => inner ℝ z t) ⁻¹' {0}) := by
        refine measure_mono fun z hz => ?_
        rw [Set.mem_singleton_iff] at hz
        simp [hz]
    _ = (ν.map (fun z : E2 => inner ℝ z t)) {0} :=
        (Measure.map_apply hmeas (measurableSet_singleton 0)).symm
    _ = 0 := by rw [h]; exact measure_singleton 0

/-! ### The vector small-ball bound -/

/-- **Small-ball bound for the width of the planar range, against the actual Gaussian.** For
`0 < ε < 1/2` and every real `a`, in particular every `a ≥ 0` and the case `a = 0`,
`limsup_n P(R_out(n) − R_in(n) ≤ a √r_n) ≤ N(0, I/2)(B̄(0, a √(3 ε / π)))`,
where `N(0, I/2)` is the Mathlib multivariate Gaussian with covariance `(1/2) I` on the Euclidean
plane and `B̄` the closed ball.

The proof composes the vector central limit theorem `vector_clt`, the pathwise geometric
inequality `compensated_le_gap` (built on the direction-free annulus bound), the proved radius
rates `planar_radii_bad_tendsto` and the closed-ball Portmanteau bound. -/
theorem gap_limsup_le_gaussian_ball {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) (a : ℝ) :
    let r : ℕ → ℝ := fun n =>
      ((((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)).toReal)) ^
        ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1))
    limsup (fun n => μ {ω | maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
        a * Real.sqrt (r n)}) atTop ≤
      multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (Metric.closedBall 0 (a * Real.sqrt (3 * ε / Real.pi))) := by
  intro r
  set K : ℝ := (3 / (4 * ε * Real.pi)) ^ ((1 : ℝ) / 3) with hKdef
  have hK : 0 < K := by positivity
  have hr : ∀ n : ℕ, r n = K * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 2 := fun n => planar_radius_eq hε0 n
  set c : ℝ := Real.sqrt (3 * ε / Real.pi) with hcdef
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hvec := vector_clt hε0 hεd μ hX
  obtain ⟨C, hC, hbadT⟩ := planar_radii_bad_tendsto hε0 hεd
  obtain ⟨e, he, hgeoE⟩ := compensated_le_gap hε0 hC.le
  have hk : ∀ k : ℕ, limsup (fun n => μ {ω | maxRadius (fun j => X j ω) n -
        innerRadius (fun j => X j ω) n ≤ a * Real.sqrt (r n)}) atTop ≤
      multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (Metric.closedBall 0 (a * c + 1 / ((k : ℝ) + 1))) := by
    intro k
    set η' : ℝ := 1 / ((k : ℝ) + 1) with hη'
    have hη'0 : 0 < η' := by positivity
    have hev : ∀ᶠ n : ℕ in atTop, e n < η' := he.eventually (gt_mem_nhds hη'0)
    have hincl : ∀ᶠ n : ℕ in atTop,
        {ω | maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
          a * Real.sqrt (r n)} ⊆
        {ω | ‖(Real.sqrt n)⁻¹ • (toSpace (X n ω) + ε • ∑ x ∈ departureRange (fun j => X j ω) n,
            unitDir (toSpace x))‖ ≤ a * c + η'} ∪
        {ω | ¬ (|innerRadius (fun j => X j ω) n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
            maxRadius (fun j => X j ω) n - r n ≤
              C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2))} := by
      filter_upwards [hgeoE, hev, eventually_ge_atTop 1] with n hn hen hn1
      intro ω hω
      by_cases hgood : |innerRadius (fun j => X j ω) n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
          maxRadius (fun j => X j ω) n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
      · left
        have h1 := hn (fun j => X j ω) hgood.1 hgood.2
        have hrpos : 0 < Real.sqrt (r n) := by
          rw [hr n]
          have hq0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 6) :=
            Real.rpow_pos_of_pos (by exact_mod_cast hn1) _
          exact Real.sqrt_pos.mpr (by positivity)
        have hω' : maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n ≤
            a * Real.sqrt (r n) := hω
        have h2 : (maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n) /
            Real.sqrt (r n) ≤ a := (div_le_iff₀ hrpos).mpr hω'
        show ‖(Real.sqrt n)⁻¹ • (toSpace (X n ω) + ε • ∑ x ∈ departureRange (fun j => X j ω) n,
            unitDir (toSpace x))‖ ≤ a * c + η'
        calc _ ≤ c * ((maxRadius (fun j => X j ω) n - innerRadius (fun j => X j ω) n) /
              Real.sqrt (r n)) + e n := h1
          _ ≤ c * a + η' := add_le_add (mul_le_mul_of_nonneg_left h2 hc0) hen.le
          _ = a * c + η' := by ring
      · right
        exact hgood
    exact limsup_measure_le_of_eventually_subset μ hincl (hbadT μ X hX)
      (limsup_measure_norm_le μ hvec _)
  exact ge_of_tendsto'
    (tendsto_measure_closedBall_add_inv
      (multivariateGaussian 0 (((1 : ℝ) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) (a * c)) hk

/-- **The case `a = 0`.** `limsup_n P(R_out(n) − R_in(n) ≤ 0) = 0`: the closed ball of radius zero
is the origin, which the Gaussian does not charge. -/
theorem gap_limsup_nonpos_eq_zero {ε : ℝ} (hε0 : 0 < ε) (hεd : ε < 1 / ((2 : ℕ) : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → Site 2} (hX : IsCERW μ ε X) :
    limsup (fun n => μ {ω | maxRadius (fun j => X j ω) n -
        innerRadius (fun j => X j ω) n ≤ 0}) atTop = 0 := by
  have h := gap_limsup_le_gaussian_ball hε0 hεd μ hX 0
  simp only [zero_mul, Metric.closedBall_zero] at h
  rw [multivariateGaussian_half_singleton_zero] at h
  exact le_antisymm h bot_le

end CERW.Support.Lower.PlanarGap
