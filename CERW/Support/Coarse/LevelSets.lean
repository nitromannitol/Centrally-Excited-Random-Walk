import CERW.Model.Potential
import LatticeProb.Walk.Ball

/-!
# Level sets of the potential kernel

`eq:levelsets`: for all large `r`, the kernel `b` stays below the radial profile `h_d(r)` on
`|x| ≤ r - 1`, and above it on `|x| ≥ r + 1`. Here `h_2(r) = (2/π) log r + κ` and
`h_d(r) = -c_d r^{2-d}` with `c_d = 2/((d - 2) ω_d)` for `d ≥ 3`. So the radial test
`φ_r = (b - h_d(r))_+` vanishes inside and equals `b - h_d(r)` outside. The leading term grows by
order `r^{1-d}` over a unit interval, while the error of `eq:kernel-asymptotics` is
`O(|x|^{-d})`. The finitely many inner sites are handled by `h_2(r) → ∞` in the plane, and by
`h_d(r) → 0` with `b < 0` in higher dimensions.
-/

namespace CERW.Support.Coarse

open LatticeProb CERW

variable {d : ℕ}

/-- For `1 < r` and `0 < ρ ≤ r - 1`, the drop of the logarithm from `r` to `ρ` is at least
`1/r`. -/
private lemma one_div_le_log_sub_log_of_sub_one_le {r ρ : ℝ} (hr : 1 < r) (hρ : 0 < ρ)
    (hρr : ρ ≤ r - 1) : 1 / r ≤ Real.log r - Real.log ρ := by
  have hr0 : 0 < r := by linarith
  have hrm1 : 0 < r - 1 := by linarith
  have hle : r / (r - 1) ≤ r / ρ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using one_div_le_one_div_of_le hρ hρr) (le_of_lt hr0)
  have hpos : 0 < r / (r - 1) := div_pos hr0 hrm1
  have hlog := Real.log_le_log hpos hle
  have hone := Real.one_sub_inv_le_log_of_pos hpos
  have hcalc : 1 - (r / (r - 1))⁻¹ = 1 / r := by
    rw [inv_div]
    field_simp
    ring
  have hdiv : Real.log (r / ρ) = Real.log r - Real.log ρ := Real.log_div hr0.ne' hρ.ne'
  rw [hcalc] at hone
  rw [hdiv] at hlog
  linarith

/-- For `0 < r` and `0 < ρ ≤ r/2`, the drop of the logarithm from `r` to `ρ` is at least
`log 2`. -/
private lemma log_two_le_log_sub_log_of_le_half {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hρr : ρ ≤ r / 2) : Real.log 2 ≤ Real.log r - Real.log ρ := by
  have h2 : 2 ≤ r / ρ := by
    rw [le_div_iff₀ hρ]
    linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
  rwa [Real.log_div hr.ne' hρ.ne'] at hlog

/-- For `0 < r` and `r + 1 ≤ ρ`, the rise of the logarithm from `r` to `ρ` is at least
`1/(r+1)`. -/
private lemma inv_add_one_le_log_sub_log {r ρ : ℝ} (hr : 0 < r) (h : r + 1 ≤ ρ) :
    1 / (r + 1) ≤ Real.log ρ - Real.log r := by
  have hr1 : 0 < r + 1 := by linarith
  have hpos : 0 < (r + 1) / r := div_pos hr1 hr
  have hle : (r + 1) / r ≤ ρ / r := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hr))
  have hlog := Real.log_le_log hpos hle
  have hone := Real.one_sub_inv_le_log_of_pos hpos
  have hcalc : 1 - ((r + 1) / r)⁻¹ = 1 / (r + 1) := by
    rw [inv_div]
    field_simp
    ring
  have hρne : ρ ≠ 0 := by linarith
  have hdiv : Real.log (ρ / r) = Real.log ρ - Real.log r := Real.log_div hρne hr.ne'
  rw [hcalc] at hone
  rw [hdiv] at hlog
  linarith

/-- For `0 < r` and `r/2 ≤ ρ`, the reciprocal square of `ρ` is at most `4` times the
reciprocal square of `r`. -/
private lemma rpow_neg_two_le_four_mul {r ρ : ℝ} (hr : 0 < r) (h : r / 2 ≤ ρ) :
    ρ ^ (-2 : ℝ) ≤ 4 * r ^ (-2 : ℝ) := by
  have h2 : 0 < r / 2 := by positivity
  have hle : ρ ^ (-2 : ℝ) ≤ (r / 2) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos h2 h (by norm_num)
  have hcalc : (r / 2) ^ (-2 : ℝ) = 4 * r ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt h2), Real.rpow_neg (le_of_lt hr)]
    field_simp
    norm_num
    ring
  rwa [hcalc] at hle

/-- If `A ≥ 0`, `0 < r` and `2πA ≤ r`, then on `ρ ≥ r/2` the term `A ρ⁻²` is at most
`(2/π) r⁻¹`. -/
private lemma middle_rpow_bound {A r ρ : ℝ} (_hA0 : 0 ≤ A) (hr : 0 < r)
    (hrA : 2 * Real.pi * A ≤ r) (hρ : r / 2 ≤ ρ) :
    A * ρ ^ (-2 : ℝ) ≤ (2 / Real.pi) * r ^ (-1 : ℝ) := by
  have hρ0 : 0 < ρ := by linarith
  have hA_le : A ≤ r / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [hrA]
  have hmono : ρ ^ (-2 : ℝ) ≤ 4 * r ^ (-2 : ℝ) := rpow_neg_two_le_four_mul hr hρ
  calc A * ρ ^ (-2 : ℝ)
      ≤ (r / (2 * Real.pi)) * ρ ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right hA_le (Real.rpow_nonneg (le_of_lt hρ0) _)
    _ ≤ (r / (2 * Real.pi)) * (4 * r ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (2 / Real.pi) * r ^ (-1 : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hr), Real.rpow_neg_one]
        field_simp
        try norm_num
        try ring

/-- If `A ≥ 0`, `0 < r`, `R > 0`, `πA/(2 log 2) ≤ R²` and `R ≤ ρ ≤ r/2`, then
`A ρ⁻² ≤ (2/π)(log r - log ρ)`. -/
private lemma half_rpow_bound {A r ρ R : ℝ} (_hA0 : 0 ≤ A) (hr : 0 < r) (hR : 0 < R)
    (hR2 : Real.pi * A / (2 * Real.log 2) ≤ R ^ 2) (hRρ : R ≤ ρ) (hρ : ρ ≤ r / 2) :
    A * ρ ^ (-2 : ℝ) ≤ (2 / Real.pi) * (Real.log r - Real.log ρ) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hR hRρ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hρ2 : Real.pi * A / (2 * Real.log 2) ≤ ρ ^ 2 :=
    hR2.trans (pow_le_pow_left₀ (le_of_lt hR) hRρ 2)
  have hAle2 : A * Real.pi ≤ (2 * Real.log 2) * ρ ^ 2 := by
    have hdiv := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log 2)).mp hρ2
    nlinarith [hdiv]
  have hAρ : A * ρ ^ (-2 : ℝ) ≤ (2 / Real.pi) * Real.log 2 := by
    rw [Real.rpow_neg (le_of_lt hρ0)]
    norm_num
    rw [show (2 / Real.pi) * Real.log 2 = (2 * Real.log 2) / Real.pi by ring]
    rw [le_div_iff₀ Real.pi_pos]
    calc A * (ρ ^ 2)⁻¹ * Real.pi = (A * Real.pi) * (ρ ^ 2)⁻¹ := by ring
      _ ≤ ((2 * Real.log 2) * ρ ^ 2) * (ρ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hAle2 (by positivity)
      _ = 2 * Real.log 2 := by field_simp
  have hlog : Real.log 2 ≤ Real.log r - Real.log ρ :=
    log_two_le_log_sub_log_of_le_half hr hρ0 hρ
  calc A * ρ ^ (-2 : ℝ) ≤ (2 / Real.pi) * Real.log 2 := hAρ
    _ ≤ (2 / Real.pi) * (Real.log r - Real.log ρ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)

/-- If `A ≥ 0`, `0 < r`, `πA ≤ 2(r+1)` and `r + 1 ≤ ρ`, then
`A ρ⁻² ≤ (2/π)(r+1)⁻¹`. -/
private lemma outer_rpow_bound {A r ρ : ℝ} (_hA0 : 0 ≤ A) (hr : 0 < r)
    (hA : Real.pi * A ≤ 2 * (r + 1)) (hρ : r + 1 ≤ ρ) :
    A * ρ ^ (-2 : ℝ) ≤ (2 / Real.pi) * (r + 1) ^ (-1 : ℝ) := by
  have hr1 : 0 < r + 1 := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hA_le : A ≤ (2 * (r + 1)) / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith [hA]
  have hmono : ρ ^ (-2 : ℝ) ≤ (r + 1) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hr1 hρ (by norm_num : (-2 : ℝ) ≤ 0)
  calc A * ρ ^ (-2 : ℝ)
      ≤ ((2 * (r + 1)) / Real.pi) * ρ ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right hA_le (Real.rpow_nonneg (le_of_lt hρ0) _)
    _ ≤ ((2 * (r + 1)) / Real.pi) * (r + 1) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (2 / Real.pi) * (r + 1) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hr1), Real.rpow_neg_one]
        field_simp
        try norm_num
        try ring

/-- The planar level sets: if `|b(x) - ((2/π) log|x| + κ)| ≤ C_b |x|^{-2}` for `|x| ≥ R_b`,
then for all large `r`, `b ≤ h_2(r)` on `|x| ≤ r - 1` and `b ≥ h_2(r)` on `|x| ≥ r + 1`. -/
theorem exists_levelsets_two {b : Site 2 → ℝ} {κ Cb Rb : ℝ} (hRb : 1 ≤ Rb)
    (hb : ∀ x, Rb ≤ euclidNorm x →
      |b x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤ Cb * euclidNorm x ^ (-2 : ℝ)) :
    ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r → ∀ x : Site 2,
      (euclidNorm x ≤ r - 1 → b x ≤ 2 / Real.pi * Real.log r + κ) ∧
      (r + 1 ≤ euclidNorm x → 2 / Real.pi * Real.log r + κ ≤ b x) := by
  set A : ℝ := max Cb 0 with hA
  have hA0 : 0 ≤ A := le_max_right Cb 0
  have hCbA : Cb ≤ A := le_max_left Cb 0
  set R' : ℝ := max Rb (Real.sqrt (Real.pi * A / (2 * Real.log 2))) + 1 with hR'
  have hR'Rb : Rb ≤ R' := by
    have h1 : Rb ≤ max Rb (Real.sqrt (Real.pi * A / (2 * Real.log 2))) := le_max_left _ _
    rw [hR']; linarith
  have hR'pos : 0 < R' := by
    have h1 : (0 : ℝ) ≤ max Rb (Real.sqrt (Real.pi * A / (2 * Real.log 2))) :=
      le_trans (by linarith : (0 : ℝ) ≤ Rb) (le_max_left _ _)
    rw [hR']; linarith
  have hR'sq : Real.pi * A / (2 * Real.log 2) ≤ R' ^ 2 := by
    have hnonneg : 0 ≤ Real.pi * A / (2 * Real.log 2) := by positivity
    have hs : 0 ≤ Real.sqrt (Real.pi * A / (2 * Real.log 2)) := Real.sqrt_nonneg _
    have hle : Real.sqrt (Real.pi * A / (2 * Real.log 2)) ≤ R' := by
      have h1 : Real.sqrt (Real.pi * A / (2 * Real.log 2)) ≤
          max Rb (Real.sqrt (Real.pi * A / (2 * Real.log 2))) := le_max_right _ _
      rw [hR']; linarith
    have hsq : (Real.sqrt (Real.pi * A / (2 * Real.log 2))) ^ 2 ≤ R' ^ 2 :=
      pow_le_pow_left₀ hs hle 2
    rwa [Real.sq_sqrt hnonneg] at hsq
  set B : ℝ := ∑ x ∈ ballFinset 2 R', |b x| with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact Finset.sum_nonneg (fun x _ => abs_nonneg _)
  have hBbound : ∀ x : Site 2, euclidNorm x ≤ R' → b x ≤ B := by
    intro x hx
    have hmem : x ∈ ballFinset 2 R' := mem_ballFinset_iff.mpr hx
    calc b x ≤ |b x| := le_abs_self _
      _ ≤ B := by
          rw [hB]
          exact Finset.single_le_sum (f := fun y : Site 2 => |b y|)
            (fun y _ => abs_nonneg _) hmem
  have hfin : ∀ᶠ r : ℝ in Filter.atTop, B ≤ 2 / Real.pi * Real.log r + κ := by
    have hpi : 0 < 2 / Real.pi := by positivity
    have htend : Filter.Tendsto (fun r : ℝ => 2 / Real.pi * Real.log r)
        Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.const_mul_atTop hpi
    have hge := htend.eventually_ge_atTop (B - κ)
    filter_upwards [hge] with r hr
    linarith
  have hmain : ∀ᶠ r : ℝ in Filter.atTop, ∀ x : Site 2,
      (euclidNorm x ≤ r - 1 → b x ≤ 2 / Real.pi * Real.log r + κ) ∧
      (r + 1 ≤ euclidNorm x → 2 / Real.pi * Real.log r + κ ≤ b x) := by
    filter_upwards [hfin, Filter.eventually_ge_atTop Rb,
      Filter.eventually_ge_atTop (2 * Real.pi * A)] with r hfin hRbr hmid
    intro x
    constructor
    · intro hx
      by_cases hρR : euclidNorm x ≤ R'
      · exact (hBbound x hρR).trans hfin
      · have hρR' : R' < euclidNorm x := lt_of_not_ge hρR
        have hρ : 0 < euclidNorm x := lt_of_lt_of_le hR'pos (le_of_lt hρR')
        have hρRb : Rb ≤ euclidNorm x := le_trans hR'Rb (le_of_lt hρR')
        have hbd := hb x hρRb
        have hupper : b x ≤ 2 / Real.pi * Real.log (euclidNorm x) + κ +
            Cb * euclidNorm x ^ (-2 : ℝ) := by
          have h2 := (abs_le.mp hbd).2
          linarith
        have hr1 : 1 < r := by linarith
        have hlog_bound : 1 / r ≤ Real.log r - Real.log (euclidNorm x) :=
          one_div_le_log_sub_log_of_sub_one_le hr1 hρ hx
        have hCb_le : Cb * euclidNorm x ^ (-2 : ℝ) ≤
            2 / Real.pi * Real.log r - 2 / Real.pi * Real.log (euclidNorm x) := by
          by_cases hhalf : r / 2 ≤ euclidNorm x
          · have hmidb := middle_rpow_bound hA0 (by linarith : 0 < r) hmid hhalf
            have hCA : Cb * euclidNorm x ^ (-2 : ℝ) ≤ A * euclidNorm x ^ (-2 : ℝ) :=
              mul_le_mul_of_nonneg_right hCbA (Real.rpow_nonneg (le_of_lt hρ) _)
            have hcomp : A * euclidNorm x ^ (-2 : ℝ) ≤
                (2 / Real.pi) * (Real.log r - Real.log (euclidNorm x)) := by
              calc A * euclidNorm x ^ (-2 : ℝ)
                  ≤ (2 / Real.pi) * r ^ (-1 : ℝ) := hmidb
                _ ≤ (2 / Real.pi) * (Real.log r - Real.log (euclidNorm x)) := by
                    apply mul_le_mul_of_nonneg_left _ (by positivity)
                    rw [Real.rpow_neg (le_of_lt (by linarith : 0 < r)), Real.rpow_one]
                    simpa only [one_div] using hlog_bound
            rw [mul_sub] at hcomp
            linarith
          · have hhalf' : euclidNorm x ≤ r / 2 := le_of_lt (lt_of_not_ge hhalf)
            have hhalfb := half_rpow_bound hA0 (by linarith : 0 < r) hR'pos hR'sq
              (le_of_lt hρR') hhalf'
            rw [mul_sub] at hhalfb
            have hCA : Cb * euclidNorm x ^ (-2 : ℝ) ≤ A * euclidNorm x ^ (-2 : ℝ) :=
              mul_le_mul_of_nonneg_right hCbA (Real.rpow_nonneg (le_of_lt hρ) _)
            linarith
        linarith
    · intro hx
      have hr0 : 0 < r := by linarith
      have hρ : 0 < euclidNorm x := by linarith
      have hρRb : Rb ≤ euclidNorm x := by linarith
      have hbd := hb x hρRb
      have hlower : 2 / Real.pi * Real.log (euclidNorm x) + κ -
          Cb * euclidNorm x ^ (-2 : ℝ) ≤ b x := by
        have h2 := (abs_le.mp hbd).1
        linarith
      have hlog_bound : 1 / (r + 1) ≤ Real.log (euclidNorm x) - Real.log r :=
        inv_add_one_le_log_sub_log hr0 hx
      have hAouter : Real.pi * A ≤ 2 * (r + 1) := by nlinarith [hmid]
      have hout := outer_rpow_bound hA0 hr0 hAouter hx
      have hCA : Cb * euclidNorm x ^ (-2 : ℝ) ≤ A * euclidNorm x ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right hCbA (Real.rpow_nonneg (le_of_lt hρ) _)
      have hcomp : Cb * euclidNorm x ^ (-2 : ℝ) ≤
          2 / Real.pi * Real.log (euclidNorm x) - 2 / Real.pi * Real.log r := by
        have hout' : A * euclidNorm x ^ (-2 : ℝ) ≤
            (2 / Real.pi) * (Real.log (euclidNorm x) - Real.log r) := by
          calc A * euclidNorm x ^ (-2 : ℝ)
              ≤ (2 / Real.pi) * (r + 1) ^ (-1 : ℝ) := hout
            _ ≤ (2 / Real.pi) * (Real.log (euclidNorm x) - Real.log r) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                rw [Real.rpow_neg (le_of_lt (by linarith : 0 < r + 1)), Real.rpow_one]
                simpa only [one_div] using hlog_bound
        rw [mul_sub] at hout'
        linarith
      linarith
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hmain
  exact ⟨r₀, fun r hr => hr₀ r hr⟩

/-- For `0 < s ≤ t` and a natural `n`, the drop `t^n - s^n` is at least
`n s^(n-1) (t - s)`. -/
private lemma pow_sub_pow_ge {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (n : ℕ) :
    (n : ℝ) * s ^ (n - 1) * (t - s) ≤ t ^ n - s ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rcases eq_or_lt_of_le hst with h | h
    · subst h; simp
    · have ht : 0 < t := lt_trans hs h
      have ha : -2 ≤ t / s - 1 := by
        have h1 : 0 ≤ t / s - 1 := by
          rw [sub_nonneg]
          exact (one_le_div hs).mpr (le_of_lt h)
        linarith
      have hbern := one_add_mul_le_pow ha n
      have h1 : 1 + (t / s - 1) = t / s := by ring
      rw [h1] at hbern
      have hmul := mul_le_mul_of_nonneg_right hbern (le_of_lt (pow_pos hs n))
      have hsp : s ^ n = s ^ (n - 1) * s := by
        conv_lhs => rw [← Nat.sub_add_cancel hn]
        rw [pow_succ]
      have hleft : (1 + (n:ℝ) * (t / s - 1)) * s ^ n
          = s ^ n + (n:ℝ) * s ^ (n - 1) * (t - s) := by
        rw [hsp]; field_simp
      have hright : (t / s) ^ n * s ^ n = t ^ n := by
        rw [div_pow]; field_simp
      rw [hleft, hright] at hmul
      linarith

/-- Under `D ω 2^(d-3) ≤ ρ ≤ r - 1`, the error `D ρ^(-d)` is bounded by the radial drop
`c_d (ρ^(2-d) - r^(2-d))`. -/
private lemma inner_d_compare {d : ℕ} (hd : 3 ≤ d) {D ρ r : ℝ} (_hD : 0 ≤ D)
    (hω : 0 < unitBallVolume d) (hρ : 1 ≤ ρ) (hr : ρ ≤ r - 1)
    (hbig : D * unitBallVolume d * 2 ^ (d - 3) ≤ ρ) :
    D * ρ ^ (-(d:ℝ)) ≤
      2 / (((d:ℝ) - 2) * unitBallVolume d) * (ρ ^ (2 - (d:ℝ)) - r ^ (2 - (d:ℝ))) := by
  set n : ℕ := d - 2 with hn
  have hn1 : 1 ≤ n := by omega
  have hdc : (d:ℝ) = (n:ℝ) + 2 := by
    rw [hn, Nat.cast_sub (show 2 ≤ d by omega)]; ring
  have hdd : -(d:ℝ) = -((n:ℝ)+2) := by rw [hdc]
  have h2d : 2 - (d:ℝ) = -(n:ℝ) := by rw [hdc]; ring
  have hd2 : (d:ℝ) - 2 = (n:ℝ) := by rw [hdc]; ring
  have hbig' : D * unitBallVolume d * 2 ^ (n - 1) ≤ ρ := by
    have : d - 3 = n - 1 := by omega
    rwa [this] at hbig
  have hpow : D * unitBallVolume d * (2:ℝ)^n ≤ 2 * ρ := by
    have h2n : (2:ℝ)^n = 2 * (2:ℝ)^(n-1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1, pow_succ]
      ring
    rw [h2n]; nlinarith [hbig']
  have hgain : (n:ℝ) / (2:ℝ) ^ n * ρ ^ (-((n:ℝ) + 1)) ≤
      ρ ^ (-(n:ℝ)) - r ^ (-(n:ℝ)) := by
    have hρpos : 0 < ρ := by linarith
    have hρ1pos : 0 < ρ + 1 := by linarith
    have hrr : r ^ (-(n:ℝ)) ≤ (ρ+1) ^ (-(n:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hρ1pos (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg n))
    refine le_trans ?_ (show ρ ^ (-(n:ℝ)) - (ρ+1) ^ (-(n:ℝ)) ≤
      ρ ^ (-(n:ℝ)) - r ^ (-(n:ℝ)) by linarith [hrr])
    have hsub : ρ ^ (-(n:ℝ)) - (ρ+1) ^ (-(n:ℝ))
        = (((ρ+1)^n) - ρ^n) / (ρ^n * (ρ+1)^n) := by
      rw [Real.rpow_neg (le_of_lt hρpos), Real.rpow_neg (le_of_lt hρ1pos)]
      norm_num
      rw [inv_sub_inv (pow_ne_zero n hρpos.ne') (pow_ne_zero n hρ1pos.ne')]
    rw [hsub]
    have hge : (n:ℝ) * ρ ^ (n - 1) * ((ρ+1) - ρ) ≤ (ρ+1)^n - ρ^n :=
      pow_sub_pow_ge hρpos (by linarith) n
    rw [add_sub_cancel_left, mul_one] at hge
    have hden : 0 < ρ ^ n * (ρ+1) ^ n := by positivity
    have h2 : (n:ℝ) * ρ ^ (n - 1) / (ρ^n * (ρ+1)^n) ≤
        (((ρ+1)^n) - ρ^n) / (ρ^n * (ρ+1)^n) :=
      div_le_div_of_nonneg_right hge (le_of_lt hden)
    refine le_trans ?_ h2
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast hn1
    have hsp : ρ ^ n = ρ ^ (n - 1) * ρ := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1, pow_succ]
    have hpow' : (ρ + 1) ^ n ≤ (2:ℝ) ^ n * ρ ^ n := by
      have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ρ + 1)
        (by linarith : ρ + 1 ≤ 2 * ρ) n
      rwa [mul_pow] at this
    have hcross : ρ * (ρ + 1) ^ n ≤ (2:ℝ) ^ n * ρ ^ (n + 1) := by
      have h1 := mul_le_mul_of_nonneg_left hpow' (le_of_lt hρpos)
      calc ρ * (ρ + 1) ^ n ≤ ρ * ((2:ℝ) ^ n * ρ ^ n) := h1
        _ = (2:ℝ) ^ n * ρ ^ (n + 1) := by ring
    have hrw1 : (n:ℝ) / (2:ℝ) ^ n * ρ ^ (-((n:ℝ) + 1))
        = (n:ℝ) / ((2:ℝ) ^ n * ρ ^ (n + 1)) := by
      rw [Real.rpow_neg (le_of_lt hρpos),
        show (n:ℝ) + 1 = ((n+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    have hrw2 : (n:ℝ) * ρ ^ (n - 1) / (ρ^n * (ρ+1)^n) = (n:ℝ) / (ρ * (ρ+1)^n) := by
      rw [hsp]; field_simp
    rw [hrw1, hrw2]
    have hone : 1 / ((2:ℝ) ^ n * ρ ^ (n + 1)) ≤ 1 / (ρ * (ρ+1)^n) :=
      one_div_le_one_div_of_le (by positivity) hcross
    have := mul_le_mul_of_nonneg_left hone (le_of_lt hnpos)
    rwa [mul_one_div, mul_one_div] at this
  rw [hdd, h2d, hd2]
  refine (le_trans ?_ (mul_le_mul_of_nonneg_left hgain
    (by positivity : (0:ℝ) ≤ 2 / ((n:ℝ) * unitBallVolume d))))
  have hkey : D * ρ ^ (-((n:ℝ)+2)) ≤
      (2 / ((n:ℝ) * unitBallVolume d)) * ((n:ℝ) / (2:ℝ)^n * ρ ^ (-((n:ℝ)+1))) := by
    have hρpos : 0 < ρ := by linarith
    have hnne : (n:ℝ) ≠ 0 := by positivity
    have hsplit : ρ ^ (-((n:ℝ)+2)) = ρ ^ (-((n:ℝ)+1)) * ρ ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hρpos (-((n:ℝ)+1)) (-1)]
      congr 1; ring
    rw [hsplit]
    rw [show D * (ρ ^ (-((n:ℝ)+1)) * ρ ^ (-1 : ℝ)) =
        (D * ρ ^ (-1 : ℝ)) * ρ ^ (-((n:ℝ)+1)) by ring]
    rw [show (2/((n:ℝ)*unitBallVolume d)) * ((n:ℝ)/(2:ℝ)^n * ρ ^ (-((n:ℝ)+1))) =
        ((2/((n:ℝ)*unitBallVolume d)) * ((n:ℝ)/(2:ℝ)^n)) * ρ ^ (-((n:ℝ)+1)) by ring]
    rw [mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos hρpos _)]
    rw [Real.rpow_neg_one]
    field_simp [hnne]
    nlinarith [hpow]
  exact hkey

/-- Under `D ω / 2 ≤ r` and `r + 1 ≤ ρ`, the error `D ρ^(-d)` is bounded by the radial drop
`c_d (r^(2-d) - ρ^(2-d))`. -/
private lemma outer_d_compare {d : ℕ} (hd : 3 ≤ d) {D ρ r : ℝ} (_hD : 0 ≤ D)
    (hω : 0 < unitBallVolume d) (hr : 0 < r) (hρ : r + 1 ≤ ρ)
    (hbig : D * unitBallVolume d / 2 ≤ r) :
    D * ρ ^ (-(d:ℝ)) ≤
      2 / (((d:ℝ) - 2) * unitBallVolume d) * (r ^ (2 - (d:ℝ)) - ρ ^ (2 - (d:ℝ))) := by
  set n : ℕ := d - 2 with hn
  have hn1 : 1 ≤ n := by omega
  have hdc : (d:ℝ) = (n:ℝ) + 2 := by
    rw [hn, Nat.cast_sub (show 2 ≤ d by omega)]; ring
  have hdd : -(d:ℝ) = -((n:ℝ)+2) := by rw [hdc]
  have h2d : 2 - (d:ℝ) = -(n:ℝ) := by rw [hdc]; ring
  have hd2 : (d:ℝ) - 2 = (n:ℝ) := by rw [hdc]; ring
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast hn1
  have hρpos : 0 < ρ := by linarith
  have hsp : r ^ n = r ^ (n-1) * r := by
    conv_lhs => rw [← Nat.sub_add_cancel hn1, pow_succ]
  have hden : 0 < r ^ n * ρ ^ n := by positivity
  have hge : (n:ℝ) * r ^ (n - 1) * (ρ - r) ≤ ρ ^ n - r ^ n :=
    pow_sub_pow_ge hr (by linarith) n
  have hge' : (n:ℝ) * r ^ (n - 1) ≤ (n:ℝ) * r ^ (n - 1) * (ρ - r) := by
    have h1 : (1:ℝ) ≤ ρ - r := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ (n:ℝ) * r ^ (n-1))
    simpa using h2
  have hgain : (n:ℝ) / (r * ρ ^ n) ≤ r ^ (-(n:ℝ)) - ρ ^ (-(n:ℝ)) := by
    have hsub : r ^ (-(n:ℝ)) - ρ ^ (-(n:ℝ)) = (ρ ^ n - r ^ n) / (r ^ n * ρ ^ n) := by
      rw [Real.rpow_neg (le_of_lt hr), Real.rpow_neg (le_of_lt hρpos)]
      norm_num
      rw [inv_sub_inv (pow_ne_zero n hr.ne') (pow_ne_zero n hρpos.ne')]
    rw [hsub]
    have hstep : (n:ℝ) * r ^ (n - 1) / (r ^ n * ρ ^ n) ≤ (ρ ^ n - r ^ n) / (r ^ n * ρ ^ n) :=
      (div_le_div_of_nonneg_right hge' (le_of_lt hden)).trans
        (div_le_div_of_nonneg_right hge (le_of_lt hden))
    have heq : (n:ℝ) * r ^ (n - 1) / (r ^ n * ρ ^ n) = (n:ℝ) / (r * ρ ^ n) := by
      rw [hsp]; field_simp
    rwa [heq] at hstep
  rw [hdd, h2d, hd2]
  refine (le_trans ?_ (mul_le_mul_of_nonneg_left hgain
    (by positivity : (0:ℝ) ≤ 2 / ((n:ℝ) * unitBallVolume d))))
  have hkey : D * ρ ^ (-((n:ℝ)+2)) ≤
      (2 / ((n:ℝ) * unitBallVolume d)) * ((n:ℝ) / (r * ρ ^ n)) := by
    have hnne : (n:ℝ) ≠ 0 := by positivity
    have hsplit : ρ ^ (-((n:ℝ)+2)) = ρ ^ (-(n:ℝ)) * ρ ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hρpos (-(n:ℝ)) (-2)]
      congr 1; ring
    rw [hsplit]
    rw [show D * (ρ ^ (-(n:ℝ)) * ρ ^ (-2 : ℝ)) =
        (D * ρ ^ (-2 : ℝ)) * ρ ^ (-(n:ℝ)) by ring]
    rw [show (2/((n:ℝ)*unitBallVolume d)) * ((n:ℝ)/(r * ρ^n)) =
        (2/(unitBallVolume d * r)) * ρ ^ (-(n:ℝ)) by
      rw [Real.rpow_neg (le_of_lt hρpos), Real.rpow_natCast]
      field_simp [hnne]]
    rw [mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos hρpos _)]
    rw [Real.rpow_neg (le_of_lt hρpos)]
    norm_num
    rw [le_div_iff₀ (by positivity : (0:ℝ) < unitBallVolume d * r)]
    field_simp
    nlinarith [hbig, hω, hr, hρpos]
  exact hkey

/-- The level sets for `d ≥ 3`, with `b = -G`: if `G > 0` and
`|G(x) - c_d |x|^{2-d}| ≤ C_G |x|^{-d}` for `|x| ≥ R_G`, then for all large `r`,
`-G ≤ -c_d r^{2-d}` on `|x| ≤ r - 1` and `-G ≥ -c_d r^{2-d}` on `|x| ≥ r + 1`. -/
theorem exists_levelsets {G : Site d → ℝ} {CG RG : ℝ} (hd : 3 ≤ d) (hRG : 1 ≤ RG)
    (hpos : ∀ x, 0 < G x)
    (hG : ∀ x, RG ≤ euclidNorm x →
      |G x - 2 / (((d : ℝ) - 2) * unitBallVolume d) * euclidNorm x ^ (2 - (d : ℝ))| ≤
        CG * euclidNorm x ^ (-(d : ℝ))) :
    ∃ r₀ : ℝ, ∀ r : ℝ, r₀ ≤ r → ∀ x : Site d,
      (euclidNorm x ≤ r - 1 →
        -G x ≤ -(2 / (((d : ℝ) - 2) * unitBallVolume d) * r ^ (2 - (d : ℝ)))) ∧
      (r + 1 ≤ euclidNorm x →
        -(2 / (((d : ℝ) - 2) * unitBallVolume d) * r ^ (2 - (d : ℝ))) ≤ -G x) := by
  set c : ℝ := 2 / (((d : ℝ) - 2) * unitBallVolume d) with hc
  set D : ℝ := max CG 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right CG 0
  have hCGD : CG ≤ D := le_max_left CG 0
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hd2pos : 0 < (d : ℝ) - 2 := by
    have hlt : (2 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 2 < d)
    linarith
  have hcpos : 0 < c := by rw [hc]; positivity
  set R' : ℝ := max RG (D * unitBallVolume d * 2 ^ (d - 3)) + 1 with hR'def
  have hR'RG : RG ≤ R' := by
    have h1 : RG ≤ max RG (D * unitBallVolume d * 2 ^ (d - 3)) := le_max_left _ _
    rw [hR'def]; linarith
  have hR'pos : 0 < R' := by
    have h1 : 0 ≤ max RG (D * unitBallVolume d * 2 ^ (d - 3)) :=
      le_trans (by linarith [hRG]) (le_max_left _ _)
    rw [hR'def]; linarith
  have hR'big : D * unitBallVolume d * 2 ^ (d - 3) ≤ R' := by
    have h1 : D * unitBallVolume d * 2 ^ (d - 3) ≤
        max RG (D * unitBallVolume d * 2 ^ (d - 3)) := le_max_right _ _
    rw [hR'def]; linarith
  have hne : (ballFinset d R').Nonempty :=
    ⟨0, mem_ballFinset_iff.mpr (by simpa using hR'pos.le)⟩
  obtain ⟨xm, _hmxmem, hmxle⟩ := Finset.exists_min_image (ballFinset d R') G hne
  have hmxpos : 0 < G xm := hpos xm
  have hfin : ∀ᶠ r : ℝ in Filter.atTop, c * r ^ (2 - (d : ℝ)) ≤ G xm := by
    have htend : Filter.Tendsto (fun r : ℝ => r ^ (-((d : ℝ) - 2))) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop hd2pos
    have h2 : Filter.Tendsto (fun r : ℝ => c * r ^ (-((d : ℝ) - 2))) Filter.atTop (nhds 0) := by
      simpa using htend.const_mul c
    have h3 := h2.eventually_le_const hmxpos
    filter_upwards [h3] with r hr
    rw [show (2 : ℝ) - (d : ℝ) = -((d : ℝ) - 2) by ring]
    exact hr
  have hmain : ∀ᶠ r : ℝ in Filter.atTop, ∀ x : Site d,
      (euclidNorm x ≤ r - 1 → -G x ≤ -(c * r ^ (2 - (d : ℝ)))) ∧
      (r + 1 ≤ euclidNorm x → -(c * r ^ (2 - (d : ℝ))) ≤ -G x) := by
    filter_upwards [hfin, Filter.eventually_ge_atTop RG,
      Filter.eventually_ge_atTop (D * unitBallVolume d / 2)] with r hfin hrRG hrbig
    intro x
    constructor
    · intro hx
      have hx' : c * r ^ (2 - (d : ℝ)) ≤ G x := by
        by_cases hρR : euclidNorm x ≤ R'
        · exact hfin.trans (hmxle x (mem_ballFinset_iff.mpr hρR))
        · have hρR' : R' < euclidNorm x := lt_of_not_ge hρR
          have hρpos : 0 < euclidNorm x := lt_of_lt_of_le hR'pos (le_of_lt hρR')
          have hρ1 : 1 ≤ euclidNorm x := le_trans (by linarith : 1 ≤ R') (le_of_lt hρR')
          have hρRG : RG ≤ euclidNorm x := le_trans hR'RG (le_of_lt hρR')
          have hρbig : D * unitBallVolume d * 2 ^ (d - 3) ≤ euclidNorm x :=
            le_trans hR'big (le_of_lt hρR')
          have hbd := hG x hρRG
          have hlower : c * euclidNorm x ^ (2 - (d : ℝ)) -
              D * euclidNorm x ^ (-(d : ℝ)) ≤ G x := by
            have h2 := (abs_le.mp hbd).1
            have hCGle : CG * euclidNorm x ^ (-(d : ℝ)) ≤
                D * euclidNorm x ^ (-(d : ℝ)) :=
              mul_le_mul_of_nonneg_right hCGD (Real.rpow_nonneg (le_of_lt hρpos) _)
            linarith
          have hgain := inner_d_compare hd hD0 hω hρ1 hx hρbig
          rw [← hc] at hgain
          rw [mul_sub] at hgain
          linarith
      exact neg_le_neg hx'
    · intro hx
      have hx' : G x ≤ c * r ^ (2 - (d : ℝ)) := by
        have hρpos : 0 < euclidNorm x := by linarith
        have hρRG : RG ≤ euclidNorm x := le_trans hrRG (by linarith)
        have hbd := hG x hρRG
        have hupper : G x ≤ c * euclidNorm x ^ (2 - (d : ℝ)) +
            D * euclidNorm x ^ (-(d : ℝ)) := by
          have h2 := (abs_le.mp hbd).2
          have hCGle : CG * euclidNorm x ^ (-(d : ℝ)) ≤
              D * euclidNorm x ^ (-(d : ℝ)) :=
            mul_le_mul_of_nonneg_right hCGD (Real.rpow_nonneg (le_of_lt hρpos) _)
          linarith
        have hgain := outer_d_compare hd hD0 hω (by linarith : 0 < r) hx hrbig
        rw [← hc] at hgain
        rw [mul_sub] at hgain
        linarith
      exact neg_le_neg hx'
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hmain
  exact ⟨r₀, fun r hr => hr₀ r hr⟩

end CERW.Support.Coarse
