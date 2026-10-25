module

public import CERW.LimitShapes.BulkProfileProbability.Geometry
public import CERW.LimitShapes.Energy.SiteScales

@[expose] public section

/-!
# Thresholds for the bulk profile

The scale comparisons used in Proposition `prop:bulk-profile` are uniform in the walk law.
-/

open Filter Topology

namespace CERW.LimitShapes

open CERW
open private eventually_log_le_mul width_le from CERW.Support.Lower.BulkProfile

/-- The radius and logarithm eventually satisfy all the bulk scale comparisons. -/
theorem bulk_scales_eventually {d : ℕ} (hd : 2 ≤ d) {κ A θ : ℝ}
    (hκ : 0 < κ) (hA : 0 < A) (hθ : 0 < θ) (hθ1 : θ < 1)
    (r : ℕ → ℝ) (hr : ∀ n, r n = (κ * n) ^ ((1 : ℝ) / (d + 1))) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ r n ∧ 1 ≤ Real.log n ∧
      Real.log n ≤ r n ∧ Real.log (n + 2) ≤ 2 * Real.log n ∧
      A * (if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) ≤
        (1 - θ) / 2 ∧ θ * r n ≤ 2 * n := by
  let c := (1 - θ) / (2 * A)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcs : 0 < min (min c (c ^ 2)) 1 := lt_min (lt_min hc (by positivity)) one_pos
  have hl : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_log_le_mul d hκ hcs, hl, eventually_ge_atTop 2,
    eventually_ge_atTop ⌈κ⌉₊] with n hn hl hn2 hnκ
  rw [← hr n] at hn
  have hr0 : 0 ≤ r n := by rw [hr]; positivity
  have hln : Real.log n ≤ r n := hn.trans (by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (min_le_right (min c (c ^ 2)) 1) hr0)
  have hr1 : 1 ≤ r n := hl.trans hln
  have hrp : 0 < r n := by linarith
  have h1 : Real.log n ≤ c * r n := hn.trans
    (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) hr0)
  have h2 : Real.log n ≤ c ^ 2 * r n := hn.trans
    (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) hr0)
  have hw := width_le d hA hθ1 hr0 h1 h2
  have he : r n * (if d = 2 then Real.sqrt (Real.log n / r n)
      else Real.log n / r n) =
      if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n := by
    split_ifs
    · exact CERW.Support.Norm.ContactAssembly.mul_sqrt_div_eq hrp
    · exact mul_div_cancel₀ _ hrp.ne'
  have hs : A * (if d = 2 then Real.sqrt (Real.log n / r n)
      else Real.log n / r n) ≤ (1 - θ) / 2 := by
    apply (mul_le_mul_iff_right₀ hrp).mp
    calc
      _ = A * (r n * (if d = 2 then Real.sqrt (Real.log n / r n)
          else Real.log n / r n)) := by ring
      _ ≤ _ := by rw [he]; simpa only [mul_comm] using hw
  have hrn : r n ≤ n := by
    have hκn : κ ≤ n := (Nat.le_ceil κ).trans (by exact_mod_cast hnκ)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hpow : r n ^ (d + 1) = κ * n := by
      rw [hr n]
      exact CERW.Support.Geometry.rpow_inv_succ_pow d (by positivity)
    apply (pow_le_pow_iff_left₀ hr0 (by positivity : (0 : ℝ) ≤ n)
      (by omega : d + 1 ≠ 0)).mp
    rw [hpow]
    calc
      κ * n ≤ n * n := mul_le_mul_of_nonneg_right hκn (by positivity)
      _ = (n : ℝ) ^ 2 := by ring
      _ ≤ (n : ℝ) ^ (d + 1) := pow_le_pow_right₀ hn1 (by omega)
  refine ⟨hn2, hr1, hl, hln, ?_, hs, ?_⟩
  · exact_mod_cast (show Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n from by
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      calc
        _ ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
        _ = _ := by rw [Real.log_pow]; norm_num)
  · nlinarith

end CERW.LimitShapes
