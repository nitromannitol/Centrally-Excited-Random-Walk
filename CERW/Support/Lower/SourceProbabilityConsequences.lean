import CERW.Frozen.FluctuationRates
import CERW.Frozen.LogLowerBounds
import CERW.Frozen.SharpRadii
import CERW.Frozen.SharpWidth
import CERW.Frozen.SharpBulk
import CERW.Frozen.BulkProfile

/-!
# The probabilistic consequences stated after the theorems on fluctuations and sharpness

After `thm:fluctuations` and `thm:sharp` the introduction states consequences of these theorems and
of `prop:log-lower` and `prop:bulk-profile`. For the centrally excited random walk (`IsCERW μ ε X`,
`d ≥ 2`, `0 < ε < 1/d`, radius `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}`), this module proves
each of them with the quantifiers, constants and scales of the source, by applying the proved
estimates.

* `log_lower_and_fluctuation_ae` (l.154): almost surely, for all large `n`, at least one of the
  two radii differs from `r_n` by more than `c log n`, and, for `d ≥ 3`,
  `c log n < R_out(n) - r_n ≤ C (log n)^{d+1}`. The almost sure events of `prop:log-lower` and of
  `thm:fluctuations` are intersected.
* `width_upper_ae` and `width_upper_ae_every_eta` (l.198): in the plane, for every `η > 0`,
  almost surely `R_out(n) - R_in(n) ≤ n^{1/6+η}` for all large `n`; the second theorem takes the
  almost sure event simultaneously for all `η > 0`. The radius bounds of `thm:fluctuations` (i)
  hold almost surely for large `n`, and `C √r_n (log n)^{5/2} + C √(r_n log n) ≤ n^{1/6+η}` for
  large `n`, because `r_n` has order `n^{1/3}`.
* `bulk_upper_sqrt_ball` (l.198): in the plane, for every `p > 0` there is `C` such that for every
  `n ≥ 2`, with probability at least `1 - C n^{-p}`, the maximum over `|x| ≤ √r_n` of
  `|ℓ_n(x) - 2dε (r_n - |x|)|` is at most `C √r_n log n`. This is `prop:bulk-profile` with
  `θ = 1/2`, because `√r_n ≤ r_n / 2` for large `n`; the finitely many remaining times are absorbed
  in `C`.
* `sharp_bulk_dyadic_ae` (l.198): with the constant `c` of `thm:sharp` (iii), almost surely
  `eq:sharp-bulk` holds at `n = 2^k` for all large `k`. The failure probabilities `n^{-c}` at
  `n = 2^k` form a convergent geometric series, and the first Borel–Cantelli lemma applies.
* `planar_width_fluctuation_bound` (l.194): in the plane, for every `p > 0`, with probability at
  least `1 - C n^{-p}`, `R_out(n) - R_in(n) ≤ C √r_n (log n)^{5/2}` for `n ≥ 3`; this is the upper
  bound of `thm:fluctuations` (i) to which the next two theorems are compared.
* `planar_not_improvable` and `planar_exponent_not_lowerable` (l.154, l.194): in the plane, for
  every `p > 0`, no deterministic bound of order `o(√(r_n log n))` on `|R_in(n) - r_n|`, on
  `R_out(n) - r_n` or on `R_out(n) - R_in(n)` fails with probability `O(n^{-p})`; in particular the
  exponent `1/2` of `r_n` cannot be lowered, with any power of `log n`. These apply `thm:sharp` (i)
  and (iv)(a) with the exponent `p/2`.
* `local_times_correct_order` (l.154): for `d ≥ 3`, the bound `C √(r_n log n)` on the local times
  of `thm:fluctuations` (iii) and the lower bound `c √(r_n log n)` of `thm:sharp` (iii) hold
  simultaneously with probability at least `1 - C n^{-c}`, and no bound of order `o(√(r_n log n))`
  holds with probability larger than `n^{-c}`.

The estimates applied are `CERW.Frozen.fluctuation_rates`, `log_lower_bounds`, `sharp_radii`,
`sharp_width`, `sharp_bulk` and `bulk_profile`. No estimate, rate or event is assumed.
-/

universe u

open MeasureTheory Filter Topology Asymptotics
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower.SourceProbabilityConsequences

/-! ## Helpers on the radius `r_n` and on eventual bounds -/

/-- The radius `r_n = ((d+1) n / (2 d ε ω_d))^{1/(d+1)}` is `(κ n)^{1/(d+1)}` with `κ > 0`. -/
private lemma radius_eq {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n : ℕ,
      (((d : ℝ) + 1) * n / (2 * d * ε *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal)) ^ ((1 : ℝ) / (d + 1)) =
        (κ * n) ^ ((1 : ℝ) / (d + 1)) := by
  have hω : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal :=
    CERW.unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨((d : ℝ) + 1) / (2 * d * ε *
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal), by positivity, fun n => ?_⟩
  congr 1
  ring

/-- The radius tends to infinity. -/
private lemma radius_tendsto {d : ℕ} {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (κ * n) ^ ((1 : ℝ) / (d + 1))) atTop atTop :=
  (tendsto_rpow_atTop (by positivity)).comp (tendsto_natCast_atTop_atTop.const_mul_atTop hκ)

/-- A constant times a fixed power of `log n` is eventually below a positive constant times any
positive power of `n`. -/
private lemma eventually_mul_log_rpow_le (A b : ℝ) {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, A * Real.log n ^ b ≤ c * (n : ℝ) ^ s := by
  have hc' : 0 < c / (|A| + 1) := by positivity
  have h := (isLittleO_log_rpow_rpow_atTop b hs).def hc'
  have h2 : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ) ^ b‖ ≤ c / (|A| + 1) * ‖(n : ℝ) ^ s‖ :=
    tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog b),
    Real.norm_of_nonneg (Real.rpow_nonneg hn0 s)] at hn
  have hA : |A| / (|A| + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc A * Real.log n ^ b ≤ |A| * Real.log n ^ b :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (Real.rpow_nonneg hlog b)
    _ ≤ |A| * (c / (|A| + 1) * (n : ℝ) ^ s) := mul_le_mul_of_nonneg_left hn (abs_nonneg A)
    _ = (|A| / (|A| + 1)) * (c * (n : ℝ) ^ s) := by ring
    _ ≤ 1 * (c * (n : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_right hA (mul_nonneg hc.le (Real.rpow_nonneg hn0 s))
    _ = c * (n : ℝ) ^ s := one_mul _

/-- A deterministic sequence of order `o(g)` is eventually below `c g` for every `c > 0`, when `g`
is eventually positive. -/
private lemma eventually_lt_of_isLittleO {a g : ℕ → ℝ} (ha : a =o[atTop] g)
    (hg : ∀ᶠ n : ℕ in atTop, 0 < g n) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, a n < c * g n := by
  filter_upwards [ha.def (half_pos hc), hg] with n hn hgn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hgn] at hn
  have h1 : a n ≤ |a n| := le_abs_self _
  nlinarith

/-- If the events `A n` have probability at least `n^{-q}` and lie in the events `B n`, then the
probabilities of the events `B n` are not of order `O(n^{-p})` for `p > q`. -/
private lemma not_isBigO_of_lower_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : ℕ → Set Ω} {p q : ℝ} (hqp : q < p)
    (hA : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((n : ℝ) ^ (-q)) ≤ μ (A n))
    (hAB : ∀ᶠ n : ℕ in atTop, A n ⊆ B n) :
    ¬ ((fun n : ℕ => (μ (B n)).toReal) =O[atTop] fun n : ℕ => (n : ℝ) ^ (-p)) := by
  intro hO
  obtain ⟨C, hC⟩ := hO.bound
  have hgrow : ∀ᶠ n : ℕ in atTop, C < (n : ℝ) ^ (p - q) :=
    ((tendsto_rpow_atTop (sub_pos.mpr hqp)).comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop C
  obtain ⟨n, h1, h2, h3, h4, hn⟩ :=
    (hC.and (hA.and (hAB.and (hgrow.and (eventually_gt_atTop 0))))).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (n : ℝ) ^ (-q) ≤ (μ (A n)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp h2
  have hAB' : (μ (A n)).toReal ≤ (μ (B n)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h3)
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] at h1
  have h5 : (n : ℝ) ^ (-q) ≤ C * (n : ℝ) ^ (-p) := hq.trans (hAB'.trans h1)
  have h6 : (n : ℝ) ^ (p - q) = (n : ℝ) ^ (-q) * (n : ℝ) ^ p := by
    rw [sub_eq_add_neg, add_comm, Real.rpow_add hn0]
  have h7 : (n : ℝ) ^ (-p) * (n : ℝ) ^ p = 1 := by
    rw [← Real.rpow_add hn0, neg_add_cancel, Real.rpow_zero]
  have hnp : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hn0 _
  have h8 : (n : ℝ) ^ (p - q) ≤ C := by
    rw [h6]
    calc (n : ℝ) ^ (-q) * (n : ℝ) ^ p ≤ C * (n : ℝ) ^ (-p) * (n : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right h5 hnp.le
      _ = C := by rw [mul_assoc, h7, mul_one]
  exact absurd h4 (not_lt.mpr h8)

/-- A power `C₀ r^α (log n)^β` of the radius `r = (κ n)^γ` with `α < 1/2` is `o(√(r log n))`. -/
private lemma isLittleO_exponent {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) {α β : ℝ} (hα : α < 1 / 2)
    (C₀ : ℝ) :
    (fun n : ℕ => C₀ * ((κ * n) ^ γ) ^ α * Real.log n ^ β) =o[atTop]
      fun n : ℕ => Real.sqrt ((κ * n) ^ γ * Real.log n) := by
  set δ : ℝ := γ * (1 / 2 - α) with hδ
  have hδ0 : 0 < δ := mul_pos hγ (by linarith)
  have hkey : Tendsto (fun n : ℕ => Real.log n ^ (β - 1 / 2) / (n : ℝ) ^ δ) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (β - 1 / 2) hδ0).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hratio : ∀ᶠ n : ℕ in atTop,
      (C₀ * ((κ * n) ^ γ) ^ α * Real.log n ^ β) / Real.sqrt ((κ * n) ^ γ * Real.log n) =
        (C₀ * κ ^ (γ * (α - 1 / 2))) * (Real.log n ^ (β - 1 / 2) / (n : ℝ) ^ δ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hL : 0 < Real.log n := Real.log_pos hn1
    have hr : 0 < (κ * n) ^ γ := Real.rpow_pos_of_pos (mul_pos hκ hn0) _
    have hs : Real.sqrt ((κ * n) ^ γ * Real.log n) =
        ((κ * n) ^ γ) ^ ((1 : ℝ) / 2) * Real.log n ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_mul hr.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have hrpow : ((κ * n) ^ γ) ^ (α - 1 / 2) = κ ^ (γ * (α - 1 / 2)) * ((n : ℝ) ^ δ)⁻¹ := by
      rw [← Real.rpow_mul (mul_pos hκ hn0).le, Real.mul_rpow hκ.le hn0.le, ← Real.rpow_neg hn0.le]
      congr 2
      rw [hδ]
      ring
    have hrsub : ((κ * n) ^ γ) ^ α = ((κ * n) ^ γ) ^ ((1 : ℝ) / 2) *
        ((κ * n) ^ γ) ^ (α - 1 / 2) := by
      rw [← Real.rpow_add hr]
      ring_nf
    have hLsub : Real.log n ^ β = Real.log n ^ ((1 : ℝ) / 2) * Real.log n ^ (β - 1 / 2) := by
      rw [← Real.rpow_add hL]
      ring_nf
    have hr2 : 0 < ((κ * n) ^ γ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hr _
    have hL2 : 0 < Real.log n ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hL _
    rw [hs, hrsub, hLsub, hrpow]
    field_simp
  rw [isLittleO_iff_tendsto' (by
    filter_upwards [eventually_ge_atTop 2] with n hn h0
    exfalso
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hr : 0 < (κ * n) ^ γ := Real.rpow_pos_of_pos (mul_pos hκ hn0) _
    have hL : 0 < Real.log n := Real.log_pos hn1
    have : 0 < Real.sqrt ((κ * n) ^ γ * Real.log n) := Real.sqrt_pos.mpr (mul_pos hr hL)
    exact this.ne' h0)]
  have h := hkey.const_mul (C₀ * κ ^ (γ * (α - 1 / 2)))
  rw [mul_zero] at h
  exact h.congr' (hratio.mono fun n hn => hn.symm)

/-! ## Consequence of l.154: the logarithmic lower bound and the fluctuation bound -/

/-- **Almost surely, at least one radius differs from `r_n` by more than `c log n`, and for `d ≥ 3`
the outer radius exceeds `r_n` by more than `c log n` and by at most `C (log n)^{d+1}`** (l.154,
from `thm:fluctuations` and `prop:log-lower`). The constants `c` and `C` depend on `d` and `ε` only
and are chosen before the probability space and the walk. The two almost sure events are
intersected: the late logarithmic lower bound of `prop:log-lower` (the maximum of `r_n - R_in(n)`
and `R_out(n) - r_n` exceeds `c log n`, and `R_out(n) - r_n > c log n` for `d ≥ 3`) and the almost
sure fluctuation bound of `thm:fluctuations` (i), which for `d ≥ 3` gives
`R_out(n) - r_n ≤ C (log n)^{d+1}`. -/
theorem log_lower_and_fluctuation_ae {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          (c * Real.log n < |CERW.innerRadius (X · ω) n - r n| ∨
            c * Real.log n < |CERW.maxRadius (X · ω) n - r n|) ∧
          (3 ≤ d → c * Real.log n < CERW.maxRadius (X · ω) n - r n ∧
            CERW.maxRadius (X · ω) n - r n ≤ C * Real.log n ^ (d + 1)) := by
  intro ωd ε hε hεd r
  obtain ⟨c, Cl, h₀, hc, -, -, n₀, hll⟩ := CERW.Frozen.log_lower_bounds.{u} hd ε hε hεd
  obtain ⟨Cf, hCf, -, hfl⟩ := CERW.Frozen.fluctuation_rates.{u} hd ε hε hεd 1 one_pos
  refine ⟨c, Cf, hc, hCf, fun {Ω} _ μ _ X hX => ?_⟩
  have h1 := (hll μ X hX).2
  have h2 := hfl μ X hX
  filter_upwards [h1, h2] with ω hω1 hω2
  filter_upwards [hω1, hω2] with n hn1 hn2
  refine ⟨?_, fun h3 => ⟨hn1.2 h3, ?_⟩⟩
  · rcases lt_max_iff.mp hn1.1 with h | h
    · left
      have := neg_le_abs (CERW.innerRadius (fun j => X j ω) n - r n)
      rw [neg_sub] at this
      exact h.trans_le this
    · right
      exact h.trans_le (le_abs_self _)
  · have h4 := hn2.1
    rw [if_neg (by omega)] at h4
    have hpow : Real.log n ^ ((d : ℝ) + 1) = Real.log n ^ (d + 1) := by
      rw [← Real.rpow_natCast]
      push_cast
      rfl
    rw [hpow] at h4
    exact h4.2

/-! ## Consequence of l.198: the width is at most `n^{1/6+η}` almost surely -/

/-- The deterministic absorption: for large `n`,
`2 C √((κ n)^{1/3}) (log n)^{5/2} ≤ n^{1/6+η}`. -/
private lemma width_absorb {κ C η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      2 * C * Real.sqrt ((κ * n) ^ ((1 : ℝ) / 3)) * Real.log n ^ ((5 : ℝ) / 2) ≤
        (n : ℝ) ^ ((1 : ℝ) / 6 + η) := by
  filter_upwards [eventually_mul_log_rpow_le (2 * C * κ ^ ((1 : ℝ) / 6)) ((5 : ℝ) / 2) hη
    one_pos, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsq : Real.sqrt ((κ * n) ^ ((1 : ℝ) / 3)) = κ ^ ((1 : ℝ) / 6) * (n : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_pos hκ hn0).le, Real.mul_rpow hκ.le hn0.le]
    norm_num
  rw [hsq, Real.rpow_add hn0]
  calc 2 * C * (κ ^ ((1 : ℝ) / 6) * (n : ℝ) ^ ((1 : ℝ) / 6)) * Real.log n ^ ((5 : ℝ) / 2)
      = (2 * C * κ ^ ((1 : ℝ) / 6) * Real.log n ^ ((5 : ℝ) / 2)) * (n : ℝ) ^ ((1 : ℝ) / 6) := by
        ring
    _ ≤ (1 * (n : ℝ) ^ η) * (n : ℝ) ^ ((1 : ℝ) / 6) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hn0.le _)
    _ = (n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ η := by ring

/-- The deterministic width bound from the two radius bounds of `thm:fluctuations` (i) in the plane,
for `log n ≥ 1`: the width is the sum of the two deviations. -/
private lemma width_le {Rin Rout r L C : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hL : 1 ≤ L)
    (h1 : |Rin - r| ≤ C * Real.sqrt (r * L))
    (h2 : Rout - r ≤ C * Real.sqrt r * L ^ ((5 : ℝ) / 2)) :
    Rout - Rin ≤ 2 * C * Real.sqrt r * L ^ ((5 : ℝ) / 2) := by
  have hL0 : 0 ≤ L := by linarith
  have hsq : Real.sqrt (r * L) ≤ Real.sqrt r * L ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_mul hr, Real.sqrt_eq_rpow L]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have h3 : -(Rin - r) ≤ |Rin - r| := neg_le_abs _
  have h4 : C * Real.sqrt (r * L) ≤ C * (Real.sqrt r * L ^ ((5 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hsq hC
  nlinarith

/-- **In the plane, almost surely, `R_out(n) - R_in(n) ≤ n^{1/6+η}` for all large `n`** (l.198), for
every `η > 0`. The radius bounds of `thm:fluctuations` (i), `|R_in(n) - r_n| ≤ C √(r_n log n)` and
`R_out(n) - r_n ≤ C √r_n (log n)^{5/2}`, hold almost surely for all large `n`, and
`2 C √r_n (log n)^{5/2} ≤ n^{1/6+η}` for large `n` because `r_n = (κ n)^{1/3}`. -/
theorem width_upper_ae {d : ℕ} (hd : d = 2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) → ∀ η : ℝ, 0 < η →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
          CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n ≤
            (n : ℝ) ^ ((1 : ℝ) / 6 + η) := by
  subst hd
  intro ε hε hεd η hη Ω _ μ _ X hX
  obtain ⟨Cf, hCf, -, hfl⟩ := CERW.Frozen.fluctuation_rates.{u} (d := 2) le_rfl ε hε hεd 1 one_pos
  obtain ⟨κ, hκ, hrκ⟩ := radius_eq (d := 2) (by norm_num) hε
  have hexp : ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) = 1 / 3 := by norm_num
  filter_upwards [hfl μ X hX] with ω hω
  filter_upwards [hω, width_absorb (C := Cf) (η := η) hκ hη, eventually_ge_atTop 3]
    with n hn hab hn3
  obtain ⟨⟨h1, h2⟩, -, -⟩ : _ ∧ _ ∧ _ := by
    obtain ⟨h, h', h''⟩ := hn
    rw [if_pos rfl] at h
    exact ⟨h, h', h''⟩
  rw [hrκ n, hexp] at h1 h2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hr0 : 0 ≤ (κ * n) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (mul_pos hκ hn0).le _
  exact (width_le hCf.le hr0 hlog h1 h2).trans hab

/-- **In the plane, almost surely, for every `η > 0` and all large `n`,
`R_out(n) - R_in(n) ≤ n^{1/6+η}`**: the almost sure event of `width_upper_ae` can be taken
simultaneously for all `η > 0`, by intersecting the events for `η = 1/(k+1)`, `k ∈ ℕ`. -/
theorem width_upper_ae_every_eta {d : ℕ} (hd : d = 2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n ≤
            (n : ℝ) ^ ((1 : ℝ) / 6 + η) := by
  intro ε hε hεd Ω _ μ _ X hX
  have h : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n ≤
        (n : ℝ) ^ ((1 : ℝ) / 6 + 1 / ((k : ℝ) + 1)) := fun k =>
    width_upper_ae hd ε hε hεd (1 / ((k : ℝ) + 1)) (by positivity) μ X hX
  filter_upwards [ae_all_iff.mpr h] with ω hω η hη
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
  filter_upwards [hω k, eventually_ge_atTop 1] with n hn hn1
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith))

/-! ## Consequence of l.198: the bulk upper estimate on the ball of radius `√r_n` -/

/-- **In the plane, with high probability, the maximum in `thm:sharp` (iii) is at most
`C √r_n log n`** (l.198, from `prop:bulk-profile`). For every `p > 0` there is `C` such that for
every `n ≥ 2`, with probability at least `1 - C n^{-p}`, every site `x` with `|x| ≤ √r_n` has
`|ℓ_n(x) - 2dε (r_n - |x|)| ≤ C √r_n log n`; the maximum over the finite set of these sites is at
most the same bound. -/
theorem bulk_upper_sqrt_ball {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ ∀ x : Site d, euclidNorm x ≤ Real.sqrt (r n) →
            |(CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * (r n - euclidNorm x)| ≤
              C * (Real.sqrt (r n) * Real.log n)} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  subst hd
  intro ωd ε hε hεd r p hp
  obtain ⟨C₁, hC₁, hGood⟩ := CERW.Frozen.bulk_profile.{u} (d := 2) le_rfl ε hε hεd (1 / 2)
    (by norm_num) (by norm_num) p hp
  obtain ⟨hprob, -⟩ := hGood
  obtain ⟨κ, hκ, hrκ⟩ := radius_eq (d := 2) (by norm_num) hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((radius_tendsto (d := 2) hκ).eventually_ge_atTop 4)
  refine ⟨max C₁ ((N : ℝ) ^ p), lt_max_of_lt_left hC₁, fun {Ω} _ μ _ X hX n hn2 => ?_⟩
  by_cases hnN : N ≤ n
  · have hr4 : 4 ≤ r n := by
      have := hN n hnN
      rw [← hrκ n] at this
      exact this
    refine le_trans (measure_mono ?_) ((hprob μ X hX n hn2).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))))
    intro ω hω hgood
    apply hω
    intro x hx
    have hr0 : 0 ≤ r n := by linarith
    have hsq : Real.sqrt (r n) ≤ (1 / 2) * r n := by
      rw [show (1 : ℝ) / 2 * r n = r n / 2 by ring]
      have h2 : (2 : ℝ) ≤ Real.sqrt (r n) := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hr4
      have h3 : Real.sqrt (r n) * Real.sqrt (r n) = r n := Real.mul_self_sqrt hr0
      nlinarith [Real.sqrt_nonneg (r n)]
    have h := hgood x (hx.trans hsq)
    rw [if_pos rfl] at h
    refine h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n)
  · have hnN' : n < N := not_le.mp hnN
    refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnN0 : (n : ℝ) ≤ N := by exact_mod_cast hnN'.le
    have h1 : 1 ≤ ((N : ℝ) / n) ^ p :=
      Real.one_le_rpow ((one_le_div hn0).mpr hnN0) hp.le
    have h2 : ((N : ℝ) / n) ^ p = (N : ℝ) ^ p * (n : ℝ) ^ (-p) := by
      rw [Real.div_rpow (Nat.cast_nonneg N) hn0.le, Real.rpow_neg hn0.le, div_eq_mul_inv]
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hn0.le _))

/-! ## Consequence of l.198: the sharp lower bound at the dyadic times -/

/-- **`eq:sharp-bulk` holds almost surely at `n = 2^k` for all large `k`** (l.198, from `thm:sharp`
(iii) and the Borel–Cantelli lemma). The constant `c > 0` is that of `thm:sharp` (iii); it depends
on `d` and `ε` only. At `n = 2^k` the failure probability `n^{-c}` of `thm:sharp` (iii) is
`(2^{-c})^k`, a convergent geometric series, so almost surely only finitely many dyadic times
fail. -/
theorem sharp_bulk_dyadic_ae {d : ℕ} (hd : 2 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ∃ x : Site d, euclidNorm x ≤ Real.sqrt (r (2 ^ k)) ∧
          c * (if d = 2 then Real.sqrt (r (2 ^ k)) * Real.log ((2 ^ k : ℕ) : ℝ)
              else Real.sqrt (r (2 ^ k) * Real.log ((2 ^ k : ℕ) : ℝ))) ≤
            |(CERW.localTime (X · ω) (2 ^ k) x : ℝ) -
              2 * d * ε * (r (2 ^ k) - euclidNorm x)| := by
  intro ωd ε hε hεd r
  obtain ⟨c, hc, n₀, hsb⟩ := CERW.Frozen.sharp_bulk.{u} hd ε hε hεd
  refine ⟨c, hc, fun {Ω} _ μ _ X hX => ?_⟩
  set q : ℝ := (2 : ℝ) ^ (-c) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set s : ℕ → Set Ω := fun k => {ω | n₀ ≤ k ∧ ¬ ∃ x : Site d, euclidNorm x ≤ Real.sqrt (r (2 ^ k)) ∧
      c * (if d = 2 then Real.sqrt (r (2 ^ k)) * Real.log ((2 ^ k : ℕ) : ℝ)
          else Real.sqrt (r (2 ^ k) * Real.log ((2 ^ k : ℕ) : ℝ))) ≤
        |(CERW.localTime (X · ω) (2 ^ k) x : ℝ) - 2 * d * ε * (r (2 ^ k) - euclidNorm x)|}
    with hs
  have hsk : ∀ k : ℕ, μ (s k) ≤ ENNReal.ofReal (q ^ k) := by
    intro k
    by_cases hk : n₀ ≤ k
    · have hn : n₀ ≤ 2 ^ k := hk.trans (Nat.lt_two_pow_self).le
      have h := hsb μ X hX (2 ^ k) hn
      have hpow : (((2 ^ k : ℕ) : ℝ)) ^ (-c) = q ^ k := by
        rw [hq, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
      rw [hpow] at h
      refine le_trans (measure_mono ?_) h
      intro ω hω
      exact hω.2
    · have : s k = ∅ := by
        ext ω
        simp only [hs, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h
        exact absurd h hk
      rw [this, measure_empty]
      exact bot_le
  have hsum : (∑' k, μ (s k)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsk)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hq0.le k)
      (summable_geometric_of_lt_one hq0.le hq1)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω, eventually_ge_atTop n₀] with k hk hk₀
  by_contra hcon
  exact hk ⟨hk₀, hcon⟩

/-! ## Consequences of l.154 and l.194: the planar bounds cannot be improved -/

/-- **In the plane, with high probability, `R_out(n) - R_in(n) ≤ C √r_n (log n)^{5/2}`**
(l.194, from `thm:fluctuations` (i)). For every `p > 0` there is `C` such that for every `n ≥ 3`,
with probability at least `1 - C n^{-p}`, the width is at most `C √r_n (log n)^{5/2}`: the sum of
the two radius bounds `C √(r_n log n)` and `C √r_n (log n)^{5/2}` of `thm:fluctuations` (i), for
`log n ≥ 1`. This is the upper bound to which `planar_not_improvable` is compared in the source. -/
theorem planar_width_fluctuation_bound {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 3 ≤ n →
        μ {ω | ¬ (CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n ≤
            C * (Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)))} ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  subst hd
  intro ωd ε hε hεd r p hp
  obtain ⟨C₁, hC₁, hprob, -⟩ := CERW.Frozen.fluctuation_rates.{u} (d := 2) le_rfl ε hε hεd p hp
  obtain ⟨κ, hκ, hrκ⟩ := radius_eq (d := 2) (by norm_num) hε
  refine ⟨2 * C₁, by positivity, fun {Ω} _ μ _ X hX n hn3 => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hr0 : 0 ≤ r n :=
    (lt_of_lt_of_eq (Real.rpow_pos_of_pos (mul_pos hκ hn0) _) (hrκ n).symm).le
  refine le_trans (measure_mono ?_) ((hprob μ X hX n (by omega)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg hn0.le _))))
  intro ω hω hgood
  apply hω
  obtain ⟨h, -, -⟩ := hgood
  rw [if_pos rfl] at h
  calc CERW.maxRadius (fun j => X j ω) n - CERW.innerRadius (fun j => X j ω) n
      ≤ 2 * C₁ * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2) :=
        width_le hC₁.le hr0 hlog h.1 h.2
    _ = 2 * C₁ * (Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)) := by ring

/-- **In the plane, no bound of order `o(√(r_n log n))` on `|R_in(n) - r_n|`, on `R_out(n) - r_n` or
on `R_out(n) - R_in(n)` fails with probability `O(n^{-p})`** (l.194, l.154, from `thm:sharp` (i) and
(iv)(a) with the exponent `p/2`). For every `p > 0`, every realization of the walk and every
deterministic sequence `a` with `a_n = o(√(r_n log n))`, the probabilities of the events
`{|R_in(n) - r_n| > a_n}`, `{R_out(n) - r_n > a_n}` and `{R_out(n) - R_in(n) > a_n}` are each not
`O(n^{-p})`. -/
theorem planar_not_improvable {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ a : ℕ → ℝ, a =o[atTop] (fun n : ℕ => Real.sqrt (r n * Real.log n)) →
          ¬ ((fun n : ℕ => (μ {ω | a n < |CERW.innerRadius (X · ω) n - r n|}).toReal) =O[atTop]
              fun n : ℕ => (n : ℝ) ^ (-p)) ∧
          ¬ ((fun n : ℕ => (μ {ω | a n < CERW.maxRadius (X · ω) n - r n}).toReal) =O[atTop]
              fun n : ℕ => (n : ℝ) ^ (-p)) ∧
          ¬ ((fun n : ℕ => (μ {ω | a n < CERW.maxRadius (X · ω) n -
                CERW.innerRadius (X · ω) n}).toReal) =O[atTop] fun n : ℕ => (n : ℝ) ^ (-p)) := by
  subst hd
  intro ωd ε hε hεd r p hp Ω _ μ _ X hX a ha
  obtain ⟨κ, hκ, hrκ⟩ := radius_eq (d := 2) (by norm_num) hε
  obtain ⟨c, hc, n₀, hrad⟩ := CERW.Frozen.sharp_radii.{u} (d := 2) rfl ε hε hεd (p / 2)
    (half_pos hp)
  obtain ⟨c', hc', n₀', hwid⟩ := (CERW.Frozen.sharp_width.{u} (d := 2) rfl ε hε hεd).1 (p / 2)
    (half_pos hp)
  have hg : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (r n * Real.log n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hr : 0 < r n :=
      lt_of_lt_of_eq (Real.rpow_pos_of_pos (mul_pos hκ hn0) _) (hrκ n).symm
    exact Real.sqrt_pos.mpr (mul_pos hr (Real.log_pos hn1))
  have hqp : p / 2 < p := by linarith
  refine ⟨?_, ?_, ?_⟩
  · refine not_isBigO_of_lower_tail (q := p / 2) hqp
      (A := fun n => {ω | c * Real.sqrt (r n * Real.log n) ≤ r n - CERW.innerRadius (X · ω) n})
      ?_ ?_
    · filter_upwards [eventually_ge_atTop n₀] with n hn
      exact (hrad μ X hX n hn).2.1
    · filter_upwards [eventually_lt_of_isLittleO ha hg hc] with n hn ω hω
      have h1 := neg_le_abs (CERW.innerRadius (fun j => X j ω) n - r n)
      rw [neg_sub] at h1
      exact hn.trans_le (hω.trans h1)
  · refine not_isBigO_of_lower_tail (q := p / 2) hqp
      (A := fun n => {ω | c * Real.sqrt (r n * Real.log n) ≤ CERW.maxRadius (X · ω) n - r n})
      ?_ ?_
    · filter_upwards [eventually_ge_atTop n₀] with n hn
      exact (hrad μ X hX n hn).2.2.2
    · filter_upwards [eventually_lt_of_isLittleO ha hg hc] with n hn ω hω
      exact hn.trans_le hω
  · refine not_isBigO_of_lower_tail (q := p / 2) hqp
      (A := fun n => {ω | c' * Real.sqrt (r n * Real.log n) ≤
        CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n}) ?_ ?_
    · filter_upwards [eventually_ge_atTop n₀'] with n hn
      exact (hwid μ X hX n hn).2
    · filter_upwards [eventually_lt_of_isLittleO ha hg hc'] with n hn ω hω
      exact hn.trans_le hω

/-- **In the plane, the exponent `1/2` of `r_n` in the bounds on the radii and on their difference
cannot be lowered** (l.154): for every `α < 1/2`, every `β` and every `C₀`, the bound
`C₀ r_n^α (log n)^β` on `|R_in(n) - r_n|`, on `R_out(n) - r_n` or on `R_out(n) - R_in(n)` fails with
probability not of order `O(n^{-p})`, for every `p > 0`. It is `planar_not_improvable` for the
sequence `a_n = C₀ r_n^α (log n)^β`, which is `o(√(r_n log n))`. -/
theorem planar_exponent_not_lowerable {d : ℕ} (hd : d = 2) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∀ p : ℝ, 0 < p →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        ∀ α β C₀ : ℝ, α < 1 / 2 →
          ¬ ((fun n : ℕ => (μ {ω | C₀ * r n ^ α * Real.log n ^ β <
                |CERW.innerRadius (X · ω) n - r n|}).toReal) =O[atTop]
              fun n : ℕ => (n : ℝ) ^ (-p)) ∧
          ¬ ((fun n : ℕ => (μ {ω | C₀ * r n ^ α * Real.log n ^ β <
                CERW.maxRadius (X · ω) n - r n}).toReal) =O[atTop]
              fun n : ℕ => (n : ℝ) ^ (-p)) ∧
          ¬ ((fun n : ℕ => (μ {ω | C₀ * r n ^ α * Real.log n ^ β <
                CERW.maxRadius (X · ω) n - CERW.innerRadius (X · ω) n}).toReal) =O[atTop]
              fun n : ℕ => (n : ℝ) ^ (-p)) := by
  have hmain := planar_not_improvable.{u} hd
  subst hd
  intro ωd ε hε hεd r p hp Ω _ μ _ X hX α β C₀ hα
  obtain ⟨κ, hκ, hrκ⟩ := radius_eq (d := 2) (by norm_num) hε
  have hreq : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (((2 : ℕ) : ℝ) + 1)) := fun n => hrκ n
  have ho : (fun n : ℕ => C₀ * r n ^ α * Real.log n ^ β) =o[atTop]
      fun n : ℕ => Real.sqrt (r n * Real.log n) := by
    simp only [hreq]
    exact isLittleO_exponent (by positivity) hκ hα C₀
  exact hmain ε hε hεd p hp μ X hX _ ho

/-! ## Consequence of l.154: the order of the local times in dimension `d ≥ 3` -/

/-- **For `d ≥ 3` the bound on the local times has the correct order** (l.154, from
`thm:fluctuations` (iii) and `thm:sharp` (iii)). There are `c, C > 0` and `n₀`, depending on `d`
and `ε` only, such that for every realization of the walk and every `n ≥ n₀`, with probability at
least `1 - C n^{-c}`, some site has local time deviation `|ℓ_n(x) - 2dε (r_n - |x|)_+|` at least
`c √(r_n log n)` and every site has it at most `C √(r_n log n)`. Moreover, for every deterministic
sequence `a_n = o(√(r_n log n))`, for all large `n` the probability that
`|ℓ_n(x) - 2dε (r_n - |x|)_+| ≤ a_n` holds at every site is at most `n^{-c}`. -/
theorem local_times_correct_order {d : ℕ} (hd : 3 ≤ d) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∀ ε : ℝ, 0 < ε → ε < 1 / (d : ℝ) →
    let r : ℕ → ℝ := fun n => ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
        (∀ n : ℕ, n₀ ≤ n →
          μ {ω | ¬ ((∃ x : Site d, c * Real.sqrt (r n * Real.log n) ≤
                |(CERW.localTime (X · ω) n x : ℝ) - 2 * d * ε * max (r n - euclidNorm x) 0|) ∧
              ∀ x : Site d, |(CERW.localTime (X · ω) n x : ℝ) -
                2 * d * ε * max (r n - euclidNorm x) 0| ≤ C * Real.sqrt (r n * Real.log n))} ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (-c))) ∧
        ∀ a : ℕ → ℝ, a =o[atTop] (fun n : ℕ => Real.sqrt (r n * Real.log n)) →
          ∀ᶠ n : ℕ in atTop,
            μ {ω | ∀ x : Site d, |(CERW.localTime (X · ω) n x : ℝ) -
                2 * d * ε * max (r n - euclidNorm x) 0| ≤ a n} ≤
              ENNReal.ofReal ((n : ℝ) ^ (-c)) := by
  intro ωd ε hε hεd r
  have hd2 : 2 ≤ d := by omega
  obtain ⟨c, hc, n₁, hsb⟩ := CERW.Frozen.sharp_bulk.{u} hd2 ε hε hεd
  obtain ⟨Cf, hCf, hprob, -⟩ := CERW.Frozen.fluctuation_rates.{u} hd2 ε hε hεd c hc
  obtain ⟨κ, hκ, hrκ⟩ := radius_eq (d := d) (by omega) hε
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((radius_tendsto (d := d) hκ).eventually_ge_atTop 1)
  have hsqrt_le : ∀ n : ℕ, N₂ ≤ n → Real.sqrt (r n) ≤ r n := by
    intro n hn
    have hr1 : 1 ≤ r n := by
      have := hN₂ n hn
      rw [← hrκ n] at this
      exact this
    exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  refine ⟨c, 1 + Cf, hc, by positivity, max (max n₁ N₂) 2, fun {Ω} _ μ _ X hX => ⟨?_, ?_⟩⟩
  · intro n hn
    have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hF := hsb μ X hX n hn₁
    have hG := hprob μ X hX n hn2
    have hsum : ENNReal.ofReal ((n : ℝ) ^ (-c)) + ENNReal.ofReal (Cf * (n : ℝ) ^ (-c)) =
        ENNReal.ofReal ((1 + Cf) * (n : ℝ) ^ (-c)) := by
      rw [← ENNReal.ofReal_add (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (mul_nonneg hCf.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
      congr 1
      ring
    refine le_trans (measure_mono ?_)
      (((measure_union_le _ _).trans (add_le_add hF hG)).trans hsum.le)
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hF', hG'⟩ := hcon
    apply hω
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx, hxb⟩ := hF'
      refine ⟨x, ?_⟩
      rw [if_neg (by omega)] at hxb
      have hxr : euclidNorm x ≤ r n := hx.trans (hsqrt_le n hnN₂)
      rw [max_eq_left (by linarith)]
      exact hxb
    · intro x
      have h := hG'.2.2 x
      rw [if_neg (by omega)] at h
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  · intro a ha
    have hg : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (r n * Real.log n) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      have hr : 0 < r n :=
        lt_of_lt_of_eq (Real.rpow_pos_of_pos (mul_pos hκ hn0) _) (hrκ n).symm
      exact Real.sqrt_pos.mpr (mul_pos hr (Real.log_pos hn1))
    filter_upwards [eventually_lt_of_isLittleO ha hg hc,
      eventually_ge_atTop (max (max n₁ N₂) 2)] with n hn hnn
    have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnn
    have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnn
    refine le_trans (measure_mono ?_) (hsb μ X hX n hn₁)
    intro ω hω hF
    obtain ⟨x, hx, hxb⟩ := hF
    rw [if_neg (by omega)] at hxb
    have hxr : euclidNorm x ≤ r n := hx.trans (hsqrt_le n hnN₂)
    have h := hω x
    rw [max_eq_left (by linarith)] at h
    exact absurd (hxb.trans h) (not_le.mpr hn)

end CERW.Support.Lower.SourceProbabilityConsequences
