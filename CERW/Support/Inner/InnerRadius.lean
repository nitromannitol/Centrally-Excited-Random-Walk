import CERW.Support.Statements
import CERW.Support.Main.LimitShape
import CERW.Support.Main.EventProb
import CERW.Support.Contact.ContactCell
import CERW.Support.Contact.ContactSetup
import CERW.Support.Contact.InradiusArith
import CERW.Support.Contact.Volume
import CERW.Support.Contact.BallExcess
import CERW.Support.Contact.NormReplace
import CERW.Support.Contact.Quadratic
import CERW.Support.Contact.EnvelopeShell
import CERW.Support.Geometry.Bound
import CERW.Generic.Kernel.RadialInner

/-!
# The inner radius of the Euclidean walk (`prop:inner`)

Let `b = R_in(n)` be the inner radius, `E = D_n \ B(0, b)` and `y₀` a contact point. The sign
inequality `eq:contact-sign`, `u_v · (v - y₀) ≥ |v - y₀|²/(2|v|)` for `|v| ≥ |y₀|`, bounds the
volume of `E` by `r_n^{d-1}` times the potential `U_{D_n}(y₀)`, which `lem:contact` (assumed, at
the Euclidean norm with `ξ(x) = u_x`) bounds by `C r_n q_n`. The quadratic martingale then gives
`|b - r_n| ≤ C r_n q_n`, the volume estimate follows, and the ball potential together with the
sup bound of the potential of `E` gives the local-time profile at every point of `ℝ^d`.

The Euclidean instances of the norm statements are obtained from
`normPotential_norm_eq`: for `Ψ = ‖·‖` the gradient is `v/|v|` off the origin.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Inner

open LatticeProb CERW.Support.Statements CERW CERW.Support.Main CERW.Support.Law
  CERW.Support.Contact

variable {d : ℕ}

/-- Splitting the potential over a measurable subset of finite volume. -/
private lemma potential_sdiff_eq (hd : 1 ≤ d) {ε : ℝ}
    {A D : Set (EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) (hD : MeasurableSet D)
    (hDfin : volume D ≠ ⊤) (hAD : A ⊆ D) (y : EuclideanSpace ℝ (Fin d)) :
    potential d ε D y = potential d ε A y + potential d ε (D \ A) y := by
  have hF : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) D :=
    CERW.Support.Geometry.integrableOn_potentialIntegrand hd hD hDfin y
  have hFA : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) A := hF.mono_set hAD
  have hFE : IntegrableOn (fun v : EuclideanSpace ℝ (Fin d) =>
      inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) (D \ A) := hF.mono_set Set.sdiff_subset
  have hunion : A ∪ (D \ A) = D := Set.union_sdiff_cancel hAD
  have hsplit : ∫ v in D, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d =
      (∫ v in A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) +
      (∫ v in D \ A, inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d) := by
    conv_lhs => rw [← hunion]
    exact setIntegral_union Set.disjoint_sdiff_right (hD.diff hA) hFA hFE
  unfold potential
  rw [hsplit]
  ring

/-- Every point `v ≠ y` with `|y| ≤ |v| ≤ R` satisfies
`(2R)^{1-d} ≤ u_v · (v - y) |v - y|^{-d}`: the sign inequality `eq:contact-sign`. -/
private lemma inv_pow_le_potentialIntegrand (hd : 2 ≤ d) {v y : EuclideanSpace ℝ (Fin d)}
    {R : ℝ} (hv : v ≠ 0) (hvy : v ≠ y) (hyv : ‖y‖ ≤ ‖v‖) (hvR : ‖v‖ ≤ R) :
    1 / (2 * R) ^ (d - 1) ≤ inner ℝ (unitDir v) (v - y) / ‖v - y‖ ^ d := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hs : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht : 0 < ‖v - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvy)
  have hR : 0 < R := hs.trans_le hvR
  have hsq := CERW.Generic.Kernel.sq_div_le_inner_unitDir_sub hv hyv
  have htR : ‖v - y‖ ≤ 2 * R := by
    calc ‖v - y‖ ≤ ‖v‖ + ‖y‖ := norm_sub_le v y
      _ ≤ 2 * R := by linarith
  have hk : 2 + k - 1 = k + 1 := by omega
  have h2R : 0 < 2 * R := by positivity
  have hdiv : ‖v - y‖ ^ 2 / (2 * ‖v‖) * (2 * R) ^ (k + 1) ≤
      inner ℝ (unitDir v) (v - y) * (2 * R) ^ (k + 1) :=
    mul_le_mul_of_nonneg_right hsq (by positivity)
  rw [show k + 2 - 1 = k + 1 by omega, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h1 : 2 * ‖v‖ * ‖v - y‖ ^ k ≤ (2 * R) ^ (k + 1) := by
    rw [pow_succ']
    exact mul_le_mul (by linarith) (pow_le_pow_left₀ ht.le htR k) (by positivity) h2R.le
  calc ‖v - y‖ ^ (k + 2) = ‖v - y‖ ^ 2 / (2 * ‖v‖) * (2 * ‖v‖ * ‖v - y‖ ^ k) := by
        field_simp
        ring
    _ ≤ ‖v - y‖ ^ 2 / (2 * ‖v‖) * (2 * R) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ _ := hdiv

/-- The volume of the part of `D` outside the ball `B(0, b)`: if `B(0, b) ⊆ D ⊆ B(0, R)` and
`|y₀| = b`, then `|D \ B(0, b)| ≤ (ω_d/(2ε)) (2R)^{d-1} U_D(y₀)`. -/
private lemma volume_excess_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (hpball : ∀ ρ : ℝ, 0 < ρ → ∀ y : EuclideanSpace ℝ (Fin d),
      potential d ε (Metric.ball 0 ρ) y = 2 * d * ε * max (ρ - ‖y‖) 0)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) {R b : ℝ} (hb : 0 < b)
    (hDR : D ⊆ Metric.ball 0 R) (hball : Metric.ball 0 b ⊆ D)
    {y₀ : EuclideanSpace ℝ (Fin d)} (hy₀ : ‖y₀‖ = b) :
    (volume (D \ Metric.ball 0 b)).toReal ≤
      unitBallVolume d / (2 * ε) * (2 * R) ^ (d - 1) * potential d ε D y₀ := by
  have hd1 : 1 ≤ d := by omega
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hDfin : volume D ≠ ⊤ := (lt_of_le_of_lt (measure_mono hDR) measure_ball_lt_top).ne
  have hEm : MeasurableSet (D \ Metric.ball 0 b) := hD.diff measurableSet_ball
  have hEfin : volume (D \ Metric.ball 0 b) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfin (measure_mono Set.sdiff_subset)
  have hsplit := potential_sdiff_eq hd1 (ε := ε) measurableSet_ball hD hDfin hball y₀
  rw [hpball b hb y₀, hy₀, sub_self, max_self, mul_zero, zero_add] at hsplit
  have hint := CERW.Support.Geometry.integrableOn_potentialIntegrand hd1 hEm hEfin y₀
  have hRpos : 0 < R := by
    obtain ⟨v, hv⟩ : ∃ v, v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b := ⟨0, by simpa using hb⟩
    have := Metric.mem_ball.mp (hDR (hball hv))
    exact lt_of_le_of_lt (dist_nonneg) this
  have hlow : ∫ _v in D \ Metric.ball 0 b, 1 / (2 * R) ^ (d - 1) ≤
      ∫ v in D \ Metric.ball 0 b, inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d := by
    refine setIntegral_mono_ae_restrict (integrableOn_const hEfin) hint ?_
    filter_upwards [ae_restrict_mem hEm,
      ae_restrict_of_ae ((Set.countable_singleton y₀).ae_notMem
        (volume : Measure (EuclideanSpace ℝ (Fin d))))] with v hvE hvne
    have hvb : b ≤ ‖v‖ := by
      have : v ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b := hvE.2
      rwa [Metric.mem_ball, dist_zero_right, not_lt] at this
    have hvR : ‖v‖ ≤ R := by
      have := Metric.mem_ball.mp (hDR hvE.1)
      rw [dist_zero_right] at this
      exact this.le
    exact inv_pow_le_potentialIntegrand hd (norm_pos_iff.mp (hb.trans_le hvb))
      (fun h => hvne (by simpa using h)) (hy₀ ▸ hvb) hvR
  rw [setIntegral_const, Measure.real_def, smul_eq_mul] at hlow
  have hpE : potential d ε (D \ Metric.ball 0 b) y₀ =
      2 * ε / unitBallVolume d *
        ∫ v in D \ Metric.ball 0 b, inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d := rfl
  have hω := unitBallVolume_pos d
  have hpow : 0 < (2 * R) ^ (d - 1) := by positivity
  rw [hsplit, hpE]
  set I := ∫ v in D \ Metric.ball 0 b, inner ℝ (unitDir v) (v - y₀) / ‖v - y₀‖ ^ d with hI
  have hpow' : (2 * R) ^ (d - 1) ≠ 0 := hpow.ne'
  calc (volume (D \ Metric.ball 0 b)).toReal
      = (volume (D \ Metric.ball 0 b)).toReal * (1 / (2 * R) ^ (d - 1)) * (2 * R) ^ (d - 1) := by
        field_simp
    _ ≤ I * (2 * R) ^ (d - 1) := mul_le_mul_of_nonneg_right hlow hpow.le
    _ = unitBallVolume d / (2 * ε) * (2 * R) ^ (d - 1) * (2 * ε / unitBallVolume d * I) := by
        field_simp

/-- The exponent of the rate `Q = (L/N)^e`: `1/2` in the plane and `1` for `d ≥ 3`. -/
private noncomputable def rateExp (d : ℕ) : ℝ := if d = 2 then (1 : ℝ) / 2 else 1

/-- The exponent of the rate is positive. -/
private lemma rateExp_pos (d : ℕ) : 0 < rateExp d := by
  rw [rateExp]
  split_ifs <;> norm_num

/-- The exponent of the rate is at most one. -/
private lemma rateExp_le_one (d : ℕ) : rateExp d ≤ 1 := by
  rw [rateExp]
  split_ifs <;> norm_num

/-- The exponent of the rate is at most `d - 1` for `d ≥ 2`. -/
private lemma rateExp_le_d_sub_one {d : ℕ} (hd : 2 ≤ d) : rateExp d ≤ (d : ℝ) - 1 := by
  have h1 : rateExp d ≤ 1 := rateExp_le_one d
  have h2 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  linarith

/-- The exponent of the rate is at least `1/2`. -/
private lemma half_le_rateExp (d : ℕ) : (1 : ℝ) / 2 ≤ rateExp d := by
  rw [rateExp]
  split_ifs <;> norm_num

/-- The exponent inequality behind `N √(nL) ≤ n Q`. -/
private lemma scaleExp {d : ℕ} (hd : 2 ≤ d) :
    (1 : ℝ) / (d + 1) + 1 / 2 ≤ 1 - ((1 : ℝ) / (d + 1)) * rateExp d := by
  rw [rateExp]
  split_ifs with h2
  · rw [h2]; norm_num
  · have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast (show 3 ≤ d by omega)
    have h4 : (1 : ℝ) / (d + 1) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    rw [mul_one]
    linarith

/-- `log(n + 2) ≥ 1` for `n ≥ 1`. -/
private lemma log_nat_add_two_ge_one {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ Real.log (n + 2) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : (3 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  linarith [Real.exp_one_lt_three]

/-- The exponent `1 - (1 + e)/(d + 1)` is positive. -/
private lemma quadExp_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < 1 - (1 + rateExp d) / (d + 1) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : (0 : ℝ) < d + 1 := by linarith
  rw [sub_pos, div_lt_one hd1]
  have h1 : rateExp d ≤ 1 := rateExp_le_one d
  linarith

/-- The basic rate identity `n (L/n^a)^e = n^{1-ae} L^e`. -/
private lemma mul_rate_eq {n L e a : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    n * (L / n ^ a) ^ e = n ^ (1 - a * e) * L ^ e := by
  rw [Real.div_rpow hL (Real.rpow_nonneg hn.le a), ← Real.rpow_mul hn.le]
  have h2 : n * n ^ (-(a * e)) = n ^ (1 - a * e) := by
    nth_rewrite 1 [← Real.rpow_one n]
    rw [← Real.rpow_add hn]
    rw [show (1 : ℝ) + -(a * e) = 1 - a * e by ring]
  calc n * (L ^ e / n ^ (a * e))
      = (n * n ^ (-(a * e))) * L ^ e := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hn.le]
        ring
    _ = n ^ (1 - a * e) * L ^ e := by rw [h2]

/-- The scale times `√(nL)` as a single product of powers. -/
private lemma scale_mul_sqrt_eq {d : ℕ} {n L : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    n ^ ((1 : ℝ) / (d + 1)) * Real.sqrt (n * L) =
      n ^ ((1 : ℝ) / (d + 1) + 1 / 2) * L ^ ((1 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hn.le hL]
  have h1 : n ^ ((1 : ℝ) / (d + 1)) * (n ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2)) =
      (n ^ ((1 : ℝ) / (d + 1)) * n ^ ((1 : ℝ) / 2)) * L ^ ((1 : ℝ) / 2) := by
    ring
  rw [h1, ← Real.rpow_add hn]

/-- `N^σ ≤ Q` whenever `σ ≤ -e` and `n ≥ 1`, `e ≥ 0`. -/
private lemma rpow_scale_le_rate {d : ℕ} {n : ℕ} {e σ : ℝ} (hn : 1 ≤ n) (he0 : 0 ≤ e)
    (hσ : σ ≤ -e) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ σ ≤
      (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ e := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (n + 2) := log_nat_add_two_ge_one hn
  have hL0 : (0 : ℝ) ≤ Real.log (n + 2) := le_trans zero_le_one hL1
  have hN0 : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hnpos _
  rw [← Real.rpow_mul hn0, Real.div_rpow hL0 hN0.le, ← Real.rpow_mul hn0]
  have hLe : (1 : ℝ) ≤ Real.log (n + 2) ^ e := Real.one_le_rpow hL1 he0
  have hden : (0 : ℝ) < (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) :=
    Real.rpow_pos_of_pos hnpos _
  have hfrac : (1 : ℝ) / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) ≤
      Real.log (n + 2) ^ e / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) :=
    div_le_div_of_nonneg_right hLe hden.le
  have hone : (1 : ℝ) / (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * e) =
      (n : ℝ) ^ (-(((1 : ℝ) / (d + 1)) * e)) := by
    rw [Real.rpow_neg hn0, inv_eq_one_div]
  have hmono : (n : ℝ) ^ (((1 : ℝ) / (d + 1)) * σ) ≤
      (n : ℝ) ^ (-(((1 : ℝ) / (d + 1)) * e)) := by
    refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    have h2 : ((1 : ℝ) / (d + 1)) * σ ≤ ((1 : ℝ) / (d + 1)) * (-e) :=
      mul_le_mul_of_nonneg_left hσ (by positivity)
    linarith
  rw [hone] at hfrac
  linarith

/-- `N √(nL) ≤ n Q` for `n ≥ 1`. -/
private lemma scale_mul_sqrt_le_n_rate {d : ℕ} {n : ℕ} {e : ℝ} (hn : 1 ≤ n)
    (he : (1 : ℝ) / 2 ≤ e)
    (hexp : (1 : ℝ) / (d + 1) + 1 / 2 ≤ 1 - ((1 : ℝ) / (d + 1)) * e) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) * Real.sqrt (n * Real.log (n + 2)) ≤
      (n : ℝ) * (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ e := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (n + 2) := log_nat_add_two_ge_one hn
  have hL0 : (0 : ℝ) ≤ Real.log (n + 2) := le_trans zero_le_one hL1
  rw [scale_mul_sqrt_eq hnpos hL0, mul_rate_eq hnpos hL0]
  refine mul_le_mul ?_ ?_ (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hn0 _)
  · refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
    linarith [hexp]
  · exact Real.rpow_le_rpow_of_exponent_le hL1 he

/-- `N L ≤ n Q` for `n ≥ 1` once `L ≤ n^c` with `1/(d+1) + c = 1 - e/(d+1)`. -/
private lemma scale_mul_log_le_n_rate {d : ℕ} {n : ℕ} {e c : ℝ} (hn : 1 ≤ n) (he0 : 0 ≤ e)
    (hc : (1 : ℝ) / (d + 1) + c = 1 - ((1 : ℝ) / (d + 1)) * e)
    (hLc : Real.log (n + 2) ≤ (n : ℝ) ^ c) :
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) * Real.log (n + 2) ≤
      (n : ℝ) * (Real.log (n + 2) / (n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ e := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (n + 2) := log_nat_add_two_ge_one hn
  have hL0 : (0 : ℝ) ≤ Real.log (n + 2) := le_trans zero_le_one hL1
  rw [mul_rate_eq hnpos hL0]
  have hLe : (1 : ℝ) ≤ Real.log (n + 2) ^ e := Real.one_le_rpow hL1 he0
  have hbase : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2) ≤
      (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) := by
    have h1 : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2) ≤
        (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ c :=
      mul_le_mul_of_nonneg_left hLc (Real.rpow_nonneg hn0 _)
    have h2 : (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ c =
        (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) := by
      rw [← Real.rpow_add hnpos]
      rw [hc]
    rwa [h2] at h1
  calc (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * Real.log (n + 2)
      ≤ (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) := hbase
    _ ≤ (n : ℝ) ^ (1 - ((1 : ℝ) / (d + 1)) * e) * Real.log (n + 2) ^ e := by
        rw [le_mul_iff_one_le_right (Real.rpow_pos_of_pos hnpos _)]
        exact hLe

/-- `eq:inradius`: there are `C` and `n₀` such that, for `n ≥ n₀`, a path from the origin with
`B(0, b) ⊆ D_n ⊆ B̄(0, K N)`, `|X_n| ≤ K N`, `|A_n| ≤ K N^d`, excess volume at most
`C₁ N^d Q`, and quadratic martingale at most `C₁ (N √(nL) + N L)` has `|b/N - a| ≤ C Q`. -/
private theorem exists_inradius_rate (hd : 2 ≤ d) {ε K C₁ : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ) (b : ℝ),
      n₀ ≤ n →
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := (L / N) ^ rateExp d
      X 0 ω = 0 → 0 ≤ b →
      Metric.ball 0 b ⊆ cellSet (fun j => X j ω) n →
      cellSet (fun j => X j ω) n ⊆ Metric.closedBall 0 (K * N) →
      euclidNorm (X n ω) ≤ K * N →
      ((departureRange (fun j => X j ω) n).card : ℝ) ≤ K * N ^ d →
      (volume (cellSet (fun j => X j ω) n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal
        ≤ C₁ * N ^ d * Q →
      |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|
        ≤ C₁ * (N * Real.sqrt (n * L) + N * L) →
        |b / N - ((d + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))| ≤ C * Q := by
  let C₁' : ℝ := K ^ 2 + (Real.sqrt d / 2 * K) + K * C₁ + 2 * C₁ + 1
  have hC₁'val : C₁' = K ^ 2 + (Real.sqrt d / 2 * K) + K * C₁ + 2 * C₁ + 1 := rfl
  have hC₁' : 0 ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    linarith
  obtain ⟨C, hCpos, hC⟩ := exists_abs_div_sub_le hd hε (C₁ := C₁') hC₁'
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    ((CERW.Support.Main.tendsto_log_rpow_div_rpow 1 (quadExp_pos hd)).eventually_lt_const
      one_pos)
  refine ⟨C, hCpos, max n₁ 1, ?_⟩
  intro Ω X ω n b hmn N L Q hX0 hb hball hDsub hXn hA hEvol hQn
  have hn : 1 ≤ n := le_trans (le_max_right n₁ 1) hmn
  have hn₁' : n₁ ≤ n := le_trans (le_max_left n₁ 1) hmn
  have hNpos : 0 < N := by
    dsimp only [N]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hNnonneg : 0 ≤ N := le_of_lt hNpos
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    exact log_nat_add_two_ge_one hn
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hQeq : Q = (L / N) ^ rateExp d := rfl
  have hQnonneg : 0 ≤ Q := by
    rw [hQeq]
    exact Real.rpow_nonneg (div_nonneg hL0 hNnonneg) _
  have hNpow : N ^ (d + 1) = (n : ℝ) := by
    dsimp only [N]
    have hx : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [show (1 : ℝ) / (d + 1) = (((d + 1 : ℕ) : ℝ))⁻¹ by
      rw [one_div, Nat.cast_add, Nat.cast_one]]
    exact Real.rpow_inv_natCast_pow hx (by omega)
  let S : ℝ := ∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x
  let I : ℝ := ∫ v in cellSet (fun j => X j ω) n, ‖v‖
  let IE : ℝ :=
    ∫ v in cellSet (fun j => X j ω) n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b, ‖v‖
  let Qn : ℝ := dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω
  let Xsq : ℝ := euclidNorm (X n ω) ^ 2
  have hX : Xsq = (n : ℝ) - 2 * ε * S + Qn := by
    dsimp only [Xsq, S, Qn]
    exact sq_euclidNorm_eq (by omega : 1 ≤ d) ε X ω hX0 n
  have hX_nonneg : 0 ≤ Xsq := by
    dsimp only [Xsq]
    positivity
  have hK2 : K ^ 2 ≤ C₁' := by
    rw [hC₁'val]
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    have h4 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    linarith
  have hXub : Xsq ≤ C₁' * N ^ 2 := by
    dsimp only [Xsq]
    calc euclidNorm (X n ω) ^ 2 ≤ (K * N) ^ 2 :=
          pow_le_pow_left₀ (euclidNorm_nonneg _) hXn 2
      _ = K ^ 2 * N ^ 2 := by ring
      _ ≤ C₁' * N ^ 2 := mul_le_mul_of_nonneg_right hK2 (sq_nonneg N)
  have hsqrtK : Real.sqrt d / 2 * K ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h4 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    linarith
  have hSI : |S - I| ≤ C₁' * N ^ d := by
    have h := abs_sum_euclidNorm_sub_integral_le (fun j => X j ω) n
    dsimp only [S, I]
    calc |∑ x ∈ departureRange (fun j => X j ω) n, euclidNorm x -
          ∫ v in cellSet (fun j => X j ω) n, ‖v‖|
        ≤ Real.sqrt d / 2 * ((departureRange (fun j => X j ω) n).card : ℝ) := h
      _ ≤ Real.sqrt d / 2 * (K * N ^ d) := mul_le_mul_of_nonneg_left hA (by positivity)
      _ = (Real.sqrt d / 2 * K) * N ^ d := by ring
      _ ≤ C₁' * N ^ d := mul_le_mul_of_nonneg_right hsqrtK (by positivity)
  have hballadd := integral_norm_eq_ball_add (d := d) (by omega : 1 ≤ d)
      (CERW.Support.Occupation.measurableSet_cellSet (fun j => X j ω) n) hb hball hDsub
  have hI : I = d * unitBallVolume d * b ^ (d + 1) / (d + 1) + IE := by
    dsimp only [I, IE]
    exact hballadd.1
  have hIE0 : 0 ≤ IE := by
    dsimp only [IE]
    exact hballadd.2.1
  have hKC₁ : K * C₁ ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    have h4 : (0 : ℝ) ≤ 2 * C₁ := by linarith
    linarith
  have hIEub : IE ≤ C₁' * n * Q := by
    have h3 := hballadd.2.2
    dsimp only [IE] at h3 ⊢
    have hKN : (0 : ℝ) ≤ K * N := mul_nonneg hK.le hNnonneg
    have hnQ : (0 : ℝ) ≤ (n : ℝ) * Q := mul_nonneg (Nat.cast_nonneg n) hQnonneg
    have hstep : (K * N) * (volume (cellSet (fun j => X j ω) n \
        Metric.ball 0 b)).toReal ≤ (K * N) * (C₁ * N ^ d * Q) :=
      mul_le_mul_of_nonneg_left hEvol hKN
    calc ∫ v in cellSet (fun j => X j ω) n \ Metric.ball 0 b, ‖v‖
        ≤ (K * N) * (volume (cellSet (fun j => X j ω) n \
            Metric.ball 0 b)).toReal := h3
      _ ≤ (K * N) * (C₁ * N ^ d * Q) := hstep
      _ = K * C₁ * (N * N ^ d) * Q := by ring
      _ = K * C₁ * N ^ (d + 1) * Q := by rw [← pow_succ']
      _ = K * C₁ * (n : ℝ) * Q := by rw [hNpow]
      _ = (K * C₁) * ((n : ℝ) * Q) := by ring
      _ ≤ C₁' * ((n : ℝ) * Q) := mul_le_mul_of_nonneg_right hKC₁ hnQ
      _ = C₁' * (n : ℝ) * Q := by ring
  have hexp : (1 : ℝ) / (d + 1) + 1 / 2 ≤ 1 - ((1 : ℝ) / (d + 1)) * rateExp d :=
    scaleExp hd
  have hc : (1 : ℝ) / (d + 1) + (1 - (1 + rateExp d) / (d + 1)) =
      1 - ((1 : ℝ) / (d + 1)) * rateExp d := by
    field_simp
    ring
  have hLc : L ≤ (n : ℝ) ^ (1 - (1 + rateExp d) / (d + 1)) := by
    have hlt := hn₁ n hn₁'
    dsimp only [L] at hlt ⊢
    rw [Real.rpow_one] at hlt
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hcp : (0 : ℝ) < (n : ℝ) ^ (1 - (1 + rateExp d) / (d + 1)) :=
      Real.rpow_pos_of_pos hnpos _
    rw [div_lt_one hcp] at hlt
    exact le_of_lt hlt
  have hQn_ev : N * Real.sqrt (n * L) ≤ (n : ℝ) * Q ∧ N * L ≤ (n : ℝ) * Q := by
    constructor
    · rw [hQeq]
      exact scale_mul_sqrt_le_n_rate hn (half_le_rateExp d) hexp
    · rw [hQeq]
      exact scale_mul_log_le_n_rate hn (rateExp_pos d).le hc hLc
  have h2C₁ : 2 * C₁ ≤ C₁' := by
    rw [hC₁'val]
    have h1 : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
    have h2 : (0 : ℝ) ≤ K * C₁ := mul_nonneg hK.le hC₁
    have h3 : (0 : ℝ) ≤ Real.sqrt d / 2 * K := by positivity
    linarith
  have hQnub : |Qn| ≤ C₁' * n * Q := by
    dsimp only [Qn]
    have hsum : N * Real.sqrt (n * L) + N * L ≤ 2 * ((n : ℝ) * Q) := by
      linarith [hQn_ev.1, hQn_ev.2]
    have hnQ : (0 : ℝ) ≤ (n : ℝ) * Q := mul_nonneg (Nat.cast_nonneg n) hQnonneg
    calc |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω|
        ≤ C₁ * (N * Real.sqrt (n * L) + N * L) := hQn
      _ ≤ C₁ * (2 * ((n : ℝ) * Q)) := mul_le_mul_of_nonneg_left hsum hC₁
      _ = (2 * C₁) * ((n : ℝ) * Q) := by ring
      _ ≤ C₁' * ((n : ℝ) * Q) := mul_le_mul_of_nonneg_right h2C₁ hnQ
      _ = C₁' * (n : ℝ) * Q := by ring
  have hNQ1 : N ^ (1 - (d : ℝ)) ≤ Q := by
    rw [hQeq]
    refine rpow_scale_le_rate hn (rateExp_pos d).le ?_
    linarith [rateExp_le_d_sub_one hd]
  have hNQ2 : N⁻¹ ≤ Q := by
    rw [hQeq]
    have h := rpow_scale_le_rate (d := d) (n := n) (e := rateExp d) (σ := -1) hn
      (rateExp_pos d).le (by linarith [rateExp_le_one d])
    simpa only [Real.rpow_neg_one] using h
  exact hC n b S I IE Qn Xsq Q hn hb hQnonneg hX hX_nonneg hXub hSI hI hIE0 hIEub
    hQnub hNQ1 hNQ2


/-- Eventually `K ≤ N`, `L³ ≤ N`, `N² ≤ n` and `1 ≤ n`, where `N = n^{1/(d+1)}` and
`L = log(n + 2)`. -/
private lemma eventually_scales (hd : 1 ≤ d) (K : ℝ) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    K ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ∧
    Real.log (n + 2) ^ 3 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) ∧
    ((n : ℝ) ^ ((1 : ℝ) / (d + 1))) ^ 2 ≤ n ∧ 1 ≤ n := by
  have hc : (0 : ℝ) < 1 / (d + 1) := by positivity
  have h1 : ∀ᶠ n : ℕ in atTop, K ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
    ((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  have h2 : ∀ᶠ n : ℕ in atTop,
      Real.log (n + 2) ^ (3 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) < 1 :=
    (tendsto_log_rpow_div_rpow 3 hc).eventually_lt_const one_pos
  have h3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hK, hL, h1n⟩ := hn₀ n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨hK, ?_, ?_, h1n⟩
  · rw [div_lt_one hNpos] at hL
    have e : Real.log (n + 2) ^ (3 : ℕ) = Real.log (n + 2) ^ (3 : ℝ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [e]; exact hL.le
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    calc (n : ℝ) ^ ((1 : ℝ) / (d + 1) * ((2 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hn1
          have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          push_cast
          linarith
      _ = n := Real.rpow_one _

/-- The error scale of the global approximation is at most `2 (√C₀ + 1) N Q^{1/d}` once
`1 ≤ L`, `L³ ≤ N` and `M ≤ C₀ N`, where `Q = (L/N)^e` is the rate. -/
private lemma error_le_scale (hd : 2 ≤ d) {M C₀ N L : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀)
    (hL : 1 ≤ L) (hLN : L ^ 3 ≤ N) (hMN : M ≤ C₀ * N) :
    (if d = 2 then Real.sqrt M * L + L else Real.sqrt (M * L) + L) ≤
      2 * (Real.sqrt C₀ + 1) * (N * ((L / N) ^ rateExp d) ^ ((1 : ℝ) / d)) := by
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hN1 : 1 ≤ N := hL3.trans hLN
  have hN : 0 < N := by linarith
  have hLN' : L ≤ N := (le_self_pow₀ hL (by norm_num)).trans hLN
  have ht : 0 < L / N := div_pos (by linarith) hN
  have ht1 : L / N ≤ 1 := (div_le_one hN).2 hLN'
  obtain ⟨h2e, h3e⟩ := CERW.Support.Contact.error_scale_le hM hC₀ hMN hN1 hL
  have hs : 0 ≤ Real.sqrt C₀ + 1 := by positivity
  split_ifs with h2
  · have he : rateExp d = 1 / 2 := by rw [rateExp, if_pos h2]
    rw [he]
    subst h2
    have key : Real.sqrt N * L ≤ N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) := by
      have hq : ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) =
          (L / N) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_mul ht.le]; norm_num
      rw [hq]
      apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
      have h4 : ((L / N) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = L / N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
      have hsN : Real.sqrt N ^ (4 : ℕ) = N ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hN.le]
      rw [mul_pow, mul_pow, h4, hsN]
      have e : N ^ 4 * (L / N) = N ^ 3 * L := by field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left hLN (by positivity : 0 ≤ N ^ 2 * L)
      nlinarith
    calc Real.sqrt M * L + L ≤ (Real.sqrt C₀ + 1) * (Real.sqrt N * L) := h2e
      _ ≤ (Real.sqrt C₀ + 1) * (N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by
          gcongr
      _ ≤ 2 * (Real.sqrt C₀ + 1) *
            (N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by
          have : 0 ≤ (Real.sqrt C₀ + 1) *
              (N * ((L / N) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ))) := by positivity
          linarith
  · have he : rateExp d = 1 := by rw [rateExp, if_neg h2]
    rw [he, Real.rpow_one]
    have hd3 : (3 : ℝ) ≤ d := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    have hexp : (1 : ℝ) / d ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hQ : (L / N) ^ ((1 : ℝ) / 2) ≤ (L / N) ^ ((1 : ℝ) / d) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 hexp
    have hsq : Real.sqrt (N * L) = N * (L / N) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, show N * L = N ^ 2 * (L / N) by field_simp,
        Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le]
    have hLsq : L ≤ Real.sqrt (N * L) := by
      calc L = Real.sqrt (L * L) := (Real.sqrt_mul_self (by linarith)).symm
        _ ≤ Real.sqrt (N * L) := Real.sqrt_le_sqrt (by nlinarith)
    calc Real.sqrt (M * L) + L ≤ (Real.sqrt C₀ + 1) * (Real.sqrt (N * L) + L) := h3e
      _ ≤ (Real.sqrt C₀ + 1) * (2 * Real.sqrt (N * L)) := by gcongr; linarith
      _ = 2 * (Real.sqrt C₀ + 1) * (N * (L / N) ^ ((1 : ℝ) / 2)) := by rw [hsq]; ring
      _ ≤ 2 * (Real.sqrt C₀ + 1) * (N * (L / N) ^ ((1 : ℝ) / d)) := by gcongr

/-- `(N ^ d) ^ (1 / d) = N` for `N ≥ 0` and `d > 0`. -/
private lemma rpow_natCast_inv_self {N : ℝ} (hN : 0 ≤ N) (hd : 0 < d) :
    (N ^ d) ^ ((1 : ℝ) / d) = N := by
  have hdR : (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  rw [← Real.rpow_natCast N d, ← Real.rpow_mul hN]
  have hmul : (d : ℝ) * ((1 : ℝ) / (d : ℝ)) = 1 := by field_simp
  rw [hmul, Real.rpow_one]

/-- Raising the excess-volume bound to the power `1 / d`. -/
private lemma volume_rpow_inv_le {m C₁ N Q : ℝ} (hm0 : 0 ≤ m) (hC₁ : 0 ≤ C₁)
    (hN : 0 ≤ N) (hQ : 0 ≤ Q) (hm : m ≤ C₁ * N ^ d * Q) (hd : 0 < d) :
    m ^ ((1 : ℝ) / d) ≤ C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : 0 ≤ (1 : ℝ) / d := le_of_lt (div_pos one_pos hdR)
  calc m ^ ((1 : ℝ) / d) ≤ (C₁ * N ^ d * Q) ^ ((1 : ℝ) / d) :=
        Real.rpow_le_rpow hm0 hm hp
    _ = C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d) := by
        rw [Real.mul_rpow (mul_nonneg hC₁ (pow_nonneg hN d)) hQ,
            Real.mul_rpow hC₁ (pow_nonneg hN d)]
        rw [rpow_natCast_inv_self hN hd]

/-- The local-time profile at every point of `ℝ^d`: under the global approximation, the
inradius, excess-volume and error bounds, `ℓ̃_n(y)` is within `C N Q^{1/d}` of the cone
`2dε (aN - |y|)_+`. -/
private theorem abs_cellLocalTime_sub_cone_le (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {Cg : ℝ}
    (hCg : 0 ≤ Cg)
    (hpball : ∀ ρ : ℝ, 0 < ρ → ∀ y : EuclideanSpace ℝ (Fin d),
      potential d ε (Metric.ball 0 ρ) y = 2 * d * ε * max (ρ - ‖y‖) 0)
    (hpbound : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |potential d ε D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d))
    {a C₁ K : ℝ} (hC₁ : 0 ≤ C₁) (hK : a + 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ → Site d) (n : ℕ) (b δ₀ N Q : ℝ), 0 < N → 0 ≤ Q → Q ≤ 1 →
      0 < b → Metric.ball 0 b ⊆ cellSet X n → cellSet X n ⊆ Metric.ball 0 ((K - 1) * N) →
      |b - a * N| ≤ C₁ * N * Q →
      (volume (cellSet X n \ Metric.ball 0 b)).toReal ≤ C₁ * N ^ d * Q →
      δ₀ ≤ C₁ * N * Q ^ ((1 : ℝ) / d) →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ < K * N →
        |cellLocalTime X n y - potential d ε (cellSet X n) y| ≤ δ₀) →
      ∀ y : EuclideanSpace ℝ (Fin d),
        |cellLocalTime X n y - 2 * d * ε * max (a * N - ‖y‖) 0| ≤ C * (N * Q ^ ((1 : ℝ) / d)) := by
  have hdpos : 0 < d := by omega
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hp_le_one : (1 : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hdR]
    simpa using hdR1
  let Cd : ℝ := Cg * ε
  have hCd0 : 0 ≤ Cd := mul_nonneg hCg hε.le
  have hCpos : 0 < C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁ + 1 := by
    have h1 : 0 ≤ Cd * C₁ ^ ((1 : ℝ) / d) := mul_nonneg hCd0 (Real.rpow_nonneg hC₁ _)
    have h2 : 0 ≤ 2 * (d : ℝ) * ε * C₁ := by positivity
    linarith
  refine ⟨C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁ + 1, hCpos, ?_⟩
  intro X n b δ₀ N Q hN hQ0 hQle hb hball hDsub hba hvol hδ hall y
  have hNpos : 0 < N := hN
  have hQp0 : 0 ≤ Q ^ ((1 : ℝ) / d) := Real.rpow_nonneg hQ0 _
  have hQleQp : Q ≤ Q ^ ((1 : ℝ) / d) := Real.self_le_rpow_of_le_one hQ0 hQle hp_le_one
  by_cases hy : ‖y‖ < K * N
  · have hlocal : |cellLocalTime X n y - potential d ε (cellSet X n) y| ≤ δ₀ := hall y hy
    have hDmeas : MeasurableSet (cellSet X n) :=
      CERW.Support.Occupation.measurableSet_cellSet X n
    have hEmeas : MeasurableSet (cellSet X n \ Metric.ball 0 b) :=
      hDmeas.diff measurableSet_ball
    have hDfin : volume (cellSet X n) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono hDsub) measure_ball_lt_top).ne
    have hEbdd : Bornology.IsBounded (cellSet X n \ Metric.ball 0 b) :=
      (Metric.isBounded_ball.subset hDsub).subset Set.sdiff_subset
    have hsplit : potential d ε (cellSet X n) y =
        potential d ε (Metric.ball 0 b) y +
        potential d ε (cellSet X n \ Metric.ball 0 b) y :=
      potential_sdiff_eq hd1 measurableSet_ball hDmeas hDfin hball y
    have hUB : potential d ε (Metric.ball 0 b) y = 2 * (d : ℝ) * ε * max (b - ‖y‖) 0 :=
      hpball b hb y
    have hmle : (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / d) ≤
        C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d) :=
      volume_rpow_inv_le ENNReal.toReal_nonneg hC₁ hN.le hQ0 hvol hdpos
    have hUE : |potential d ε (cellSet X n \ Metric.ball 0 b) y| ≤
        Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) := by
      calc |potential d ε (cellSet X n \ Metric.ball 0 b) y|
          ≤ Cd * (volume (cellSet X n \ Metric.ball 0 b)).toReal ^ ((1 : ℝ) / d) :=
            hpbound _ hEmeas hEbdd y
        _ ≤ Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) :=
            mul_le_mul_of_nonneg_left hmle hCd0
    have hUBdiff : |potential d ε (Metric.ball 0 b) y -
        2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0| ≤
        2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) := by
      rw [hUB]
      have hcoef : 0 ≤ 2 * (d : ℝ) * ε := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hcoef]
      have hmaxle : |max (b - ‖y‖) 0 - max (a * N - ‖y‖) 0| ≤ C₁ * N * Q := by
        have h1 := abs_max_sub_max_le_abs (b - ‖y‖) (a * N - ‖y‖) 0
        have h2 : (b - ‖y‖) - (a * N - ‖y‖) = b - a * N := by ring
        rw [h2] at h1
        exact h1.trans hba
      calc 2 * (d : ℝ) * ε * |max (b - ‖y‖) 0 - max (a * N - ‖y‖) 0|
          ≤ 2 * (d : ℝ) * ε * (C₁ * N * Q) := mul_le_mul_of_nonneg_left hmaxle hcoef
        _ = 2 * (d : ℝ) * ε * C₁ * N * Q := by ring
        _ ≤ 2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) := by
            have hQstep : C₁ * N * Q ≤ C₁ * N * Q ^ ((1 : ℝ) / d) :=
              mul_le_mul_of_nonneg_left hQleQp (mul_nonneg hC₁ hN.le)
            calc 2 * (d : ℝ) * ε * C₁ * N * Q
                = 2 * (d : ℝ) * ε * (C₁ * N * Q) := by ring
              _ ≤ 2 * (d : ℝ) * ε * (C₁ * N * Q ^ ((1 : ℝ) / d)) :=
                  mul_le_mul_of_nonneg_left hQstep hcoef
              _ = 2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) := by ring
    have htri : |(cellLocalTime X n y - potential d ε (cellSet X n) y) +
          potential d ε (cellSet X n \ Metric.ball 0 b) y +
          (potential d ε (Metric.ball 0 b) y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0)| ≤
        |cellLocalTime X n y - potential d ε (cellSet X n) y| +
          |potential d ε (cellSet X n \ Metric.ball 0 b) y| +
          |potential d ε (Metric.ball 0 b) y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0| := by
      have h1 := abs_add_le (cellLocalTime X n y - potential d ε (cellSet X n) y)
          (potential d ε (cellSet X n \ Metric.ball 0 b) y)
      have h2 := abs_add_le
          ((cellLocalTime X n y - potential d ε (cellSet X n) y) +
            potential d ε (cellSet X n \ Metric.ball 0 b) y)
          (potential d ε (Metric.ball 0 b) y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0)
      linarith
    have hdecomp : cellLocalTime X n y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0 =
        (cellLocalTime X n y - potential d ε (cellSet X n) y) +
          potential d ε (cellSet X n \ Metric.ball 0 b) y +
          (potential d ε (Metric.ball 0 b) y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0) := by
      rw [hsplit]
      ring
    calc |cellLocalTime X n y - 2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0|
        = |(cellLocalTime X n y - potential d ε (cellSet X n) y) +
            potential d ε (cellSet X n \ Metric.ball 0 b) y +
            (potential d ε (Metric.ball 0 b) y -
              2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0)| := by rw [hdecomp]
      _ ≤ |cellLocalTime X n y - potential d ε (cellSet X n) y| +
          |potential d ε (cellSet X n \ Metric.ball 0 b) y| +
          |potential d ε (Metric.ball 0 b) y -
            2 * (d : ℝ) * ε * max (a * N - ‖y‖) 0| := htri
      _ ≤ C₁ * N * Q ^ ((1 : ℝ) / d) +
          Cd * (C₁ ^ ((1 : ℝ) / d) * N * Q ^ ((1 : ℝ) / d)) +
          2 * (d : ℝ) * ε * C₁ * N * Q ^ ((1 : ℝ) / d) :=
          add_le_add (add_le_add (hlocal.trans hδ) hUE) hUBdiff
      _ = (C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁) * (N * Q ^ ((1 : ℝ) / d)) := by
          ring
      _ ≤ (C₁ + Cd * C₁ ^ ((1 : ℝ) / d) + 2 * (d : ℝ) * ε * C₁ + 1) *
            (N * Q ^ ((1 : ℝ) / d)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hN.le hQp0)
          linarith
  · have hKN : K * N ≤ ‖y‖ := le_of_not_gt hy
    have hynot : y ∉ cellSet X n := by
      intro hymem
      have hlt := Metric.mem_ball.mp (hDsub hymem)
      rw [dist_zero_right] at hlt
      have hle : (K - 1) * N ≤ K * N := mul_le_mul_of_nonneg_right (by linarith) hN.le
      linarith
    have hloc0 : cellLocalTime X n y = 0 :=
      CERW.Support.Occupation.cellLocalTime_eq_zero_of_not_mem X n hynot
    have hmax0 : max (a * N - ‖y‖) 0 = 0 := by
      apply max_eq_right
      have : a * N ≤ K * N := mul_le_mul_of_nonneg_right (by linarith) hN.le
      linarith
    rw [hloc0, hmax0]
    simp only [mul_zero, sub_zero, abs_zero]
    exact mul_nonneg hCpos.le (mul_nonneg hN.le hQp0)

/-- The rate `q_n = (log n/(aN))^e` and the rate `Q = (log(n + 2)/N)^e` are comparable:
`a^e q_n ≤ Q ≤ 2^e a^e q_n` for `n ≥ 2`. -/
private lemma rate_compare {n : ℕ} (hn : 2 ≤ n) {a N e : ℝ} (ha : 0 < a) (hN : 0 < N)
    (he : 0 ≤ e) :
    a ^ e * (Real.log n / (a * N)) ^ e ≤ (Real.log (n + 2) / N) ^ e ∧
    (Real.log (n + 2) / N) ^ e ≤ 2 ^ e * (a ^ e * (Real.log n / (a * N)) ^ e) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlogL : Real.log n ≤ Real.log (n + 2) := Real.log_le_log hn0 (by linarith)
  have hLlog : Real.log (n + 2) ≤ 2 * Real.log n := by
    have h1 : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n := by
      rw [Real.log_pow]; norm_num
    rw [← h1]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hmul : a ^ e * (Real.log n / (a * N)) ^ e = (Real.log n / N) ^ e := by
    rw [← Real.mul_rpow ha.le (div_nonneg hlog0 (mul_nonneg ha.le hN.le))]
    congr 1
    field_simp
  rw [hmul]
  refine ⟨Real.rpow_le_rpow (div_nonneg hlog0 hN.le) (div_le_div_of_nonneg_right hlogL hN.le) he,
    ?_⟩
  calc (Real.log (n + 2) / N) ^ e ≤ (2 * (Real.log n / N)) ^ e := by
        apply Real.rpow_le_rpow (div_nonneg (hlog0.trans hlogL) hN.le) _ he
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right hLlog hN.le
    _ = 2 ^ e * (Real.log n / N) ^ e :=
        Real.mul_rpow (by norm_num) (div_nonneg hlog0 hN.le)

/-- The gradient of the Euclidean norm at a nonzero point is the direction `v/|v|`. -/
theorem gradient_norm_eq_unitDir {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    gradient (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) v = CERW.unitDir v := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := (hasStrictFDerivAt_norm_sq v).hasFDerivAt.sqrt (by positivity)
  have h2 : (fun w : EuclideanSpace ℝ (Fin d) => Real.sqrt (‖w‖ ^ 2)) =
      fun w => ‖w‖ := by
    funext w
    exact Real.sqrt_sq (norm_nonneg w)
  rw [h2] at h1
  have h4 : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) (CERW.unitDir v) =
      (1 / (2 * √(‖v‖ ^ 2))) • 2 • (innerSL ℝ) v := by
    ext w
    simp only [InnerProductSpace.toDual_apply_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Real.sqrt_sq hpos.le, CERW.unitDir,
      real_inner_smul_left]
    norm_num
    field_simp
  have h3 : HasGradientAt (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) (CERW.unitDir v) v := by
    rw [hasGradientAt_iff_hasFDerivAt, h4]
    exact h1
  exact h3.gradient

/-- For the Euclidean norm, the norm potential `eq:potential-norm` is the potential
`eq:potential-intro`, since the gradient is `v/|v|` off the origin. -/
theorem normPotential_norm_eq (hd : 1 ≤ d) (ε : ℝ) (D : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) :
    CERW.normPotential d ε (fun w : EuclideanSpace ℝ (Fin d) => ‖w‖) D y =
      CERW.potential d ε D y := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  unfold CERW.normPotential CERW.potential
  congr 1
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [(Set.countable_singleton (0 : EuclideanSpace ℝ (Fin d))).ae_notMem
    (volume : Measure (EuclideanSpace ℝ (Fin d)))] with v hv
  rw [gradient_norm_eq_unitDir hv]

/-- The volume of the Euclidean unit ball, written as the volume of `{|v| < 1}`. -/
theorem normBallVolume_norm : CERW.normBallVolume (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) =
    unitBallVolume d := by
  unfold CERW.normBallVolume CERW.unitBallVolume
  congr 2
  ext v
  simp

/-- The deterministic core of the inner-radius estimates. On the event of the fluctuation
theorem's proof, for large `n`, a contact-point bound `U_{D_n}(y₀) ≤ C_c r_n q_n` at every contact
point `y₀` gives the inner radius, the volume and the local-time profile estimates. -/
private theorem inner_core (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) {b₀ : Site d → ℝ}
    {C₀ C₁ Cc Cg : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hCc : 0 < Cc) (hCg : 0 ≤ Cg) {bd r₀ : ℕ}
    (hpball : ∀ ρ : ℝ, 0 < ρ → ∀ y : EuclideanSpace ℝ (Fin d),
      potential d ε (Metric.ball 0 ρ) y = 2 * d * ε * max (ρ - ‖y‖) 0)
    (hpbound : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |potential d ε D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d)) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ {Ω : Type*} (X : ℕ → Ω → Site d) (ω : Ω) (n : ℕ), n₀ ≤ n →
      let r : ℝ := ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
      let q : ℝ := if d = 2 then Real.sqrt (Real.log n / r) else Real.log n / r
      fluctEvent d ε b₀ C₀ C₁ bd r₀ X ω n →
      (∀ y₀ : EuclideanSpace ℝ (Fin d), ‖y₀‖ = innerRadius (fun j => X j ω) n →
          y₀ ∈ closure (cellSet (fun j => X j ω) n)ᶜ →
          potential d ε (cellSet (fun j => X j ω) n) y₀ ≤ Cc * r * q) →
      |innerRadius (fun j => X j ω) n - r| ≤ C * r * q ∧
      volume ((r⁻¹ • cellSet (fun j => X j ω) n) ∆
          Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ ENNReal.ofReal (C * q) ∧
      ∀ y : EuclideanSpace ℝ (Fin d),
        |cellLocalTime (fun j => X j ω) n y - 2 * d * ε * max (r - ‖y‖) 0|
          ≤ C * r * q ^ ((1 : ℝ) / d) := by
  intro ωd
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hωpos : 0 < ωd := unitBallVolume_pos d
  have hbase : 0 < ((d : ℝ) + 1) / (2 * d * ε * ωd) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hbase _
  have he0 : 0 < rateExp d := rateExp_pos d
  have hae : 0 < a ^ rateExp d := Real.rpow_pos_of_pos ha _
  set CE : ℝ := ωd / (2 * ε) * (2 * (C₀ + 1)) ^ (d - 1) * Cc * a * (a ^ rateExp d)⁻¹ with hCE
  have hCEpos : 0 < CE := by positivity
  set cQ : ℝ := 2 ^ rateExp d * a ^ rateExp d with hcQ
  have hcQpos : 0 < cQ := by positivity
  set C₄ : ℝ := max (1 / a) (CE / a ^ d) with hC₄
  have hC₄nn : 0 ≤ C₄ := le_max_of_le_left (by positivity)
  set C₂ : ℝ := max (max (2 * C₁ * (Real.sqrt C₀ + 1)) CE) (max C₁ CE) with hC₂
  have hC₂nn : 0 ≤ C₂ := le_max_of_le_left (le_max_of_le_left (by positivity))
  obtain ⟨Cs, -, hcs⟩ := exists_contact_setup hd
  obtain ⟨Ci, hCi, ni, hir⟩ := exists_inradius_rate hd hε (K := C₀ + 2) (C₁ := max C₁ CE)
    (by linarith only [hC₀]) (le_max_of_le_left hC₁.le)
  obtain ⟨Cv, hCv, hvol⟩ := exists_volume_symmDiff_add_le (d := d) hd1 (a := 1)
    (C₁ := max C₄ (Ci / a)) one_pos (le_max_of_le_left hC₄nn)
  obtain ⟨Cp, hCp, hprof⟩ := abs_cellLocalTime_sub_cone_le hd hε hCg hpball hpbound (a := a)
    (C₁ := max C₂ Ci) (K := a + C₀ + 3) (le_max_of_le_left hC₂nn) (by linarith only [hC₀])
  obtain ⟨ns, hns⟩ := eventually_scales hd1 (max (a + C₀ + 3) (Real.sqrt d + 1))
  refine ⟨max (max (Ci * cQ / a) (Cv * cQ)) (Cp * cQ ^ ((1 : ℝ) / d) / a),
    lt_max_of_lt_left (lt_max_of_lt_left (by positivity)), max (max ni ns) 2, ?_⟩
  intro Ω X ω n hn r q hE hcont
  have hni : ni ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnsn : ns ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hKN, hL3, hN2, h1n⟩ := hns n hnsn
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN_def
  set L : ℝ := Real.log (n + 2) with hL_def
  set Q : ℝ := (L / N) ^ rateExp d with hQ_def
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hsd : Real.sqrt d + 1 ≤ N := (le_max_right _ _).trans hKN
  have hK'N : a + C₀ + 3 ≤ N := (le_max_left _ _).trans hKN
  have hN1 : 1 ≤ N := by linarith only [hsd, Real.sqrt_nonneg (d : ℝ)]
  have hNpos : 0 < N := by linarith only [hN1]
  have hL1 : 1 ≤ L := by
    rw [hL_def, Real.le_log_iff_exp_le (by positivity)]
    linarith only [Real.exp_one_lt_d9, hn1]
  have hL0 : 0 ≤ L := by linarith only [hL1]
  have hLN : L ≤ N := (le_self_pow₀ hL1 (by norm_num)).trans hL3
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg (div_nonneg hL0 hNpos.le) _
  have hQ1 : Q ≤ 1 :=
    Real.rpow_le_one (div_nonneg hL0 hNpos.le) ((div_le_one hNpos).2 hLN) he0.le
  have hNd : 0 ≤ N ^ d := pow_nonneg hNpos.le d
  have hr : r = a * N := by
    show (((d : ℝ) + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) = a * N
    rw [show ((d : ℝ) + 1) * n / (2 * d * ε * ωd) =
      (((d : ℝ) + 1) / (2 * d * ε * ωd)) * n by ring]
    exact Real.mul_rpow hbase.le (Nat.cast_nonneg n)
  have hrpos : 0 < r := by rw [hr]; positivity
  have hq : q = (Real.log n / (a * N)) ^ rateExp d := by
    show (if d = 2 then Real.sqrt (Real.log n / r) else Real.log n / r) = _
    rw [hr]
    by_cases h2 : d = 2
    · rw [if_pos h2, rateExp, if_pos h2, Real.sqrt_eq_rpow]
    · rw [if_neg h2, rateExp, if_neg h2, Real.rpow_one]
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact Real.rpow_nonneg (div_nonneg hlog0 (by positivity)) _
  obtain ⟨hcmp1, hcmp2⟩ := rate_compare hn2 ha hNpos he0.le
  rw [← hq] at hcmp1 hcmp2
  have hQq : Q ≤ cQ * q := by
    rw [hQ_def, hcQ]
    calc (L / N) ^ rateExp d ≤ 2 ^ rateExp d * (a ^ rateExp d * q) := hcmp2
      _ = 2 ^ rateExp d * a ^ rateExp d * q := by ring
  have hqQ : q ≤ (a ^ rateExp d)⁻¹ * Q := by
    rw [inv_mul_eq_div, le_div_iff₀ hae]
    calc q * a ^ rateExp d = a ^ rateExp d * q := by ring
      _ ≤ Q := hcmp1
  dsimp only [fluctEvent] at hE
  obtain ⟨⟨h0, -⟩, hcard, hM, hH, -, hglob, -, -, hquad, -, -⟩ := hE
  have hM0 : (0 : ℝ) ≤ (maxLocalTime (fun j => X j ω) n : ℝ) := Nat.cast_nonneg _
  have hD : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((C₀ + 1) * N) :=
    (CERW.Support.Occupation.cellSet_subset_ball hd1 (fun j => X j ω) n).trans
      (Metric.ball_subset_ball (by linarith only [hH, hsd]))
  have hDmeas : MeasurableSet (cellSet (fun j => X j ω) n) :=
    CERW.Support.Occupation.measurableSet_cellSet _ n
  have hDfin : volume (cellSet (fun j => X j ω) n) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hD) measure_ball_lt_top).ne
  have hR1 : 1 ≤ (C₀ + 1) * N := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (C₀ + 1) * N :=
          mul_le_mul (by linarith only [hC₀]) hN1 zero_le_one (by linarith only [hC₀])
  obtain ⟨hb', hball', -⟩ := hcs ε hε.le (fun j => X j ω) n ((C₀ + 1) * N) h1n h0 hR1 hD
  set b : ℝ := innerRadius (fun j => X j ω) n with hb_def
  have hb : 0 < b := hb'
  have hball : Metric.ball 0 b ⊆ cellSet (fun j => X j ω) n := hball'
  -- a contact point in the closure of the complement
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hRpos : 0 < (C₀ + 1) * N := by positivity
  obtain ⟨y₁, hy₁⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin d)))
    (r := (C₀ + 1) * N)).mpr hRpos.le
  have hy₁c : y₁ ∉ cellSet (fun j => X j ω) n := by
    intro hy
    have h := Metric.mem_ball.mp (hD hy)
    rw [dist_zero_right] at h
    have h' : ‖y₁‖ = (C₀ + 1) * N := by simpa using (mem_sphere_iff_norm.mp hy₁)
    linarith only [h, h']
  obtain ⟨y₀, hy₀cl, hy₀norm⟩ := exists_mem_closure_norm_eq_sInf (d := d)
    (E := (cellSet (fun j => X j ω) n)ᶜ) ⟨y₁, hy₁c⟩
  have hy₀b : ‖y₀‖ = b := hy₀norm
  have hH0 := hcont y₀ hy₀b hy₀cl
  -- the excess volume
  have hEvol : (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal ≤ CE * N ^ d * Q := by
    have h1 := volume_excess_le hd hε hpball hDmeas hb hD hball hy₀b
    have hcoef : 0 ≤ ωd / (2 * ε) * (2 * ((C₀ + 1) * N)) ^ (d - 1) := by positivity
    have h2 : potential d ε (cellSet (fun j => X j ω) n) y₀ ≤
        Cc * (a * N) * ((a ^ rateExp d)⁻¹ * Q) := by
      calc potential d ε (cellSet (fun j => X j ω) n) y₀ ≤ Cc * r * q := hH0
        _ = Cc * (a * N) * q := by rw [hr]
        _ ≤ Cc * (a * N) * ((a ^ rateExp d)⁻¹ * Q) :=
            mul_le_mul_of_nonneg_left hqQ (by positivity)
    have hNd1 : N ^ (d - 1) * N = N ^ d := by
      rw [← pow_succ]
      congr 1
      omega
    calc (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal
        ≤ ωd / (2 * ε) * (2 * ((C₀ + 1) * N)) ^ (d - 1) *
            potential d ε (cellSet (fun j => X j ω) n) y₀ := by
          exact h1
      _ ≤ ωd / (2 * ε) * (2 * ((C₀ + 1) * N)) ^ (d - 1) *
            (Cc * (a * N) * ((a ^ rateExp d)⁻¹ * Q)) :=
          mul_le_mul_of_nonneg_left h2 hcoef
      _ = CE * N ^ d * Q := by
          rw [hCE, ← hNd1]
          simp only [mul_pow]
          ring
  -- the inner radius
  have hXn : euclidNorm (X n ω) ≤ (C₀ + 2) * N :=
    (euclidNorm_le_maxRadius (fun j => X j ω) (le_refl n)).trans (by linarith only [hH, hNpos])
  have hquad' : |dynkin ε (fun z : Site d => euclidNorm z ^ 2) X n ω| ≤
      max C₁ CE * (N * Real.sqrt (n * L) + N * L) :=
    hquad.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (add_nonneg (mul_nonneg hNpos.le (Real.sqrt_nonneg _)) (mul_nonneg hNpos.le hL0)))
  have hKN1 : (C₀ + 1) * N ≤ (C₀ + 2) * N :=
    mul_le_mul_of_nonneg_right (by linarith only []) hNpos.le
  have hKd : C₀ * N ^ d ≤ (C₀ + 2) * N ^ d := mul_le_mul_of_nonneg_right (by linarith only []) hNd
  have hDcl : cellSet (fun j => X j ω) n ⊆ Metric.closedBall 0 ((C₀ + 2) * N) :=
    hD.trans ((Metric.ball_subset_ball hKN1).trans Metric.ball_subset_closedBall)
  have hrad : |b / N - a| ≤ Ci * Q :=
    hir X ω n b hni h0 hb.le hball hDcl
      hXn (hcard.trans hKd)
      (hEvol.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hNd) hQ0)) hquad'
  have hb_abs : |b - a * N| ≤ Ci * N * Q := by
    rw [show b - a * N = N * (b / N - a) by field_simp, abs_mul, abs_of_pos hNpos]
    calc N * |b / N - a| ≤ N * (Ci * Q) := mul_le_mul_of_nonneg_left hrad hNpos.le
      _ = Ci * N * Q := by ring
  have hC1 : Ci * cQ / a ≤ max (max (Ci * cQ / a) (Cv * cQ)) (Cp * cQ ^ ((1 : ℝ) / d) / a) :=
    le_max_of_le_left (le_max_left _ _)
  have hC2 : Cv * cQ ≤ max (max (Ci * cQ / a) (Cv * cQ)) (Cp * cQ ^ ((1 : ℝ) / d) / a) :=
    le_max_of_le_left (le_max_right _ _)
  have hC3 : Cp * cQ ^ ((1 : ℝ) / d) / a ≤
      max (max (Ci * cQ / a) (Cv * cQ)) (Cp * cQ ^ ((1 : ℝ) / d) / a) := le_max_right _ _
  refine ⟨?_, ?_, ?_⟩
  · -- (i)
    show |b - r| ≤ _ * r * q
    rw [hr]
    calc |b - a * N| ≤ Ci * N * Q := hb_abs
      _ ≤ Ci * N * (cQ * q) := mul_le_mul_of_nonneg_left hQq (by positivity)
      _ = Ci * cQ / a * (a * N) * q := by field_simp
      _ ≤ _ * (a * N) * q := by gcongr
  · -- (ii)
    have hb_r : |b / r - 1| ≤ max C₄ (Ci / a) * Q := by
      rw [hr, show b / (a * N) - 1 = (b / N - a) / a by field_simp, abs_div, abs_of_pos ha]
      calc |b / N - a| / a ≤ (Ci * Q) / a := div_le_div_of_nonneg_right hrad ha.le
        _ = (Ci / a) * Q := by ring
        _ ≤ max C₄ (Ci / a) * Q := mul_le_mul_of_nonneg_right (le_max_right _ _) hQ0
    have hEr : (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal ≤
        max C₄ (Ci / a) * r ^ d * Q := by
      calc (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal ≤ CE * N ^ d * Q :=
            hEvol
        _ = (CE / a ^ d) * (a * N) ^ d * Q := by
            rw [mul_pow]; field_simp
        _ ≤ max C₄ (Ci / a) * r ^ d * Q := by
            rw [hr]
            have h1 : CE / a ^ d ≤ max C₄ (Ci / a) :=
              (le_max_right _ _).trans (le_max_left _ _)
            gcongr
    have hv := hvol (cellSet (fun j => X j ω) n) b r Q hDmeas hDfin hb.le hrpos hQ0 hQ1 hball
      hEr hb_r
    refine (le_trans le_self_add hv).trans (ENNReal.ofReal_le_ofReal ?_)
    calc Cv * Q ≤ Cv * (cQ * q) := mul_le_mul_of_nonneg_left hQq hCv.le
      _ = Cv * cQ * q := by ring
      _ ≤ _ * q := mul_le_mul_of_nonneg_right hC2 hq0
  · -- (iii)
    intro y
    have hK'1 : (a + C₀ + 3) * N ≤ N * N := mul_le_mul_of_nonneg_right hK'N hNpos.le
    have hNN : N * N ≤ (n : ℝ) := by rw [← sq]; exact hN2
    have hK'n : (a + C₀ + 3) * N ≤ 2 * n := by linarith only [hK'1, hNN, hn1]
    have hKm : (a + C₀ + 3 - 1) * N ≥ (C₀ + 1) * N :=
      mul_le_mul_of_nonneg_right (by linarith only [ha]) hNpos.le
    have hDsub' : cellSet (fun j => X j ω) n ⊆ Metric.ball 0 ((a + C₀ + 3 - 1) * N) :=
      hD.trans (Metric.ball_subset_ball hKm)
    have hCE2 : CE ≤ max C₂ Ci :=
      le_max_of_le_left ((le_max_right _ _).trans (le_max_left _ _))
    have hEvol' : (volume (cellSet (fun j => X j ω) n \ Metric.ball 0 b)).toReal ≤
        max C₂ Ci * N ^ d * Q :=
      hEvol.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCE2 hNd) hQ0)
    have hbnd : |b - a * N| ≤ max C₂ Ci * N * Q :=
      hb_abs.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hNpos.le) hQ0)
    have herr := error_le_scale hd hM0 hC₀.le hL1 hL3 hM
    have hC₂a : 2 * C₁ * (Real.sqrt C₀ + 1) ≤ max C₂ Ci :=
      le_max_of_le_left ((le_max_left _ _).trans (le_max_left _ _))
    have hδ : C₁ * (if d = 2 then Real.sqrt (maxLocalTime (fun j => X j ω) n : ℝ) * L + L
          else Real.sqrt ((maxLocalTime (fun j => X j ω) n : ℝ) * L) + L) ≤
        max C₂ Ci * N * Q ^ ((1 : ℝ) / d) := by
      calc _ ≤ C₁ * (2 * (Real.sqrt C₀ + 1) * (N * Q ^ ((1 : ℝ) / d))) :=
            mul_le_mul_of_nonneg_left herr hC₁.le
        _ = (2 * C₁ * (Real.sqrt C₀ + 1)) * (N * Q ^ ((1 : ℝ) / d)) := by ring
        _ ≤ max C₂ Ci * (N * Q ^ ((1 : ℝ) / d)) :=
            mul_le_mul_of_nonneg_right hC₂a
              (mul_nonneg hNpos.le (Real.rpow_nonneg hQ0 _))
        _ = max C₂ Ci * N * Q ^ ((1 : ℝ) / d) := by ring
    have hall : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ < (a + C₀ + 3) * N →
        |cellLocalTime (fun j => X j ω) n y - potential d ε (cellSet (fun j => X j ω) n) y| ≤
          C₁ * (if d = 2 then Real.sqrt (maxLocalTime (fun j => X j ω) n : ℝ) * L + L
            else Real.sqrt ((maxLocalTime (fun j => X j ω) n : ℝ) * L) + L) :=
      fun y hy => hglob y (by linarith only [hy, hK'n])
    have hprofile := hprof (fun j => X j ω) n b _ N Q hNpos hQ0 hQ1 hb hball hDsub' hbnd hEvol'
      hδ hall y
    rw [hr]
    calc _ ≤ Cp * (N * Q ^ ((1 : ℝ) / d)) := hprofile
      _ ≤ Cp * (N * (cQ * q) ^ ((1 : ℝ) / d)) := by
          have h1 : Q ^ ((1 : ℝ) / d) ≤ (cQ * q) ^ ((1 : ℝ) / d) :=
            Real.rpow_le_rpow hQ0 hQq (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hNpos.le) hCp.le
      _ = Cp * cQ ^ ((1 : ℝ) / d) / a * (a * N) * q ^ ((1 : ℝ) / d) := by
          rw [Real.mul_rpow hcQpos.le hq0]
          field_simp
      _ ≤ _ * (a * N) * q ^ ((1 : ℝ) / d) := by
          have hq1 : 0 ≤ q ^ ((1 : ℝ) / d) := Real.rpow_nonneg hq0 _
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC3 (by positivity)) hq1

/-- The inner radius, the volume and the local times of the Euclidean walk (`prop:inner`). -/
theorem inner_radius_of (hcontact : contact_potential.{u}) (hball : norm_ball_potential)
    (hgeom : norm_potential_geometry) : inner_radius.{u} := by
  intro d hd ωd ε hε hεd r q p hp
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hΨ, hsub, hξ0, hell⟩ := CERW.Support.Main.euclidean_norm_hypotheses (d := d) hεd
  have hpball : ∀ ρ : ℝ, 0 < ρ → ∀ y : EuclideanSpace ℝ (Fin d),
      potential d ε (Metric.ball 0 ρ) y = 2 * d * ε * max (ρ - ‖y‖) 0 := by
    intro ρ hρ y
    have h := hball hd hΨ ε hρ y
    have hset : {v : EuclideanSpace ℝ (Fin d) | ‖v‖ < ρ} = Metric.ball 0 ρ := by
      ext v
      simp
    rw [hset, normPotential_norm_eq hd1] at h
    exact h
  obtain ⟨Cg, hCg, hg⟩ := hgeom hd (fun v => ‖v‖) hΨ
  have hpbound : ∀ D : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet D → Bornology.IsBounded D →
      ∀ y, |potential d ε D y| ≤ Cg * ε * (volume D).toReal ^ ((1 : ℝ) / d) := by
    intro D hDm hDb y
    obtain ⟨h1, -, -⟩ := hg ε hε D hDm hDb
    have h := h1 y
    rw [normPotential_norm_eq hd1] at h
    exact h
  have hvol : CERW.normBallVolume (fun v : EuclideanSpace ℝ (Fin d) => ‖v‖) = ωd :=
    normBallVolume_norm
  obtain ⟨Cc, hCc, n₁, hcc⟩ := hcontact hd (fun v => ‖v‖) hΨ ε hε hell p hp
  rw [hvol] at hcc
  obtain ⟨b₀, h₀, hK⟩ := CERW.Support.LocalTime.exists_kernelFacts hd
  obtain ⟨r₀, hr₀⟩ := exists_event_prob.{u} hd hK
  obtain ⟨C₀, C₁, hC₀, hC₁, hprob⟩ := hr₀ ε hε hεd p hp
  obtain ⟨Cin, hCin, nin, hcore⟩ := inner_core hd hε hC₀ hC₁ hCc hCg.le
    (bd := ⌈Real.sqrt d / 2⌉₊ + 6) (r₀ := r₀) (b₀ := b₀) hpball hpbound
  set nbig : ℕ := max (max nin n₁) 2 with hnbig
  have hnbig0 : (0 : ℝ) ≤ (nbig : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg nbig) p
  refine ⟨Cin + C₁ + Cc + (nbig : ℝ) ^ p, by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn2
  have hCle : Cin ≤ Cin + C₁ + Cc + (nbig : ℝ) ^ p := by linarith
  have hnp0 : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hr0 : ∀ m : ℕ, 0 ≤ r m := fun m => Real.rpow_nonneg (by positivity) _
  have hq0 : ∀ m : ℕ, 1 ≤ m → 0 ≤ q m := by
    intro m hm
    show 0 ≤ (if d = 2 then Real.sqrt (Real.log m / r m) else Real.log m / r m)
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) (hr0 m)
  by_cases hnb : nbig ≤ n
  · have hnin : nin ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnb
    have hn₁n : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnb
    have hXd := (CERW.Support.Drift.isCERW_iff_isDriftCERW μ ε X).1 hX
    have hmeas1 := hprob μ X hX n hn2
    have hmeas2 := hcc (fun z => CERW.unitDir (CERW.toSpace z)) hsub hξ0 μ X hXd n hn₁n
    have hq1 : 0 ≤ q n := hq0 n (by omega)
    refine (measure_mono ?_).trans ((measure_union_le _ _).trans
      ((add_le_add hmeas1 hmeas2).trans ?_))
    · intro ω hω
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      obtain ⟨h1, h2⟩ := hcon
      simp only [Set.mem_setOf_eq, not_not] at h1 h2
      apply hω
      obtain ⟨c1, c2, c3⟩ := hcore X ω n hnin h1 (fun y₀ hy₀ hcl => by
        have h := h2 y₀ hy₀ hcl
        rwa [normPotential_norm_eq hd1] at h)
      refine ⟨c1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCle (hr0 n)) hq1), c2.trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCle hq1)), fun y => (c3 y).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle (hr0 n))
            (Real.rpow_nonneg hq1 _))⟩
    · rw [← ENNReal.ofReal_add (mul_nonneg hC₁.le hnp0) (mul_nonneg hCc.le hnp0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_right
        (show C₁ + Cc ≤ Cin + C₁ + Cc + (nbig : ℝ) ^ p by linarith) hnp0
      linarith
  · rw [not_le] at hnb
    refine (prob_le_one).trans ?_
    rw [ENNReal.one_le_ofReal]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnp : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hn0 p
    have hle : (n : ℝ) ^ p ≤ (nbig : ℝ) ^ p :=
      Real.rpow_le_rpow hn0.le (by exact_mod_cast hnb.le) hp.le
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, le_div_iff₀ hnp, one_mul]
    linarith

end CERW.Support.Inner
