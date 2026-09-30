import CERW.Support.Statements
import CERW.Frozen.CoarseBounds
import CERW.Frozen.LocalTimePotential
import CERW.Support.Geometry.Bound
import CERW.Support.Geometry.Newton
import CERW.Support.Occupation.CellNorm
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Main.BorelCantelli
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The bulk profile of the local times

`prop:bulk-profile`: for the Euclidean norm, `0 < θ < 1` and `p > 0`, with probability at least
`1 - C n^{-p}` and almost surely for all large `n`, the local times at the sites `|y| ≤ θ r_n`
satisfy `|ℓ_n(y) - 2dε (r_n - |y|)| ≤ C √r_n log n` if `d = 2` and `C √(r_n log n)` if `d ≥ 3`.

The fluctuation bounds of `fluctuation_rates` (Theorem 1.2 (i), (ii)) give `|R_in(n) - r_n| ≤
C r_n q_n` and `|r_n⁻¹ D_n ∆ B(0, 1)| ≤ C q_n`. Every point of `D_n ∆ B(0, r_n)` has norm at least
`r_n - C r_n q_n`, hence lies at distance at least `c_θ r_n` from every site with `|y| ≤ θ r_n`,
so the potential of `D_n` differs from the Euclidean ball potential `2dε (r_n - |y|)` by at most
`C_θ r_n q_n` (the contribution of the symmetric difference, bounded by its volume times
`(c_θ r_n)^{1-d}`). The approximation of the local time by the potential (`eq:approx`) with
`M_n ≤ C r_n` from the coarse bounds then gives the bound, and the Borel–Cantelli lemma the
almost-sure statement.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Lower

open CERW.Support.Statements

section

variable {d : ℕ}

/-- For measurable sets of finite volume and a function integrable on both, the difference of
the integrals over `D` and over `B` is at most `M |D ∆ B|` if `|g| ≤ M` on `D ∆ B`. -/
private lemma abs_setIntegral_sub_le {g : EuclideanSpace ℝ (Fin d) → ℝ}
    {D B : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hB : MeasurableSet B)
    (hDfin : volume D ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hgD : IntegrableOn g D) (hgB : IntegrableOn g B) {M : ℝ} (hM : ∀ v ∈ D ∆ B, |g v| ≤ M) :
    |(∫ v in D, g v) - ∫ v in B, g v| ≤ M * (volume (D ∆ B)).toReal := by
  have h1 := integral_inter_add_sdiff hB hgD
  have h2 := integral_inter_add_sdiff hD hgB
  rw [Set.inter_comm B D] at h2
  have hdiff : (∫ v in D, g v) - ∫ v in B, g v =
      (∫ v in D \ B, g v) - ∫ v in B \ D, g v := by linarith
  have hfin1 : volume (D \ B) < ⊤ := (measure_mono Set.sdiff_subset).trans_lt hDfin.lt_top
  have hfin2 : volume (B \ D) < ⊤ := (measure_mono Set.sdiff_subset).trans_lt hBfin.lt_top
  have hb1 := norm_setIntegral_le_of_norm_le_const (f := g) (C := M) hfin1
    (fun v hv => by rw [Real.norm_eq_abs]; exact hM v (Or.inl hv))
  have hb2 := norm_setIntegral_le_of_norm_le_const (f := g) (C := M) hfin2
    (fun v hv => by rw [Real.norm_eq_abs]; exact hM v (Or.inr hv))
  rw [Real.norm_eq_abs] at hb1 hb2
  have hsd : (volume (D ∆ B)).toReal = (volume (D \ B)).toReal + (volume (B \ D)).toReal := by
    rw [measure_symmDiff_eq hD.nullMeasurableSet hB.nullMeasurableSet,
      ENNReal.toReal_add hfin1.ne hfin2.ne]
  rw [hdiff, hsd]
  calc |(∫ v in D \ B, g v) - ∫ v in B \ D, g v|
      ≤ |∫ v in D \ B, g v| + |∫ v in B \ D, g v| := abs_sub _ _
    _ ≤ M * (volume (D \ B)).toReal + M * (volume (B \ D)).toReal := add_le_add hb1 hb2
    _ = M * ((volume (D \ B)).toReal + (volume (B \ D)).toReal) := by ring

/-- At distance at least `ρ` from `v`, the potential's integrand is at most `ρ^{1-d}`. -/
private lemma abs_potentialIntegrand_le_inv_pow (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ)
    {v z : EuclideanSpace ℝ (Fin d)} (hvz : ρ ≤ ‖v - z‖) :
    |inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d| ≤ (ρ ^ (d - 1))⁻¹ := by
  refine (Geometry.abs_potentialIntegrand_le v z).trans ?_
  have hw : 0 < ‖v - z‖ := hρ.trans_le hvz
  have h : ‖v - z‖ ^ (1 - (d : ℝ)) = (‖v - z‖ ^ (d - 1))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hw.le]
    congr 1
    rw [Nat.cast_sub hd]
    push_cast
    ring
  rw [h]
  exact inv_anti₀ (pow_pos hρ _) (pow_le_pow_left₀ hρ.le hvz _)

/-- The potential of a bounded measurable set `D` differs from that of `B(0, r)` at a point `z`
at distance at least `ρ` from `D ∆ B(0, r)` by at most `(2ε / ω_d) ρ^{1-d} |D ∆ B(0, r)|`. -/
private theorem abs_potential_sub_ball_le (hd : 2 ≤ d) {ε r ρ m : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    {z : EuclideanSpace ℝ (Fin d)}
    (hfar : ∀ v ∈ D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, ρ ≤ ‖v - z‖)
    (hm : (volume (D ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal ≤ m) :
    |potential d ε D z - potential d ε (Metric.ball 0 r) z| ≤
      2 * ε / unitBallVolume d * ((ρ ^ (d - 1))⁻¹ * m) := by
  have hω := unitBallVolume_pos d
  have hc : 0 ≤ 2 * ε / unitBallVolume d := by positivity
  have hBm : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) :=
    Metric.isOpen_ball.measurableSet
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have hBfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hfD := Geometry.integrableOn_potentialIntegrand (d := d) (by omega) hD hDfin z
  have hfB := Geometry.integrableOn_potentialIntegrand (d := d) (by omega) hBm hBfin z
  have hM0 : 0 ≤ (ρ ^ (d - 1))⁻¹ := by positivity
  have key := abs_setIntegral_sub_le hD hBm hDfin hBfin hfD hfB (M := (ρ ^ (d - 1))⁻¹)
    (fun v hv => abs_potentialIntegrand_le_inv_pow (by omega) hρ (hfar v hv))
  have hdiff : potential d ε D z - potential d ε (Metric.ball 0 r) z =
      2 * ε / unitBallVolume d *
        ((∫ v in D, inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d) -
          ∫ v in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
            inner ℝ (unitDir v) (v - z) / ‖v - z‖ ^ d) := by
    unfold potential
    ring
  rw [hdiff, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (key.trans (mul_le_mul_of_nonneg_left hm hM0)) hc

/-- Scaling by `r` carries `(r⁻¹ • S) ∆ B(0, 1)` to `S ∆ B(0, r)`, so the volumes differ by
`r^d`. -/
private lemma volume_symmDiff_ball {r : ℝ} (hr : 0 < r) (S : Set (EuclideanSpace ℝ (Fin d))) :
    volume (S ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) =
      ENNReal.ofReal (r ^ d) *
        volume ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have h : S ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r =
      r • ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [Set.smul_set_symmDiff₀ hr.ne', smul_inv_smul₀ hr.ne', smul_ball hr.ne', smul_zero,
      Real.norm_eq_abs, abs_of_pos hr, mul_one]
  rw [h, Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_pos (pow_pos hr d)]

/-- The volume of `S ∆ B(0, r)` is at most `r^d m` when that of `(r⁻¹ • S) ∆ B(0, 1)` is at
most `m`. -/
private lemma toReal_volume_symmDiff_le {r m : ℝ} (hr : 0 < r) (hm0 : 0 ≤ m)
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hm : volume ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ENNReal.ofReal m) :
    (volume (S ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).toReal ≤ r ^ d * m := by
  rw [volume_symmDiff_ball hr S]
  have h : ENNReal.ofReal (r ^ d) *
      volume ((r⁻¹ • S) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ENNReal.ofReal (r ^ d) * ENNReal.ofReal m := by gcongr
  rw [← ENNReal.ofReal_mul (pow_pos hr d).le] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

/-- Every point of `D_n ∆ B(0, r)` has norm at least `r - A` when `r - A ≤ R_in(n)` and
`A ≥ 0`. -/
private lemma le_norm_of_mem_symmDiff {X : ℕ → Site d} {n : ℕ} {r A : ℝ} (hA : 0 ≤ A)
    (hin : r - A ≤ innerRadius X n) {v : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ cellSet X n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r) : r - A ≤ ‖v‖ := by
  rcases Set.mem_symmDiff.mp hv with ⟨_, hvB⟩ | ⟨_, hvD⟩
  · have h1 : r ≤ ‖v‖ := not_lt.mp (fun h => hvB (mem_ball_zero_iff.mpr h))
    linarith
  · have h2 : innerRadius X n ≤ ‖v‖ :=
      csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg w⟩ ⟨v, hvD, rfl⟩
    linarith

/-- For `ρ > 0` and `t > 0`, `((t ρ)^{d-1})⁻¹ ρ^d = (t^{d-1})⁻¹ ρ` when `d ≥ 1`. -/
private lemma inv_mul_pow_mul_pow (hd : 1 ≤ d) {t ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ) :
    ((t * ρ) ^ (d - 1))⁻¹ * ρ ^ d = (t ^ (d - 1))⁻¹ * ρ := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, mul_pow, pow_succ ρ k]
  have : 0 < t ^ k := pow_pos ht k
  have : 0 < ρ ^ k := pow_pos hρ k
  field_simp


/-! ### Arithmetic of the scales -/

/-- `log n` is eventually at most `c (κ n)^{1/(d+1)}`, for every `c > 0`. -/
private lemma eventually_log_le_mul (d : ℕ) {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * (κ * n) ^ ((1 : ℝ) / (d + 1)) := by
  have hs : (0 : ℝ) < 1 / (d + 1) := by positivity
  have hO := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hs).def
    (c := c * κ ^ ((1 : ℝ) / (d + 1))) (by positivity)
  have h' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hO
  filter_upwards [h'] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0 _)] at hn
  rw [Real.mul_rpow hκ.le hn0]
  calc Real.log n ≤ |Real.log n ^ (1 : ℝ)| := by rw [Real.rpow_one]; exact le_abs_self _
    _ ≤ c * κ ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := hn
    _ = c * (κ ^ ((1 : ℝ) / (d + 1)) * (n : ℝ) ^ ((1 : ℝ) / (d + 1))) := by ring

/-- The width of the inner-radius error is a small multiple of `ρ`: if `ℓ ≤ c ρ` and
`ℓ ≤ c² ρ` with `c = (1 - θ) / (2 C₁)`, then `C₁ · (√(ρ ℓ) or ℓ) ≤ (1 - θ) ρ / 2`. -/
private lemma width_le (d : ℕ) {ρ ℓ C₁ θ : ℝ} (hC₁ : 0 < C₁) (hθ : θ < 1) (hρ : 0 ≤ ρ)
    (h1 : ℓ ≤ (1 - θ) / (2 * C₁) * ρ) (h2 : ℓ ≤ ((1 - θ) / (2 * C₁)) ^ 2 * ρ) :
    C₁ * (if d = 2 then Real.sqrt (ρ * ℓ) else ℓ) ≤ (1 - θ) / 2 * ρ := by
  have hc0 : 0 ≤ (1 - θ) / (2 * C₁) := by
    have : 0 < 1 - θ := by linarith
    positivity
  have hcC : C₁ * ((1 - θ) / (2 * C₁)) = (1 - θ) / 2 := by
    field_simp
  split_ifs
  · have hs : Real.sqrt (ρ * ℓ) ≤ (1 - θ) / (2 * C₁) * ρ := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      calc ρ * ℓ ≤ ρ * (((1 - θ) / (2 * C₁)) ^ 2 * ρ) := mul_le_mul_of_nonneg_left h2 hρ
        _ = ((1 - θ) / (2 * C₁) * ρ) ^ 2 := by ring
    calc C₁ * Real.sqrt (ρ * ℓ) ≤ C₁ * ((1 - θ) / (2 * C₁) * ρ) :=
          mul_le_mul_of_nonneg_left hs hC₁.le
      _ = (1 - θ) / 2 * ρ := by rw [← mul_assoc, hcC]
  · calc C₁ * ℓ ≤ C₁ * ((1 - θ) / (2 * C₁) * ρ) := mul_le_mul_of_nonneg_left h1 hC₁.le
      _ = (1 - θ) / 2 * ρ := by rw [← mul_assoc, hcC]

/-- The volume scale `ρ q` is at most the bulk scale. -/
private lemma mul_q_le (d : ℕ) {ρ ℓ : ℝ} (hℓ : 1 ≤ ℓ) (hℓρ : ℓ ≤ ρ) :
    ρ * (if d = 2 then Real.sqrt (ℓ / ρ) else ℓ / ρ) ≤
      if d = 2 then Real.sqrt ρ * ℓ else Real.sqrt (ρ * ℓ) := by
  have hρ : 0 < ρ := by linarith
  split_ifs
  · have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
    have e : ρ * Real.sqrt (ℓ / ρ) = Real.sqrt ρ * Real.sqrt ℓ := by
      rw [Real.sqrt_div (by linarith)]
      calc ρ * (Real.sqrt ℓ / Real.sqrt ρ)
          = (Real.sqrt ρ * Real.sqrt ρ) * (Real.sqrt ℓ / Real.sqrt ρ) := by
            rw [Real.mul_self_sqrt hρ.le]
        _ = Real.sqrt ρ * Real.sqrt ℓ := by field_simp
    have hsℓ : Real.sqrt ℓ ≤ ℓ := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    rw [e]
    exact mul_le_mul_of_nonneg_left hsℓ hsρ.le
  · have e : ρ * (ℓ / ρ) = ℓ := by field_simp
    rw [e]
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith

/-- The error scale of the approximation of the local time by the potential is at most a
multiple of the bulk scale, when the maximal local time is at most a multiple of `ρ`. -/
private lemma error_scale_le (d : ℕ) {ρ ℓ M L C : ℝ} (hM0 : 0 ≤ M) (hC : 0 ≤ C)
    (hM : M ≤ C * ρ) (hρ : 1 ≤ ρ) (hℓ : 1 ≤ ℓ) (hℓρ : ℓ ≤ ρ) (hL0 : 0 ≤ L) (hL : L ≤ 2 * ℓ) :
    (if d = 2 then Real.sqrt M * L + L else Real.sqrt (M * L) + L) ≤
      (2 * Real.sqrt (2 * C) + 2) *
        if d = 2 then Real.sqrt ρ * ℓ else Real.sqrt (ρ * ℓ) := by
  have hρ0 : 0 ≤ ρ := by linarith
  have hs2 : 0 ≤ Real.sqrt (2 * C) := Real.sqrt_nonneg _
  split_ifs
  · have hsρ : 1 ≤ Real.sqrt ρ := Real.one_le_sqrt.mpr hρ
    have h1 : Real.sqrt M ≤ Real.sqrt (2 * C) * Real.sqrt ρ := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : Real.sqrt M * L ≤ Real.sqrt (2 * C) * Real.sqrt ρ * (2 * ℓ) :=
      mul_le_mul h1 hL hL0 (by positivity)
    have h3 : L ≤ 2 * (Real.sqrt ρ * ℓ) := by nlinarith
    calc Real.sqrt M * L + L
        ≤ Real.sqrt (2 * C) * Real.sqrt ρ * (2 * ℓ) + 2 * (Real.sqrt ρ * ℓ) := add_le_add h2 h3
      _ = (2 * Real.sqrt (2 * C) + 2) * (Real.sqrt ρ * ℓ) := by ring
  · have hML : M * L ≤ 2 * C * (ρ * ℓ) := by
      calc M * L ≤ C * ρ * (2 * ℓ) := mul_le_mul hM hL hL0 (by positivity)
        _ = 2 * C * (ρ * ℓ) := by ring
    have h1 : Real.sqrt (M * L) ≤ Real.sqrt (2 * C) * Real.sqrt (ρ * ℓ) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hML
    have hℓs : ℓ ≤ Real.sqrt (ρ * ℓ) := Real.le_sqrt_of_sq_le (by nlinarith)
    have h3 : L ≤ 2 * Real.sqrt (ρ * ℓ) := by linarith
    have h4 : 0 ≤ Real.sqrt (2 * C) * Real.sqrt (ρ * ℓ) := by positivity
    calc Real.sqrt (M * L) + L ≤ Real.sqrt (2 * C) * Real.sqrt (ρ * ℓ) +
          2 * Real.sqrt (ρ * ℓ) := add_le_add h1 h3
      _ ≤ (2 * Real.sqrt (2 * C) + 2) * Real.sqrt (ρ * ℓ) := by nlinarith


/-- `log (n + 2) ≤ 2 log n` for `n ≥ 2`. -/
private lemma log_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) h
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- The `d + 1`-st power of `x ^ (1 / (d + 1))` is `x`. -/
private lemma rpow_inv_succ_pow (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / (d + 1))) ^ (d + 1) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have h : (1 : ℝ) / (d + 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [h, Real.rpow_one]

/-! ### The deterministic core -/

/-- The inner-radius and volume clauses of the fluctuation bounds of `fluctuation_rates`, with
constant `C`: `|R_in(n) - r_n| ≤ C r_n q_n` and `|r_n⁻¹ D_n ∆ B(0, 1)| ≤ C q_n`, where
`r_n q_n` is `√(r_n log n)` if `d = 2` and `log n` otherwise. -/
private def InnerVolume (d : ℕ) (r : ℕ → ℝ) (C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  |innerRadius Y n - r n| ≤ C * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n) ∧
    volume (((r n)⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      ENNReal.ofReal (C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n)

/-- The bound `M_n ≤ C n^{1/(d+1)}` of the coarse bounds on the maximal local time. -/
private def MaxLocalBound (d : ℕ) (C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  (maxLocalTime Y n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / (d + 1))

/-- The approximation `|ℓ̃_n(y) - U_{D_n}(y)| ≤ C e_n(M_n)` of the cell local time by the
potential, for `|y| ≤ 2n`. -/
private def PotentialApprox (d : ℕ) (ε C : ℝ) (Y : ℕ → Site d) (n : ℕ) : Prop :=
  ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 2 * n →
    |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ C *
      (if d = 2 then Real.sqrt (maxLocalTime Y n) * Real.log (n + 2) + Real.log (n + 2)
        else Real.sqrt (maxLocalTime Y n * Real.log (n + 2)) + Real.log (n + 2))

/-- The bulk profile is deterministic once the inner radius, the volume, the maximal local time
and the potential approximation are controlled: for all large `n` and all paths `Y` satisfying
the three clauses, the local times at the sites `|y| ≤ θ r_n` are within a multiple of
`√r_n log n` (`d = 2`) or `√(r_n log n)` of `2dε (r_n - |y|)`. -/
private theorem bulk_core (hd : 2 ≤ d) {ε κ θ C₁ C₂ C₃ : ℝ} (hε : 0 < ε) (hκ : 0 < κ)
    (hθ1 : θ < 1) (hC₁ : 0 < C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (r : ℕ → ℝ)
    (hr : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ Y : ℕ → Site d,
      InnerVolume d r C₁ Y n → MaxLocalBound d C₃ Y n → PotentialApprox d ε C₂ Y n →
      ∀ y : Site d, euclidNorm y ≤ θ * r n →
        |(localTime Y n y : ℝ) - 2 * d * ε * (r n - euclidNorm y)| ≤
          K * if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n) := by
  have hω := unitBallVolume_pos d
  have hd1 : 1 ≤ d := by omega
  have hθ' : 0 < 1 - θ := by linarith
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = κ ^ ((1 : ℝ) / (d + 1)) := ⟨_, rfl⟩
  have hK₀0 : 0 < K₀ := by rw [hK₀]; positivity
  have hrN : ∀ n : ℕ, r n = K₀ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    rw [hr n, hK₀, Real.mul_rpow hκ.le (Nat.cast_nonneg n)]
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = C₃ / K₀ := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * ε / unitBallVolume d := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (1 - θ) / 2 := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; linarith
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = (1 - θ) / (2 * C₁) := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  obtain ⟨cs, hcs⟩ : ∃ cs : ℝ, cs = min (min c₁ (c₁ ^ 2)) 1 := ⟨_, rfl⟩
  have hcs0 : 0 < cs := by rw [hcs]; exact lt_min (lt_min hc₁0 (by positivity)) one_pos
  refine ⟨C₂ * (2 * Real.sqrt (2 * C') + 2) + a * (t ^ (d - 1))⁻¹ * C₁ + 1, by positivity, ?_⟩
  have hlog1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_log_le_mul d hκ hcs0, hlog1, eventually_ge_atTop 2,
    eventually_ge_atTop ⌈κ⌉₊] with n hlog hℓ1 hn2 hnκ
  intro Y hYin hYM hYap y hy
  obtain ⟨hin, hvolY⟩ := hYin
  rw [← hr n] at hlog
  have hρ0 : 0 ≤ r n := by rw [hr n]; positivity
  have hcs1 : cs ≤ 1 := by rw [hcs]; exact min_le_right _ _
  have hℓρ : Real.log n ≤ r n := by
    calc Real.log n ≤ cs * r n := hlog
      _ ≤ 1 * r n := mul_le_mul_of_nonneg_right hcs1 hρ0
      _ = r n := one_mul _
  have hρ1 : 1 ≤ r n := hℓ1.trans hℓρ
  have hρpos : 0 < r n := by linarith
  have h1c : Real.log n ≤ (1 - θ) / (2 * C₁) * r n := by
    rw [← hc₁]
    refine hlog.trans (mul_le_mul_of_nonneg_right ?_ hρ0)
    rw [hcs]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have h2c : Real.log n ≤ ((1 - θ) / (2 * C₁)) ^ 2 * r n := by
    rw [← hc₁]
    refine hlog.trans (mul_le_mul_of_nonneg_right ?_ hρ0)
    rw [hcs]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hwidth := width_le d hC₁ hθ1 hρ0 h1c h2c
  rw [← ht] at hwidth
  have hA0 : 0 ≤ C₁ * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n) :=
    mul_nonneg hC₁.le (by split_ifs <;> [exact Real.sqrt_nonneg _; linarith])
  have hinner : r n - C₁ * (if d = 2 then Real.sqrt (r n * Real.log n) else Real.log n) ≤
      innerRadius Y n := by linarith [(abs_le.mp hin).1]
  have hDm : MeasurableSet (cellSet Y n) := Occupation.measurableSet_cellSet Y n
  have hDb : Bornology.IsBounded (cellSet Y n) :=
    Metric.isBounded_ball.subset (Occupation.cellSet_subset_ball hd1 Y n)
  have hq0 : 0 ≤ C₁ * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n :=
    mul_nonneg hC₁.le (by split_ifs <;> positivity)
  have hvol := toReal_volume_symmDiff_le hρpos hq0 (cellSet Y n) hvolY
  have hρn : r n ≤ n := by
    have hκn : κ ≤ n := (Nat.le_ceil κ).trans (by exact_mod_cast hnκ)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hpow : r n ^ (d + 1) = κ * n := by rw [hr n]; exact rpow_inv_succ_pow d (by positivity)
    have h2 : κ * n ≤ (n : ℝ) ^ (d + 1) :=
      calc κ * n ≤ n * n := mul_le_mul_of_nonneg_right hκn (by linarith)
        _ = (n : ℝ) ^ 2 := by ring
        _ ≤ (n : ℝ) ^ (d + 1) := pow_le_pow_right₀ hn1 (by omega)
    exact (pow_le_pow_iff_left₀ hρ0 (by linarith) (by omega)).mp (hpow ▸ h2)
  have hz : ‖toSpace y‖ ≤ θ * r n := by rw [norm_toSpace]; exact hy
  have hfar : ∀ v ∈ cellSet Y n ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (r n),
      t * r n ≤ ‖v - toSpace y‖ := by
    intro v hv
    have h1 := le_norm_of_mem_symmDiff hA0 hinner hv
    have h2 : ‖v‖ - ‖toSpace y‖ ≤ ‖v - toSpace y‖ := norm_sub_norm_le v (toSpace y)
    rw [ht] at hwidth ⊢
    linarith
  have hpot := abs_potential_sub_ball_le hd hε (mul_pos ht0 hρpos) hDm hDb hfar hvol
  have hθr : θ * r n ≤ r n := mul_le_of_le_one_left hρ0 hθ1.le
  have hUB : potential d ε (Metric.ball 0 (r n)) (toSpace y) =
      2 * d * ε * (r n - euclidNorm y) := by
    rw [Geometry.potential_ball hd ε hρpos, norm_toSpace, max_eq_left (by linarith)]
  have hcell : cellLocalTime Y n (toSpace y) = (localTime Y n y : ℝ) :=
    cellLocalTime_of_mem_cell Y n (toSpace_mem_cell y)
  have hap := hYap (toSpace y) (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  rw [hcell] at hap
  -- the error scale
  have hMC : (maxLocalTime Y n : ℝ) ≤ C' * r n := by
    have : C₃ * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) = C' * r n := by
      rw [hC', hrN n]
      field_simp
    exact this ▸ hYM
  have hL0 : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hL := log_add_two_le hn2
  have hescale := error_scale_le d (Nat.cast_nonneg _) hC'0 hMC hρ1 hℓ1 hℓρ hL0 hL
  have hqB := mul_q_le d hℓ1 hℓρ
  have hB0 : 0 ≤ if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n) := by
    split_ifs
    · exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    · exact Real.sqrt_nonneg _
  have hsplit : (localTime Y n y : ℝ) - 2 * d * ε * (r n - euclidNorm y) =
      ((localTime Y n y : ℝ) - potential d ε (cellSet Y n) (toSpace y)) +
        (potential d ε (cellSet Y n) (toSpace y) -
          potential d ε (Metric.ball 0 (r n)) (toSpace y)) := by
    rw [hUB]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hfirst : |(localTime Y n y : ℝ) - potential d ε (cellSet Y n) (toSpace y)| ≤
      C₂ * (2 * Real.sqrt (2 * C') + 2) *
        if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n) := by
    rw [mul_assoc]
    exact hap.trans (mul_le_mul_of_nonneg_left hescale hC₂)
  have hsecond : |potential d ε (cellSet Y n) (toSpace y) -
      potential d ε (Metric.ball 0 (r n)) (toSpace y)| ≤
      a * (t ^ (d - 1))⁻¹ * C₁ *
        if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n) := by
    have hcalc : a * (((t * r n) ^ (d - 1))⁻¹ *
        (r n ^ d * (C₁ * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n))) =
        a * (t ^ (d - 1))⁻¹ * C₁ *
          (r n * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) := by
      rw [← mul_assoc (((t * r n) ^ (d - 1))⁻¹), inv_mul_pow_mul_pow hd1 ht0 hρpos]
      ring
    rw [← ha] at hpot
    calc _ ≤ a * (((t * r n) ^ (d - 1))⁻¹ *
          (r n ^ d * (C₁ * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n))) :=
          hpot
      _ = _ := hcalc
      _ ≤ _ := mul_le_mul_of_nonneg_left hqB (by positivity)
  calc _ ≤ C₂ * (2 * Real.sqrt (2 * C') + 2) *
        (if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n)) +
        a * (t ^ (d - 1))⁻¹ * C₁ *
          (if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n)) :=
        add_le_add hfirst hsecond
    _ = (C₂ * (2 * Real.sqrt (2 * C') + 2) + a * (t ^ (d - 1))⁻¹ * C₁) *
        (if d = 2 then Real.sqrt (r n) * Real.log n else Real.sqrt (r n * Real.log n)) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hB0

/-- The inner-radius and volume clauses inside the fluctuation event of `fluctuation_rates`. -/
private lemma innerVolume_of_clauses {r : ℕ → ℝ} {C : ℝ} {Y : ℕ → Site d} {n : ℕ} {R : Prop}
    (h : (if d = 2 then
            |innerRadius Y n - r n| ≤ C * Real.sqrt (r n * Real.log n) ∧
              maxRadius Y n - r n ≤ C * Real.sqrt (r n) * Real.log n ^ ((5 : ℝ) / 2)
          else
            |innerRadius Y n - r n| ≤ C * Real.log n ∧
              maxRadius Y n - r n ≤ C * Real.log n ^ ((d : ℝ) + 1)) ∧
        volume (((r n)⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
          ENNReal.ofReal (C * if d = 2 then Real.sqrt (Real.log n / r n) else Real.log n / r n) ∧
        R) :
    InnerVolume d r C Y n := by
  obtain ⟨hA, hvol, -⟩ := h
  refine ⟨?_, hvol⟩
  by_cases hd2 : d = 2
  · simp only [if_pos hd2] at hA ⊢
    exact hA.1
  · simp only [if_neg hd2] at hA ⊢
    exact hA.1

/-- If `Q` holds wherever `P₁`, `P₂` and `P₃` hold, the failure probability of `Q` is at most
the sum of those of `P₁`, `P₂` and `P₃`. -/
private lemma measure_not_le_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {P₁ P₂ P₃ Q : Ω → Prop} (h : ∀ ω, P₁ ω → P₂ ω → P₃ ω → Q ω) :
    μ {ω | ¬ Q ω} ≤ μ {ω | ¬ P₁ ω} + μ {ω | ¬ P₂ ω} + μ {ω | ¬ P₃ ω} := by
  calc μ {ω | ¬ Q ω} ≤ μ ({ω | ¬ P₁ ω} ∪ {ω | ¬ P₂ ω} ∪ {ω | ¬ P₃ ω}) := by
        refine measure_mono fun ω hω => ?_
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
        exact hω (h ω hcon.1.1 hcon.1.2 hcon.2)
    _ ≤ μ ({ω | ¬ P₁ ω} ∪ {ω | ¬ P₂ ω}) + μ {ω | ¬ P₃ ω} := measure_union_le _ _
    _ ≤ μ {ω | ¬ P₁ ω} + μ {ω | ¬ P₂ ω} + μ {ω | ¬ P₃ ω} :=
        add_le_add (measure_union_le _ _) le_rfl

end

/-- The bulk profile of the local times: for `|y| ≤ θ r_n`, `ℓ_n(y)` is within `C √r_n log n`
(`d = 2`) or `C √(r_n log n)` (`d ≥ 3`) of `2dε (r_n - |y|)`, with probability at least
`1 - C n^{-p}` and, almost surely, for all large `n`. -/
theorem bulk_profile_of (hfluct : fluctuation_rates.{u}) : bulk_profile.{u} := by
  intro d hd ωd ε hε0 hε1 r θ hθ0 hθ1 p hp
  have hp' : 0 < max p 2 := lt_max_of_lt_right two_pos
  have hp1 : 1 < max p 2 := lt_max_of_lt_right one_lt_two
  -- the events of Theorem 1.2 and of the coarse and local-time bounds
  obtain ⟨C₁, hC₁, hprob₁, hae₁⟩ := hfluct hd ε hε0 hε1 (max p 2) hp'
  have hIV : ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
      μ {ω | ¬ InnerVolume d r C₁ (X · ω) n} ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (-max p 2)) := by
    intro Ω _ μ _ X hX n hn
    refine le_trans (measure_mono ?_) (hprob₁ μ X hX n hn)
    intro ω hω hg
    exact hω (innerVolume_of_clauses (r := r) hg)
  have hIVae : ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X →
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, InnerVolume d r C₁ (X · ω) n := by
    intro Ω _ μ _ X hX
    filter_upwards [hae₁ μ X hX] with ω hω
    exact hω.mono fun n hg => innerVolume_of_clauses (r := r) hg
  obtain ⟨c, C₃, -, hC₃, hcoarse⟩ := CERW.Frozen.coarse_bounds.{u} hd ε hε0 hε1 (max p 2) hp'
  have hMB : ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
      μ {ω | ¬ MaxLocalBound d C₃ (X · ω) n} ≤ ENNReal.ofReal (C₃ * (n : ℝ) ^ (-max p 2)) := by
    intro Ω _ μ _ X hX n hn
    have h := hcoarse μ X hX n hn
    dsimp only at h
    refine le_trans (measure_mono ?_) h
    intro ω hω hg
    exact hω hg.2.2.2.1
  obtain ⟨Cd, -, hloc⟩ := CERW.Frozen.local_time_potential.{u} hd
  obtain ⟨C₂, hC₂, hlocp⟩ := hloc ε hε0 hε1 (max p 2) hp'
  have hPA : ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), CERW.IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
      μ {ω | ¬ PotentialApprox d ε C₂ (X · ω) n} ≤ ENNReal.ofReal (C₂ * (n : ℝ) ^ (-max p 2)) := by
    intro Ω _ μ _ X hX n hn
    have h := hlocp μ X hX n hn
    dsimp only at h
    refine le_trans (measure_mono ?_) h
    intro ω hω hg
    exact hω hg.2.2
  -- the deterministic core
  have hω0 : 0 < ωd := unitBallVolume_pos d
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (d + 1) / (2 * d * ε * ωd) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hrκ : ∀ n : ℕ, r n = (κ * n) ^ ((1 : ℝ) / (d + 1)) := fun n => by
    show ((d + 1) * n / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) = _
    rw [hκ, mul_div_right_comm]
  obtain ⟨K, hK, hev⟩ := bulk_core hd hε0 hκ0 hθ1 hC₁ hC₂.le hC₃.le r hrκ
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hev
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = K + (C₁ + C₂ + C₃) + ((max n₁ 2 : ℕ) : ℝ) ^ p := ⟨_, rfl⟩
  have hCfK : K ≤ Cf := by
    have h1 : 0 ≤ C₁ + C₂ + C₃ := by positivity
    have h2 : 0 ≤ ((max n₁ 2 : ℕ) : ℝ) ^ p := by positivity
    rw [hCf]
    linarith
  have hCfC : C₁ + C₃ + C₂ ≤ Cf := by
    have h2 : 0 ≤ ((max n₁ 2 : ℕ) : ℝ) ^ p := by positivity
    rw [hCf]
    linarith
  have hCfn : ((max n₁ 2 : ℕ) : ℝ) ^ p ≤ Cf := by
    have h1 : 0 ≤ C₁ + C₂ + C₃ := by positivity
    rw [hCf]
    linarith
  refine ⟨Cf, by rw [hCf]; positivity, ?_⟩
  intro Good
  have hgood : ∀ (Y : ℕ → Site d) (n : ℕ), n₁ ≤ n → InnerVolume d r C₁ Y n →
      MaxLocalBound d C₃ Y n → PotentialApprox d ε C₂ Y n → Good Y n := by
    intro Y n hn h1 h2 h3 y hy
    refine (hn₁ n hn Y h1 h2 h3 y hy).trans ?_
    refine mul_le_mul_of_nonneg_right hCfK ?_
    split_ifs
    · exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_natCast_nonneg n)
    · exact Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · intro Ω _ μ _ X hX n hn2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    by_cases hn : max n₁ 2 ≤ n
    · have hn1' : n₁ ≤ n := (le_max_left _ _).trans hn
      have h := measure_not_le_add μ (Q := fun ω => Good (X · ω) n)
        (P₁ := fun ω => InnerVolume d r C₁ (X · ω) n)
        (P₂ := fun ω => MaxLocalBound d C₃ (X · ω) n)
        (P₃ := fun ω => PotentialApprox d ε C₂ (X · ω) n)
        (fun ω h1 h2 h3 => hgood (X · ω) n hn1' h1 h2 h3)
      refine h.trans ((add_le_add (add_le_add (hIV μ X hX n hn2) (hMB μ X hX n hn2))
        (hPA μ X hX n hn2)).trans ?_)
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-max p 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp : (n : ℝ) ^ (-max p 2) ≤ (n : ℝ) ^ (-p) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg (le_max_left p 2))
      calc C₁ * (n : ℝ) ^ (-max p 2) + C₃ * (n : ℝ) ^ (-max p 2) +
            C₂ * (n : ℝ) ^ (-max p 2) = (C₁ + C₃ + C₂) * (n : ℝ) ^ (-max p 2) := by ring
        _ ≤ Cf * (n : ℝ) ^ (-p) := mul_le_mul hCfC hexp hnn (by rw [hCf]; positivity)
    · have hlt : (n : ℝ) ≤ ((max n₁ 2 : ℕ) : ℝ) := by exact_mod_cast (not_le.mp hn).le
      have hnp : (n : ℝ) ^ p ≤ Cf :=
        (Real.rpow_le_rpow (Nat.cast_nonneg n) hlt hp.le).trans hCfn
      calc μ {ω | ¬ Good (X · ω) n} ≤ 1 := prob_le_one
        _ ≤ ENNReal.ofReal (Cf * (n : ℝ) ^ (-p)) := by
            rw [ENNReal.one_le_ofReal]
            calc (1 : ℝ) = (n : ℝ) ^ p * (n : ℝ) ^ (-p) := by
                  rw [← Real.rpow_add (by linarith)]
                  simp
              _ ≤ Cf * (n : ℝ) ^ (-p) :=
                  mul_le_mul_of_nonneg_right hnp (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · intro Ω _ μ _ X hX
    have hae₂ : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, MaxLocalBound d C₃ (X · ω) n :=
      CERW.Support.Main.ae_eventually_of_le_rpow
        (P := fun n ω => MaxLocalBound d C₃ (X · ω) n) (n₀ := 2) hp1
        (fun n hn => hMB μ X hX n hn)
    have hae₃ : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, PotentialApprox d ε C₂ (X · ω) n :=
      CERW.Support.Main.ae_eventually_of_le_rpow
        (P := fun n ω => PotentialApprox d ε C₂ (X · ω) n) (n₀ := 2) hp1
        (fun n hn => hPA μ X hX n hn)
    filter_upwards [hIVae μ X hX, hae₂, hae₃] with ω h1 h2 h3
    filter_upwards [h1, h2, h3, eventually_ge_atTop n₁] with n g1 g2 g3 hn
    exact hgood (X · ω) n hn g1 g2 g3

end CERW.Support.Lower
