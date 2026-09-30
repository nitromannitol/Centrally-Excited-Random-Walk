import CERW.Support.Main.GoodEvent
import CERW.Support.Contact.Volume
import CERW.Support.Contact.Profile
import CERW.Support.Contact.Envelope
import CERW.Support.Occupation.CellSetVolume
import CERW.Support.Main.ScaleLimits

/-!
# The inner clauses of the fluctuation event

Deterministically, for all large `n`. Take an inradius `b > 0` with `|b/N - a| ≤ C₂ Q`,
`B(0, b) ⊆ D_n ⊆ B(0, (K - 1) N)`, excess volume at most `C₂ N^d Q`, the global approximation
`|ℓ̃_n - U| ≤ δ₀ ≤ C₂ N Q^{1/d}` on `B(0, K N)`, and an unvisited site `z` with
`|z| ≤ b + √d/2`. These give four clauses of `fluctGood`, plus a site outside `A_n` near radius
`a N`:
1. the inner inclusion, from `mem_departureRange_of_lt` and `b ≥ (a - C₂ Q) N`;
2. `A_n ⊆ V_n`;
3. the volume clause, from `exists_volume_symmDiff_add_le` and `volume_cellSet`;
4. the profile clause, from `exists_abs_localTime_div_sub_le`;
5. the unvisited site `z ∉ A_n`, with `|z| < a N + C N Q` since `N Q → ∞`.
-/

namespace CERW.Support.Main

open MeasureTheory Filter LatticeProb CERW
open scoped symmDiff Pointwise

variable {d : ℕ}

/-- For `N > 0` and `L ≥ 0`, `N (L / N)^α = N^(1-α) L^α`. -/
private lemma mul_div_rpow_eq {N L α : ℝ} (hN : 0 < N) (hL : 0 ≤ L) :
    N * (L / N) ^ α = N ^ (1 - α) * L ^ α := by
  have hNα : N ^ α ≠ 0 := (Real.rpow_pos_of_pos hN α).ne'
  rw [Real.div_rpow hL hN.le, Real.rpow_sub hN 1 α, Real.rpow_one]
  field_simp

/-- The inner deficit `N Q` is eventually at least `1`, so the unvisited site can be absorbed
into a `C N Q` margin. -/
private lemma eventually_one_le_rate_mul {d : ℕ} (hd : 2 ≤ d) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * rate d n := by
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n + 2) :=
    (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog] with n hn1 hL1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := Real.rpow_pos_of_pos hnpos _
  have hN1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
    Real.one_le_rpow (by exact_mod_cast hn1) (by positivity)
  have hL0 : 0 ≤ Real.log (n + 2) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
  rw [rate]
  by_cases h2 : d = 2
  · rw [if_pos h2]
    rw [mul_div_rpow_eq (N := (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
      (L := Real.log (n + 2)) (α := (1 : ℝ) / 2) hNpos hL0]
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hN1 (by norm_num)) (Real.one_le_rpow hL1 (by norm_num))
  · rw [if_neg h2]
    rw [mul_div_rpow_eq (N := (n : ℝ) ^ ((1 : ℝ) / (d + 1)))
      (L := Real.log (n + 2)) (α := (d : ℝ) / (2 * d - 1)) hNpos hL0]
    have hd3 : 3 ≤ d := by omega
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hden : (0 : ℝ) < 2 * (d : ℝ) - 1 := by
      have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd3
      linarith
    have hα0 : 0 ≤ (d : ℝ) / (2 * d - 1) := div_nonneg hdR.le hden.le
    have hβ0 : 0 ≤ 1 - (d : ℝ) / (2 * d - 1) := by
      rw [sub_nonneg, div_le_one hden]
      have h1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      linarith
    exact one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hN1 hβ0) (Real.one_le_rpow hL1 hα0)

/-- The inner inclusion, the volume and profile clauses of `fluctGood`, and an unvisited site
near radius `a N`, from the inradius, the excess volume and the global approximation. -/
theorem exists_inner_clauses (hd : 2 ≤ d) {ε C₂ K : ℝ} (hε : 0 < ε) (hC₂ : 0 ≤ C₂) :
    let ωd : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
    let a : ℝ := ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1))
    a + 1 ≤ K →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (Y : ℕ → Site d) (n : ℕ) (b δ₀ : ℝ) (z : Site d), n₀ ≤ n →
      let N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1))
      let L : ℝ := Real.log (n + 2)
      let Q : ℝ := if d = 2 then (L / N) ^ ((1 : ℝ) / 2) else (L / N) ^ ((d : ℝ) / (2 * d - 1))
      0 < b → Metric.ball 0 b ⊆ cellSet Y n → cellSet Y n ⊆ Metric.ball 0 ((K - 1) * N) →
      |b / N - a| ≤ C₂ * Q →
      (volume (cellSet Y n \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) b)).toReal
        ≤ C₂ * N ^ d * Q →
      δ₀ ≤ C₂ * N * Q ^ ((1 : ℝ) / d) →
      (∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ < K * N →
        |cellLocalTime Y n y - potential d ε (cellSet Y n) y| ≤ δ₀) →
      localTime Y n z = 0 → euclidNorm z ≤ b + Real.sqrt d / 2 →
        {x : Site d | euclidNorm x < (a - C * Q) * N} ⊆ ↑(departureRange Y n) ∧
        (↑(departureRange Y n) : Set (Site d)) ⊆ ↑(visitedRange Y n) ∧
        volume ((N⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a)
            + ENNReal.ofReal |((departureRange Y n).card : ℝ) / N ^ d - ωd * a ^ d|
          ≤ ENNReal.ofReal (C * Q) ∧
        (∀ x : Site d,
          |(localTime Y n x : ℝ) / N - 2 * d * ε * max (a - euclidNorm x / N) 0|
            ≤ C * Q ^ ((1 : ℝ) / d)) ∧
        z ∉ departureRange Y n ∧ euclidNorm z < a * N + C * N * Q := by
  intro ωd a haK
  have hω : 0 < ωd := unitBallVolume_pos d
  have ha : 0 < a := by
    have h : a = ((d + 1) / (2 * d * ε * ωd)) ^ ((1 : ℝ) / (d + 1)) := rfl
    rw [h]
    exact Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨C_v, hC_v_pos, hC_v⟩ :=
    CERW.Support.Contact.exists_volume_symmDiff_add_le (d := d) (by omega)
      (a := a) (C₁ := C₂) ha hC₂
  obtain ⟨C_p, hC_p_pos, hC_p⟩ :=
    CERW.Support.Contact.exists_abs_localTime_div_sub_le (d := d) hd (a := a)
      (C₁ := C₂) (K := K) hε hC₂ haK
  have hQle : ∀ᶠ n : ℕ in atTop, rate d n ≤ 1 :=
    ((tendsto_rate_zero hd).eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun n hn => le_of_lt hn)
  have hev : ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ rate d n ≤ 1 ∧ 1 ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) * rate d n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hQle,
      eventually_one_le_rate_mul hd] with n hn1 hQ1 hNQ
    exact ⟨hn1, hQ1, hNQ⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  set C : ℝ := C_v + C_p + C₂ + Real.sqrt d + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, hCpos, n₀, ?_⟩
  intro Y n b δ₀ z hn N L Q hb hball hDsub hba hexcess hδ hall hz hznorm
  have hn1 : 1 ≤ n := (hn₀ n hn).1
  have hQ1 : Q ≤ 1 := (hn₀ n hn).2.1
  have hNQ1 : 1 ≤ N * Q := (hn₀ n hn).2.2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < N := Real.rpow_pos_of_pos hnpos _
  have hQ0 : 0 ≤ Q := rate_nonneg d n
  have hCge_v : C_v ≤ C := by rw [hCdef]; linarith [hC_p_pos.le, hC₂, Real.sqrt_nonneg d]
  have hCge_p : C_p ≤ C := by rw [hCdef]; linarith [hC_v_pos.le, hC₂, Real.sqrt_nonneg d]
  have hCge₂ : C₂ ≤ C := by
    rw [hCdef]; linarith [hC_v_pos.le, hC_p_pos.le, Real.sqrt_nonneg d]
  have hDmeas : MeasurableSet (cellSet Y n) := CERW.Support.Occupation.measurableSet_cellSet Y n
  have hDfin : volume (cellSet Y n) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hDsub)
  have hv0 := hC_v (cellSet Y n) b N Q hDmeas hDfin hb.le hNpos hQ0 hQ1 hball hexcess hba
  rw [CERW.Support.Occupation.volume_cellSet, ENNReal.toReal_natCast] at hv0
  have hvol : volume ((N⁻¹ • cellSet Y n) ∆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) a)
      + ENNReal.ofReal |((departureRange Y n).card : ℝ) / N ^ d - ωd * a ^ d|
      ≤ ENNReal.ofReal (C * Q) := by
    refine le_trans hv0 ?_
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hCge_v hQ0
  have hb_lower : (a - C₂ * Q) * N ≤ b := by
    have h1 : a - C₂ * Q ≤ b / N := by
      have h2 := (abs_le.mp hba).1
      linarith
    calc (a - C₂ * Q) * N ≤ (b / N) * N := mul_le_mul_of_nonneg_right h1 hNpos.le
      _ = b := div_mul_cancel₀ b hNpos.ne'
  have hCQ_le : a - C * Q ≤ a - C₂ * Q := by
    have h2 : C₂ * Q ≤ C * Q := mul_le_mul_of_nonneg_right hCge₂ hQ0
    linarith
  have hinner : {x : Site d | euclidNorm x < (a - C * Q) * N} ⊆ ↑(departureRange Y n) := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    exact CERW.Support.Contact.mem_departureRange_of_lt Y n hball
      (lt_of_lt_of_le hx (le_trans (mul_le_mul_of_nonneg_right hCQ_le hNpos.le) hb_lower))
  have hAV : (↑(departureRange Y n) : Set (Site d)) ⊆ ↑(visitedRange Y n) := by
    intro x hx
    rw [visitedRange_eq_insert]
    exact Finset.mem_insert_of_mem hx
  have hbaN : |b - a * N| ≤ C₂ * N * Q := by
    have h1 : b - a * N = (b / N - a) * N := by
      rw [sub_mul, div_mul_cancel₀ b hNpos.ne']
    rw [h1, abs_mul, abs_of_pos hNpos]
    calc |b / N - a| * N ≤ (C₂ * Q) * N := mul_le_mul_of_nonneg_right hba hNpos.le
      _ = C₂ * N * Q := by ring
  have hprof0 := hC_p Y n b δ₀ N Q hNpos hQ0 hQ1 hb hball hDsub hbaN hexcess hδ hall
  have hprof : ∀ x : Site d,
      |(localTime Y n x : ℝ) / N - 2 * d * ε * max (a - euclidNorm x / N) 0|
        ≤ C * Q ^ ((1 : ℝ) / d) := by
    intro x
    have hQp0 : 0 ≤ Q ^ ((1 : ℝ) / d) := Real.rpow_nonneg hQ0 _
    exact le_trans (hprof0 x) (mul_le_mul_of_nonneg_right hCge_p hQp0)
  have hznot : z ∉ departureRange Y n := by
    rw [mem_departureRange_iff, hz]
    omega
  have hb_upper : b ≤ (a + C₂ * Q) * N := by
    have h1 : b / N ≤ a + C₂ * Q := by
      have h2 := (abs_le.mp hba).2
      linarith
    calc b = (b / N) * N := (div_mul_cancel₀ b hNpos.ne').symm
      _ ≤ (a + C₂ * Q) * N := mul_le_mul_of_nonneg_right h1 hNpos.le
  have hz_upper : euclidNorm z ≤ a * N + (C₂ * N * Q + Real.sqrt d / 2) := by
    have h2 : b + Real.sqrt d / 2 ≤ a * N + (C₂ * N * Q + Real.sqrt d / 2) := by
      have h3 : (a + C₂ * Q) * N = a * N + C₂ * N * Q := by ring
      linarith
    linarith
  have hstrict : C₂ * N * Q + Real.sqrt d / 2 < C * N * Q := by
    have hcoef : Real.sqrt d + 1 ≤ C - C₂ := by
      rw [hCdef]; linarith [hC_v_pos.le, hC_p_pos.le]
    have hnn : 0 ≤ C - C₂ := by rw [hCdef]; positivity
    have hCNQ : Real.sqrt d + 1 ≤ (C - C₂) * (N * Q) :=
      calc Real.sqrt d + 1 ≤ C - C₂ := hcoef
        _ = (C - C₂) * 1 := (mul_one (C - C₂)).symm
        _ ≤ (C - C₂) * (N * Q) := mul_le_mul_of_nonneg_left hNQ1 hnn
    have hlt : C₂ * N * Q + Real.sqrt d / 2 < C₂ * N * Q + (C - C₂) * (N * Q) := by
      linarith [hCNQ, Real.sqrt_nonneg d]
    have heq : C₂ * N * Q + (C - C₂) * (N * Q) = C * N * Q := by ring
    linarith
  have hzfinal : euclidNorm z < a * N + C * N * Q :=
    lt_of_le_of_lt hz_upper (by linarith [hstrict])
  exact ⟨hinner, hAV, hvol, hprof, hznot, hzfinal⟩

end CERW.Support.Main
