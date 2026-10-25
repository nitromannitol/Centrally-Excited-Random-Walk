module

public import CERW.Support.Outer.Radius.LocalMassIntegral

@[expose] public section

/-!
# Higher Dimension Scales

The radius and logarithmic scales satisfy the inequalities needed in higher dimensions. These
estimates isolate the arithmetic used for exterior probes.
The section label `sec:outer-high`
refers to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

/-- For large `n`, the radius `r_n` is positive, `K log n ≤ r_n` and `4 r_n ≤ n`. -/
lemma hx_scales (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      0 < radius d ε n ∧ K * Real.log n ≤ radius d ε n ∧ 4 * radius d ε n ≤ n := by
  have hω : 0 < unitBallVolume d := unitBallVolume_pos d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc : 0 < ((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d) := by positivity
  have he : (0 : ℝ) < 1 / ((d : ℝ) + 1) := by positivity
  set a : ℝ := (((d : ℝ) + 1) / (2 * d * ε * unitBallVolume d)) ^ ((1 : ℝ) / (d + 1))
    with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hrad : ∀ n : ℕ, radius d ε n = a * (n : ℝ) ^ ((1 : ℝ) / (d + 1)) := by
    intro n
    rw [radius, ha_def, ← Real.mul_rpow hc.le (Nat.cast_nonneg n)]
    congr 1
    ring
  have hK1 : 0 < |K| + 1 := by positivity
  have h1 : ∀ᶠ n : ℕ in atTop, 4 * a ≤ (n : ℝ) ^ ((1 : ℝ) / (d + 1)) :=
    ((tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (4 * a)
  have h2 : ∀ᶠ n : ℕ in atTop,
      Real.log (n + 2) ^ (1 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (d + 1)) < a / (|K| + 1) :=
    (CERW.Support.Main.tendsto_log_rpow_div_rpow 1 he).eventually_lt_const (div_pos ha hK1)
  have h3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hA, hB, h1n⟩ := hn₀ n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / (d + 1)) with hN_def
  have hNpos : 0 < N := Real.rpow_pos_of_pos (by linarith) _
  rw [hrad n]
  refine ⟨mul_pos ha hNpos, ?_, ?_⟩
  · rw [Real.rpow_one, div_lt_iff₀ hNpos] at hB
    have hlog : Real.log n ≤ Real.log (n + 2) := Real.log_le_log (by linarith) (by linarith)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    calc K * Real.log n ≤ |K| * Real.log (n + 2) :=
          (mul_le_mul_of_nonneg_right (le_abs_self K) hlog0).trans
            (mul_le_mul_of_nonneg_left hlog (abs_nonneg K))
      _ ≤ (|K| + 1) * Real.log (n + 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (hlog0.trans hlog)
      _ ≤ (|K| + 1) * (a / (|K| + 1) * N) := mul_le_mul_of_nonneg_left hB.le hK1.le
      _ = a * N := by field_simp
  · have hN2 : N * N ≤ n := by
      rw [hN_def, ← Real.rpow_add (by linarith)]
      calc (n : ℝ) ^ ((1 : ℝ) / (d + 1) + 1 / (d + 1)) ≤ (n : ℝ) ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le hn1
            have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
            rw [← add_div, div_le_one (by positivity)]
            linarith
        _ = n := Real.rpow_one _
    calc 4 * (a * N) = (4 * a) * N := by ring
      _ ≤ N * N := mul_le_mul_of_nonneg_right hA hNpos.le
      _ ≤ n := hN2

/-- For `n ≥ 3`: `1 ≤ log n` and `log (n + 2) ≤ 2 log n`. -/
lemma hx_log_facts {n : ℕ} (hn : 3 ≤ n) :
    1 ≤ Real.log n ∧ Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    norm_num at h
    linarith
  · have h9 : (3 : ℝ) * n ≤ (n : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hn3 (by linarith)
    calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

/-- `log (n + √d + 2) ≤ (1 + log (1 + √d)) log (n + 2)` once `log (n + 2) ≥ 1`. -/
lemma hx_log_shift (d n : ℕ) (hL : 1 ≤ Real.log ((n : ℝ) + 2)) :
    Real.log ((n : ℝ) + Real.sqrt d + 2) ≤
      (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog1 : 0 ≤ Real.log (1 + Real.sqrt d) := Real.log_nonneg (by linarith)
  have hprod : (n : ℝ) + Real.sqrt d + 2 ≤ ((n : ℝ) + 2) * (1 + Real.sqrt d) := by
    have : 0 ≤ ((n : ℝ) + 1) * Real.sqrt d := mul_nonneg (by linarith) hs
    linarith
  have hmul : Real.log (1 + Real.sqrt d) * 1 ≤
      Real.log (1 + Real.sqrt d) * Real.log ((n : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hL hlog1
  calc Real.log ((n : ℝ) + Real.sqrt d + 2) ≤ Real.log (((n : ℝ) + 2) * (1 + Real.sqrt d)) :=
        Real.log_le_log (by linarith) hprod
    _ = Real.log ((n : ℝ) + 2) + Real.log (1 + Real.sqrt d) :=
        Real.log_mul (by linarith) (by linarith)
    _ ≤ (1 + Real.log (1 + Real.sqrt d)) * Real.log ((n : ℝ) + 2) := by linarith

/-- The arithmetic of Step 1: the point bound at an unvisited site, the bracket bound and the
cell modulus give `|U_E(y)| ≤ C_p Θ`. -/
lemma hx_probe_arith {C₁ Cenv γ μ κ Θ L Λ W h P U : ℝ} (hCenv : 0 ≤ Cenv)
    (hγ : 0 ≤ γ) (hμ : 0 ≤ μ) (hκ : 0 ≤ κ) (hL0 : 0 ≤ L) (hL : L ≤ 2 * Θ)
    (hpt : |0 - P| ≤ C₁ * (Real.sqrt (W * L) + L)) (hW : W ≤ Cenv * (L + h))
    (hh : h ≤ γ * Θ) (hmod : |U - P| ≤ μ * Λ) (hΛ : Λ ≤ κ * L) :
    |U| ≤ (max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + γ)) + 2) + 2 * μ * κ) * Θ := by
  have hΘ : 0 ≤ Θ := by linarith
  have hA : 0 ≤ Cenv * (2 + γ) := mul_nonneg hCenv (by linarith)
  have hW' : W ≤ Cenv * (2 + γ) * Θ := by
    calc W ≤ Cenv * (L + h) := hW
      _ ≤ Cenv * (2 * Θ + γ * Θ) := mul_le_mul_of_nonneg_left (by linarith) hCenv
      _ = Cenv * (2 + γ) * Θ := by ring
  have hWL : W * L ≤ 2 * Cenv * (2 + γ) * Θ ^ 2 := by
    calc W * L ≤ Cenv * (2 + γ) * Θ * L := mul_le_mul_of_nonneg_right hW' hL0
      _ ≤ Cenv * (2 + γ) * Θ * (2 * Θ) := mul_le_mul_of_nonneg_left hL (mul_nonneg hA hΘ)
      _ = 2 * Cenv * (2 + γ) * Θ ^ 2 := by ring
  have hsq : Real.sqrt (W * L) ≤ Real.sqrt (2 * Cenv * (2 + γ)) * Θ := by
    calc Real.sqrt (W * L) ≤ Real.sqrt (2 * Cenv * (2 + γ) * Θ ^ 2) := Real.sqrt_le_sqrt hWL
      _ = Real.sqrt (2 * Cenv * (2 + γ)) * Θ := by
          rw [Real.sqrt_mul (by linarith) (Θ ^ 2), Real.sqrt_sq hΘ]
  have hC : 0 ≤ max C₁ 0 := le_max_right _ _
  have hs0 : 0 ≤ Real.sqrt (W * L) + L := add_nonneg (Real.sqrt_nonneg _) hL0
  have hP : |P| ≤ max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + γ)) * Θ + 2 * Θ) := by
    calc |P| = |0 - P| := by rw [zero_sub, abs_neg]
      _ ≤ C₁ * (Real.sqrt (W * L) + L) := hpt
      _ ≤ max C₁ 0 * (Real.sqrt (W * L) + L) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
      _ ≤ max C₁ 0 * (Real.sqrt (2 * Cenv * (2 + γ)) * Θ + 2 * Θ) :=
          mul_le_mul_of_nonneg_left (by linarith) hC
  have hμΛ : μ * Λ ≤ μ * (κ * (2 * Θ)) :=
    mul_le_mul_of_nonneg_left (hΛ.trans (mul_le_mul_of_nonneg_left hL hκ)) hμ
  have hU : |U| - |P| ≤ |U - P| := abs_sub_abs_le_abs_sub U P
  linarith

/-- `ε/(ω b) I ≤ (2ε/ω) Θ` when `I ≤ r Θ` and `r ≤ 2b`. -/
lemma hx_outside_arith {ε ω b r I Θ : ℝ} (hε : 0 ≤ ε) (hω : 0 < ω) (hb : 0 < b)
    (hΘ : 0 ≤ Θ) (hI : I ≤ r * Θ) (hrb : r ≤ 2 * b) :
    ε / (ω * b) * I ≤ 2 * ε / ω * Θ := by
  have hc : 0 ≤ ε / (ω * b) := div_nonneg hε (mul_pos hω hb).le
  have hω' := hω.ne'
  have hb' := hb.ne'
  calc ε / (ω * b) * I ≤ ε / (ω * b) * (2 * b * Θ) :=
        mul_le_mul_of_nonneg_left (hI.trans (mul_le_mul_of_nonneg_right hrb hΘ)) hc
    _ = 2 * ε / ω * Θ := by field_simp

/-- `((X^{(d-2)/(d-1)} Y^{1/(d-1)})^{d-1} = X^{d-2} Y` for `X, Y ≥ 0`. -/
lemma hx_rpow_pow (hd : 3 ≤ d) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (X ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) * Y ^ ((1 : ℝ) / ((d : ℝ) - 1))) ^ (d - 1) =
      X ^ (d - 2) * Y := by
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hd2 : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hpos : (d : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [mul_pow, ← Real.rpow_natCast (X ^ _), ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hX,
    ← Real.rpow_mul hY, hd1, div_mul_cancel₀ _ hpos, div_mul_cancel₀ _ hpos, Real.rpow_one,
    ← hd2, Real.rpow_natCast]

/-- Step 4 of `sec:outer-high` (Young's inequality): if `Θ ≥ lg > 0` satisfies
`Θ ≤ lg + (c₁ w² + (d-1) (aΘ)^{(d-2)/(d-1)} (c r^{d-1} lg)^{1/(d-1)}) / r`, then
`Θ ≤ K (w²/r + lg)`. -/
lemma hx_theta_arith (hd : 3 ≤ d) {a c c₁ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hc₁ : 0 ≤ c₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ Θ lg r w : ℝ, 0 < lg → lg ≤ Θ → 0 < r →
      Θ ≤ lg + (c₁ * w ^ 2 + ((d : ℝ) - 1) * ((a * Θ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
        (c * r ^ (d - 1) * lg) ^ ((1 : ℝ) / ((d : ℝ) - 1)))) / r →
      Θ ≤ K * (w ^ 2 / r + lg) := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1ne : (d : ℝ) - 1 ≠ 0 := by linarith
  set k : ℝ := 2 * ((d : ℝ) - 1) with hk_def
  have hk : 0 < k := by linarith
  set M : ℝ := k ^ (d - 1) * a ^ (d - 2) * c with hM_def
  have hM : 0 < M := by positivity
  refine ⟨M + 2 + 2 * c₁, by linarith, ?_⟩
  intro Θ lg r w hlg hlgΘ hr h
  have hΘ : 0 < Θ := lt_of_lt_of_le hlg hlgΘ
  set F : ℝ := (a * Θ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1)) *
    (c * r ^ (d - 1) * lg) ^ ((1 : ℝ) / ((d : ℝ) - 1)) with hF_def
  have hF0 : 0 ≤ F := by positivity
  have hw2 : 0 ≤ w ^ 2 / r := div_nonneg (sq_nonneg w) hr.le
  have h1 : 0 ≤ M * (w ^ 2 / r) := mul_nonneg hM.le hw2
  have h2 : 0 ≤ c₁ * lg := mul_nonneg hc₁ hlg.le
  have h3 : 0 ≤ M * lg := mul_nonneg hM.le hlg.le
  have h4 : 0 ≤ c₁ * (w ^ 2 / r) := mul_nonneg hc₁ hw2
  rcases le_or_gt F (r * Θ / k) with hA | hB
  · have hdF : ((d : ℝ) - 1) * F ≤ r * Θ / 2 := by
      calc ((d : ℝ) - 1) * F ≤ ((d : ℝ) - 1) * (r * Θ / k) :=
            mul_le_mul_of_nonneg_left hA (by linarith)
        _ = r * Θ / 2 := by rw [hk_def]; field_simp
    have hdiv : (c₁ * w ^ 2 + ((d : ℝ) - 1) * F) / r ≤ c₁ * (w ^ 2 / r) + Θ / 2 := by
      rw [div_le_iff₀ hr]
      have e : (c₁ * (w ^ 2 / r) + Θ / 2) * r = c₁ * w ^ 2 + r * Θ / 2 := by
        field_simp
      rw [e]
      linarith
    linarith
  · have hpow : (r * Θ / k) ^ (d - 1) < F ^ (d - 1) :=
      pow_lt_pow_left₀ hB (by positivity) (by omega)
    have hFpow : F ^ (d - 1) = (a * Θ) ^ (d - 2) * (c * r ^ (d - 1) * lg) :=
      hx_rpow_pow hd (by positivity) (by positivity)
    have hΘpow : Θ ^ (d - 1) = Θ ^ (d - 2) * Θ := by
      rw [← pow_succ]
      congr 1
      omega
    have e1 : (r * Θ / k) ^ (d - 1) = r ^ (d - 1) * Θ ^ (d - 2) * Θ / k ^ (d - 1) := by
      rw [div_pow, mul_pow, hΘpow, mul_assoc]
    have e2 : (a * Θ) ^ (d - 2) * (c * r ^ (d - 1) * lg) =
        r ^ (d - 1) * Θ ^ (d - 2) * (a ^ (d - 2) * c * lg) := by
      rw [mul_pow]
      ring
    rw [hFpow, e1, e2, div_lt_iff₀ (pow_pos hk _), mul_assoc (r ^ (d - 1) * Θ ^ (d - 2))] at hpow
    have hP : 0 < r ^ (d - 1) * Θ ^ (d - 2) := by positivity
    have hlt : Θ < a ^ (d - 2) * c * lg * k ^ (d - 1) := lt_of_mul_lt_mul_left hpow hP.le
    have hΘM : Θ ≤ M * lg := by
      rw [hM_def]
      linarith
    linarith

end CERW.Support.Outer.Radius
