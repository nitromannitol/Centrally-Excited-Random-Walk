import CERW.Generic.Martingale.LilAssembly.PaddedConstruction

/-!
# The ratio field of the padded data

The ratio `B̃_n √(log log (Ṽ_n ∨ e^e)) / √Ṽ_n` of the padded bound and bracket tends to zero almost
surely: either the gate stays open and it is the ratio of the original process, or the gate
closes, the bound is `1` from then on and the bracket tends to infinity.
-/

namespace CERW.Generic.Martingale.LilAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open CERW.Generic.Martingale.LilLower
open CERW.Generic.Martingale.CLT (pathBracket)

variable {Ω : Type*} {Ξ : Type*} {m0 : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ}

/-- The quotient `√(log log (x ∨ e^e)) / √x` tends to zero as `x` tends to infinity. -/
private lemma tendsto_sqrt_loglog_div_sqrt :
    Tendsto (fun x : ℝ => Real.sqrt (Real.log (Real.log (max x (Real.exp (Real.exp 1))))) /
      Real.sqrt x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (Real.log x / x)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlog
    rwa [Real.sqrt_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun x => by positivity) ?_ hsqrt
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1))] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlx : Real.exp 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hx
  have h1 : 1 ≤ Real.log x := by linarith [Real.add_one_le_exp 1]
  rw [max_eq_left hx, ← Real.sqrt_div (Real.log_nonneg h1)]
  refine Real.sqrt_le_sqrt ?_
  exact div_le_div_of_nonneg_right (Real.log_le_self (by linarith)) hx0.le

/-- When the gate is open at every time, the ratio of the padded data tends to zero: from time `1`
on it is the product of `max (B n) 0` and the nonnegative square-root quotient of the bracket, so
it is squeezed by the absolute value of the ratio of the original data. -/
private lemma padData_bRatio_of_open (μ : Measure Ω) (ℱ : Filtration ℕ m0) {S B : ℕ → Ω → ℝ}
    (εg : ℝ) (N : ℕ) (z : Ω × Ξ)
    (hR : Tendsto (fun n => B n z.1 *
      Real.sqrt (Real.log (Real.log (max (CERW.predBracket μ ℱ S S n z.1)
        (Real.exp (Real.exp 1))))) / Real.sqrt (CERW.predBracket μ ℱ S S n z.1)) atTop (𝓝 0))
    (hpath : ∀ n, pathBracket μ ℱ S n z.1 = CERW.predBracket μ ℱ S S n z.1)
    (hopen : ∀ j, padGate μ ℱ S B εg N j z.1 = 1) :
    Tendsto (fun n => padB (Ξ := Ξ) μ ℱ S B εg N n z *
      Real.sqrt (Real.log (Real.log (max (padVar (Ξ := Ξ) μ ℱ S B εg N n z)
        (Real.exp (Real.exp 1))))) /
          Real.sqrt (padVar (Ξ := Ξ) μ ℱ S B εg N n z)) atTop (𝓝 0) := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, r = fun n => Real.sqrt (Real.log (Real.log
      (max (CERW.predBracket μ ℱ S S n z.1) (Real.exp (Real.exp 1))))) /
        Real.sqrt (CERW.predBracket μ ℱ S S n z.1) := ⟨_, rfl⟩
  have hr0 : ∀ n, 0 ≤ r n := fun n => by rw [hr]; positivity
  have habs : Tendsto (fun n => |B n z.1 * r n|) atTop (𝓝 0) := by
    have h := hR.abs
    rw [abs_zero] at h
    refine h.congr fun n => ?_
    rw [hr, mul_div_assoc]
  have hgate : ∀ n, 1 ≤ n → padB (Ξ := Ξ) μ ℱ S B εg N n z *
      Real.sqrt (Real.log (Real.log (max (padVar (Ξ := Ξ) μ ℱ S B εg N n z)
        (Real.exp (Real.exp 1))))) / Real.sqrt (padVar (Ξ := Ξ) μ ℱ S B εg N n z) =
          max (B n z.1) 0 * r n := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hB : padB (Ξ := Ξ) μ ℱ S B εg N (k + 1) z = max (B (k + 1) z.1) 0 := by
      show padGate μ ℱ S B εg N k z.1 * max (B (k + 1) z.1) 0 +
        (1 - padGate μ ℱ S B εg N k z.1) = _
      rw [hopen k]
      ring
    have hV : padVar (Ξ := Ξ) μ ℱ S B εg N (k + 1) z = CERW.predBracket μ ℱ S S (k + 1) z.1 := by
      show paddedBracket (clipVar μ ℱ S) (padGate μ ℱ S B εg N) (k + 1) z.1 = _
      rw [paddedBracket_eq_of_gate fun j _ => hopen j, ← hpath]
      rfl
    rw [hB, hV, mul_div_assoc, hr]
  refine squeeze_zero' ?_ ?_ habs
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hgate n hn]
    exact mul_nonneg (le_max_right _ _) (hr0 n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hgate n hn]
    calc max (B n z.1) 0 * r n ≤ |B n z.1| * r n :=
          mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (hr0 n)
      _ = |B n z.1 * r n| := by rw [abs_mul, abs_of_nonneg (hr0 n)]

/-- When the gate closes, the ratio of the padded data tends to zero. -/
private lemma padData_bRatio_of_closed (μ : Measure Ω) (ℱ : Filtration ℕ m0) {S B : ℕ → Ω → ℝ}
    (εg : ℝ) (N : ℕ) (z : Ω × Ξ)
    (hP : Tendsto (fun n => CERW.predBracket μ ℱ S S n z.1) atTop atTop)
    (hpath : ∀ n, pathBracket μ ℱ S n z.1 = CERW.predBracket μ ℱ S S n z.1)
    (hclosed : ∃ j, padGate μ ℱ S B εg N j z.1 ≠ 1) :
    Tendsto (fun n => padB (Ξ := Ξ) μ ℱ S B εg N n z *
      Real.sqrt (Real.log (Real.log (max (padVar (Ξ := Ξ) μ ℱ S B εg N n z)
        (Real.exp (Real.exp 1))))) /
          Real.sqrt (padVar (Ξ := Ξ) μ ℱ S B εg N n z)) atTop (𝓝 0) := by
  obtain ⟨j₀, hj₀⟩ := hclosed
  have hG : ∀ j, padGate μ ℱ S B εg N j z.1 = 0 ∨ padGate μ ℱ S B εg N j z.1 = 1 :=
    fun j => levelGate_eq_zero_or_one _ _ _ _ _
  have hanti : ∀ j, padGate μ ℱ S B εg N (j + 1) z.1 ≤ padGate μ ℱ S B εg N j z.1 :=
    fun j => levelGate_antitone _ _ _ _ _
  have hzero : ∀ j, j₀ ≤ j → padGate μ ℱ S B εg N j z.1 = 0 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact (hG j₀).resolve_right hj₀
    | succ j _ ih =>
      rcases hG (j + 1) with h | h
      · exact h
      · have h1 := hanti j
        rw [h, ih] at h1
        exact absurd h1 (by norm_num)
  have hc : ∀ j, 0 ≤ clipVar μ ℱ S j z.1 := fun j => le_max_right _ _
  have hP' : Tendsto (fun n => ∑ j ∈ Finset.range n, clipVar μ ℱ S j z.1) atTop atTop :=
    hP.congr fun n => (hpath n).symm
  have hV : Tendsto (fun n => padVar (Ξ := Ξ) μ ℱ S B εg N n z) atTop atTop :=
    tendsto_paddedBracket_atTop hc hG hanti hP'
  refine (tendsto_sqrt_loglog_div_sqrt.comp hV).congr' ?_
  filter_upwards [eventually_ge_atTop (j₀ + 1)] with n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hB : padB (Ξ := Ξ) μ ℱ S B εg N (k + 1) z = 1 := by
    show padGate μ ℱ S B εg N k z.1 * max (B (k + 1) z.1) 0 +
      (1 - padGate μ ℱ S B εg N k z.1) = 1
    rw [hzero k (by omega)]
    ring
  rw [hB, one_mul]
  rfl

/-- The ratio of the hypothesis of the law tends to zero for the padded data. -/
theorem padData_bRatio
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (ℱ : Filtration ℕ m0) {S B : ℕ → Ω → ℝ} (hS : SureData μ ℱ S B) (εg : ℝ) (N : ℕ) :
    ∀ᵐ z ∂(μ.prod ν), Tendsto (fun n => padB (Ξ := Ξ) μ ℱ S B εg N n z *
      Real.sqrt (Real.log (Real.log (max (padVar (Ξ := Ξ) μ ℱ S B εg N n z)
        (Real.exp (Real.exp 1))))) /
          Real.sqrt (padVar (Ξ := Ξ) μ ℱ S B εg N n z)) atTop (𝓝 0) := by
  have hpath : ∀ᵐ ω ∂μ, ∀ k, pathBracket μ ℱ S k ω = CERW.predBracket μ ℱ S S k ω :=
    ae_all_iff.2 fun k => CERW.Generic.Martingale.CLT.pathBracket_ae_eq_predBracket μ ℱ S k
  have h1 : ∀ᵐ ω ∂μ, Tendsto (fun n => CERW.predBracket μ ℱ S S n ω) atTop atTop := hS.vInf
  have h2 := hS.bRatio
  have h3 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (h1.and (h2.and hpath))
  filter_upwards [h3] with z hz
  by_cases hopen : ∀ j, padGate μ ℱ S B εg N j z.1 = 1
  · exact padData_bRatio_of_open μ ℱ εg N z hz.2.1 hz.2.2 hopen
  · exact padData_bRatio_of_closed μ ℱ εg N z hz.1 hz.2.2 (not_forall.1 hopen)

end CERW.Generic.Martingale.LilAssembly
