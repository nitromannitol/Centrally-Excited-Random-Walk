import CERW.Model
import CERW.Generic.Martingale.Clamp
import CERW.Generic.Martingale.Dyadic

/-!
# Freedman's inequality at a logarithmic threshold for the predictable bracket

For a real martingale `Z` whose increments are almost surely at most `1` in modulus, the
increment `Z_n - Z_0` is at most `C (√(⟨Z⟩_n log n) + log n)` outside an event of probability at
most `C n^{-p}` (Lemma `lem:freedman` of the paper). The proof replaces `Z` by the almost surely
equal martingale with surely bounded increments, replaces the predictable bracket by a
nondecreasing adapted version bounded by `n` everywhere, and applies the dyadic form of
Freedman's inequality at the threshold `L = log n` with `K = p + 1` and `W = n`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Norm

/-- A martingale with increments of modulus at most `1` everywhere has a bracket version `V`
that is adapted, starts at `0`, is nondecreasing, is at most `k` at time `k` everywhere,
dominates the conditional variances of the increments, and agrees almost surely with the
predictable bracket of any process that almost surely agrees with `M`. -/
private lemma exists_bracket_version {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {M Z : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hb : ∀ i ω, |M (i + 1) ω - M i ω| ≤ 1)
    (hae : ∀ᵐ ω ∂μ, ∀ i, M i ω = Z i ω) :
    ∃ V : ℕ → Ω → ℝ, (∀ k, StronglyMeasurable[ℱ k] (V (k + 1))) ∧ (∀ ω, V 0 ω = 0) ∧
      (∀ k ω, V k ω ≤ V (k + 1) ω) ∧ (∀ k ω, V k ω ≤ k) ∧
      (∀ k, μ[fun ω => (M (k + 1) ω - M k ω) ^ 2 | ℱ k] ≤ᵐ[μ]
        fun ω => V (k + 1) ω - V k ω) ∧
      ∀ᵐ ω ∂μ, ∀ k, V k ω = CERW.predBracket μ ℱ Z Z k ω := by
  set e : ℕ → Ω → ℝ := fun t => μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t] with he
  have hint : ∀ t, Integrable (fun ω => (M (t + 1) ω - M t ω) ^ 2) μ := by
    intro t
    have hmeas : StronglyMeasurable fun ω => (M (t + 1) ω - M t ω) ^ 2 :=
      (((hM.stronglyMeasurable (t + 1)).mono (ℱ.le (t + 1))).sub
        ((hM.stronglyMeasurable t).mono (ℱ.le t))).pow 2
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have h := hb t ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    calc |M (t + 1) ω - M t ω| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 1 := one_pow 2
  have he01 : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ e t ω ∧ e t ω ≤ 1 := by
    intro t
    have hlow : 0 ≤ᵐ[μ] e t :=
      condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    have hup : e t ≤ᵐ[μ] μ[fun _ : Ω => (1 : ℝ) | ℱ t] :=
      condExp_mono (hint t) (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall fun ω => by
        have h := hb t ω
        calc (M (t + 1) ω - M t ω) ^ 2 = |M (t + 1) ω - M t ω| ^ 2 := (sq_abs _).symm
          _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
          _ = 1 := one_pow 2)
    rw [condExp_const (ℱ.le t) (1 : ℝ)] at hup
    filter_upwards [hlow, hup] with ω h1 h2
    exact ⟨h1, h2⟩
  set d : ℕ → Ω → ℝ := fun t ω => max 0 (min 1 (e t ω)) with hd
  have hd_nonneg : ∀ t ω, 0 ≤ d t ω := fun t ω => le_max_left _ _
  have hd_le_one : ∀ t ω, d t ω ≤ 1 := fun t ω => max_le zero_le_one (min_le_left _ _)
  have hd_eq : ∀ t, ∀ᵐ ω ∂μ, d t ω = e t ω := by
    intro t
    filter_upwards [he01 t] with ω h
    simp only [hd]
    rw [min_eq_right h.2, max_eq_right h.1]
  have hd_meas : ∀ t, StronglyMeasurable[ℱ t] (d t) := by
    intro t
    have hcont : Continuous fun x : ℝ => max 0 (min 1 x) :=
      continuous_const.max (continuous_const.min continuous_id)
    exact hcont.comp_stronglyMeasurable (stronglyMeasurable_condExp (m := ℱ t))
  refine ⟨fun k ω => ∑ t ∈ Finset.range k, d t ω, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    refine Finset.stronglyMeasurable_fun_sum _ fun t ht => ?_
    have htk : t ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    exact (hd_meas t).mono (ℱ.mono htk)
  · intro ω
    simp only [Finset.range_zero, Finset.sum_empty]
  · intro k ω
    beta_reduce
    rw [Finset.sum_range_succ]
    have := hd_nonneg k ω
    linarith
  · intro k ω
    induction k with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, le_refl]
    | succ k ih =>
        beta_reduce at ih ⊢
        rw [Finset.sum_range_succ, Nat.cast_succ]
        have := hd_le_one k ω
        linarith
  · intro k
    filter_upwards [hd_eq k] with ω h
    rw [Finset.sum_range_succ, add_sub_cancel_left, h]
  · have hall : ∀ᵐ ω ∂μ, ∀ t, d t ω = μ[fun ω => (Z (t + 1) ω - Z t ω) *
        (Z (t + 1) ω - Z t ω) | ℱ t] ω := by
      refine ae_all_iff.mpr fun t => ?_
      have hcongr : μ[fun ω => (M (t + 1) ω - M t ω) ^ 2 | ℱ t] =ᵐ[μ]
          μ[fun ω => (Z (t + 1) ω - Z t ω) * (Z (t + 1) ω - Z t ω) | ℱ t] := by
        refine condExp_congr_ae ?_
        filter_upwards [hae] with ω h
        rw [h (t + 1), h t, sq]
      filter_upwards [hd_eq t, hcongr] with ω h1 h2
      rw [h1]
      exact h2
    filter_upwards [hall] with ω hω k
    unfold CERW.predBracket
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => hω t

/-- The threshold comparison: replacing `max V 1` by `V` in the dyadic Freedman threshold
costs a constant factor, for `V ≥ 0`, `c ≥ 0` and `L ≥ 1/4`. -/
private lemma dyadic_threshold_le {c V L : ℝ} (hc : 0 ≤ c) (hV : 0 ≤ V) (hL : 1 / 4 ≤ L) :
    c * (Real.sqrt (max V 1 * L) + 1 * L) ≤ (3 * c + 4) * (Real.sqrt (V * L) + L) := by
  have hL0 : 0 ≤ L := by linarith
  have hVL : 0 ≤ V * L := mul_nonneg hV hL0
  set s : ℝ := Real.sqrt (V * L) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = V * L := Real.sq_sqrt hVL
  have hmax : max V 1 ≤ V + 1 := max_le (by linarith) (by linarith)
  have hmaxL : max V 1 * L ≤ (V + 1) * L := mul_le_mul_of_nonneg_right hmax hL0
  have h4L : L ≤ 4 * L ^ 2 := by nlinarith
  have hsq : Real.sqrt (max V 1 * L) ≤ s + 2 * L := by
    refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
    have hsL : 0 ≤ s * L := mul_nonneg hs0 hL0
    nlinarith
  have h1 : c * (Real.sqrt (max V 1 * L) + 1 * L) ≤ c * (s + 3 * L) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  have h2 : c * (s + 3 * L) ≤ (3 * c + 4) * (s + L) := by
    have hcs : 0 ≤ c * s := mul_nonneg hc hs0
    nlinarith
  exact le_trans h1 h2

/-- The union bound of the dyadic levels: at `K = p + 1`, `L = log n` and `W = n`, the failure
probability `(⌈log₂ n⌉ + 1) · 2 e^{-K L}` is at most `4 n^{-p}`. -/
private lemma dyadic_failure_le {p : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    ((Nat.clog 2 ⌈(n : ℝ)⌉₊ : ℝ) + 1) * (2 * Real.exp (-((p + 1) * Real.log n)))
      ≤ 4 * (n : ℝ) ^ (-p) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hexp : Real.exp (-((p + 1) * Real.log n)) = (n : ℝ) ^ (-(p + 1)) := by
    rw [Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  have hclog : (Nat.clog 2 ⌈(n : ℝ)⌉₊ : ℝ) ≤ n := by
    rw [Nat.ceil_natCast]
    exact_mod_cast Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := n)).le
  have hpow := CERW.Generic.Martingale.pow_mul_rpow_neg_le (n := n) (by omega) 1 p
  simp only [Nat.cast_one, pow_one] at hpow
  have hrpow : 0 ≤ (n : ℝ) ^ (-(p + 1)) := Real.rpow_nonneg hnpos.le _
  rw [hexp]
  calc ((Nat.clog 2 ⌈(n : ℝ)⌉₊ : ℝ) + 1) * (2 * (n : ℝ) ^ (-(p + 1)))
      ≤ ((n : ℝ) + 1) * (2 * (n : ℝ) ^ (-(p + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg zero_le_two hrpow)
    _ = 2 * (((n : ℝ) + 1) * (n : ℝ) ^ (-(p + 1))) := by ring
    _ ≤ 2 * (2 * (n : ℝ) ^ (-p)) := mul_le_mul_of_nonneg_left hpow zero_le_two
    _ = 4 * (n : ℝ) ^ (-p) := by ring

theorem freedman_bound :
    ∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
      ∀ {Ω : Type u} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ℱ : Filtration ℕ m0) (Z : ℕ → Ω → ℝ), Martingale Z ℱ μ →
        (∀ᵐ ω ∂μ, ∀ t, |Z (t + 1) ω - Z t ω| ≤ 1) →
        μ {ω | ¬ |Z n ω - Z 0 ω|
            ≤ C * (Real.sqrt (CERW.predBracket μ ℱ Z Z n ω * Real.log n) + Real.log n)}
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  intro p hp
  obtain ⟨c, hc1, hc⟩ :=
    CERW.Generic.Martingale.exists_dyadic_bound.{u} (K := p + 1) (by linarith)
  refine ⟨3 * c + 4, by linarith, ?_⟩
  intro n hn Ω m0 μ hμ ℱ Z hZ hinc
  obtain ⟨M, hM, hMb, -, hMae⟩ :=
    CERW.Generic.Martingale.exists_martingale_clamp hZ zero_le_one (ae_all_iff.mp hinc)
  obtain ⟨V, hVpred, hV0, hVmono, hVn, hVdom, hVae⟩ := exists_bracket_version hM hMb hMae
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hL4 : 1 / 4 ≤ Real.log n := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 1 - (2 : ℝ)⁻¹ ≤ Real.log 2 := Real.one_sub_inv_le_log_of_pos zero_lt_two
    have hmono : Real.log 2 ≤ Real.log n := Real.log_le_log zero_lt_two h2
    norm_num at hlog
    linarith
  have hdy := hc hM hVpred hV0 hVmono hVdom (b := 1) one_pos 0 n
    (fun i _ _ ω => hMb i ω) (W := (n : ℝ)) (L := Real.log n) hn1 hL (fun ω => by
      rw [zero_add, hV0 ω, sub_zero]
      exact hVn n ω)
  have hfail := dyadic_failure_le (p := p) hn
  have hcast : ⌈(n : ℝ)⌉₊ = n := Nat.ceil_natCast n
  have hsub : {ω | ¬ |Z n ω - Z 0 ω|
        ≤ (3 * c + 4) * (Real.sqrt (CERW.predBracket μ ℱ Z Z n ω * Real.log n) + Real.log n)}
      ≤ᵐ[μ] {ω | c * (Real.sqrt (max (V (0 + n) ω - V 0 ω) 1 * Real.log n) + 1 * Real.log n)
        < |M (0 + n) ω - M 0 ω|} := by
    filter_upwards [hMae, hVae] with ω h1 h2 hω
    have hω' : (3 * c + 4) * (Real.sqrt (CERW.predBracket μ ℱ Z Z n ω * Real.log n)
        + Real.log n) < |Z n ω - Z 0 ω| := not_le.mp hω
    have hVnn : 0 ≤ V n ω := by
      have hmono : Monotone fun k => V k ω :=
        monotone_nat_of_le_succ fun k => hVmono k ω
      calc (0 : ℝ) = V 0 ω := (hV0 ω).symm
        _ ≤ V n ω := hmono (Nat.zero_le n)
    rw [← h2 n] at hω'
    show c * (Real.sqrt (max (V (0 + n) ω - V 0 ω) 1 * Real.log n) + 1 * Real.log n)
      < |M (0 + n) ω - M 0 ω|
    rw [zero_add, hV0 ω, sub_zero, h1 n, h1 0]
    exact lt_of_le_of_lt (dyadic_threshold_le (by linarith) hVnn hL4) hω'
  refine le_trans (measure_mono_ae hsub) (le_trans hdy ?_)
  apply ENNReal.ofReal_le_ofReal
  rw [hcast] at hfail ⊢
  have hrpow : 0 ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg hnpos.le _
  calc ((Nat.clog 2 n : ℝ) + 1) * (2 * Real.exp (-((p + 1) * Real.log n)))
      ≤ 4 * (n : ℝ) ^ (-p) := hfail
    _ ≤ (3 * c + 4) * (n : ℝ) ^ (-p) :=
        mul_le_mul_of_nonneg_right (by linarith) hrpow

end CERW.Support.Norm
