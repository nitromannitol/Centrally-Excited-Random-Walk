import CERW.Support.Outer.Radius.RampMartingale

/-!
# Ramp Probability

Martingale tails are summed over lattice directions and ramp levels. The resulting probability bound
produces the uniform linear martingale event.
The retained labels `eq:linear-mart`
refer to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

section

open CERW.Support.Law CERW.Support.LocalTime
open LatticeProb (ballFinset mem_ballFinset_iff card_ballFinset_le)

/-- One ramp: Freedman's inequality at dyadic brackets bounds the probability that the Dynkin
martingale of the ramp exceeds `c (√(max(V, 1) L) + 2L)`, `V` the count, `L = log (n + 2)`. -/
lemma lm_event_bound (hd : 1 ≤ d) {ε : ℝ} (hε : 0 ≤ ε) (hεd : ε < 1 / (d : ℝ))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → Site d}, IsCERW μ ε X → ∀ n : ℕ, 1 ≤ n →
        ∀ {q : EuclideanSpace ℝ (Fin d)}, ‖q‖ ≤ 1 → ∀ a : ℝ,
        μ {ω | c * (Real.sqrt (max (lm_count q a X n ω) 1 * Real.log (n + 2)) +
            2 * Real.log (n + 2)) <
            |dynkin ε (fun z => max (inner ℝ q (toSpace z) - a) 0) X n ω|} ≤
          ENNReal.ofReal (((n : ℝ) + 1) * (2 * Real.exp (-(K * Real.log (n + 2))))) := by
  obtain ⟨c, hc1, hc⟩ := CERW.Generic.Martingale.exists_dyadic_bound hK
  refine ⟨c, hc1, ?_⟩
  intro Ω _ μ _ X hX n hn q hq a
  obtain ⟨M, hM, hbd, hvar, hae⟩ := lm_exists_clamped hd hε hεd hX hq a
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hVW : ∀ ω, lm_count q a X (0 + n) ω - lm_count q a X 0 ω ≤ n := by
    intro ω
    rw [zero_add, lm_count_zero, sub_zero]
    exact lm_count_le q a X n ω
  have hdy := hc hM (V := lm_count q a X) (lm_stronglyMeasurable_count hX.measurable q a)
    (lm_count_zero q a X) (lm_count_mono q a X) hvar (b := 2) (by norm_num) 0 n
    (fun i _ _ ω => hbd i ω) (W := n) hnR hL hVW
  refine le_trans (measure_mono_ae ?_) (hdy.trans ?_)
  · filter_upwards [hae] with ω hω hE
    change _ < _ at hE
    change _ < _
    rw [zero_add, lm_count_zero, sub_zero, hω n, hω 0, dynkin_zero, sub_zero]
    exact hE
  · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [Nat.ceil_natCast]
    have hclog : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    have : (Nat.clog 2 n : ℝ) ≤ n := by exact_mod_cast hclog
    linarith

/-- The deterministic step: for `ℓ = log n ≥ 1/2` and `ℓ ≤ L ≤ 2ℓ`, the Freedman threshold
`c (√(max(V, 1) L) + 2L)` is at most `6c (√(ℓ V) + ℓ)`. -/
lemma lm_threshold_arith {c : ℝ} (hc : 0 ≤ c) {V ℓ L : ℝ} (hV : 0 ≤ V) (hℓ : 1 / 2 ≤ ℓ)
    (hL2 : L ≤ 2 * ℓ) (hL0 : 0 ≤ L) :
    c * (Real.sqrt (max V 1 * L) + 2 * L) ≤ (6 * c) * (Real.sqrt (ℓ * V) + ℓ) := by
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hmax : max V 1 ≤ V + 1 := max_le (by linarith) (by linarith)
  have h1 : Real.sqrt (max V 1 * L) ≤ Real.sqrt (V * L) + Real.sqrt L := by
    calc Real.sqrt (max V 1 * L) ≤ Real.sqrt ((V + 1) * L) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmax hL0)
      _ = Real.sqrt (V * L + L) := by
          congr 1
          ring
      _ ≤ Real.sqrt (V * L) + Real.sqrt L := sqrt_add_le_add (mul_nonneg hV hL0) hL0
  have h2 : Real.sqrt (V * L) ≤ 2 * Real.sqrt (ℓ * V) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hℓ0 hV)]
    nlinarith [mul_nonneg hℓ0 hV, mul_le_mul_of_nonneg_left hL2 hV]
  have h3 : Real.sqrt L ≤ 2 * ℓ := by
    refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
    nlinarith
  have hsum : Real.sqrt (max V 1 * L) + 2 * L ≤ 6 * (Real.sqrt (ℓ * V) + ℓ) := by
    have := Real.sqrt_nonneg (ℓ * V)
    linarith
  calc c * (Real.sqrt (max V 1 * L) + 2 * L)
      ≤ c * (6 * (Real.sqrt (ℓ * V) + ℓ)) := mul_le_mul_of_nonneg_left hsum hc
    _ = (6 * c) * (Real.sqrt (ℓ * V) + ℓ) := by ring

/-- The arithmetic of the union bound: `(3(n+1))^D · (n+1) · (n+1) · 2 e^{-(p + D + 2)L}` is at
most `(3^D 2^{D+3}) n^{-p}`. -/
lemma lm_union_arith {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (D : ℕ) :
    (3 * ((n : ℝ) + 1)) ^ D * (((n : ℝ) + 1) * (((n : ℝ) + 1) *
      (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))) ≤
    (3 ^ D * 2 ^ (D + 3)) * (n : ℝ) ^ (-p) := by
  have h1 := CERW.Generic.Martingale.two_mul_exp_neg_mul_log_le
    (K := p + ((D + 2 : ℕ) : ℝ)) (by positivity) hn
  have h2 := CERW.Generic.Martingale.pow_mul_rpow_neg_le hn (D + 2) p
  have h3 : (0 : ℝ) ≤ 3 ^ D * ((n : ℝ) + 1) ^ (D + 2) := by positivity
  calc (3 * ((n : ℝ) + 1)) ^ D * (((n : ℝ) + 1) * (((n : ℝ) + 1) *
        (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))))
      = (3 ^ D * ((n : ℝ) + 1) ^ (D + 2)) *
          (2 * Real.exp (-((p + ((D + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) := by
        rw [mul_pow]
        ring
    _ ≤ (3 ^ D * ((n : ℝ) + 1) ^ (D + 2)) * (2 * (n : ℝ) ^ (-(p + ((D + 2 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 h3
    _ = 2 * 3 ^ D * (((n : ℝ) + 1) ^ (D + 2) * (n : ℝ) ^ (-(p + ((D + 2 : ℕ) : ℝ)))) := by
        ring
    _ ≤ 2 * 3 ^ D * (2 ^ (D + 2) * (n : ℝ) ^ (-p)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (3 ^ D * 2 ^ (D + 3)) * (n : ℝ) ^ (-p) := by ring

/-- `eq:linear-mart`: with probability at least `1 - C n^{-p}` the martingales of the ramps
`(u_s · x - k)₊` are bounded simultaneously for `|s| ≤ n` and `k ≤ n`. -/
theorem exists_linOK_prob (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) (hεd : ε < 1 / (d : ℝ)) {p : ℝ}
    (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → Site d), IsCERW μ ε X → ∀ n : ℕ, 2 ≤ n →
        μ {ω | ¬ LinOK d ε C (fun j => X j ω) n} ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-p)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hc1, hc⟩ := lm_event_bound hd1 hε.le hεd (K := p + ((d + 2 : ℕ) : ℝ))
    (by positivity)
  have hc0 : 0 ≤ c := by linarith
  have hA : (0 : ℝ) ≤ 3 ^ d * 2 ^ (d + 3) := by positivity
  refine ⟨6 * c + 3 ^ d * 2 ^ (d + 3), by positivity, ?_⟩
  intro Ω _ μ _ X hX n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set S : Finset (Site d × ℕ) := ballFinset d (n : ℝ) ×ˢ Finset.range (n + 1) with hS
  set B : Site d × ℕ → Set Ω := fun sk =>
    {ω | c * (Real.sqrt (max (lm_count (unitDir (toSpace sk.1)) (sk.2 : ℝ) X n ω) 1 *
        Real.log (n + 2)) + 2 * Real.log (n + 2)) <
      |dynkin ε (fun z => max (inner ℝ (unitDir (toSpace sk.1)) (toSpace z) - (sk.2 : ℝ)) 0)
        X n ω|} with hB
  have hbound : ∀ sk ∈ S, μ (B sk) ≤ ENNReal.ofReal (((n : ℝ) + 1) *
      (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2))))) := fun sk _ =>
    hc hX n (by omega) (norm_unitDir_le _) (sk.2 : ℝ)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log n := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    linarith
  have hlogle : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
    have h1 : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log (by linarith) h1
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hScard : (S.card : ℝ) ≤ (3 * ((n : ℝ) + 1)) ^ d * ((n : ℝ) + 1) := by
    have h1 : (S.card : ℝ) = ((ballFinset d (n : ℝ)).card : ℝ) * ((n : ℝ) + 1) := by
      rw [hS, Finset.card_product, Finset.card_range]
      push_cast
      ring
    rw [h1]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact (card_ballFinset_le d (R := (n : ℝ)) (by positivity)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) d)
  set a : ℝ := ((n : ℝ) + 1) *
    (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))) with ha
  have ha0 : 0 ≤ a := by positivity
  refine (measure_mono (t := ⋃ sk ∈ S, B sk) ?_).trans ?_
  · intro ω hω
    have hω' : ¬ LinOK d ε (6 * c + 3 ^ d * 2 ^ (d + 3)) (fun j => X j ω) n := hω
    unfold LinOK at hω'
    push Not at hω'
    obtain ⟨s, hs, k, hk, hlt⟩ := hω'
    simp only [Set.mem_iUnion]
    refine ⟨(s, k), ?_, ?_⟩
    · rw [hS, Finset.mem_product, mem_ballFinset_iff, Finset.mem_range]
      exact ⟨hs, by omega⟩
    · rw [lm_dynkinMart_eq hd1 ε _ X n ω,
        ← lm_count_eq_sum (unitDir (toSpace s)) (k : ℝ) X n ω] at hlt
      have hV0 : 0 ≤ lm_count (unitDir (toSpace s)) (k : ℝ) X n ω := by
        rw [lm_count_eq_sum]
        exact Finset.sum_nonneg fun z _ => Nat.cast_nonneg _
      have hthr := lm_threshold_arith hc0 hV0 hlog2 hlogle hlog0
      have hterm : 0 ≤ Real.sqrt (Real.log n * lm_count (unitDir (toSpace s)) (k : ℝ) X n ω) +
          Real.log n :=
        add_nonneg (Real.sqrt_nonneg _) (by linarith)
      have hmono : (6 * c) * (Real.sqrt (Real.log n *
            lm_count (unitDir (toSpace s)) (k : ℝ) X n ω) + Real.log n) ≤
          (6 * c + 3 ^ d * 2 ^ (d + 3)) * (Real.sqrt (Real.log n *
            lm_count (unitDir (toSpace s)) (k : ℝ) X n ω) + Real.log n) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA) hterm
      exact lt_of_le_of_lt (hthr.trans hmono) hlt
  · calc μ (⋃ sk ∈ S, B sk) ≤ ∑ sk ∈ S, μ (B sk) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _sk ∈ S, ENNReal.ofReal a := Finset.sum_le_sum hbound
      _ = ENNReal.ofReal ((S.card : ℝ) * a) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [ENNReal.ofReal_mul (p := (S.card : ℝ)) (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((6 * c + 3 ^ d * 2 ^ (d + 3)) * (n : ℝ) ^ (-p)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (S.card : ℝ) * a ≤
              (3 * ((n : ℝ) + 1)) ^ d * ((n : ℝ) + 1) * a :=
            mul_le_mul_of_nonneg_right hScard ha0
          have h2 := lm_union_arith hp.le (by omega : 1 ≤ n) d
          have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-p) := Real.rpow_nonneg (Nat.cast_nonneg n) _
          have h4 : (3 * ((n : ℝ) + 1)) ^ d * ((n : ℝ) + 1) * a =
              (3 * ((n : ℝ) + 1)) ^ d * (((n : ℝ) + 1) * (((n : ℝ) + 1) *
                (2 * Real.exp (-((p + ((d + 2 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 2)))))) := by
            rw [ha]
            ring
          have h5 : (0 : ℝ) ≤ (6 * c) * (n : ℝ) ^ (-p) := mul_nonneg (by linarith) h3
          rw [h4] at h1
          linarith

/-! ### The good event of local-time and crossing good events (`sec:local`, `sec:crossing`) -/

end

end CERW.Support.Outer.Radius
