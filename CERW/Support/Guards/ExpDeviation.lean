import CERW.Frozen.ExpDeviation
import CERW.Support.Guards.ExpDeviationModel

/-!
# Guard for the exponential-deviation lemma

`lem:exp-deviation` is abstract. The guard applies it to a finite family of `m ≥ 2` sites of the
fair-coin model of `ExpDeviationModel`, with constants and parameters chosen after the constants
`c`, `C` of the lemma. The start and the increments of the sites satisfy the hypotheses only almost
surely, the brackets lie in `[1, 2]` and the cross brackets vanish, and the sites are continued after
time `n` by a jump, so they are martingales up to time `n` only. The window `C ≤ β ≤ c / b` is not
empty. The conclusions are used at the sites at time `n`: both lower tails at every site and every
`β` of the window, and, at `β = C`, the bound `1/2` for the probability that every site stays
below `c C`.
-/

namespace CERW.Support.Guards

open MeasureTheory ProbabilityTheory
open CoinSites

noncomputable section

/-- Parameters of the guard, chosen after `c` and `C`: `m ≥ 2` sites with `4 C e^{C³} ≤ m`, a step
size `b ≤ 1` with `C ≤ c / b`, `C³ b ≤ 1` and `4 C⁴ b ≤ 1`, and `L` rounds with `1 ≤ L b² ≤ 2`. -/
private lemma params {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    ∃ (m L : ℕ) (b : ℝ), 2 ≤ m ∧ 0 < L ∧ 0 < b ∧ C ≤ c / b ∧ C ^ 3 * b ≤ 1 ∧
      4 * C ^ 4 * b ≤ 1 ∧ 1 ≤ (L : ℝ) * b ^ 2 ∧ (L : ℝ) * b ^ 2 ≤ 2 ∧
      4 * C * Real.exp (C ^ 3) ≤ m := by
  set b : ℝ := min (min 1 (c / (2 * C))) (min (1 / (4 * C ^ 4)) (1 / C ^ 3)) with hbdef
  have hb0 : 0 < b :=
    lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity) (by positivity))
  have hb1 : b ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hb2 : b ≤ c / (2 * C) := (min_le_left _ _).trans (min_le_right _ _)
  have hb3 : b ≤ 1 / (4 * C ^ 4) := (min_le_right _ _).trans (min_le_left _ _)
  have hb4 : b ≤ 1 / C ^ 3 := (min_le_right _ _).trans (min_le_right _ _)
  set L : ℕ := ⌈(b ^ 2)⁻¹⌉₊ with hLdef
  have hL : 0 < L := Nat.ceil_pos.2 (by positivity)
  have hL1 : (b ^ 2)⁻¹ ≤ L := Nat.le_ceil _
  have hL2 : (L : ℝ) < (b ^ 2)⁻¹ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLb1 : 1 ≤ (L : ℝ) * b ^ 2 := by
    have := mul_le_mul_of_nonneg_right hL1 (sq_nonneg b)
    rwa [inv_mul_cancel₀ (by positivity)] at this
  have hLb2 : (L : ℝ) * b ^ 2 ≤ 2 := by
    have := mul_lt_mul_of_pos_right hL2 (by positivity : 0 < b ^ 2)
    rw [add_mul, inv_mul_cancel₀ (by positivity), one_mul] at this
    nlinarith
  refine ⟨⌈4 * C * Real.exp (C ^ 3)⌉₊ + 2, L, b, by omega, hL, hb0, ?_, ?_, ?_, hLb1, hLb2, ?_⟩
  · rw [le_div_iff₀ hb0]
    have := hb2
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  · have := hb4
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  · have := hb3
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  · push_cast
    have := Nat.le_ceil (4 * C * Real.exp (C ^ 3))
    linarith

/-- The lemma at a finite family of `m ≥ 2` martingales, each started at `0` and with increments of
size at most `b` only almost surely, and each a martingale up to time `n` only. -/
theorem exp_deviation_applies :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ (m n : ℕ) (b : ℝ), 2 ≤ m ∧ 0 < n ∧ 0 < b ∧ C ≤ c / b ∧
      (∀ i : Fin m, ¬ Martingale (stopped b m n i) filt law) ∧
      (∀ i : Fin m, ∃ ω, stopped b m n i 0 ω ≠ 0) ∧
      (∀ i : Fin m, ∃ t < n, ∃ ω, b < |stopped b m n i (t + 1) ω - stopped b m n i t ω|) ∧
      (∀ β : ℝ, C ≤ β → β * b ≤ c → ∀ i : Fin m,
        Real.exp (-(C * β ^ 2)) / 4 ≤ (law {ω | c * β ≤ stopped b m n i n ω}).toReal ∧
        Real.exp (-(C * β ^ 2)) / 4 ≤ (law {ω | stopped b m n i n ω ≤ -(c * β)}).toReal) ∧
      (law {ω | ∀ i : Fin m, stopped b m n i n ω < c * C}).toReal ≤ 1 / 2 := by
  obtain ⟨c, C, hc, hC, H⟩ := CERW.Frozen.exp_deviation.{0} 1 2 one_pos (by norm_num)
  obtain ⟨m, L, b, hm2, hL, hb0, hCb, hC3, hC4, hLb1, hLb2, hmC⟩ := params hc hC
  have hm : 0 < m := by omega
  have hn : 0 < m * L := Nat.mul_pos hm hL
  have hadp : ∀ i : Fin m, ∀ t ≤ m * L, StronglyMeasurable[filt t] (stopped b m (m * L) i t) :=
    fun i t ht => stronglyMeasurable_stopped i ht
  have hint : ∀ i : Fin m, ∀ t ≤ m * L, Integrable (stopped b m (m * L) i t) law :=
    fun i t ht => integrable_stopped i ht
  have hcond : ∀ i : Fin m, ∀ t < m * L,
      law[stopped b m (m * L) i (t + 1) | filt t] =ᵐ[law] stopped b m (m * L) i t :=
    fun i t ht => condExp_stopped i ht
  have hS0 : ∀ i : Fin m, ∀ᵐ ω ∂law, stopped b m (m * L) i 0 ω = 0 :=
    fun i => stopped_zero_ae b m (m * L) i
  have hinc : ∀ i : Fin m, ∀ t < m * L,
      ∀ᵐ ω ∂law, |stopped b m (m * L) i (t + 1) ω - stopped b m (m * L) i t ω| ≤ b :=
    fun i t ht => stopped_inc_ae hb0 m (m * L) i ht
  have hbrEq : ∀ i j : Fin m,
      CERW.predBracket law filt (stopped b m (m * L) i) (stopped b m (m * L) j) (m * L)
        =ᵐ[law] CERW.predBracket law filt (site b m i) (site b m j) (m * L) :=
    fun i j => predBracket_stopped b m (m * L) i j
  have hbr : ∀ i : Fin m, ∀ᵐ ω ∂law, ω ∈ (Set.univ : Set (ℕ → ℝ)) →
      1 ≤ CERW.predBracket law filt (stopped b m (m * L) i) (stopped b m (m * L) i) (m * L) ω ∧
        CERW.predBracket law filt (stopped b m (m * L) i) (stopped b m (m * L) i) (m * L) ω
          ≤ 2 := by
    intro i
    filter_upwards [hbrEq i i, predBracket_site_same b m i L] with ω h1 h2 _
    rw [h1, h2]
    exact ⟨hLb1, hLb2⟩
  have key := fun β (hβC : C ≤ β) (hβb : β * b ≤ c) =>
    H law filt m (m * L) hm hn b 0 0 hb0 le_rfl le_rfl zero_le_one
      (fun i => stopped b m (m * L) i) hadp hint hcond hS0 hinc Set.univ MeasurableSet.univ
      (by simp) hbr β hβC hβb
  have hwin : C * b ≤ c := (le_div_iff₀ hb0).1 hCb
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨c, C, hc, hC, m, m * L, b, hm2, hn, hb0, hCb,
    fun i => not_martingale_stopped b m (m * L) i, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨fun _ => 0, ?_⟩
    simp [stopped, site, coin]
  · intro i
    have hi : (i : ℕ) + 1 ≤ m * L :=
      (Nat.succ_le_of_lt i.isLt).trans (Nat.le_mul_of_pos_right m hL)
    refine ⟨i, Nat.lt_of_succ_le hi, fun k => if k = (i : ℕ) + 1 then 2 else 0, ?_⟩
    rw [stopped_eq hi, stopped_eq (Nat.le_of_succ_le hi), site_succ_sub]
    simp only [siteInc, Nat.mod_eq_of_lt i.isLt, if_true, coin, abs_mul, abs_of_pos hb0]
    norm_num
    linarith
  · intro β hβC hβb i
    obtain ⟨h1, h2⟩ := (key β hβC hβb).1 i
    exact ⟨by simpa using h1, by simpa using h2⟩
  · have hcr : ∀ i j : Fin m, i ≠ j → ∀ᵐ ω ∂law, ω ∈ (Set.univ : Set (ℕ → ℝ)) →
        |CERW.predBracket law filt (stopped b m (m * L) i) (stopped b m (m * L) j) (m * L) ω|
          ≤ 0 := by
      intro i j hij
      filter_upwards [hbrEq i j] with ω h _
      rw [h, predBracket_site_cross b m hij]
      simp
    have hsmall : C ^ 2 * 0 + C ^ 3 * b ≤ 1 := by simpa using hC3
    refine ((key C le_rfl hwin).2 hcr hsmall).trans ?_
    have e : C * C ^ 2 = C ^ 3 := by ring
    have h1 : C * ((m : ℝ)⁻¹ * Real.exp (C ^ 3)) ≤ 1 / 4 := by
      have : C * ((m : ℝ)⁻¹ * Real.exp (C ^ 3)) = C * Real.exp (C ^ 3) / m := by
        field_simp
      rw [this, div_le_iff₀ hmpos]
      linarith
    have h2 : C * (C ^ 3 * b) ≤ 1 / 4 := by
      have : C * (C ^ 3 * b) = C ^ 4 * b := by ring
      rw [this]
      linarith
    have h3 : C * ((m : ℝ)⁻¹ * Real.exp (C * C ^ 2) + C ^ 2 * 0 + C ^ 3 * b
        + Real.exp (C * C ^ 2) * Real.sqrt 0)
        = C * ((m : ℝ)⁻¹ * Real.exp (C ^ 3)) + C * (C ^ 3 * b) := by
      rw [e]
      simp
      ring
    rw [h3]
    linarith

end

end CERW.Support.Guards
