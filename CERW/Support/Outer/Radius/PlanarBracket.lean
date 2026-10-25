module

public import CERW.Support.Outer.Radius.HigherDimensionWidth

@[expose] public section

/-!
# Planar Bracket

The planar bracket sum is bounded from the occupation counts and cone estimate. These bounds control
the error in the potential approximation.
The section label `sec:outer-planar`
refers to the earlier source `paper/limit-shapes.tex`.
-/

universe u

open MeasureTheory Filter Topology ProbabilityTheory
open scoped symmDiff Pointwise NNReal
open LatticeProb (Site euclidNorm)

namespace CERW.Support.Outer.Radius

open CERW.Support.Statements CERW

variable {d : ℕ}

section

open Filter LatticeProb

/-- `r_n³ = 3 n / (4 ε ω₂)` in the plane. -/
lemma pl_radius_cube {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    radius 2 ε n ^ 3 = 3 / (4 * ε * unitBallVolume 2) * n := by
  have hω := unitBallVolume_pos 2
  have hx : 0 ≤ (((2 : ℕ) : ℝ) + 1) * n / (2 * ((2 : ℕ) : ℝ) * ε * unitBallVolume 2) := by
    positivity
  rw [radius, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num
  ring

/-- For large `n`: `16 ≤ n`, `4 ≤ log n`, `(log n)^5 ≤ η r_n` and `r_n ≤ n/8`. -/
lemma pl_eventually {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 16 ≤ (n : ℝ) ∧ 4 ≤ Real.log n ∧
      Real.log n ^ 5 ≤ η * radius 2 ε n ∧ radius 2 ε n ≤ n / 8 := by
  have hω := unitBallVolume_pos 2
  set c : ℝ := 3 / (4 * ε * unitBallVolume 2) with hc_def
  have hc : 0 < c := by positivity
  have h1 : ∀ᶠ n : ℕ in atTop, (16 + 512 * c : ℝ) ≤ n :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have h2 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  have h3 : ∀ᶠ n : ℕ in atTop, Real.log n ^ 15 / (1 * (n : ℝ) + 0) < η ^ 3 * c :=
    ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 15 one_ne_zero).comp
      tendsto_natCast_atTop_atTop).eventually_lt_const (by positivity)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨hn1, hn2, hn3⟩ := hn₀ n hn
  have hr3 := pl_radius_cube hε n
  have hr0 : 0 ≤ radius 2 ε n := Real.rpow_nonneg (by positivity) _
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog0 : 0 ≤ Real.log n := by linarith
  refine ⟨by linarith, hn2, ?_, ?_⟩
  · have h15 : Real.log n ^ 15 ≤ η ^ 3 * c * n := by
      rw [one_mul, add_zero, div_lt_iff₀ hnpos] at hn3
      exact hn3.le
    rw [← pow_le_pow_iff_left₀ (pow_nonneg hlog0 5) (by positivity) three_ne_zero]
    calc (Real.log n ^ 5) ^ 3 = Real.log n ^ 15 := by ring
      _ ≤ η ^ 3 * c * n := h15
      _ = (η * radius 2 ε n) ^ 3 := by rw [mul_pow, hr3]; ring
  · rw [← pow_le_pow_iff_left₀ hr0 (by positivity) three_ne_zero, hr3]
    have h512 : 512 * c ≤ (n : ℝ) ^ 2 := by nlinarith
    calc c * n = (512 * c) * n / 512 := by ring
      _ ≤ (n : ℝ) ^ 2 * n / 512 := by gcongr
      _ = ((n : ℝ) / 8) ^ 3 := by ring

/-- `a (1 + a)^{-2} ≤ (1 + a)^{-1}` for `a ≥ 0`. -/
lemma pl_mul_rpow_neg_two_le {a : ℝ} (ha : 0 ≤ a) :
    a * (1 + a) ^ (-2 : ℝ) ≤ (1 + a) ^ (-1 : ℝ) := by
  have h1 : 0 < 1 + a := by linarith
  have hk : 0 ≤ (1 + a) ^ (-2 : ℝ) := Real.rpow_nonneg h1.le _
  calc a * (1 + a) ^ (-2 : ℝ) ≤ (1 + a) * (1 + a) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hk
    _ = (1 + a) ^ (1 : ℝ) * (1 + a) ^ (-2 : ℝ) := by rw [Real.rpow_one]
    _ = (1 + a) ^ (-1 : ℝ) := by rw [← Real.rpow_add h1]; norm_num

/-- The bracket sum at `x` from a bound `ℓ_n(z) ≤ c |z - x| + A` on the local times, the
packing bound and the logarithmic lattice sum: `W_x ≤ K (c (2ρ + 1) + A log(R + 2))`. -/
lemma pl_braSum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (x : Site 2) (c A ρ R : ℝ), 0 ≤ c → 0 ≤ A →
      0 ≤ ρ → 1 ≤ R → departureRange Y n ⊆ ballFinset 2 ρ →
      (∀ z ∈ departureRange Y n, euclidNorm (z - x) ≤ R) →
      (∀ z ∈ departureRange Y n, (localTime Y n z : ℝ) ≤ c * euclidNorm (z - x) + A) →
      braSum Y n x ≤ K * (c * (2 * ρ + 1) + A * Real.log (R + 2)) := by
  obtain ⟨Cp, hCp, hpack⟩ :=
    CERW.Generic.Lattice.sum_rpow_one_sub_le_card_rpow (d := 2) (by norm_num)
  obtain ⟨C₂, hC₂, hlog⟩ := CERW.Generic.Lattice.sum_finset_rpow_neg_le_log (d := 2) (by norm_num)
  refine ⟨Cp + C₂, by positivity, ?_⟩
  intro Y n x c A ρ R hc hA hρ hR hball hdist hloc
  set S := departureRange Y n with hS
  have hk : ∀ z : Site 2, 0 ≤ (1 + euclidNorm (z - x)) ^ (-2 : ℝ) :=
    fun z => Real.rpow_nonneg (by linarith [euclidNorm_nonneg (z - x)]) _
  have hbra : braSum Y n x =
      ∑ z ∈ S, (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) := by
    rw [braSum, CERW.Support.LocalTime.sum_range_eq_sum_localTime Y n
      (fun z => (1 + euclidNorm (z - x)) ^ (2 - 2 * ((2 : ℕ) : ℝ)))]
    norm_num [hS]
  have hterm : ∀ z ∈ S, (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) ≤
      c * (1 + euclidNorm (z - x)) ^ (1 - ((2 : ℕ) : ℝ)) +
        A * (1 + euclidNorm (z - x)) ^ (-((2 : ℕ) : ℝ)) := by
    intro z hz
    have h1 := pl_mul_rpow_neg_two_le (euclidNorm_nonneg (z - x))
    have e1 : (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 := by norm_num
    have e2 : -((2 : ℕ) : ℝ) = -2 := by norm_num
    rw [e1, e2]
    calc (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ)
        ≤ (c * euclidNorm (z - x) + A) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right (hloc z hz) (hk z)
      _ = c * (euclidNorm (z - x) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ)) +
            A * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) := by ring
      _ ≤ c * (1 + euclidNorm (z - x)) ^ (-1 : ℝ) + A * (1 + euclidNorm (z - x)) ^ (-2 : ℝ) := by
          gcongr
  have hcard : (S.card : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) ≤ 2 * ρ + 1 := by
    have h1 : (S.card : ℝ) ≤ (2 * ρ + 1) ^ 2 := by
      calc (S.card : ℝ) ≤ ((ballFinset 2 ρ).card : ℝ) := by exact_mod_cast Finset.card_le_card hball
        _ ≤ (2 * ρ + 1) ^ 2 := card_ballFinset_le 2 hρ
    calc (S.card : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) ≤ ((2 * ρ + 1) ^ 2) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by norm_num)
      _ = 2 * ρ + 1 := by
          rw [show (1 : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
            Real.sqrt_sq (by linarith)]
  have hsum1 := (hpack S x).trans (mul_le_mul_of_nonneg_left hcard hCp.le)
  have hsum2 := hlog S x R hR hdist
  have hL : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  rw [hbra]
  calc ∑ z ∈ S, (localTime Y n z : ℝ) * (1 + euclidNorm (z - x)) ^ (-2 : ℝ)
      ≤ ∑ z ∈ S, (c * (1 + euclidNorm (z - x)) ^ (1 - ((2 : ℕ) : ℝ)) +
        A * (1 + euclidNorm (z - x)) ^ (-((2 : ℕ) : ℝ))) := Finset.sum_le_sum hterm
    _ = c * ∑ z ∈ S, (1 + euclidNorm (z - x)) ^ (1 - ((2 : ℕ) : ℝ)) +
          A * ∑ z ∈ S, (1 + euclidNorm (z - x)) ^ (-((2 : ℕ) : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ c * (Cp * (2 * ρ + 1)) + A * (C₂ * Real.log (R + 2)) := by gcongr
    _ ≤ (Cp + C₂) * (c * (2 * ρ + 1) + A * Real.log (R + 2)) := by
        have h1 : 0 ≤ c * (2 * ρ + 1) := by positivity
        have h2 : 0 ≤ A * Real.log (R + 2) := mul_nonneg hA hL
        nlinarith

/-- Step 1 of `sec:outer-planar`: if `ℓ_n(z) ≤ 4ε (r - |z|)_+ + a₁` on the departure range and
`|b - r| ≤ a₂`, then for `b ≤ |x| ≤ 3n` the bracket sum satisfies
`W_x ≤ K (4ε (2ρ + 1) + (4ε a₂ + a₁) log(4n + 2))`. -/
lemma pl_braSum_le_of_cone {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y : ℕ → Site 2) (n : ℕ) (r b ρ a₁ a₂ : ℝ), 0 ≤ a₁ → 0 ≤ a₂ →
      0 ≤ ρ → (1 : ℝ) ≤ n → ρ ≤ n → departureRange Y n ⊆ ballFinset 2 ρ →
      (∀ z ∈ departureRange Y n,
        (localTime Y n z : ℝ) ≤ 4 * ε * max (r - euclidNorm z) 0 + a₁) →
      |b - r| ≤ a₂ → ∀ x : Site 2, b ≤ euclidNorm x → euclidNorm x ≤ 3 * n →
      braSum Y n x ≤
        K * (4 * ε * (2 * ρ + 1) + (4 * ε * a₂ + a₁) * Real.log (4 * n + 2)) := by
  obtain ⟨K, hK, hsum⟩ := pl_braSum_le
  refine ⟨K, hK, ?_⟩
  intro Y n r b ρ a₁ a₂ ha₁ ha₂ hρ hn hρn hball hloc hbr x hbx hx3
  refine hsum Y n x (4 * ε) (4 * ε * a₂ + a₁) ρ (4 * n) (by positivity) (by positivity) hρ
    (by linarith) hball ?_ ?_
  · intro z hz
    have hz' : euclidNorm z ≤ ρ := mem_ballFinset_iff.mp (hball hz)
    have h1 : euclidNorm (z - x) ≤ euclidNorm z + euclidNorm x := by
      have := CERW.Support.Occupation.euclidNorm_add_le z (-x)
      rwa [← sub_eq_add_neg, CERW.Generic.Lattice.euclidNorm_neg] at this
    linarith
  · intro z hz
    have h1 := CERW.Support.Contact.max_sub_euclidNorm_le (x := z) (z := x) hbx
    have h2 : max (r - euclidNorm z) 0 ≤ euclidNorm (z - x) + a₂ := by
      refine max_le ?_ (by linarith [euclidNorm_nonneg (z - x)])
      have := le_max_left (b - euclidNorm z) 0
      linarith [(abs_le.mp hbr).1]
    calc (localTime Y n z : ℝ) ≤ 4 * ε * max (r - euclidNorm z) 0 + a₁ := hloc z hz
      _ ≤ 4 * ε * (euclidNorm (z - x) + a₂) + a₁ := by gcongr
      _ = 4 * ε * euclidNorm (z - x) + (4 * ε * a₂ + a₁) := by ring

/-- From `W ≤ K r`, `L ≤ 2 lg` and `lg ≤ √(r lg)`, the martingale error `C₁ (√(W L) + L)` is at
most `|C₁| (√(2K) + 2) √(r lg)`. -/
lemma pl_err_le {C₁ K W L r lg : ℝ} (hK : 0 ≤ K) (hW : W ≤ K * r) (hL0 : 0 ≤ L)
    (hL : L ≤ 2 * lg) (hlg : lg ≤ Real.sqrt (r * lg)) (hr : 0 ≤ r) :
    C₁ * (Real.sqrt (W * L) + L) ≤ |C₁| * (Real.sqrt (2 * K) + 2) * Real.sqrt (r * lg) := by
  have hlg0 : 0 ≤ lg := by linarith
  have h1 : Real.sqrt (W * L) ≤ Real.sqrt (2 * K) * Real.sqrt (r * lg) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    calc W * L ≤ (K * r) * (2 * lg) := mul_le_mul hW hL hL0 (by positivity)
      _ = 2 * K * (r * lg) := by ring
  have h2 : 0 ≤ Real.sqrt (W * L) + L := by positivity
  calc C₁ * (Real.sqrt (W * L) + L) ≤ |C₁| * (Real.sqrt (W * L) + L) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) h2
    _ ≤ |C₁| * (Real.sqrt (2 * K) * Real.sqrt (r * lg) + 2 * Real.sqrt (r * lg)) := by
        gcongr
        linarith
    _ = |C₁| * (Real.sqrt (2 * K) + 2) * Real.sqrt (r * lg) := by ring

end

end CERW.Support.Outer.Radius
