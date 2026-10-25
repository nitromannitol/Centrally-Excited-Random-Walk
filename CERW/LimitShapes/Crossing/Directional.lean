module

public import CERW.Support.Norm.OuterCrossing

@[expose] public section

/-!
# Directional crossings before a fixed horizon

The level-count contraction and the final excursion argument use the logarithm
of a terminal horizon. The elapsed path time may be any earlier integer.
-/

open LatticeProb (Site euclidNorm)

namespace CERW.LimitShapes.Crossing.Directional

open CERW
open private half_le_log norm_toSpace_le_index aboveCount aboveCount_anti
  level_inequality recurrence_step exists_small_level final_arithmetic top_bound
  sqrt_crossing_bound from CERW.Support.Norm.OuterCrossing

/-- The directional crossing estimate uses the terminal horizon's logarithm while
counting departures and occupation times only through the current path time. -/
theorem directional_crossing {d : ℕ} (hd : 1 ≤ d) {ε α C₁ Λ : ℝ} (hε : 0 < ε) (hα : 0 < α)
    (hC₁ : 0 < C₁) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
      (∀ z i, ε * |ξ z i| ≤ 1 / (d : ℝ)) → ∀ N : ℕ, 2 ≤ N → ∀ n : ℕ, n ≤ N →
      ∀ q : EuclideanSpace ℝ (Fin d), ‖q‖ ≤ Λ →
      ∀ x : ℕ → Site d, x 0 = 0 → (∀ j, x (j + 1) - x j ∈ unitSteps d) →
      (∀ s t : ℕ, s < t → t ≤ n → ‖(toSpace (x t) + ε • ∑ j ∈ Finset.range t,
            if x j ∉ departureRange x j then ξ (x j) else 0) -
          (toSpace (x s) + ε • ∑ j ∈ Finset.range s,
            if x j ∉ departureRange x j then ξ (x j) else 0)‖ ≤
        C₁ * Real.sqrt ((t - s : ℝ) * Real.log N)) →
      (∀ k : ℕ, k ≤ n →
        |dynkinMart (driftStepProb d ε ξ) (fun z => max (inner ℝ q (toSpace z) - k * Λ) 0) x n| ≤
          C₁ * (Real.sqrt (Real.log N * ∑ z ∈ (departureRange x n).filter
            (fun z => k * Λ - Λ < inner ℝ q (toSpace z)), (localTime x n z : ℝ)) +
              Real.log N)) →
      ∀ j₀ : ℕ, j₀ ≤ n → ∀ h : ℝ, 0 < h →
      (∀ j ≤ n, inner ℝ q (toSpace (x j₀)) - h < inner ℝ q (toSpace (x j)) →
        α ≤ inner ℝ q (ξ (x j))) →
      ∀ b : ℝ, 0 ≤ b →
        inner ℝ q (toSpace (x j₀)) ≤ max (inner ℝ q (toSpace (x j₀)) - h) b +
          C * (1 + ((((departureRange x n).filter
            (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) : ℕ) : ℝ)) *
              Real.log N := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Λ / (ε * α) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = C₁ / (ε * α) := ⟨_, rfl⟩
  have hεα : 0 < ε * α := mul_pos hε hα
  have hA : 0 < A := by rw [hAdef]; positivity
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : ℝ, K₁ = 2 * A + 4 := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂def⟩ : ∃ K₂ : ℝ, K₂ = B ^ 2 + 2 * B + 2 := ⟨_, rfl⟩
  have hK₁ : 0 < K₁ := by rw [hK₁def]; linarith
  have hK₂ : 0 < K₂ := by rw [hK₂def]; positivity
  refine ⟨4 * Λ + 2 * K₁ * Λ + Λ * C₁ * (K₂ + 1), by positivity, ?_⟩
  intro ξ hξ N hN n hnN q hq x hx0 hstep hZ hmart j₀ hj₀ h hh hα' b hb
  have hlg2 : 1 / 2 ≤ Real.log N := half_le_log hN
  have hlg0 : 0 ≤ Real.log N := by linarith
  -- the largest local time above `b`
  have hSloc : ∀ z ∈ departureRange x n, b ≤ inner ℝ q (toSpace z) → localTime x n z ≤
      ((departureRange x n).filter (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) :=
    fun z hz hbz => Finset.le_sup (f := localTime x n) (Finset.mem_filter.mpr ⟨hz, hbz⟩)
  generalize ((departureRange x n).filter
    (fun z => b ≤ inner ℝ q (toSpace z))).sup (localTime x n) = S at hSloc ⊢
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 1 + S := ⟨_, rfl⟩
  rw [← hLdef]
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hSL : (S : ℝ) ≤ L := by rw [hLdef]; linarith
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = inner ℝ q (toSpace (x j₀)) := ⟨_, rfl⟩
  rw [← hTdef] at hα' ⊢
  have hproj : ∀ j : ℕ, inner ℝ q (toSpace (x j)) ≤ Λ * j := fun j =>
    calc inner ℝ q (toSpace (x j)) ≤ ‖q‖ * ‖toSpace (x j)‖ := real_inner_le_norm _ _
      _ ≤ Λ * j := mul_le_mul hq (norm_toSpace_le_index x hx0 hstep j) (norm_nonneg _) hΛ.le
  -- the first level above `max {T - h, b + Λ}` on the grid `Λ ℕ`
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = max (T - h) (b + Λ) := ⟨_, rfl⟩
  have hTm : T - h ≤ m := hmdef ▸ le_max_left _ _
  have hbm : b + Λ ≤ m := hmdef ▸ le_max_right _ _
  have hmax : m ≤ max (T - h) b + Λ := by
    rw [hmdef]
    exact max_le (by linarith [le_max_left (T - h) b]) (by linarith [le_max_right (T - h) b])
  obtain ⟨k₀, hk₀def⟩ : ∃ k₀ : ℕ, k₀ = ⌈m / Λ⌉₊ := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = k₀ * Λ := ⟨_, rfl⟩
  have hma₀ : m ≤ a₀ := by
    have := Nat.le_ceil (m / Λ)
    rw [← hk₀def, div_le_iff₀ hΛ] at this
    rwa [ha₀]
  have ha₀m : a₀ < m + Λ := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ m / Λ from div_nonneg (by linarith) hΛ.le)
    rw [← hk₀def] at h1
    have h2 := mul_lt_mul_of_pos_right h1 hΛ
    rw [add_mul, div_mul_cancel₀ _ hΛ.ne', one_mul] at h2
    rwa [ha₀]
  have ha₀nn : 0 ≤ a₀ := by linarith
  -- the number of sites above the levels `a₀ - Λ + 2 i Λ`
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ i : ℕ,
      u i = (aboveCount q x n (a₀ - Λ + 2 * i * Λ) : ℝ) := ⟨fun i => _, fun i => rfl⟩
  have hu0 : ∀ i, 0 ≤ u i := fun i => by rw [hu]; exact Nat.cast_nonneg _
  have hun : u 0 ≤ n := by
    rw [hu]
    have h1 : aboveCount q x n (a₀ - Λ + 2 * ((0 : ℕ) : ℝ) * Λ) ≤ n :=
      (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp))
    exact_mod_cast h1
  have hu_anti : ∀ i, u (i + 1) ≤ u i := fun i => by
    rw [hu, hu]
    refine Nat.cast_le.mpr (aboveCount_anti q x n ?_)
    push_cast
    linarith
  have hrec : ∀ i : ℕ, u (i + 1) ≤
      A * L * (u i - u (i + 1)) + B * Real.sqrt (L * u i * Real.log N) + B * Real.log N := by
    intro i
    have hlo : a₀ ≤ ((k₀ + 2 * i : ℕ) : ℝ) * Λ := by
      push_cast
      rw [ha₀]
      have : 0 ≤ 2 * (i : ℝ) * Λ := by positivity
      linarith
    have hul : a₀ - Λ + 2 * (i : ℝ) * Λ = ((k₀ + 2 * i : ℕ) : ℝ) * Λ - Λ := by
      push_cast
      rw [ha₀]
      ring
    have huh : a₀ - Λ + 2 * ((i + 1 : ℕ) : ℝ) * Λ = ((k₀ + 2 * i : ℕ) : ℝ) * Λ + Λ := by
      push_cast
      rw [ha₀]
      ring
    by_cases hk : k₀ + 2 * i ≤ n
    · have hlev := level_inequality hd hε hα hΛ hlg0 hC₁.le hξ hq x hx0 n
        (a := ((k₀ + 2 * i : ℕ) : ℝ) * Λ) (by positivity) (S := S)
        (fun z hz hzq => hSloc z hz (by linarith))
        (fun j hj hjq => hα' j hj.le (by linarith)) (hmart _ hk)
      rw [← hul, ← huh, ← hu, ← hu] at hlev
      exact recurrence_step hεα hΛ hlg0 hC₁.le hSL (hu0 i) (hu_anti i) hAdef hBdef hlev
    · have hzero : u i = 0 := by
        rw [hu, hul]
        have : aboveCount q x n (((k₀ + 2 * i : ℕ) : ℝ) * Λ - Λ) = 0 := by
          refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun z hz => ?_)
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
          rw [Finset.mem_range] at hj
          rw [not_lt]
          refine (hproj j).trans ?_
          have h1 : (n : ℝ) ≤ ((k₀ + 2 * i : ℕ) : ℝ) - 1 := by
            have : n + 1 ≤ k₀ + 2 * i := by omega
            have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((k₀ + 2 * i : ℕ) : ℝ) := Nat.cast_le.mpr this
            linarith [(Nat.cast_add_one n : ((n + 1 : ℕ) : ℝ) = n + 1)]
          have h2 : (j : ℝ) ≤ n := by exact_mod_cast hj.le
          have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) hΛ.le
          linarith
        rw [this]
        simp
      have hzero' : u (i + 1) = 0 := le_antisymm (hzero ▸ hu_anti i) (hu0 _)
      rw [hzero, hzero']
      simp only [sub_self, mul_zero, zero_mul, Real.sqrt_zero, zero_add]
      exact mul_nonneg hB hlg0
  -- the level at which few sites remain
  obtain ⟨k, hk1, hkK, hukK⟩ := exists_small_level hA hB hL1 hN u hu0
    (hun.trans (Nat.cast_le.mpr hnN)) hrec
  rw [← hK₁def] at hkK
  rw [← hK₂def] at hukK
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hbar : a₀ + Λ ≤ a₀ - Λ + 2 * (k : ℝ) * Λ := by
    have := mul_nonneg (sub_nonneg.mpr hk1') hΛ.le
    linarith
  have hL0 : 0 ≤ L := by linarith
  by_cases hcase : T ≤ a₀ - Λ + 2 * (k : ℝ) * Λ + Λ
  · refine final_arithmetic (Y := 0) hΛ hC₁.le hL1 hlg2 hmax ha₀m hkK ?_ ?_
    · exact mul_nonneg (by linarith) (mul_nonneg hL0 hlg0)
    · rw [mul_zero, mul_zero, add_zero]
      exact hcase
  · have htop := top_bound hε.le ξ hΛ hq x hx0 hstep hC₁.le hlg0 hZ hj₀
      (ā := a₀ - Λ + 2 * (k : ℝ) * Λ) (by linarith)
      (by rw [← hTdef]; exact not_le.mp hcase)
      (fun j hj hjq _ => by
        have := hα' j (by omega) (by linarith)
        linarith)
      (S := S) (fun z hz hzq => hSloc z hz (by linarith))
    rw [← hTdef] at htop
    have hukS : (aboveCount q x n (a₀ - Λ + 2 * (k : ℝ) * Λ) : ℝ) ≤ K₂ * (L * Real.log N) := by
      rw [← hu k]
      linarith
    exact final_arithmetic hΛ hC₁.le hL1 hlg2 hmax ha₀m hkK
      (sqrt_crossing_bound hSL hS0 (Nat.cast_nonneg _) hlg0 hK₂.le hukS) htop


end CERW.LimitShapes.Crossing.Directional
