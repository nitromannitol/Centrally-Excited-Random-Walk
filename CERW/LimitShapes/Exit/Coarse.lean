module

public import CERW.LimitShapes.Exit.CoarseProbability

@[expose] public section

/-!
# Coarse bounds from two-sided exit estimates

Proposition `prop:coarse` follows conditionally from a two-sided exit-time estimate
with a uniform bound on local times at the exit. The exit estimate is an explicit input.
-/

universe u

namespace CERW.LimitShapes.Exit

open CERW LatticeProb MeasureTheory
open CERW.Support.Norm.CoarseVolume

/-- The two-sided exit estimate implies all six bounds of Proposition `prop:coarse`. -/
theorem norm_coarse_bounds_of_exit
    (hexit : ∀ {d : ℕ} (_hd : 2 ≤ d)
      (Ψ : EuclideanSpace ℝ (Fin d) → ℝ), CERW.IsNorm Ψ →
      ∀ ε : ℝ, 0 < ε → (∀ i : Fin d, ε * Ψ (CERW.coordVec i) < 1 / (d : ℝ)) →
      ∀ p : ℝ, 0 < p → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ ξ : Site d → EuclideanSpace ℝ (Fin d),
        (∀ x : Site d, x ≠ 0 → CERW.IsSubgradient Ψ (CERW.toSpace x) (ξ x)) → ξ 0 = 0 →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → Site d), CERW.IsDriftCERW μ ε ξ X →
      ∀ R : ℝ, R₀ ≤ R →
        μ {ω | ¬ ∃ τ : ℕ,
          c * R ^ (d + 1) ≤ (τ : ℝ) ∧ (τ : ℝ) ≤ C * R ^ (d + 1) ∧
          R ≤ Ψ (CERW.toSpace (X τ ω)) ∧
          (∀ j : ℕ, j < τ → Ψ (CERW.toSpace (X j ω)) < R) ∧
          (∀ y : Site d, (CERW.localTime (X · ω) τ y : ℝ) ≤ C * R)} ≤
            ENNReal.ofReal (C * R ^ (-p))) :
    CERW.Support.Statements.norm_coarse_bounds.{u} := by
  intro d hd Ψ hΨ ε hε hcoord
  dsimp only
  intro p hp
  have hd1 : 1 ≤ d := by omega
  have hV : 0 < normBallVolume Ψ :=
    CERW.Support.Norm.ContactAssembly.normBallVolume_pos' hd1 hΨ
  have hm : 0 < normMin Ψ := (Generic.Norm.normMin_pos_mul_le hΨ hd1).1
  let κ := 2 * d * ε * normBallVolume Ψ / (d + 1)
  have hκ : 0 < κ := by
    dsimp [κ]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  let q := ((d : ℝ) + 1) * p
  have hq : 0 < q := mul_pos (by positivity) hp
  obtain ⟨ce, Ce, hce, hCe, R₀, hR₀, he⟩ := hexit hd Ψ hΨ ε hε hcoord q hq
  let A := κ / ce + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let H := A / normMin Ψ
  let L := Ce * A
  have hH : 0 < H := div_pos hA hm
  have hL : 0 < L := mul_pos hCe hA
  obtain ⟨c, C₀, T, hc, hC₀, hT, hdet⟩ := exists_coarse_constants hd1 hκ hH hL
  let K := max T (R₀ / A)
  have hK : 0 < K := hT.trans_le (le_max_left _ _)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_le_coarseScale hd1 hε hV hK)
  let B := Ce * (A ^ (-q) * κ ^ p)
  have hB : 0 < B := by dsimp [B]; positivity
  let C := C₀ + B + (N : ℝ) ^ p
  have hNpow : 0 ≤ (N : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨c, C, hc, hC, ?_⟩
  intro ξ hξ hξ0 Ω _ μ _ X hX n hn
  change μ {ω | ¬ CoarseBounds c C (coarseScale Ψ ε n) (X · ω) n} ≤
    ENNReal.ofReal (C * (n : ℝ) ^ (-p))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < coarseScale Ψ ε n := coarseScale_pos hd1 hε hV (by omega)
  have ht : (n : ℝ) = κ * coarseScale Ψ ε n ^ (d + 1) :=
    nat_eq_coarseScale_pow hd1 hε hV n
  by_cases hNn : N ≤ n
  · have hKr := hN n hNn
    have hTr : T ≤ coarseScale Ψ ε n := (le_max_left _ _).trans hKr
    have hR : R₀ ≤ A * coarseScale Ψ ε n := by
      have hb := (le_max_right T (R₀ / A)).trans hKr
      have hb' := (div_le_iff₀ hA).mp hb
      simpa only [mul_comm] using hb'
    have htime : (n : ℝ) < ce * (A * coarseScale Ψ ε n) ^ (d + 1) := by
      rw [ht]
      exact time_lt_exit_scale hκ hce hr
    have hsub : {ω | ¬ CoarseBounds c C (coarseScale Ψ ε n) (X · ω) n} ⊆
        {ω | ¬ ∃ τ : ℕ,
          ce * (A * coarseScale Ψ ε n) ^ (d + 1) ≤ (τ : ℝ) ∧
          (τ : ℝ) ≤ Ce * (A * coarseScale Ψ ε n) ^ (d + 1) ∧
          A * coarseScale Ψ ε n ≤ Ψ (toSpace (X τ ω)) ∧
          (∀ j : ℕ, j < τ → Ψ (toSpace (X j ω)) < A * coarseScale Ψ ε n) ∧
          (∀ y : Site d, (localTime (X · ω) τ y : ℝ) ≤
            Ce * (A * coarseScale Ψ ε n))} := by
      intro ω hbad hgood
      obtain ⟨τ, hτ, _, _, hi, hl⟩ := hgood
      obtain ⟨hh, hm'⟩ := maxima_le_of_exit hd1 hΨ (X · ω) htime hτ hi hl
      have hh' : maxRadius (X · ω) n ≤ H * coarseScale Ψ ε n := by
        simpa only [H, mul_div_right_comm] using hh
      have hm'' : (maxLocalTime (X · ω) n : ℝ) ≤ L * coarseScale Ψ ε n := by
        simpa only [L, mul_assoc] using hm'
      exact hbad (coarseBounds_mono hC₀C hr.le
        (hdet (X · ω) n _ hTr ht hh' hm''))
    have hevent := (measure_mono hsub).trans (he ξ hξ hξ0 μ X hX _ hR)
    have htail : Ce * (A * coarseScale Ψ ε n) ^ (-q) = B * (n : ℝ) ^ (-p) := by
      rw [exit_tail_scale hκ hA hr p, ← ht]
      exact (mul_assoc _ _ _).symm
    rw [htail] at hevent
    exact hevent.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg hnpos.le _)))
  · apply prob_le_one.trans
    rw [ENNReal.one_le_ofReal]
    have hpow : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hnpos p
    have hle : (n : ℝ) ^ p ≤ (N : ℝ) ^ p :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast (by omega : n ≤ N)) hp.le
    rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, le_div_iff₀ hpow, one_mul]
    dsimp [C]
    linarith

end CERW.LimitShapes.Exit
